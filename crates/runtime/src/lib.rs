use mlua::{BorrowedBytes, BorrowedStr, ErrorContext, Lua, UserDataMethods, Value};
use std::alloc;
use std::mem;
use std::num::NonZeroU32;
use std::sync::LazyLock;
use wit_dylib_ffi::{
    Enum, Flags, Function, Future, Interpreter, List, Record, Resource, Stream, Tuple, Type,
    Variant, Wit, WitOption, WitResult,
};

struct LuaWit;

wit_dylib_ffi::export!(LuaWit);

#[derive(Default)]
struct State {
    lua: Lua,
}

fn state() -> &'static State {
    static mut STATE: LazyLock<State> = LazyLock::new(State::default);
    unsafe { &*STATE }
}

fn lua() -> &'static Lua {
    &state().lua
}

struct LuaResource {
    ty: Resource,
    handle: Option<NonZeroU32>,
}

impl LuaResource {
    fn drop_now(&mut self) {
        if let Some(handle) = self.handle.take() {
            unsafe {
                self.ty.drop()(handle.get());
            }
        }
    }
}

impl mlua::UserData for LuaResource {
    fn add_methods<M: UserDataMethods<Self>>(methods: &mut M) {
        methods.add_method_mut("drop", |_, this, ()| {
            this.drop_now();
            Ok(())
        });
    }
}

impl Drop for LuaResource {
    fn drop(&mut self) {
        self.drop_now();
    }
}

impl State {
    fn initialize(&self, wit: Wit) -> mlua::Result<()> {
        let imports = self.lua.create_table()?;
        for (i, func) in wit.iter_funcs().enumerate() {
            if !func.is_import() {
                continue;
            }
            let func = mlua::Function::wrap(Import { func });
            imports.set(format!("import{i}"), func)?;
        }

        // TODO: define imports in a `require`-able module
        // TODO: define enums as `Foo = { Name = 1, Other = 2 }`
        // TODO: define flags as `Foo = { Name = 1<<0, Other = 1<<1 }`

        self.lua.register_module("componentize_lua", imports)?;

        let file = std::fs::read_to_string("main.lua").expect("failed to read `main.lua`");
        self.lua.load(&file).exec()?;
        Ok(())
    }

    fn call_export(&self, _wit: Wit, func: Function, cx: &mut Call<'_>) -> mlua::Result<()> {
        let globals = self.lua.globals();
        let lua_func: mlua::Function = globals
            .get(func.name())
            .with_context(|_| format!("failed to lookup export {:?}", func.name()))?;
        let ret: Value = lua_func.call(mlua::Variadic::from(mem::take(&mut cx.stack)))?;
        match func.result() {
            Some(ty) => {
                typecheck(&self.lua, &ret, ty)?;
                cx.stack.push(ret);
            }
            None => assert_eq!(ret, Value::Nil),
        }
        Ok(())
    }
}

struct Import {
    func: Function,
}

impl mlua::LuaNativeFn<mlua::Variadic<Value>> for Import {
    type Output = mlua::Result<Value>;

    fn call(&self, args: mlua::Variadic<Value>) -> mlua::Result<Value> {
        let mut stack = Call::default();
        let lua = lua();
        for (i, param) in self.func.params().enumerate() {
            let arg = match args.get(i) {
                Some(arg) => arg,
                None => return Err(mlua::Error::runtime("not enough arguments provided")),
            };
            typecheck(lua, arg, param)?;
            stack.stack.push(arg.clone())
        }
        stack.stack.reverse();

        self.func.call_import_sync(&mut stack);
        if self.func.result().is_some() {
            Ok(stack.stack.pop().unwrap())
        } else {
            Ok(Value::Nil)
        }
    }
}

fn typecheck(lua: &Lua, val: &Value, ty: Type) -> mlua::Result<()> {
    match ty {
        Type::Alias(ty) => typecheck(lua, val, ty.ty())?,
        Type::U8 => drop(lua.convert::<u8>(val)?),
        Type::S8 => drop(lua.convert::<i8>(val)?),
        Type::U16 => drop(lua.convert::<u16>(val)?),
        Type::S16 => drop(lua.convert::<i16>(val)?),
        Type::U32 => drop(lua.convert::<u32>(val)?),
        Type::S32 => drop(lua.convert::<i32>(val)?),
        Type::U64 => drop(lua.convert::<u64>(val)?),
        Type::S64 => drop(lua.convert::<i64>(val)?),
        Type::F32 => drop(lua.convert::<f32>(val)?),
        Type::F64 => drop(lua.convert::<f64>(val)?),
        Type::Bool => drop(lua.convert::<bool>(val)?),
        Type::Char => drop(lua.convert::<char>(val)?),
        Type::String => drop(lua.convert::<BorrowedStr<'_>>(val)?),
        Type::List(ty) => {
            if ty.ty() == Type::U8 {
                lua.convert::<BorrowedBytes<'_>>(val)?;
            } else {
                let table = lua.convert::<mlua::Table>(val)?;
                for val in table.sequence_values() {
                    typecheck(lua, &val?, ty.ty())?;
                }
            }
        }
        Type::Tuple(ty) => {
            let table = lua.convert::<mlua::Table>(val)?;
            if table.raw_len() != ty.types().len() {
                return Err(mlua::Error::runtime("wrong number of tuple fields"));
            }
            for (value, ty) in table.sequence_values().zip(ty.types()) {
                typecheck(lua, &value?, ty)?;
            }
        }
        Type::Record(ty) => {
            let table = lua.convert::<mlua::Table>(val)?;
            for (name, ty) in ty.fields() {
                let value = table.get(name)?;
                typecheck(lua, &value, ty)?;
            }
        }
        Type::Enum(ty) => {
            let val = lua.convert::<usize>(val)?;
            if val == 0 || val > ty.names().len() {
                return Err(mlua::Error::runtime("invalid enum discriminant"));
            }
        }
        Type::Flags(ty) => {
            let val = lua.convert::<u32>(val)?;
            let mask = 1 << ty.names().len() - 1;
            if val & mask != 0 {
                return Err(mlua::Error::runtime("invalid flags value"));
            }
        }
        Type::Option(ty) => LuaVariant::from(ty).typecheck(lua, val)?,
        Type::Result(ty) => LuaVariant::from(ty).typecheck(lua, val)?,
        Type::Variant(ty) => LuaVariant::from(ty).typecheck(lua, val)?,
        Type::Own(ty) | Type::Borrow(ty) => {
            let data = lua.convert::<mlua::AnyUserData>(val)?;
            let import = data.borrow::<LuaResource>()?;
            if import.ty != ty {
                return Err(mlua::Error::runtime("wrong resource type"));
            }
            if import.handle.is_none() {
                return Err(mlua::Error::runtime("resource already taken"));
            }
        }

        Type::FixedSizeList(_ty) => todo!(),
        Type::ErrorContext => todo!(),
        Type::Future(_ty) => todo!(),
        Type::Stream(_ty) => todo!(),
    }
    Ok(())
}

#[derive(Default)]
struct Call<'a> {
    stack: Vec<Value>,
    strings: Vec<BorrowedStr<'a>>,
    bytes: Vec<BorrowedBytes<'a>>,
    iter_points: Vec<usize>,
    deferred_deallocs: Vec<DeferredDealloc>,
    resource_borrows_to_drop: Vec<Value>,
}

impl Drop for Call<'_> {
    fn drop(&mut self) {
        let lua = lua();
        for val in self.resource_borrows_to_drop.drain(..) {
            let data = lua.convert::<mlua::AnyUserData>(val).unwrap();
            data.borrow_mut::<LuaResource>().unwrap().drop_now();
        }
    }
}

impl Interpreter for LuaWit {
    type CallCx<'a> = Call<'a>;

    fn initialize(wit: Wit) {
        state().initialize(wit).expect("failed to initialize");
    }

    fn export_start<'a>(_: Wit, _: Function) -> Box<Self::CallCx<'a>> {
        Box::new(Call::default())
    }

    fn export_call(wit: Wit, func: Function, cx: &mut Self::CallCx<'_>) {
        if let Err(e) = state().call_export(wit, func, cx) {
            panic!("failed to call export: {e}");
        }
    }

    async fn export_call_async(wit: Wit, func: Function, cx: Box<Self::CallCx<'static>>) {
        let _ = (wit, func, cx);
        todo!()
    }

    fn resource_dtor(_: Resource, _: usize) {
        todo!()
    }
}

impl wit_dylib_ffi::Call for Call<'_> {
    unsafe fn defer_deallocate(&mut self, ptr: *mut u8, layout: alloc::Layout) {
        self.deferred_deallocs.push(DeferredDealloc { ptr, layout });
    }

    fn push_u8(&mut self, val: u8) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_u8(&mut self) -> u8 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_s8(&mut self, val: i8) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_s8(&mut self) -> i8 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_u16(&mut self, val: u16) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_u16(&mut self) -> u16 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_s16(&mut self, val: i16) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_s16(&mut self) -> i16 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_u32(&mut self, val: u32) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_u32(&mut self) -> u32 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_s32(&mut self, val: i32) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_s32(&mut self) -> i32 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_u64(&mut self, val: u64) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_u64(&mut self) -> u64 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_s64(&mut self, val: i64) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_s64(&mut self) -> i64 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_f32(&mut self, val: f32) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_f32(&mut self) -> f32 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_f64(&mut self, val: f64) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_f64(&mut self) -> f64 {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_char(&mut self, val: char) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_char(&mut self) -> char {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_bool(&mut self, val: bool) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_bool(&mut self) -> bool {
        lua().unpack(self.stack.pop().unwrap()).unwrap()
    }

    fn push_string(&mut self, val: String) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_string(&mut self) -> &str {
        let s = lua().unpack(self.stack.pop().unwrap()).unwrap();
        self.strings.push(s);
        self.strings.last().unwrap()
    }

    unsafe fn push_raw_list(&mut self, ty: List, ptr: *mut u8, len: usize) -> bool {
        if ty.ty() != Type::U8 {
            return false;
        }
        let val = unsafe { Vec::from_raw_parts(ptr, len, len) };
        self.stack.push(lua().convert(val).unwrap());
        true
    }

    fn push_list(&mut self, ty: List, len: usize) {
        assert!(ty.ty() != Type::U8);
        self.stack.push(Value::Table(
            lua().create_table_with_capacity(len, 0).unwrap(),
        ));
    }

    fn list_append(&mut self, ty: List) {
        assert!(ty.ty() != Type::U8);
        let val = self.stack.pop().unwrap();
        match self.stack.last_mut().unwrap() {
            Value::Table(table) => table.push(val).unwrap(),
            _ => unreachable!(),
        }
    }

    unsafe fn maybe_pop_list(&mut self, ty: List) -> Option<(*const u8, usize)> {
        if ty.ty() != Type::U8 {
            return None;
        }
        let bytes = lua().unpack(self.stack.pop().unwrap()).unwrap();
        self.bytes.push(bytes);
        let buf = self.bytes.last().unwrap();
        Some((buf.as_ptr(), buf.len()))
    }

    fn pop_list(&mut self, ty: List) -> usize {
        assert!(ty.ty() != Type::U8);
        self.iter_points.push(0);
        match self.stack.last().unwrap() {
            Value::Table(table) => table.raw_len(),
            _ => unreachable!(),
        }
    }

    fn pop_iter_next(&mut self, ty: List) {
        assert!(ty.ty() != Type::U8);
        let index = self.iter_points.last_mut().unwrap();
        *index += 1;
        match self.stack.last().unwrap() {
            Value::Table(table) => self.stack.push(table.raw_get(*index).unwrap()),
            _ => unreachable!(),
        }
    }

    fn pop_iter(&mut self, _: List) {
        self.iter_points.pop().unwrap();
        self.stack.pop().unwrap();
    }

    fn push_option(&mut self, ty: WitOption, is_some: bool) {
        self.push_lua_variant(if is_some { 1 } else { 0 }, ty.into())
    }

    fn pop_option(&mut self, ty: WitOption) -> u32 {
        self.pop_lua_variant(ty.into())
    }

    fn push_tuple(&mut self, ty: Tuple) {
        let len = self.stack.len();
        let table = lua()
            .create_sequence_from(self.stack.drain(len - ty.types().len()..len))
            .unwrap();
        self.stack.push(Value::Table(table));
    }

    fn pop_tuple(&mut self, _ty: Tuple) {
        let Value::Table(table) = self.stack.pop().unwrap() else {
            panic!()
        };
        let values = table
            .sequence_values()
            .map(|v| v.unwrap())
            .collect::<Vec<_>>();
        self.stack.extend(values.into_iter().rev())
    }

    fn pop_borrow(&mut self, ty: Resource) -> u32 {
        let val = self.stack.pop().unwrap();
        let data = lua().convert::<mlua::AnyUserData>(val).unwrap();
        let val = data.borrow::<LuaResource>().unwrap();
        assert_eq!(val.ty, ty);
        val.handle.unwrap().get()
    }

    fn push_borrow(&mut self, ty: Resource, handle: u32) {
        // TODO: if this is an exported resource, meaning there's a `new` ctor
        // available, then `handle` is a private representation and needs to be
        // handled differently.
        assert!(ty.new().is_none());

        let val = lua()
            .pack(LuaResource {
                ty,
                handle: Some(NonZeroU32::new(handle).unwrap()),
            })
            .unwrap();
        self.resource_borrows_to_drop.push(val.clone());
        self.stack.push(val);
    }

    fn pop_own(&mut self, ty: Resource) -> u32 {
        let val = self.stack.pop().unwrap();
        let data = lua().convert::<mlua::AnyUserData>(val).unwrap();
        let mut val = data.borrow_mut::<LuaResource>().unwrap();
        assert_eq!(val.ty, ty);
        val.handle.take().unwrap().get()
    }

    fn push_own(&mut self, ty: Resource, handle: u32) {
        let val = lua()
            .pack(LuaResource {
                ty,
                handle: Some(NonZeroU32::new(handle).unwrap()),
            })
            .unwrap();
        self.stack.push(val);
    }

    fn pop_enum(&mut self, _: Enum) -> u32 {
        lua().unpack::<u32>(self.stack.pop().unwrap()).unwrap() - 1
    }

    fn push_enum(&mut self, _: Enum, val: u32) {
        self.stack.push(lua().convert(val + 1).unwrap());
    }

    fn pop_flags(&mut self, _: Flags) -> u32 {
        lua().unpack::<u32>(self.stack.pop().unwrap()).unwrap()
    }

    fn push_flags(&mut self, _: Flags, val: u32) {
        self.stack.push(lua().convert(val).unwrap());
    }

    fn pop_record(&mut self, ty: Record) {
        let Value::Table(table) = self.stack.pop().unwrap() else {
            panic!()
        };
        for (name, _ty) in ty.fields().collect::<Vec<_>>().iter().rev() {
            let val = table.get(*name).unwrap();
            self.stack.push(val);
        }
    }

    fn push_record(&mut self, ty: Record) {
        let len = self.stack.len();
        let table = lua()
            .create_table_from(
                self.stack
                    .drain(len - ty.fields().len()..len)
                    .zip(ty.fields())
                    .map(|(val, (name, _ty))| (name, val)),
            )
            .unwrap();
        self.stack.push(Value::Table(table));
    }

    fn pop_variant(&mut self, ty: Variant) -> u32 {
        self.pop_lua_variant(ty.into())
    }

    fn push_variant(&mut self, ty: Variant, case: u32) {
        self.push_lua_variant(case, ty.into())
    }

    fn push_result(&mut self, ty: WitResult, is_err: bool) {
        self.push_lua_variant(if is_err { 1 } else { 0 }, ty.into())
    }

    fn pop_result(&mut self, ty: WitResult) -> u32 {
        self.pop_lua_variant(ty.into())
    }

    fn pop_future(&mut self, _: Future) -> u32 {
        todo!()
    }

    fn pop_stream(&mut self, _: Stream) -> u32 {
        todo!()
    }

    fn push_future(&mut self, _: Future, _: u32) {
        todo!()
    }

    fn push_stream(&mut self, _: Stream, _: u32) {
        todo!()
    }
}

impl Call<'_> {
    fn push_lua_variant(&mut self, case: u32, ty: LuaVariant) {
        let lua = lua();

        match ty {
            LuaVariant::Nullable {
                null_discr,
                some_ty: _,
            } => {
                assert!(case == 0 || case == 1);
                if case == null_discr {
                    self.stack.push(Value::Nil);
                } else {
                    // nothing to do, the value's on the top of the stack and it's
                    // already in its `some(val)` form as-is.
                }
            }
            LuaVariant::Payload(payload) => {
                if payload[case as usize] == LuaType::Nil {
                    self.stack.push(Value::Nil);
                } else {
                    // nothing to do, the value's on the top of the stack and
                    // it's already in its variant form.
                }
            }
            LuaVariant::Fallback(variants) => {
                let (name, ty) = variants[case as usize];
                let table = lua.create_table().unwrap();
                table.set("tag", name).unwrap();
                if ty.is_some() {
                    table.set("val", self.stack.pop().unwrap()).unwrap();
                }
                self.stack.push(Value::Table(table));
            }
        }
    }

    fn pop_lua_variant(&mut self, ty: LuaVariant) -> u32 {
        let lua = lua();
        let val = self.stack.pop().unwrap();
        match ty {
            LuaVariant::Nullable {
                null_discr,
                some_ty: _,
            } => match val {
                Value::Nil => null_discr,
                other => {
                    self.stack.push(other);
                    1 - null_discr
                }
            },
            LuaVariant::Payload(payloads) => {
                for (i, ty) in payloads.iter().enumerate() {
                    match (ty, &val) {
                        (LuaType::Nil, Value::Nil)
                        | (LuaType::Boolean, Value::Boolean(_))
                        | (LuaType::Number, Value::Number(_))
                        | (LuaType::String, Value::String(_))
                        | (LuaType::Table, Value::Table(_))
                        | (LuaType::UserData, Value::UserData(_))
                        | (LuaType::UserData, Value::LightUserData(_)) => {
                            return i as u32;
                        }

                        (LuaType::Nil, _)
                        | (LuaType::Boolean, _)
                        | (LuaType::Number, _)
                        | (LuaType::String, _)
                        | (LuaType::Table, _)
                        | (LuaType::UserData, _) => {}
                    }
                }
                unreachable!()
            }
            LuaVariant::Fallback(variants) => {
                let table = lua.convert::<mlua::Table>(val).unwrap();
                let name: String = table.get("tag").unwrap();
                for (i, (vname, vty)) in variants.iter().enumerate() {
                    if *vname == name {
                        if let Some(vty) = vty {
                            let vval = table.get("val").unwrap();
                            typecheck(lua, &vval, *vty).unwrap();
                            self.stack.push(vval);
                        }
                        return i as u32;
                    }
                }
                panic!("no variant case matched");
            }
        }
    }
}

enum LuaVariant {
    Nullable { null_discr: u32, some_ty: Type },
    Payload(Vec<LuaType>),
    Fallback(Vec<(&'static str, Option<Type>)>),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum LuaType {
    Nil,
    Boolean,
    Number,
    String,
    Table,
    UserData,
}

impl LuaVariant {
    fn classify(cases: impl IntoIterator<Item = (&'static str, Option<Type>)>) -> Self {
        let cases = cases.into_iter().collect::<Vec<_>>();
        match &cases[..] {
            [(_, None), (_, Some(ty))] if Self::nullable(*ty) => LuaVariant::Nullable {
                null_discr: 0,
                some_ty: *ty,
            },
            [(_, Some(ty)), (_, None)] if Self::nullable(*ty) => LuaVariant::Nullable {
                null_discr: 1,
                some_ty: *ty,
            },

            other => {
                let mut lua_types = Vec::new();
                let mut fallback = false;
                for (_name, ty) in other {
                    let bad = match ty {
                        Some(ty) => Self::already_used(*ty, &mut lua_types),
                        None => {
                            if lua_types.contains(&LuaType::Nil) {
                                true
                            } else {
                                lua_types.push(LuaType::Nil);
                                false
                            }
                        }
                    };
                    if bad {
                        fallback = true;
                        break;
                    }
                }

                if fallback {
                    LuaVariant::Fallback(cases)
                } else {
                    LuaVariant::Payload(lua_types)
                }
            }
        }
    }

    fn already_used(ty: Type, types: &mut Vec<LuaType>) -> bool {
        let lua_type = match ty {
            Type::Alias(ty) => return Self::already_used(ty.ty(), types),

            Type::U8
            | Type::S8
            | Type::U16
            | Type::S16
            | Type::U32
            | Type::S32
            | Type::U64
            | Type::S64
            | Type::F32
            | Type::F64
            | Type::Enum(_)
            | Type::Flags(_) => LuaType::Number,

            Type::Bool => LuaType::Boolean,

            Type::Char | Type::String => LuaType::String,

            Type::Future(_)
            | Type::Stream(_)
            | Type::ErrorContext
            | Type::Own(_)
            | Type::Borrow(_) => LuaType::UserData,

            Type::List(_) | Type::Record(_) | Type::Tuple(_) | Type::FixedSizeList(_) => {
                LuaType::Table
            }

            Type::Result(_) | Type::Variant(_) | Type::Option(_) => return true,
        };
        if types.contains(&lua_type) {
            return true;
        }
        types.push(lua_type);
        false
    }

    fn typecheck(&self, lua: &Lua, val: &Value) -> mlua::Result<()> {
        match self {
            LuaVariant::Nullable {
                null_discr: _,
                some_ty,
            } => match val {
                Value::Nil => Ok(()),
                other => typecheck(lua, other, *some_ty),
            },
            LuaVariant::Payload(payloads) => {
                for ty in payloads {
                    let ok = match (ty, val) {
                        (LuaType::Nil, Value::Nil)
                        | (LuaType::Boolean, Value::Boolean(_))
                        | (LuaType::Number, Value::Number(_))
                        | (LuaType::String, Value::String(_))
                        | (LuaType::Table, Value::Table(_))
                        | (LuaType::UserData, Value::UserData(_))
                        | (LuaType::UserData, Value::LightUserData(_)) => true,

                        (LuaType::Nil, _)
                        | (LuaType::Boolean, _)
                        | (LuaType::Number, _)
                        | (LuaType::String, _)
                        | (LuaType::Table, _)
                        | (LuaType::UserData, _) => false,
                    };
                    if ok {
                        return Ok(());
                    }
                }
                Err(mlua::Error::runtime(
                    "value does not match any payload type",
                ))
            }
            LuaVariant::Fallback(cases) => {
                let table = lua.convert::<mlua::Table>(val)?;
                let tag: BorrowedStr<'_> = table.get("tag")?;
                for (name, ty) in cases {
                    if tag == *name {
                        if let Some(ty) = ty {
                            let val = table.get("val")?;
                            typecheck(lua, &val, *ty)?;
                        }
                        return Ok(());
                    }
                }
                Err(mlua::Error::runtime("no variant case matched"))
            }
        }
    }

    fn nullable(ty: Type) -> bool {
        match ty {
            Type::Alias(ty) => Self::nullable(ty.ty()),

            Type::U8
            | Type::S8
            | Type::U16
            | Type::S16
            | Type::U32
            | Type::S32
            | Type::U64
            | Type::S64
            | Type::F32
            | Type::F64
            | Type::Bool
            | Type::Char
            | Type::String
            | Type::List(_)
            | Type::ErrorContext
            | Type::Record(_)
            | Type::Tuple(_)
            | Type::Enum(_)
            | Type::Flags(_)
            | Type::Future(_)
            | Type::Stream(_)
            | Type::FixedSizeList(_)
            | Type::Own(_)
            | Type::Borrow(_) => true,

            Type::Result(ty) => !LuaVariant::from(ty).may_be_nil(),
            Type::Variant(ty) => !LuaVariant::from(ty).may_be_nil(),
            Type::Option(ty) => !LuaVariant::from(ty).may_be_nil(),
        }
    }

    fn may_be_nil(&self) -> bool {
        match self {
            LuaVariant::Nullable { .. } => true,
            LuaVariant::Payload(payloads) => payloads.contains(&LuaType::Nil),
            LuaVariant::Fallback(_) => false,
        }
    }
}

impl From<WitOption> for LuaVariant {
    fn from(ty: WitOption) -> LuaVariant {
        LuaVariant::classify([("none", None), ("some", Some(ty.ty()))])
    }
}

impl From<WitResult> for LuaVariant {
    fn from(ty: WitResult) -> LuaVariant {
        LuaVariant::classify([("ok", ty.ok()), ("err", ty.err())])
    }
}

impl From<Variant> for LuaVariant {
    fn from(ty: Variant) -> LuaVariant {
        LuaVariant::classify(ty.cases())
    }
}

struct DeferredDealloc {
    ptr: *mut u8,
    layout: alloc::Layout,
}

impl Drop for DeferredDealloc {
    fn drop(&mut self) {
        unsafe { alloc::dealloc(self.ptr, self.layout) }
    }
}
