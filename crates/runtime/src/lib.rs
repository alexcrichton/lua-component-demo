use mlua::{BorrowedBytes, BorrowedStr, ErrorContext, Lua, Value};
use std::mem;
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

struct ResourceImport {
    ty: Resource,
    handle: u32,
}

impl mlua::UserData for ResourceImport {
    // TODO: name method? interface method?
}

impl Drop for ResourceImport {
    fn drop(&mut self) {
        unsafe { self.ty.drop()(self.handle) }
    }
}

impl State {
    fn initialize(&self, wit: Wit) -> mlua::Result<()> {
        let imports = self.lua.create_table()?;
        for (i, func) in wit.iter_funcs().enumerate() {
            if func.import_impl().is_none() {
                continue;
            }
            let func = mlua::Function::wrap(Import { func });
            imports.set(format!("import{i}"), func)?;
        }

        self.lua.register_module("componentize_lua", imports)?;

        let file = std::fs::read_to_string("main.lua").expect("failed to read `main.lua`");
        self.lua.load(&file).exec()?;
        Ok(())
    }

    fn call_export(&self, wit: Wit, func: Function, cx: &mut Call<'_>) -> mlua::Result<()> {
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

        self.func.call_import(&mut stack);
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
        Type::Option(ty) => {
            if nullable(ty.ty()) {
                match val {
                    Value::Nil => {}
                    other => typecheck(lua, other, ty.ty())?,
                }
            } else {
                todo!()
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
        Type::ErrorContext => todo!(),
        Type::Record(_ty) => todo!(),
        Type::Enum(_ty) => todo!(),
        Type::Flags(_ty) => todo!(),
        Type::Result(_ty) => todo!(),
        Type::Variant(_ty) => todo!(),
        Type::Future(_ty) => todo!(),
        Type::Stream(_ty) => todo!(),
        Type::FixedSizeList(_ty) => todo!(),
        Type::Own(ty) | Type::Borrow(ty) => {
            let data = lua.convert::<mlua::AnyUserData>(val)?;
            let import = data.borrow::<ResourceImport>()?;
            if import.ty != ty {
                return Err(mlua::Error::runtime("wrong resource type"));
            }
        }
    }
    Ok(())
}

fn nullable(ty: Type) -> bool {
    match ty {
        Type::Alias(ty) => nullable(ty.ty()),

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
        | Type::Result(_)
        | Type::Own(_)
        | Type::Borrow(_) => true,

        Type::Variant(_) | Type::Option(_) => false,
    }
}

#[derive(Default)]
struct Call<'a> {
    stack: Vec<Value>,
    strings: Vec<BorrowedStr<'a>>,
    bytes: Vec<BorrowedBytes<'a>>,
    iter_points: Vec<usize>,
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

    fn resource_dtor(_: Resource, _: usize) {
        todo!()
    }
}

impl wit_dylib_ffi::Call for Call<'_> {
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
        if nullable(ty.ty()) {
            if is_some {
                // nothing to do, the value's on the top of the stack and it's
                // already in it's `some(val)` form as-is.
            } else {
                self.stack.push(Value::Nil);
            }
        } else {
            todo!()
        }
    }

    fn pop_option(&mut self, ty: WitOption) -> u32 {
        let val = self.stack.pop().unwrap();
        if nullable(ty.ty()) {
            match val {
                Value::Nil => 0,
                other => {
                    self.stack.push(other);
                    1
                }
            }
        } else {
            todo!()
        }
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

    fn pop_borrow(&mut self, _: Resource) -> u32 {
        todo!()
    }

    fn pop_own(&mut self, _: Resource) -> u32 {
        todo!()
    }

    fn push_borrow(&mut self, _: Resource, _: u32) {
        todo!()
    }

    fn push_own(&mut self, _: Resource, _: u32) {
        todo!()
    }

    fn pop_enum(&mut self, _: Enum) -> u32 {
        todo!()
    }

    fn pop_flags(&mut self, _: Flags) -> u32 {
        todo!()
    }

    fn pop_future(&mut self, _: Future) -> u32 {
        todo!()
    }

    fn pop_stream(&mut self, _: Stream) -> u32 {
        todo!()
    }

    fn pop_result(&mut self, _: WitResult) -> u32 {
        todo!()
    }

    fn pop_variant(&mut self, _: Variant) -> u32 {
        todo!()
    }

    fn pop_record(&mut self, _: Record) {
        todo!()
    }

    fn push_record(&mut self, _: Record) {
        todo!()
    }

    fn push_flags(&mut self, _: Flags, _: u32) {
        todo!()
    }

    fn push_enum(&mut self, _: Enum, _: u32) {
        todo!()
    }

    fn push_future(&mut self, _: Future, _: u32) {
        todo!()
    }

    fn push_stream(&mut self, _: Stream, _: u32) {
        todo!()
    }

    fn push_variant(&mut self, _: Variant, _: u32) {
        todo!()
    }

    fn push_result(&mut self, _: WitResult, _: bool) {
        todo!()
    }
}
