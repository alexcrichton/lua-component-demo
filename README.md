# Lua Component Demo

This repository is a demo of compiling Lua to a WebAssembly component. The tools
used here are:

* Lua - either 5.{1,2,3,4} through the [`lua-src` crate]
* [`mlua`] - Rust bindings to the Lua C API
* [`wasi-sdk`] - C toolchain to compile Lua
* [`wasm-tools wit-dylib`] - hooks up components to the Lua interpreter
* [`wasm-tools component link`] - assembles libraries into a single component.

The end result is that you're able to do something like this:

```
$ cat test.wit
package my:test;

world test {
  export run: func(x: string);
}
$ cat main.lua
function run(s)
  print('Hello ' .. s .. '!')
end
$ cargo run ./test.wit -o lua.wasm
...
$ wasmtime run -Wexceptions --invoke 'run("World")' --dir . ./lua.wasm
Hello World!
()
```

[`mlua`]: https://crates.io/crates/mlua
[`lua-src` crate]: https://crates.io/crates/lua-src
[`wasi-sdk`]: https://github.com/WebAssembly/wasi-sdk
[`wit-dylib`]: https://github.com/bytecodealliance/wasm-tools/tree/main/crates/wit-dylib
[`wasm-tools component link`]: https://docs.rs/wit-component/latest/wit_component/struct.Linker.html

## Disclaimer

I am not a Lua programmer. I don't know Lua, nor do I know idiomatic Lua. I'm
aware it's a common choice as an embedding language and I wanted to
use it to test out the creation of [`wit-dylib`]. I do not plan to maintain
this project to become a production-ready embedding of Lua nor is it complete
as-is (there's a number of `todo!()` throughout the codebase). The purpose of
this repository is to provide a road map to how componentizing Lua might
work, but it'll require someone more invested than I to take this over the
finish line.

## What works and what doesn't

The state of things can be seen in `crates/runtime/src/lib.rs` and the amount
of `todo!()` there. Implemented features are:

* Type conversions for integers
* Type conversions for floats
* Type conversions for bools
* Type conversions for chars
* Type conversions for strings
* Type conversions for lists
* Type conversions for tuples
* Type conversions for `option<T>`
* Invoking world-exported functions
* Raw bindings to call imported functions

Unimplemented features are:

* [ ] Defining imports under an appropriate name (they're just `import1` right
  now).
* [ ] Exported functions of interfaces aren't supported.
* [ ] WIT `variant` and `result` types.
* [ ] WIT `record` type.
* [ ] WIT `flags` type.
* [ ] WIT `enum` type.
* [ ] WIT `option<option<T>>` type.
* [ ] WIT exported resources
* [ ] WIT imported resources
