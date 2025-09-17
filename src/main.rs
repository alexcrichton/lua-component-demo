use anyhow::{Context, Result};
use clap::Parser;
use std::fmt;
use std::path::PathBuf;
use wasi_preview1_component_adapter_provider::WASI_SNAPSHOT_PREVIEW1_REACTOR_ADAPTER;
use wit_parser::Resolve;

include!(concat!(env!("OUT_DIR"), "/output.rs"));

#[derive(Parser)]
struct App {
    /// Path to WIT files to load.
    ///
    /// This can be a directory containing `*.wit` files, a `*.wit` file itself,
    /// or a `*.wasm` file which is a WIT package encoded as WebAssembly.
    wit: PathBuf,

    #[clap(short, long, default_value_t = Lua::default(), value_name = "LUA")]
    lua: Lua,

    #[clap(short, long)]
    output: PathBuf,

    /// Features to enable when parsing the `wit` option.
    ///
    /// This flag enables the `@unstable` feature in WIT documents where the
    /// items are otherwise hidden by default.
    #[clap(long)]
    features: Vec<String>,

    /// Enable all features when parsing the `wit` option.
    ///
    /// This flag enables all `@unstable` features in WIT documents where the
    /// items are otherwise hidden by default.
    #[clap(long)]
    all_features: bool,

    /// The WIT world to use, if the WIT input has more than one.
    #[clap(short, long)]
    world: Option<String>,
}

#[derive(Default, Debug, Eq, PartialEq, Clone, Copy, clap::ValueEnum)]
pub enum Lua {
    #[default]
    Lua54,
    Lua53,
    Lua52,
    Lua51,
}

impl Lua {
    fn wasm(&self) -> &[u8] {
        match self {
            Lua::Lua54 => LUA54,
            Lua::Lua53 => LUA53,
            Lua::Lua52 => LUA52,
            Lua::Lua51 => LUA51,
        }
    }
}

impl fmt::Display for Lua {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lua::Lua54 => "lua54".fmt(f),
            Lua::Lua53 => "lua53".fmt(f),
            Lua::Lua52 => "lua52".fmt(f),
            Lua::Lua51 => "lua51".fmt(f),
        }
    }
}

fn main() -> Result<()> {
    App::parse().run()
}

impl App {
    fn run(&mut self) -> Result<()> {
        let mut resolve = Resolve::default();
        resolve.all_features = self.all_features;
        for feature in self.features.iter() {
            for f in feature.split_whitespace() {
                for f in f.split(',').filter(|s| !s.is_empty()) {
                    resolve.features.insert(f.to_string());
                }
            }
        }
        let (pkg_id, _) = resolve.push_path(&self.wit)?;
        let world = resolve.select_world(&[pkg_id], self.world.as_deref())?;

        let mut wit_dylib = wit_dylib::create(&resolve, world, None);
        wit_component::embed_component_metadata(
            &mut wit_dylib,
            &resolve,
            world,
            wit_component::StringEncoding::UTF8,
        )?;

        let mut linker = wit_component::Linker::default()
            .validate(false)
            .debug_names(false);
        linker = linker
            .library("libc.so", LIBC_SO, false)?
            .library("libsetjmp.so", LIBSETJMP_SO, false)?
            .library(
                "libwasi-emulated-signal.so",
                LIBWASI_EMULATED_SIGNAL_SO,
                false,
            )?
            .library("lua_component_runtime.wasm", self.lua.wasm(), false)?
            .library("wit-dylib.wasm", &wit_dylib, false)?
            .adapter(
                "wasi_snapshot_preview1",
                WASI_SNAPSHOT_PREVIEW1_REACTOR_ADAPTER,
            )?;

        let result = linker.encode()?;

        std::fs::write(&self.output, result)
            .with_context(|| format!("failed to write output {:?}", self.output))?;

        Ok(())
    }
}
