use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let wasi_sdk_path = PathBuf::from(std::env::var_os("WASI_SDK_PATH").unwrap());
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let target = "wasm32-wasip2";
    let upcase = target.to_uppercase().replace("-", "_");
    let debug = true;

    println!("cargo:rerun-if-changed=./crates/runtime");

    let mut output = String::new();

    let mut build = |lua: &str| {
        let mut rustflags = Vec::new();
        rustflags.push("-Clink-arg=-shared");

        // FIXME(WebAssembly/wasi-sdk#564):
        // Don't use libc.a, which is not compiled with `-fPIC`, from Rust's
        // sysroot.
        rustflags.push("-Clink-self-contained=n");

        // FIXME(rust-lang/rust#146457) this shouldn't be required
        rustflags.push("-Ctarget-feature=+exception-handling");
        rustflags.push("-Cllvm-args=-wasm-use-legacy-eh=false");

        let mut cargo = Command::new("cargo");
        cargo
            .arg("build")
            .arg("--target")
            .arg(target)
            .arg("--package=lua-component-runtime")
            .env("CARGO_TARGET_DIR", &out_dir)
            .env(
                format!("CARGO_TARGET_{upcase}_RUSTFLAGS"),
                rustflags.join(" "),
            )
            .env(
                format!("CARGO_TARGET_{upcase}_LINKER"),
                wasi_sdk_path.join("bin/clang"),
            )
            .env(
                format!("CC_{}", target.replace('-', "_")),
                wasi_sdk_path.join("bin/clang"),
            )
            .env(format!("CFLAGS_{}", target.replace('-', "_")), "-fPIC")
            .env_remove("CARGO_ENCODED_RUSTFLAGS");

        cargo.arg("--features").arg(lua);
        if !debug {
            cargo.arg("--release");
        }
        let dir = if debug { "debug" } else { "release" };

        eprintln!("running {cargo:?}");
        let status = cargo.status().unwrap();
        assert!(status.success());

        let dst = out_dir.join(&format!("{lua}.wasm"));
        fs::rename(
            &out_dir
                .join("wasm32-wasip2")
                .join(dir)
                .join("lua_component_runtime.wasm"),
            &dst,
        )
        .unwrap();

        output.push_str(&format!(
            "const {}: &[u8] = include_bytes!({:?});\n",
            lua.to_uppercase(),
            dst,
        ));
    };

    build("lua51");
    build("lua52");
    build("lua53");
    build("lua54");

    output.push_str(&format!(
        "

const LIBC_SO: &[u8] = include_bytes!({:?});
const LIBSETJMP_SO: &[u8] = include_bytes!({:?});
const LIBWASI_EMULATED_SIGNAL_SO: &[u8] = include_bytes!({:?});
",
        wasi_sdk_path
            .join("share/wasi-sysroot/lib")
            .join(target)
            .join("libc.so"),
        wasi_sdk_path
            .join("share/wasi-sysroot/lib")
            .join(target)
            .join("libsetjmp.so"),
        wasi_sdk_path
            .join("share/wasi-sysroot/lib")
            .join(target)
            .join("libwasi-emulated-signal.so"),
    ));

    fs::write(out_dir.join("output.rs"), &output).unwrap();
}
