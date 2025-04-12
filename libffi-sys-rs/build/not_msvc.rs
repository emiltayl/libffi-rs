use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

use crate::run_command;

pub fn build_and_link() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let build_dir = Path::new(&out_dir).join("libffi-build");
    let prefix = Path::new(&out_dir).join("libffi-root");
    let libdir = Path::new(&prefix).join("lib");
    let libdir64 = Path::new(&prefix).join("lib64");

    // Copy LIBFFI_DIR into build_dir to avoid an unnecessary build
    if let Err(e) = fs::remove_dir_all(&build_dir) {
        assert_eq!(
            e.kind(),
            std::io::ErrorKind::NotFound,
            "can't remove the build directory: {e}",
        );
    }

    // On Linux, don't preserve the attributes of the source directory.
    // Not all cp versions support --no-preserve=mode,ownership, so we
    // first check if it's available.
    let mut cp = Command::new("cp");

    let has_no_preserve_flag = {
        let output = Command::new("cp").arg("--help").output().unwrap().stdout;
        String::from_utf8(output).unwrap().contains("--no-preserve")
    };

    if has_no_preserve_flag {
        cp.arg("--no-preserve=mode,ownership");
    }

    run_command(
        "Copying libffi into the build directory",
        cp.arg("-R").arg("libffi").arg(&build_dir),
    );

    // Generate configure, run configure, make, make install
    configure_libffi(prefix, &build_dir);

    run_command(
        "Building libffi",
        Command::new("make")
            .env_remove("DESTDIR")
            .arg("install")
            .current_dir(&build_dir),
    );

    // Cargo linking directives
    println!("cargo:rustc-link-lib=static=ffi");
    println!("cargo:rustc-link-search={}", libdir.display());
    println!("cargo:rustc-link-search={}", libdir64.display());
    println!("cargo::rerun-if-changed=build/");
    println!("cargo::rerun-if-changed=libffi/include");
    println!("cargo::rerun-if-changed=libffi/src");
}

pub fn configure_libffi(prefix: PathBuf, build_dir: &Path) {
    let mut configure = Command::new("sh");

    configure
        .arg("./configure")
        .arg("--with-pic")
        .arg("--disable-shared")
        .arg("--disable-docs");

    // Note: in autoconf land, host is where the code will run and not the machine compiling the
    // code, unlike in Rust where target is where the code will run and host is the machine
    // compiling.
    let target = env::var("TARGET").unwrap();
    let host = env::var("HOST").unwrap();

    if target != host {
        let cross_host = match target.as_str() {
            // Autoconf uses different target triplets for compiling with mingw
            "i686-pc-windows-gnu" => "i686-w64-mingw32",
            "x86_64-pc-windows-gnu" => "x86_64-w64-mingw32",
            // Autoconf uses riscv64 while Rust uses riscv64gc for the architecture
            "riscv64gc-unknown-linux-gnu" => "riscv64-unknown-linux-gnu",
            // Autoconf does not yet recognize illumos, but Solaris should be fine
            "x86_64-unknown-illumos" => "x86_64-unknown-solaris",
            // configure.host does not extract `ios-sim` as OS.
            // The sources for `ios-sim` should be the same as `ios`.
            "aarch64-apple-ios-sim" => "aarch64-apple-ios",
            // Everything else should be fine to pass straight through
            other => other,
        };
        configure.arg(format!("--host={cross_host}"));
    }

    let c_compiler = cc::Build::new().cargo_metadata(false).get_compiler();

    configure.env("CC", c_compiler.path());

    let mut cflags = c_compiler.cflags_env();
    match env::var_os("CFLAGS") {
        None => (),
        Some(flags) => {
            cflags.push(" ");
            cflags.push(&flags);
        }
    }
    configure.env("CFLAGS", cflags);

    for (k, v) in c_compiler.env() {
        configure.env(k, v);
    }

    configure.current_dir(build_dir);

    if env::var("CARGO_CFG_TARGET_OS").unwrap() == "windows" {
        // When using MSYS2, OUT_DIR will be a Windows like path such as
        // C:\foo\bar. Unfortunately, the various scripts used for building
        // libffi do not like such a path, so we have to turn this into a Unix
        // like path such as /c/foo/bar.
        let mut msys_prefix = prefix
            .to_str()
            .unwrap()
            .replacen(':', "", 1)
            .replace('\\', "/");

        msys_prefix.insert(0, '/');

        configure.arg("--prefix").arg(msys_prefix);
    } else {
        configure.arg("--prefix").arg(prefix);
    }

    run_command("Configuring libffi", &mut configure);
}

pub fn link_dylib() {
    println!("cargo:rustc-link-lib=dylib=ffi");
}
