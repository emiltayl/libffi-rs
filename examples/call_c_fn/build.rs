//! Build script for compiling lib.c.

fn main() {
    println!("cargo::rerun-if-changed=src/lib.c");
    cc::Build::new().file("src/lib.c").compile("lib");
}
