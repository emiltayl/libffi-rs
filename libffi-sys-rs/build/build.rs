//! Build script for libffi-sys. MSVC targets are handled as a special case because it is assumed
//! that it may not be possible to run the configure script. All other targets use the configure
//! script and compile with "make".

mod msvc;
mod not_msvc;

use std::env;
use std::process::Command;

fn run_command(which: &'static str, cmd: &mut Command) {
    assert!(cmd.status().expect(which).success(), "{}", which);
}

fn main() {
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap();

    if target_env == "msvc" {
        msvc::build_and_link();
    } else if env::var_os("CARGO_FEATURE_SYSTEM").is_some() {
        not_msvc::link_dylib();
    } else {
        not_msvc::build_and_link();
    }
}
