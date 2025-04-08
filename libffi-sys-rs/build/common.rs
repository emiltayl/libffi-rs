pub use std::process::Command;
pub use std::{env, fs};

pub fn run_command(which: &'static str, cmd: &mut Command) {
    assert!(cmd.status().expect(which).success(), "{}", which);
}
