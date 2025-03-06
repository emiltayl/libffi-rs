pub use std::{
    env, fs,
    process::Command,
};

pub fn run_command(which: &'static str, cmd: &mut Command) {
    assert!(cmd.status().expect(which).success(), "{}", which);
}
