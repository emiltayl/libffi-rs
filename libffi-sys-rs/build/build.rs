#![allow(
    clippy::all,
    missing_docs,
    reason = "Ignoring lints until build scripts are reworked."
)]

mod common;
#[cfg(target_env = "msvc")]
mod msvc;
#[cfg(not(target_env = "msvc"))]
mod not_msvc;

#[cfg(target_env = "msvc")]
use msvc::{build_and_link, probe_and_link};
#[cfg(not(target_env = "msvc"))]
use not_msvc::{build_and_link, probe_and_link};

fn main() {
    if cfg!(feature = "system") {
        probe_and_link();
    } else {
        build_and_link();
    }
}
