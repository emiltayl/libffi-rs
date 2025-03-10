#![doc(html_root_url = "https://docs.rs/libffi/3.2.0")]
//! Rust bindings for [libffi](https://sourceware.org/libffi/).
//!
//! The C libffi library provides two main facilities: assembling calls
//! to functions dynamically, and creating closures that can be called
//! as ordinary C functions. In Rust, the latter means that we can turn
//! a Rust lambda (or any object implementing [`Fn`]/[`FnMut`]) into an
//! ordinary C function pointer that we can pass as a callback to C.
//!
//! # Usage
//!
//! Building libffi will build lifbffi-sys, which will in turn build the
//! libffi C library [from github](https://github.com/libffi/libffi), which
//! requires that you have a working make, C compiler, automake, and
//! autoconf first. It’s [on crates.io](https://crates.io/crates/libffi), so
//! you can add
//!
//! ```toml
//! [dependencies]
//! libffi = "3.2.0"
//! ```
//!
//! This crate depends on [the `libffi-sys` crate], which by default
//! attempts to build its own version of the C libffi library. In order to
//! use your system’s C libffi instead, enable this crate’s  `system`
//! feature in your `Cargo.toml`:
//!
//! ```toml
//! [features]
//! libffi = { version = "3.2.0", features = ["system"] }
//! ```
//!
//! See [the `libffi-sys` documentation] for more information about how it
//! finds C libffi.
//!
//! This crate supports Rust version 1.85 and later.
//!
//! # Organization
//!
//! This library is organized in four layers, each of which attempts to
//! provide more safety and a simpler interface than the next layer
//! down. From top to bottom:
//!
//!   - The [`mod@middle`] layer provides memory-managed
//!     abstractions for assembling calls and closures.
//!   - The [`mod@low`] layer makes no attempts at safety,
//!     but provides a more idiomatically “Rusty” API than the underlying
//!     C library.
//!   - The [`mod@raw`] layer is a re-export of the
//!     [`libffi-sys`](https://crates.io/crates/libffi-sys) crate,
//!     a direct mapping of the C libffi library into Rust, generated by
//!     [bindgen](https://crates.io/crates/bindgen).
//!
//! It should be possible to use any layer without dipping into lower
//! layers (and it will be considered a bug to the extent that it
//! isn’t).
//!
//! # Examples
//!
//! TODO new examples with middle and low.
//!
//! [the `libffi-sys` crate]: https://crates.io/crates/libffi-sys/
//!
//! [the `libffi-sys` documentation]: https://docs.rs/libffi-sys/#usage
//!

#![deny(missing_docs)]

/// Raw definitions imported from the C library (via bindgen).
///
/// This module is generated by bindgen and undocumented. It’s intended
/// as the basis for higher-level bindings.
pub mod raw {
    pub use libffi_sys::*;
}

pub mod low;
pub mod middle;
