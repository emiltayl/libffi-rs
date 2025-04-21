//! Higher-level abstractions of the libffi API. The `high` module uses Rust's type system to
//! make using libffi more ergonomic and provide more safety guarantees. However, ffi will never be
//! completely safe. Additionally, the `high` module requires compile-time knowledge of signatures
//! and is therefore not suited for running arbitrary functions at run-time.

mod closures;
mod foreign_func;
mod types;

pub use closures::{Closurable, Closure, ClosureMut, ClosureMutable, ClosureOnce, ClosureOnceable};
pub use foreign_func::{ForeignFunc, ForeignFuncSendSync};
pub use types::{AsFfiType, FfiArgs, FfiRet};

pub use crate::middle::CodePtr;
