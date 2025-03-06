#![doc(html_root_url = "https://docs.rs/libffi-sys/2.3.0")]
//! Low-level Rust bindings for [libffi](https://sourceware.org/libffi/)
//!
//! The C libffi library provides two main facilities: assembling calls
//! to functions dynamically, and creating closures that can be called
//! as ordinary C functions.
//!
//! This is an undocumented wrapper, originally generated by bindgen then
//! cleaned up manually, intended as the basis for higher-level bindings.
//!
//! See [the libffi crate](https://crates.io/crates/libffi/) for a
//! higher-level API.
//!
//! # Usage
//!
//! `libffi-sys` can either build its own copy of the libffi C library [from
//! github](https://github.com/libffi/libffi) or it can link against your
//! system’s C libffi. By default it builds its own because many systems
//! ship with an old C libffi; this requires that you have a working make,
//! C compiler, automake, and autoconf first. If your system libffi
//! is new enough (v3.2.1 as of October 2019), you can instead enable the
//! `system` feature flag to use that. If you want this crate to build
//! a C libffi for you, add
//!
//! ```toml
//! [dependencies]
//! libffi-sys = "2.3.0"
//! ```
//!
//! to your `Cargo.toml`. If you want to use your system C libffi, then
//!
//! ```toml
//! [dependencies.libffi-sys]
//! version = "2.3.0"
//! features = ["system"]
//! ```
//!
//! to your `Cargo.toml` instead.
//!
//! This crate supports Rust version 1.32 and later.

#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(improper_ctypes)]
#![allow(unused_imports)]

use std::fmt::{self, Debug};
use std::mem::zeroed;
use std::os::raw::{c_char, c_int, c_long, c_schar, c_uint, c_ulong, c_ushort, c_void};

mod arch;
pub use arch::*;
use fmt::Formatter;

pub type ffi_arg = c_ulong;
pub type ffi_sarg = c_long;
pub type ffi_abi = u32;
pub type ffi_status = u32;
pub type ffi_type_enum = u32;

pub const FFI_64_BIT_MAX: u64 = 9223372036854775807;
pub const FFI_CLOSURES: u32 = 1;
pub const FFI_SIZEOF_ARG: usize = std::mem::size_of::<c_long>();
// NOTE: This only differs from FFI_SIZEOF_ARG on ILP platforms, which Rust does not support
pub const FFI_SIZEOF_JAVA_RAW: usize = FFI_SIZEOF_ARG;

pub const FFI_TYPE_VOID: u32 = 0;
pub const FFI_TYPE_INT: u32 = 1;
pub const FFI_TYPE_FLOAT: u32 = 2;
pub const FFI_TYPE_DOUBLE: u32 = 3;
pub const FFI_TYPE_LONGDOUBLE: u32 = 4;
pub const FFI_TYPE_UINT8: u32 = 5;
pub const FFI_TYPE_SINT8: u32 = 6;
pub const FFI_TYPE_UINT16: u32 = 7;
pub const FFI_TYPE_SINT16: u32 = 8;
pub const FFI_TYPE_UINT32: u32 = 9;
pub const FFI_TYPE_SINT32: u32 = 10;
pub const FFI_TYPE_UINT64: u32 = 11;
pub const FFI_TYPE_SINT64: u32 = 12;
pub const FFI_TYPE_STRUCT: u32 = 13;
pub const FFI_TYPE_POINTER: u32 = 14;
pub const FFI_TYPE_COMPLEX: u32 = 15;
pub const FFI_TYPE_LAST: u32 = 15;

pub const ffi_status_FFI_OK: ffi_status = 0;
pub const ffi_status_FFI_BAD_TYPEDEF: ffi_status = 1;
pub const ffi_status_FFI_BAD_ABI: ffi_status = 2;
pub const ffi_status_FFI_BAD_ARGTYPE: ffi_status = 3;

pub const ffi_type_enum_STRUCT: ffi_type_enum = 13;
pub const ffi_type_enum_COMPLEX: ffi_type_enum = 15;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct ffi_type {
    pub size: usize,
    pub alignment: c_ushort,
    pub type_: c_ushort,
    pub elements: *mut *mut ffi_type,
}

impl Default for ffi_type {
    fn default() -> Self {
        unsafe { zeroed() }
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct ffi_cif {
    pub abi: ffi_abi,
    pub nargs: c_uint,
    pub arg_types: *mut *mut ffi_type,
    pub rtype: *mut ffi_type,
    pub bytes: c_uint,
    pub flags: c_uint,
    #[cfg(all(target_arch = "aarch64", target_os = "windows"))]
    pub is_variadic: c_uint,
    #[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
    pub aarch64_nfixedargs: c_uint,
    #[cfg(target_arch = "arm")]
    pub vfp_used: c_int,
    #[cfg(target_arch = "arm")]
    pub vfp_reg_free: c_ushort,
    #[cfg(target_arch = "arm")]
    pub vfp_nargs: c_ushort,
    #[cfg(target_arch = "arm")]
    pub vfp_args: [c_schar; 16],
    #[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
    pub nfixedargs: c_uint,
    #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
    pub riscv_nfixedargs: c_uint,
    #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
    pub riscv_unused: c_uint,
    #[cfg(target_arch = "loongarch64")]
    pub loongarch_nfixedargs: c_uint,
    #[cfg(target_arch = "loongarch64")]
    pub loongarch_unused: c_uint,
    #[cfg(any(
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6"
    ))]
    pub mips_nfixedargs: c_uint,
}

impl Default for ffi_cif {
    fn default() -> Self {
        unsafe { zeroed() }
    }
}

#[repr(C, align(64))]
#[derive(Copy, Clone)]
pub union ffi_raw {
    pub sint: ffi_sarg,
    pub uint: ffi_arg,
    pub flt: f32,
    pub data: [c_char; FFI_SIZEOF_ARG],
    pub ptr: *mut c_void,
}

impl Default for ffi_raw {
    fn default() -> Self {
        unsafe { zeroed() }
    }
}

pub type ffi_java_raw = ffi_raw;

#[repr(C, align(64))]
#[derive(Copy, Clone)]
pub union ffi_trampoline {
    pub tramp: [c_char; FFI_TRAMPOLINE_SIZE],
    pub ftramp: *mut c_void,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ffi_closure {
    pub tramp: ffi_trampoline,
    pub cif: *mut ffi_cif,
    pub fun: Option<
        unsafe extern "C" fn(
            arg1: *mut ffi_cif,
            arg2: *mut c_void,
            arg3: *mut *mut c_void,
            arg4: *mut c_void,
        ),
    >,
    pub user_data: *mut c_void,
}

/// Implements Debug manually since sometimes FFI_TRAMPOLINE_SIZE is too large
impl Debug for ffi_closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("ffi_closure")
            .field("tramp", unsafe { &self.tramp.tramp })
            .field("cif", &self.cif)
            .field("fun", &self.fun)
            .field("user_data", &self.user_data)
            .finish()
    }
}

impl Default for ffi_closure {
    fn default() -> Self {
        unsafe { zeroed() }
    }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ffi_raw_closure {
    pub tramp: [c_char; FFI_TRAMPOLINE_SIZE],
    pub cif: *mut ffi_cif,
    // See: https://github.com/libffi/libffi/blob/3a7580da73b7f16f275277316d00e3497cbb5a8c/include/ffi.h.in#L364
    #[cfg(not(target_arch = "x86"))]
    pub translate_args: Option<
        unsafe extern "C" fn(
            arg1: *mut ffi_cif,
            arg2: *mut c_void,
            arg3: *mut *mut c_void,
            arg4: *mut c_void,
        ),
    >,
    #[cfg(not(target_arch = "x86"))]
    pub this_closure: *mut c_void,
    pub fun: Option<
        unsafe extern "C" fn(
            arg1: *mut ffi_cif,
            arg2: *mut c_void,
            arg3: *mut ffi_raw,
            arg4: *mut c_void,
        ),
    >,
    pub user_data: *mut c_void,
}

/// Implements Debug manually since sometimes FFI_TRAMPOLINE_SIZE is too large
impl Debug for ffi_raw_closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut debug_struct = f.debug_struct("ffi_raw_closure");
        debug_struct
            .field("tramp", &&self.tramp[..])
            .field("cif", &self.cif);

        #[cfg(not(target_arch = "x86"))]
        debug_struct.field("translate_args", &self.translate_args);
        #[cfg(not(target_arch = "x86"))]
        debug_struct.field("this_closure", &self.this_closure);

        debug_struct
            .field("fun", &self.fun)
            .field("user_data", &self.user_data)
            .finish()
    }
}

impl Default for ffi_raw_closure {
    fn default() -> Self {
        unsafe { zeroed() }
    }
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct ffi_java_raw_closure {
    pub tramp: [c_char; FFI_TRAMPOLINE_SIZE],
    pub cif: *mut ffi_cif,
    // See: https://github.com/libffi/libffi/blob/3a7580da73b7f16f275277316d00e3497cbb5a8c/include/ffi.h.in#L390
    #[cfg(not(target_arch = "x86"))]
    pub translate_args: Option<
        unsafe extern "C" fn(
            arg1: *mut ffi_cif,
            arg2: *mut c_void,
            arg3: *mut *mut c_void,
            arg4: *mut c_void,
        ),
    >,
    #[cfg(not(target_arch = "x86"))]
    pub this_closure: *mut c_void,
    pub fun: Option<
        unsafe extern "C" fn(
            arg1: *mut ffi_cif,
            arg2: *mut c_void,
            arg3: *mut ffi_java_raw,
            arg4: *mut c_void,
        ),
    >,
    pub user_data: *mut c_void,
}

/// Implements Debug manually since sometimes FFI_TRAMPOLINE_SIZE is too large
impl Debug for ffi_java_raw_closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut debug_struct = f.debug_struct("ffi_java_raw_closure");
        debug_struct
            .field("tramp", &&self.tramp[..])
            .field("cif", &self.cif);

        #[cfg(not(target_arch = "x86"))]
        debug_struct.field("translate_args", &self.translate_args);
        #[cfg(not(target_arch = "x86"))]
        debug_struct.field("this_closure", &self.this_closure);

        debug_struct
            .field("fun", &self.fun)
            .field("user_data", &self.user_data)
            .finish()
    }
}

impl Default for ffi_java_raw_closure {
    fn default() -> Self {
        unsafe { zeroed() }
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct ffi_go_closure {
    pub tramp: *mut c_void,
    pub cif: *mut ffi_cif,
    pub fun: Option<
        unsafe extern "C" fn(
            arg1: *mut ffi_cif,
            arg2: *mut c_void,
            arg3: *mut *mut c_void,
            arg4: *mut c_void,
        ),
    >,
}
impl Default for ffi_go_closure {
    fn default() -> Self {
        unsafe { zeroed() }
    }
}

unsafe extern "C" {
    pub static mut ffi_type_void: ffi_type;
    pub static mut ffi_type_uint8: ffi_type;
    pub static mut ffi_type_sint8: ffi_type;
    pub static mut ffi_type_uint16: ffi_type;
    pub static mut ffi_type_sint16: ffi_type;
    pub static mut ffi_type_uint32: ffi_type;
    pub static mut ffi_type_sint32: ffi_type;
    pub static mut ffi_type_uint64: ffi_type;
    pub static mut ffi_type_sint64: ffi_type;
    pub static mut ffi_type_float: ffi_type;
    pub static mut ffi_type_double: ffi_type;
    pub static mut ffi_type_pointer: ffi_type;

    #[cfg(not(target_arch = "aarch64"))]
    #[cfg(not(all(target_arch = "arm", target_os = "linux", target_env = "gnu")))]
    pub static mut ffi_type_longdouble: ffi_type;

    #[cfg(feature = "complex")]
    pub static mut ffi_type_complex_float: ffi_type;

    #[cfg(feature = "complex")]
    pub static mut ffi_type_complex_double: ffi_type;

    #[cfg(feature = "complex")]
    #[cfg(not(all(target_arch = "arm", target_os = "linux", target_env = "gnu")))]
    pub static mut ffi_type_complex_longdouble: ffi_type;

    pub fn ffi_raw_call(
        cif: *mut ffi_cif,
        fn_: Option<unsafe extern "C" fn()>,
        rvalue: *mut c_void,
        avalue: *mut ffi_raw,
    );

    pub fn ffi_ptrarray_to_raw(cif: *mut ffi_cif, args: *mut *mut c_void, raw: *mut ffi_raw);

    pub fn ffi_raw_to_ptrarray(cif: *mut ffi_cif, raw: *mut ffi_raw, args: *mut *mut c_void);

    pub fn ffi_raw_size(cif: *mut ffi_cif) -> usize;

    // See: https://github.com/libffi/libffi/blob/3a7580da73b7f16f275277316d00e3497cbb5a8c/include/ffi.h.in#L286
    #[cfg(not(target_arch = "x86"))]
    pub fn ffi_java_raw_call(
        cif: *mut ffi_cif,
        fn_: Option<unsafe extern "C" fn()>,
        rvalue: *mut c_void,
        avalue: *mut ffi_java_raw,
    );

    pub fn ffi_java_ptrarray_to_raw(
        cif: *mut ffi_cif,
        args: *mut *mut c_void,
        raw: *mut ffi_java_raw,
    );

    pub fn ffi_java_raw_to_ptrarray(
        cif: *mut ffi_cif,
        raw: *mut ffi_java_raw,
        args: *mut *mut c_void,
    );

    pub fn ffi_java_raw_size(cif: *mut ffi_cif) -> usize;

    pub fn ffi_closure_alloc(size: usize, code: *mut *mut c_void) -> *mut c_void;

    pub fn ffi_closure_free(arg1: *mut c_void);

    pub fn ffi_prep_closure(
        arg1: *mut ffi_closure,
        arg2: *mut ffi_cif,
        fun: Option<
            unsafe extern "C" fn(
                arg1: *mut ffi_cif,
                arg2: *mut c_void,
                arg3: *mut *mut c_void,
                arg4: *mut c_void,
            ),
        >,
        user_data: *mut c_void,
    ) -> ffi_status;

    pub fn ffi_prep_closure_loc(
        arg1: *mut ffi_closure,
        arg2: *mut ffi_cif,
        fun: Option<
            unsafe extern "C" fn(
                arg1: *mut ffi_cif,
                arg2: *mut c_void,
                arg3: *mut *mut c_void,
                arg4: *mut c_void,
            ),
        >,
        user_data: *mut c_void,
        codeloc: *mut c_void,
    ) -> ffi_status;

    pub fn ffi_prep_raw_closure(
        arg1: *mut ffi_raw_closure,
        cif: *mut ffi_cif,
        fun: Option<
            unsafe extern "C" fn(
                arg1: *mut ffi_cif,
                arg2: *mut c_void,
                arg3: *mut ffi_raw,
                arg4: *mut c_void,
            ),
        >,
        user_data: *mut c_void,
    ) -> ffi_status;

    pub fn ffi_prep_raw_closure_loc(
        arg1: *mut ffi_raw_closure,
        cif: *mut ffi_cif,
        fun: Option<
            unsafe extern "C" fn(
                arg1: *mut ffi_cif,
                arg2: *mut c_void,
                arg3: *mut ffi_raw,
                arg4: *mut c_void,
            ),
        >,
        user_data: *mut c_void,
        codeloc: *mut c_void,
    ) -> ffi_status;

    // See: https://github.com/libffi/libffi/blob/3a7580da73b7f16f275277316d00e3497cbb5a8c/include/ffi.h.in#L419
    #[cfg(not(target_arch = "x86"))]
    pub fn ffi_prep_java_raw_closure(
        arg1: *mut ffi_java_raw_closure,
        cif: *mut ffi_cif,
        fun: Option<
            unsafe extern "C" fn(
                arg1: *mut ffi_cif,
                arg2: *mut c_void,
                arg3: *mut ffi_java_raw,
                arg4: *mut c_void,
            ),
        >,
        user_data: *mut c_void,
    ) -> ffi_status;

    // See: https://github.com/libffi/libffi/blob/3a7580da73b7f16f275277316d00e3497cbb5a8c/include/ffi.h.in#L419
    #[cfg(not(target_arch = "x86"))]
    pub fn ffi_prep_java_raw_closure_loc(
        arg1: *mut ffi_java_raw_closure,
        cif: *mut ffi_cif,
        fun: Option<
            unsafe extern "C" fn(
                arg1: *mut ffi_cif,
                arg2: *mut c_void,
                arg3: *mut ffi_java_raw,
                arg4: *mut c_void,
            ),
        >,
        user_data: *mut c_void,
        codeloc: *mut c_void,
    ) -> ffi_status;

    pub fn ffi_prep_go_closure(
        arg1: *mut ffi_go_closure,
        arg2: *mut ffi_cif,
        fun: Option<
            unsafe extern "C" fn(
                arg1: *mut ffi_cif,
                arg2: *mut c_void,
                arg3: *mut *mut c_void,
                arg4: *mut c_void,
            ),
        >,
    ) -> ffi_status;

    pub fn ffi_call_go(
        cif: *mut ffi_cif,
        fn_: Option<unsafe extern "C" fn()>,
        rvalue: *mut c_void,
        avalue: *mut *mut c_void,
        closure: *mut c_void,
    );

    pub fn ffi_prep_cif(
        cif: *mut ffi_cif,
        abi: ffi_abi,
        nargs: c_uint,
        rtype: *mut ffi_type,
        atypes: *mut *mut ffi_type,
    ) -> ffi_status;

    pub fn ffi_prep_cif_var(
        cif: *mut ffi_cif,
        abi: ffi_abi,
        nfixedargs: c_uint,
        ntotalargs: c_uint,
        rtype: *mut ffi_type,
        atypes: *mut *mut ffi_type,
    ) -> ffi_status;

    pub fn ffi_call(
        cif: *mut ffi_cif,
        fn_: Option<unsafe extern "C" fn()>,
        rvalue: *mut c_void,
        avalue: *mut *mut c_void,
    );

    pub fn ffi_get_struct_offsets(
        abi: ffi_abi,
        struct_type: *mut ffi_type,
        offsets: *mut usize,
    ) -> ffi_status;
}

#[cfg(test)]
mod test {
    use super::*;

    extern "C" fn add(x: u64, y: u64) -> u64 {
        x + y
    }

    #[test]
    fn test_function_with_two_arguments() {
        unsafe {
            let mut cif: ffi_cif = Default::default();
            let mut arg_types: Vec<*mut ffi_type> =
                vec![&raw mut ffi_type_uint64, &raw mut ffi_type_uint64];

            let prep_status = ffi_prep_cif(
                &mut cif,
                ffi_abi_FFI_DEFAULT_ABI,
                2,
                &raw mut ffi_type_uint64,
                arg_types.as_mut_ptr(),
            );

            assert_eq!(prep_status, ffi_status_FFI_OK);

            let mut rval = 0u64;
            let func = &*(&(add as *mut extern "C" fn(u64, u64) -> u64) as *const _
                as *const extern "C" fn());

            ffi_call(
                &mut cif,
                Some(*func),
                &mut rval as *mut _ as *mut c_void,
                vec![
                    &mut 4u64 as *mut _ as *mut c_void,
                    &mut 5u64 as *mut _ as *mut c_void,
                ]
                .as_mut_ptr(),
            );

            assert_eq!(rval, 9);
        }
    }
}
