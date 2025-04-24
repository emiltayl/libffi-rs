//! The `low` module provides thin wrappers around [libffi]'s functions for
//! direct, low-level interactions with the libffi API from Rust.
//!
//! This module requires manual memory management to ensure all memory used by libffi is valid
//! and accessible. For automatic memory management, consider using the [`middle`] or [`high`]
//! modules.
//!
//! Essential types and constants for using libffi are re-exported by this module, reducing the need
//! to use the [`raw`] module directly. While `low` is slightly more idiomatic to Rust than [`raw`],
//! function and symbol names remain close to their original libffi counterparts.
//!
//! For an example of how to use the `low` module to call FFI functions, see [`call`].
//!
//! [libffi]: https://github.com/libffi/libffi/
//! [`call`]: `crate::low::call`#example
//! [`middle`]: `crate::middle`
//! [`high`]: `crate::high`

use core::ffi::{c_uint, c_void};
use core::mem::{MaybeUninit, transmute};

/// A constant with the default ABI of the target platform.
pub use raw::ffi_abi_FFI_DEFAULT_ABI;
pub use raw::{ffi_abi, ffi_cif, ffi_closure, ffi_status, ffi_type};

use crate::raw;

/// Re-exports of the [`ffi_type`] objects used to describe argument and result types.
///
/// These are from [the raw module](crate::raw), but are renamed by removing the `ffi_type_` prefix.
/// For example, [`raw::ffi_type_void`] becomes [`types::void`].
pub mod types {
    #[cfg(feature = "complex")]
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64", target_env = "msvc")))]
    pub use crate::raw::ffi_type_complex_longdouble as complex_longdouble;
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64", target_env = "msvc")))]
    pub use crate::raw::ffi_type_longdouble as longdouble;
    #[cfg(feature = "complex")]
    #[cfg(not(target_env = "msvc"))]
    pub use crate::raw::{
        ffi_type_complex_double as complex_double, ffi_type_complex_float as complex_float,
    };
    pub use crate::raw::{
        ffi_type_double as double, ffi_type_float as float, ffi_type_pointer as pointer,
        ffi_type_sint8 as sint8, ffi_type_sint16 as sint16, ffi_type_sint32 as sint32,
        ffi_type_sint64 as sint64, ffi_type_uint8 as uint8, ffi_type_uint16 as uint16,
        ffi_type_uint32 as uint32, ffi_type_uint64 as uint64, ffi_type_void as void,
    };
}

/// Type tags used when constructing and inspecting [`ffi_type`]s.
///
/// It is not necessary to use these type tags when passing plain scalar types (integers, floats,
/// and pointers) to function as libffi pre-defines [`ffi_type`s for these types](mod@types).
/// However, for composite types (I.E. structs), new instances of the [`ffi_type`] struct must be
/// created.
///
/// # Example
///
/// Suppose we have the following C struct:
///
/// ```c
/// struct my_struct {
///     uint16_t f1;
///     uint64_t f2;
/// };
/// ```
///
/// To pass it by value to a function using libffi, the appropriate `ffi_type` can be constructed
/// as follows using `type_tag::STRUCT`:
///
/// ```
/// use std::ptr;
///
/// use libffi::low::{ffi_type, type_tag, types};
///
/// let mut elements = [
///     &raw mut types::uint16,
///     &raw mut types::uint64,
///     ptr::null_mut(),
/// ];
///
/// let my_struct: ffi_type = ffi_type {
///     type_: type_tag::STRUCT,
///     elements: elements.as_mut_ptr(),
///     ..Default::default()
/// };
/// ```
pub mod type_tag {
    use crate::raw;

    /// Type tag representing a `void` return type.
    pub const VOID: u16 = raw::FFI_TYPE_VOID;
    /// Type tag representing a C `int`.
    pub const INT: u16 = raw::FFI_TYPE_INT;
    /// Type tag representing a `f32`.
    pub const FLOAT: u16 = raw::FFI_TYPE_FLOAT;
    /// Type tag representing a `f64`.
    pub const DOUBLE: u16 = raw::FFI_TYPE_DOUBLE;
    /// Type tag representing a C `long double`.
    pub const LONGDOUBLE: u16 = raw::FFI_TYPE_LONGDOUBLE;
    /// Type tag representing a `i8`.
    pub const SINT8: u16 = raw::FFI_TYPE_SINT8;
    /// Type tag representing a `u8`.
    pub const UINT8: u16 = raw::FFI_TYPE_UINT8;
    /// Type tag representing a `i16`.
    pub const SINT16: u16 = raw::FFI_TYPE_SINT16;
    /// Type tag representing a `u16`.
    pub const UINT16: u16 = raw::FFI_TYPE_UINT16;
    /// Type tag representing a `i32`.
    pub const SINT32: u16 = raw::FFI_TYPE_SINT32;
    /// Type tag representing a `u32`.
    pub const UINT32: u16 = raw::FFI_TYPE_UINT32;
    /// Type tag representing a `i64`.
    pub const SINT64: u16 = raw::FFI_TYPE_SINT64;
    /// Type tag representing a `u64`.
    pub const UINT64: u16 = raw::FFI_TYPE_UINT64;
    /// Type tag representing a custom struct.
    pub const STRUCT: u16 = raw::FFI_TYPE_STRUCT;
    /// Type tag representing a pointer.
    pub const POINTER: u16 = raw::FFI_TYPE_POINTER;
    /// Type tag representing a complex.
    pub const COMPLEX: u16 = raw::FFI_TYPE_COMPLEX;
}

/// Represents errors that may occur when interacting with libffi.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Error {
    /// Returned if an invalid, malformed, or otherwise unsupported type in provided to libffi.
    Typedef,
    /// Returned if an unknown or unsupported ABI was provided to this function. In general, this
    /// error should not be encountered unless ABIs are referred to using numbers instead of the
    /// `ffi_abi_*` constants in [`raw`].
    Abi,
    /// Returned if invalid data types are provided to `ffi_prep_cif_var`.
    ///
    /// `ffi_prep_cif_var` only supports 64-bit floats (f64/double) and integers of at least `int`
    /// size.
    ArgType,
    /// Returned from [`closure_alloc`] in case libffi was unable to allocate the closure.
    UnableToAllocateClosure,
    /// An unrecognized error code, potentially a bug.
    Unknown(u32),
}

/// Helper function to convert return values from libffi to a `Result`.
fn status_to_result<R>(status: ffi_status, good: R) -> Result<R, Error> {
    match status {
        raw::ffi_status_FFI_OK => Ok(good),
        raw::ffi_status_FFI_BAD_TYPEDEF => Err(Error::Typedef),
        raw::ffi_status_FFI_BAD_ABI => Err(Error::Abi),
        raw::ffi_status_FFI_BAD_ARGTYPE => Err(Error::ArgType),
        _ => Err(Error::Unknown(status)),
    }
}

/// A wrapper for function pointers.
///
/// This is used to make the API a bit easier to understand, and as a simple type lint. As a
/// `repr(C)` struct of one element, it should be safe to transmute between `CodePtr` and
/// `NonNull<c_void>` / `*mut c_void`, or between collections thereof.
///
/// # Example
///
/// To create a `CodePtr` for a function, cast the function pointer using `as *mut _`:
///
/// ```
/// use std::ffi::c_void;
///
/// use libffi::low::CodePtr;
///
/// unsafe extern "C" {
///     unsafe fn qsort(
///         ptr: *mut c_void,
///         count: usize,
///         size: usize,
///         cmp_fn: extern "C" fn(cmp_a: *const c_void, cmp_b: *const c_void) -> i32,
///     );
/// }
///
/// let qsort_ptr = CodePtr(qsort as *mut _);
/// // `qsort_ptr` now contains a `CodePtr` to the `qsort` libc function.
/// ```
#[derive(Clone, Copy, Debug, Hash)]
#[repr(C)]
pub struct CodePtr(pub *mut c_void);

impl CodePtr {
    /// Initializes a code pointer from a function pointer.
    ///
    /// This is useful mainly for talking to C APIs that take untyped callbacks specified in the API
    /// as having type `void(*)()`.
    pub fn from_fun(fun: unsafe extern "C" fn()) -> Self {
        CodePtr(fun as *mut _)
    }

    /// Initializes a code pointer from a void, non-null pointer.
    ///
    /// This is the other common type used in APIs (or at least in libffi) for untyped callback
    /// arguments.
    pub fn from_ptr(fun: *mut c_void) -> Self {
        CodePtr(fun)
    }

    /// Gets the code pointer as a `const void *`.
    pub fn as_ptr(self) -> *const c_void {
        self.0
    }

    /// Gets the code pointer as a `void *`.
    pub fn as_mut_ptr(self) -> *mut c_void {
        self.0
    }

    /// Gets a function pointer to self.0 as a `Option<extern "C" fn()>`.
    ///
    /// If you use `as_fun` to call function you **must** make sure that it is a `extern "C"`
    /// function that does not accept any parameters and does not return a value.
    fn as_option_void_fn(&self) -> Option<unsafe extern "C" fn()> {
        // SAFETY:
        // * `*mut c_void` and `Option<unsafe extern "C" fn()>` have the same size.
        // * A NULL pointer will be transmuted to `None`.
        unsafe { transmute::<*mut c_void, Option<unsafe extern "C" fn()>>(self.0) }
    }
}

/// Initializes a CIF (Call Interface) with the given ABI and type signature.
///
/// Before a CIF can be used to call a function or create a closure, it must be initialized. This
/// function accepts the calling convention to use and the argument and result types, and uses these
/// values to initialize the CIF. For vararg CIF initialization, see [`prep_cif_var`].
///
/// # Safety
///
/// * `cif` must be a pointer to a mutable and properly aligned [`ffi_cif`].
/// * `rtype` must be a pointer to a properly aligned [`ffi_type`]. This pointer must be valid for
///   the entire lifetime of `cif`.
/// * `atypes` must be a pointer to a properly aligned array of [`ffi_type`]. The array must contain
///   at least `nargs` `ffi_type`s. This array must be valid for the entire lifetime of `cif`.
///
/// # Arguments
///
/// - `cif` — Pointer to the CIF to initialize
/// - `abi` — The calling convention to use
/// - `nargs` — The number of arguments
/// - `rtype` — Pointer to the result type
/// - `atypes` — Pointer to array of the argument types (the array must be at least `nargs` long)
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function returns an error if the underlying `ffi_prep_cif` returns an error. The following
/// error conditions are listed in libffi's man pages:
///
/// * `cif` is `NULL`
/// * `rtype` or `atypes` are malformed
///   * This should not happen when passing types in [`types`].
/// * An invalid ABI is passed
///
/// # Example
///
/// The following code creates a CIF that can be used to call a `extern "C"` function that accepts
/// one `i32` and one `u64` argument and returns a pointer.
///
/// ```
/// use libffi::low::{ffi_abi_FFI_DEFAULT_ABI, ffi_cif, ffi_type, prep_cif, types};
///
/// extern "C" fn ffi_function(a: i32, b: u64) -> *const i32 {
///     // ...
/// # std::ptr::null() // Just to make the function compile
/// }
///
/// let mut args = [&raw mut types::sint32, &raw mut types::uint64];
/// let mut cif = ffi_cif::default();
///
/// // SAFETY:
/// // * `cif` is a mutable `ffi_cif` that is properly aligned.
/// // * The return type is pointer to a valid `ffi_type`.
/// // * The argument array contains 2 pointers to valid `ffi_type`s.
/// unsafe {
///     prep_cif(
///         &mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         2,
///         &raw mut types::pointer,
///         args.as_mut_ptr(),
///     )?;
/// }
///
/// // `cif` can now be used to call `ffi_function`.
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn prep_cif(
    cif: *mut ffi_cif,
    abi: ffi_abi,
    nargs: u32,
    rtype: *mut ffi_type,
    atypes: *mut *mut ffi_type,
) -> Result<(), Error> {
    // SAFETY:
    // The caller must ensure that the safety requirements of this function are upheld.
    let status = unsafe { raw::ffi_prep_cif(cif, abi, nargs, rtype, atypes) };
    status_to_result(status, ())
}

/// Initializes a CIF (Call Interface) for a vararg function with the given ABI and type signature.
///
/// To call a vararg function with a different number or type of arguments, prepare a new CIF for
/// each variation.
///
/// Before a CIF can be used to call a function it must be initialized. This function accepts the
/// calling convention to use and the argument and result types, and uses these values to initialize
/// the CIF. For non-vararg CIF initialization, see [`prep_cif`].
///
/// # Safety
///
/// * `cif` must be a pointer to a mutable and properly aligned [`ffi_cif`].
/// * `rtype` must be a pointer to a properly aligned [`ffi_type`]. This pointer must be valid for
///   the entire lifetime of `cif`.
/// * `atypes` must be a pointer to a properly aligned array of [`ffi_type`]. The array must contain
///   at least `ntotalargs` `ffi_type`s. This array must be valid for the entire lifetime of `cif`.
///
/// # Arguments
///
/// - `cif` — Pointer to the CIF to initialize
/// - `abi` — The calling convention to use
/// - `nfixedargs` — the number of fixed arguments
/// - `ntotalargs` — the total number of arguments, including fixed and var args
/// - `rtype` — Pointer to the result type
/// - `atypes` — Pointer to array of the argument types (the array must be at least `ntotalargs`
///   long)
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function returns an error if the underlying `ffi_prep_cif_var` returns an error. The
/// following error conditions are listed in libffi's man pages:
///
/// * `cif` is `NULL`
/// * `rtype` or `atypes` are malformed
///   * This should not happen when passing types in [`types`].
/// * An invalid ABI is passed
/// * Integers smaller than 32 bits or floats smaller than 64 bits are passed as "variable" (not
///   fixed) arguments.
///
/// # Example
///
/// The following code creates a CIF that can be used to call `printf` to print a pointer, an 32-bit
/// signed integer and a 64-bit floating point number.
///
/// ```
/// use libffi::low::{ffi_abi_FFI_DEFAULT_ABI, ffi_cif, ffi_type, prep_cif_var, types};
///
/// let mut args = [
///     // The format string
///     &raw mut types::pointer,
///     // A pointer
///     &raw mut types::pointer,
///     // A signed 32-bit integer
///     &raw mut types::sint32,
///     // A 64-bit float
///     &raw mut types::double,
/// ];
/// let mut printf_cif = ffi_cif::default();
///
/// // SAFETY:
/// // * `cif` is a mutable `ffi_cif` that is properly aligned.
/// // * The return type is pointer to a valid `ffi_type`.
/// // * The argument array contains 4 pointers to valid `ffi_type`s.
/// unsafe {
///     prep_cif_var(
///         &mut printf_cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         1,
///         4,
///         &raw mut types::sint32,
///         args.as_mut_ptr(),
///     )?;
/// }
///
/// // `printf_cif` can now be used to call `printf` with a format string such as:
/// // `c"Pointer: %p, number: %d, double: %f\n"`
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn prep_cif_var(
    cif: *mut ffi_cif,
    abi: ffi_abi,
    nfixedargs: u32,
    ntotalargs: u32,
    rtype: *mut ffi_type,
    atypes: *mut *mut ffi_type,
) -> Result<(), Error> {
    // SAFETY:
    // The caller must ensure that `cif`, `rtype`, and `atypes` are valid pointers and that `atypes`
    // points to an array of (at least) `nargs` size.
    let status = unsafe {
        raw::ffi_prep_cif_var(
            cif,
            abi,
            nfixedargs as c_uint,
            ntotalargs as c_uint,
            rtype,
            atypes,
        )
    };
    status_to_result(status, ())
}

/// Calls a C function specified by a CIF.
///
/// While libffi's `ffi_call` requires return values to be at least the size of a CPU register, this
/// function does not have those restrictions and can be used with return types of any size.
///
/// # Safety
///
/// * `cif` must be a pointer to an initialized and aligned `ffi_cif`.
/// * The argument array and return type must be readable when calling `ffi_call`.
/// * `fun` must be a function pointer to a function with a signature identical to the one provided
///   when initializing `cif`.
/// * It must be safe to call the function pointed to by `fun`.
/// * `args` must point to an array of pointers to arguments that have identical layout to the
///   arguments specified by `cif`.
/// * The return type defined in `cif` must match the layout of `R`.
///
/// Thorough testing is strongly recommended when working with FFI functions.
///
/// # Arguments
///
/// * `cif` — Pointer to the initialized CIF that describes `fun`'s signature and ABI
/// * `fun` — Pointer to the function to call
/// * `args` — Pointer to array of pointers to arguments to pass to `fun`
///
/// # Result
///
/// The result of calling `fun` with `args`.
///
/// # Example
///
/// ```
/// use std::ffi::c_void;
/// use std::ptr;
///
/// use libffi::low::{CodePtr, call, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif, types};
///
/// extern "C" fn add_function(a: u64, b: u64) -> u64 {
///     a + b
/// }
///
/// let mut arg_types = [&raw mut types::uint64, &raw mut types::uint64];
/// let mut cif = ffi_cif::default();
///
/// // SAFETY:
/// // * `cif` is a pointer to a mutable `ffi_cif` that is properly aligned.
/// // * The return type is pointer to a valid `ffi_type`.
/// // * The argument array contains 2 pointers to valid `ffi_type`s.
/// unsafe {
///     prep_cif(
///         &raw mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         2,
///         &raw mut types::uint64,
///         arg_types.as_mut_ptr(),
///     )?;
/// }
///
/// let mut arg_a: u64 = 4;
/// let mut arg_b: u64 = 5;
/// let mut args = [
///     (&raw mut arg_a).cast::<c_void>(),
///     (&raw mut arg_b).cast::<c_void>(),
/// ];
///
/// // SAFETY:
/// // * `cif` is a pointer to an initialized `ffi_cif` to a function with the "C" ABI.
/// // * `arg_types` is still readable.
/// // * `add_function` points to an `extern "C"` function that accepts two `u64`s and returns a
/// //   `u64`.
/// // * `add_function` does not perform any unsafe actions.
/// // * `args` is a pointer to an array of two pointers to `u64`s.
/// let result: u64 = unsafe { call(&mut cif, CodePtr(add_function as *mut _), args.as_mut_ptr()) };
///
/// assert_eq!(9, result);
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn call<R>(cif: *mut ffi_cif, fun: CodePtr, args: *mut *mut c_void) -> R {
    // libffi always writes *at least* a full register to the result pointer. Therefore, if the
    // return value is smaller, we need to handle the return value with extra care to prevent out of
    // bounds write and returning the correct value in big endian architectures.
    //
    // There is no data type in rust that is guaranteed to be a full register(?), but the assumption
    // that usize is the full width of a register holds for all tested architectures.
    if size_of::<R>() < size_of::<usize>() {
        // Alignments are a power of 2 (1, 2, 4, 8, etc). `result`'s alignment is greater than or
        // equal to that of `R`, so `result` should be properly aligned for `R` since a larger
        // alignment is always divisible by any of the smaller alignments.
        let mut result = MaybeUninit::<usize>::uninit();

        // SAFETY: It is up to the caller to ensure that the ffi_call is safe to perform.
        unsafe {
            raw::ffi_call(
                cif,
                fun.as_option_void_fn(),
                result.as_mut_ptr().cast::<c_void>(),
                args,
            );

            let result = result.assume_init();

            if cfg!(target_endian = "big") {
                call_return_small_big_endian_result((*(*cif).rtype).type_, &raw const result)
            } else {
                (&raw const result).cast::<R>().read()
            }
        }
    } else {
        let mut result = MaybeUninit::<R>::uninit();

        // SAFETY: It is up to the caller to ensure that the ffi_call is safe to perform.
        unsafe {
            raw::ffi_call(
                cif,
                fun.as_option_void_fn(),
                result.as_mut_ptr().cast::<c_void>(),
                args,
            );

            result.assume_init()
        }
    }
}

/// Helper function to get the return value of a ffi call on big endian architectures.
///
/// # Safety
///
/// `result` must be a pointer to a `usize` and `mem::size_of::<R> <= mem::size_of::<usize>()`.
unsafe fn call_return_small_big_endian_result<R>(type_tag: u16, result: *const usize) -> R {
    if type_tag == type_tag::FLOAT || type_tag == type_tag::STRUCT || type_tag == type_tag::VOID {
        // SAFETY:
        // Testing has shown that these types appear at `result`. For voids, this should be
        // optimized to a NOP.
        unsafe { result.cast::<R>().read() }
    } else {
        // SAFETY:
        // Consider `*result` an array with `size_of::<usize>() / size_of::<R>()` items of `R`. The
        // following code reads the last element to get the least significant bits of `result` on
        // big endian architectures. The most significant bits are zeroed by libffi.
        unsafe {
            result
                .cast::<R>()
                .add((size_of::<usize>() / size_of::<R>()) - 1)
                .read()
        }
    }
}

/// Allocates a closure.
///
/// This function allocates a closure and returns a writable closure object and its corresponding
/// function pointer. The former acts as a handle to the closure, and is used to configure and free
/// the closure. The latter is the code pointer used to invoke the closure. Before it can be
/// invoked, it must be initialized with [`prep_closure`] or [`prep_closure_mut`]. The closure must
/// be freed using [`closure_free`], after which point the code pointer must not be used.
///
/// # Errors
///
/// Returns an error if libffi fails to allocate the closure.
///
/// # Example
///
/// ```
/// use libffi::low::{closure_alloc, closure_free};
///
/// let (closure_handle, code_ptr) = closure_alloc()?;
///
/// // Use `closure_handle` and `code_ptr` here.
///
/// // Always be sure to call closure_free after use to free the closure's memory.
///
/// // SAFETY:
/// // * `closure_handle` is a valid handle that has not been freed already.
/// // * `code_ptr` is not used after this point.
/// unsafe { closure_free(closure_handle) };
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub fn closure_alloc() -> Result<(*mut ffi_closure, CodePtr), Error> {
    let mut code_pointer = MaybeUninit::<*mut c_void>::uninit();

    // SAFETY:
    // Call `ffi_closure_alloc` with sufficient size for a `ffi_closure`. This writes a pointer
    // to `code_pointer` if successful.
    let closure =
        unsafe { raw::ffi_closure_alloc(size_of::<ffi_closure>(), code_pointer.as_mut_ptr()) };

    if closure.is_null() {
        return Err(Error::UnableToAllocateClosure);
    }

    // SAFETY:
    // `ffi_closure_alloc` was called and has returned a non-null handle to a closure, indicating it
    // was successful. This resulted in a function pointer being written to `code_pointer`.
    let code_pointer = unsafe { code_pointer.assume_init() };

    Ok((closure.cast(), CodePtr::from_ptr(code_pointer)))
}

/// Frees a closure.
///
/// Closures allocated with [`closure_alloc`] must be deallocated with [`closure_free`].
///
/// # Safety
///
/// * This should only be called on a `*mut ffi_closure` created by [`closure_alloc`] that has not
///   been already freed.
/// * `code_ptr` **must not** be used to call the closure after `closure_free` has been called to
///   free the closure.
///
/// # Example
///
/// ```
/// use libffi::low::{closure_alloc, closure_free};
///
/// let (closure_handle, code_ptr) = closure_alloc()?;
///
/// // Use `closure_handle` and `code_ptr` here.
///
/// // SAFETY:
/// // * `closure_handle` is a valid handle that has not been freed already.
/// // * `code_ptr` is not used after this point.
/// unsafe {
///     closure_free(closure_handle);
/// }
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn closure_free(closure: *mut ffi_closure) {
    // SAFETY: `ffi_closure_free` must be called to free any memory allocated by
    // `ffi_closure_alloc`.
    unsafe { raw::ffi_closure_free(closure.cast::<c_void>()) }
}

/// The function signature of a callback handler used for calling immutable closures with libffi.
/// Handler functions of this type will abort if a panic is thrown by the closure.
///
/// `U` is the type of the user data captured by the closure and passed to the callback, and `R` is
/// the type of the result. The parameters are not typed, since they are passed as a C array of
/// `void *`.
pub type Callback<U, R> = unsafe extern "C" fn(
    cif: &ffi_cif,
    result: *mut MaybeUninit<R>,
    args: *const *const c_void,
    userdata: *const U,
);

/// The function signature of a callback handler used for calling immutable closures with libffi.
/// Handler functions of this type can be used to catch unwinding panics thrown by its closure.
///
/// `U` is the type of the user data captured by the closure and passed to the callback, and `R` is
/// the type of the result. The parameters are not typed, since they are passed as a C array of
/// `void *`.
pub type CallbackUnwindable<U, R> = unsafe extern "C-unwind" fn(
    cif: &ffi_cif,
    result: *mut MaybeUninit<R>,
    args: *const *const c_void,
    userdata: *const U,
);

/// The function signature of a callback handler used for calling mutable closures with libffi.
/// Handler functions of this type will abort if a panic is thrown by the closure.
///
/// `U` is the type of the user data captured by the closure and passed to the callback, and `R` is
/// the type of the result. The parameters are not typed, since they are passed as a C array of
/// `void *`.
pub type CallbackMut<U, R> = unsafe extern "C" fn(
    cif: &ffi_cif,
    result: *mut MaybeUninit<R>,
    args: *const *const c_void,
    userdata: *mut U,
);

/// The function signature of a callback handler used for calling mutable closures with libffi.
/// Handler functions of this type can be used to catch unwinding panics thrown by its closure.
///
/// `U` is the type of the user data captured by the closure and passed to the callback, and `R` is
/// the type of the result. The parameters are not typed, since they are passed as a C array of
/// `void *`.
pub type CallbackUnwindableMut<U, R> = unsafe extern "C-unwind" fn(
    cif: &ffi_cif,
    result: *mut MaybeUninit<R>,
    args: *const *const c_void,
    userdata: *mut U,
);

/// The callback type expected by [`raw::ffi_prep_closure_loc`].
pub type RawCallback = unsafe extern "C" fn(
    cif: *mut ffi_cif,
    result: *mut c_void,
    args: *mut *mut c_void,
    userdata: *mut c_void,
);

/// Initializes a closure with a callback function and user data.
///
/// After allocating a closure with [`closure_alloc`], it needs to be initialized with a function
/// `callback` to call and a pointer `userdata` to pass to it. Invoking the closure's code pointer
/// will then pass the provided arguments and the user data pointer to the callback.
///
/// If mutable access to the user data is required, use [`prep_closure_mut`].
///
/// # Safety
///
/// * `closure` and `code` must point to values retrieved from the same call to [`closure_alloc`].
/// * `cif` and `userdata` must point to memory that live for at least as long as `closure`.
///
/// # Arguments
///
/// - `closure` - Pointer to the closure to initialize
/// - `cif` - Pointer the CIF describing the calling convention and types for calling the closure
/// - `callback` - Pointer to the function that will be called when the closure is invoked
/// - `userdata` - Pointer to the closed-over value, stored in the closure and passed to the
///   callback upon invocation
/// - `code` - the closure's code pointer, the second component returned by [`closure_alloc`].
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function will return an error if `cif` is NULL, malformed, or contains an invalid ABI.
///
/// # Example
///
/// ```
/// use std::ffi::c_void;
/// use std::mem;
///
/// use libffi::low::{
///     CodePtr, closure_alloc, closure_free, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif,
///     prep_closure, types,
/// };
///
/// unsafe extern "C" fn callback(
///     _cif: &ffi_cif,
///     result: *mut mem::MaybeUninit<u64>,
///     args: *const *const c_void,
///     userdata: *const u64,
/// ) {
///     // SAFETY:
///     // This function accepts a single `u64`, which it adds with its userdata and writes to the
///     // result pointer.
///     unsafe {
///         let args: *const *const u64 = args.cast();
///         (*result).write(**args + *userdata);
///     }
/// }
///
/// let mut cif = ffi_cif::default();
/// let mut args = [(&raw mut types::uint64).cast()];
/// let mut userdata: u64 = 5;
///
/// // SAFETY:
/// // * `cif` points to a mutable `ffi_cif`.
/// // * `rtype` points to a `ffi_type`.
/// // * `atypes` points to an array of `ffi_types` with one element.
/// unsafe {
///     prep_cif(
///         &mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         1,
///         &raw mut types::uint64,
///         args.as_mut_ptr(),
///     )?;
/// }
///
/// let (closure, code) = closure_alloc()?;
///
/// // SAFETY:
/// // * `closure` and `code` point to memory from the same call to `closure_alloc`.
/// // * `closure_alloc` returned successfully as we have not returned early yet.
/// // * `cif` and `userdata` point to memory that live until the end of this function, at which
/// //   point `closure` will have been freed.
/// unsafe {
///     prep_closure(closure, &mut cif, callback, &raw mut userdata, code)?;
/// }
///
/// // SAFETY:
/// // * `cif` and `callback` both describe a function that accepts one `u64` and returns a `u64`.
/// // * `code` contains a function pointer that will be used to execute `callback`.
/// let add5: extern "C" fn(u64) -> u64 = unsafe { mem::transmute(code) };
///
/// assert_eq!(11, add5(6));
/// assert_eq!(12, add5(7));
///
/// // Make sure to free the closure after we are finished with it.
/// // SAFETY:
/// // * `closure` is a valid `ffi_closure` that has not been freed yet.
/// // * `code` / `add5` is not called beyond this point.
/// unsafe { closure_free(closure) };
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn prep_closure<U, R>(
    closure: *mut ffi_closure,
    cif: *mut ffi_cif,
    callback: Callback<U, R>,
    userdata: *const U,
    code: CodePtr,
) -> Result<(), Error> {
    // SAFETY:
    // The caller must ensure that this function's safety requirements are met.
    let status = unsafe {
        raw::ffi_prep_closure_loc(
            closure,
            cif,
            Some(transmute::<Callback<U, R>, RawCallback>(callback)),
            userdata as *mut c_void,
            code.as_mut_ptr(),
        )
    };

    status_to_result(status, ())
}

/// Similar to [`prep_closure`], but allows panics in the closure to unwind.
///
/// See [`prep_closure`] for details about calling this function and its arguments.
///
/// # Safety
///
/// See [`prep_closure`'s safety documentation](prep_closure#safety).
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function will return an error if `cif` is NULL, malformed, or contains an invalid ABI.
///
/// # Example
///
/// Allocating a closure that will panic and catching it with [`std::panic::catch_unwind`].
///
/// ```
/// use std::ffi::c_void;
/// use std::{mem, panic, ptr};
///
/// use libffi::low::{
///     CodePtr, closure_alloc, closure_free, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif,
///     prep_closure_unwindable, types,
/// };
///
/// unsafe extern "C-unwind" fn callback(
///     _cif: &ffi_cif,
///     result: *mut mem::MaybeUninit<()>,
///     args: *const *const c_void,
///     userdata: *const (),
/// ) {
///     panic!("Panic from a libffi closure");
/// }
///
/// let mut cif = ffi_cif::default();
///
/// /// // SAFETY:
/// // * `cif` points to a mutable `ffi_cif`.
/// // * `rtype` points to a `ffi_type`.
/// // * `nargs` is 0, so it is safe for `atypes` to be `NULL`.
/// unsafe {
///     prep_cif(
///         &raw mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         0,
///         &raw mut types::void,
///         ptr::null_mut(),
///     )?;
/// }
///
/// let (closure, code) = closure_alloc()?;
///
/// // SAFETY:
/// // * `closure` and `code` point to memory from the same call to `closure_alloc`.
/// // * `closure_alloc` returned successfully as we have not returned early yet.
/// // * `cif` points to memory that live until the end of this function, at which point `closure`
/// //   will have been freed.
/// // * `userdata` is not used.
/// unsafe {
///     prep_closure_unwindable(closure, &raw mut cif, callback, &(), code)?;
/// }
///
/// // SAFETY:
/// // * `cif` and `callback` both describe a function that does not accept any argument and does
/// //   not return anything.
/// // * `code` contains a function pointer that will be used to execute `callback`.
/// let this_panics: extern "C-unwind" fn() = unsafe { mem::transmute(code) };
///
/// let catch_result = panic::catch_unwind(move || {
///     this_panics();
///     println!("This should not print as `this_panics` paniced.");
/// });
///
/// // If a panic is "caught", `catch_unwind` returns an `Err`.
/// assert!(catch_result.is_err());
/// // Make sure to free the closure after we are finished with it.
/// // * `closure` is a valid `ffi_closure` that has not been freed yet.
/// // * `code` / `this_panics` is not called beyond this point.
/// unsafe { closure_free(closure) };
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn prep_closure_unwindable<U, R>(
    closure: *mut ffi_closure,
    cif: *mut ffi_cif,
    callback: CallbackUnwindable<U, R>,
    userdata: *const U,
    code: CodePtr,
) -> Result<(), Error> {
    // SAFETY:
    // The caller must ensure that this function's safety requirements are met.
    let status = unsafe {
        raw::ffi_prep_closure_loc(
            closure,
            cif,
            Some(transmute::<CallbackUnwindable<U, R>, RawCallback>(callback)),
            userdata as *mut c_void,
            code.as_mut_ptr(),
        )
    };

    status_to_result(status, ())
}

/// Initializes a mutable closure with a callback function and mutable user data.
///
/// While it is possible to use mutable closures, they are typically unsafe as they allow multiple
/// closures mutable access to the same memory location at the same time. If possible, it is
/// recommended to use immutable closures with something that allows interior mutability, such as
/// a `Mutex` instead.
///
/// After allocating a closure with [`closure_alloc`], it needs to be initialized with a function
/// `callback` to call and a pointer `userdata` to pass to it. Invoking the closure's code pointer
/// will then pass the provided arguments and the user data pointer to the callback.
///
/// For immutable user data use [`prep_closure`].
///
/// # Safety
///
/// * `closure` and `code` must point to values retrieved from the same call to [`closure_alloc`].
/// * `cif` and `userdata` must point to memory that live for at least as long as `closure`.
/// * `callback` must ensure that it is safe to mutate `userdata`.
///
/// # Arguments
///
/// - `closure` - Pointer to the closure to initialize
/// - `cif` - Pointer the CIF describing the calling convention and types for calling the closure
/// - `callback` - Pointer to the function that will be called when the closure is invoked
/// - `userdata` - Pointer to the closed-over value, stored in the closure and passed to the
///   callback upon invocation
/// - `code` - the closure's code pointer, the second component returned by [`closure_alloc`].
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function will return an error if `cif` is NULL, malformed, or contains an invalid ABI.
///
/// # Example
///
/// ```
/// use std::ffi::c_void;
/// use std::mem;
///
/// use libffi::low::{
///     CodePtr, closure_alloc, closure_free, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif,
///     prep_closure_mut, types,
/// };
///
/// unsafe extern "C" fn callback(
///     _cif: &ffi_cif,
///     result: *mut mem::MaybeUninit<u64>,
///     args: *const *const c_void,
///     userdata: *mut u64,
/// ) {
///     // SAFETY:
///     // * This function accepts a single `u64`, which it adds with its user data and writes to
///     //   the result pointer.
///     // * In this code example it is "safe" to mutate `userdata`, but this is generally hard to
///     //   prove in real-world cases, so immutable closures are preferred.
///     unsafe {
///         let args: *const *const u64 = args.cast();
///         (*result).write(*userdata);
///         *userdata += **args;
///     }
/// }
///
/// let mut cif = ffi_cif::default();
/// let mut args = [(&raw mut types::uint64).cast()];
/// let mut userdata: u64 = 5;
///
/// // SAFETY:
/// // * `cif` points to a mutable `ffi_cif`.
/// // * `rtype` points to a `ffi_type`.
/// // * `atypes` points to an array of `ffi_types` with one element.
/// unsafe {
///     prep_cif(
///         &mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         1,
///         &raw mut types::uint64,
///         args.as_mut_ptr(),
///     )?;
/// }
///
/// let (closure, code) = closure_alloc()?;
///
/// // SAFETY:
/// // * `closure` and `code` point to memory from the same call to `closure_alloc`.
/// // * `closure_alloc` returned successfully as we have not returned early yet.
/// // * `cif` and `userdata` point to memory that live until the end of this function, at which
/// //   point `closure` will have been freed.
/// unsafe {
///     prep_closure_mut(closure, &mut cif, callback, &raw mut userdata, code)?;
/// }
///
/// // SAFETY:
/// // * `cif` and `callback` both describe a function that accepts one `u64` and returns a `u64`.
/// // * `code` contains a function pointer that will be used to execute `callback`.
/// let add5: extern "C" fn(u64) -> u64 = unsafe { mem::transmute(code) };
///
/// assert_eq!(5, add5(6));
/// assert_eq!(11, add5(7));
/// assert_eq!(userdata, 5 + 6 + 7);
///
/// // Make sure to free the closure after we are finished with it.
/// // SAFETY:
/// // * `closure` is a valid `ffi_closure` that has not been freed yet.
/// // * `code` / `add5` is not called beyond this point.
/// unsafe { closure_free(closure) };
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn prep_closure_mut<U, R>(
    closure: *mut ffi_closure,
    cif: *mut ffi_cif,
    callback: CallbackMut<U, R>,
    userdata: *mut U,
    code: CodePtr,
) -> Result<(), Error> {
    // SAFETY:
    // The caller must ensure that this function's safety requirements are met.
    let status = unsafe {
        raw::ffi_prep_closure_loc(
            closure,
            cif,
            Some(transmute::<CallbackMut<U, R>, RawCallback>(callback)),
            userdata.cast::<c_void>(),
            code.as_mut_ptr(),
        )
    };

    status_to_result(status, ())
}

/// Similar to [`prep_closure_mut`], but allows panics in the closure to unwind.
///
/// See [`prep_closure_mut`] for details about calling this function and its arguments.
///
/// # Safety
///
/// See [`prep_closure_mut`'s safety documentation](prep_closure_mut#safety).
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function will return an error if `cif` is NULL, malformed, or contains an invalid ABI.
///
/// # Example
///
/// Allocating a closure that will panic and catching it with [`std::panic::catch_unwind`].
///
/// ```
/// use std::ffi::c_void;
/// use std::{mem, panic, ptr};
///
/// use libffi::low::{
///     CodePtr, closure_alloc, closure_free, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif,
///     prep_closure_unwindable_mut, types,
/// };
///
/// unsafe extern "C-unwind" fn callback(
///     _cif: &ffi_cif,
///     result: *mut mem::MaybeUninit<()>,
///     args: *const *const c_void,
///     userdata: *mut u64,
/// ) {
///     // * This function does not accept any parameters and does not return a result.
///     // * In this code example it is "safe" to mutate `userdata`, but this is generally hard to
///     //   prove in real-world cases, so immutable closures are preferred.
///     unsafe {
///         *userdata += 1;
///         panic!("Panic from a libffi closure");
///         *userdata += 1;
///     }
/// }
///
/// let mut cif = ffi_cif::default();
/// let mut userdata: u64 = 0;
///
/// /// // SAFETY:
/// // * `cif` points to a mutable `ffi_cif`.
/// // * `rtype` points to a `ffi_type`.
/// // * `nargs` is 0, so it is safe to set `atypes` to `NULL`.
/// unsafe {
///     prep_cif(
///         &raw mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         0,
///         &raw mut types::void,
///         ptr::null_mut(),
///     )?;
/// }
/// let (closure, code) = closure_alloc()?;
////// // SAFETY:
/// // * `closure` and `code` point to memory from the same call to `closure_alloc`.
/// // * `closure_alloc` returned successfully as we have not returned early yet.
/// // * `cif` and `userdata` point to memory that live until the end of this function, at which
/// //   point `closure` will have been freed.
/// unsafe {
///     prep_closure_unwindable_mut(closure, &raw mut cif, callback, &mut userdata, code)?;
/// }
///
/// /// // SAFETY:
/// // * `cif` and `callback` both describe a function that does not accept any arguments and does
/// //   not return any value.
/// // * `code` contains a function pointer that will be used to execute `callback`.
/// let this_panics: extern "C-unwind" fn() = unsafe { mem::transmute(code) };
///
/// let catch_result = panic::catch_unwind(move || {
///     this_panics();
/// });
///
/// // If a panic is "caught", `catch_unwind` returns an `Err`.
/// assert!(catch_result.is_err());
/// // `userdata` was incremented once before `this_panics` panicked.
/// assert_eq!(userdata, 1);
/// // Make sure to free the closure after we are finished with it.
/// // SAFETY:
/// // * `closure` is a valid `ffi_closure` that has not been freed yet.
/// // * `code` / `this_panics` is not called beyond this point.
/// unsafe { closure_free(closure) };
/// # Ok::<(), libffi::low::Error>(())
/// ```
pub unsafe fn prep_closure_unwindable_mut<U, R>(
    closure: *mut ffi_closure,
    cif: *mut ffi_cif,
    callback: CallbackUnwindableMut<U, R>,
    userdata: *mut U,
    code: CodePtr,
) -> Result<(), Error> {
    // SAFETY:
    // The caller must ensure that this function's safety requirements are met.
    let status = unsafe {
        raw::ffi_prep_closure_loc(
            closure,
            cif,
            Some(transmute::<CallbackUnwindableMut<U, R>, RawCallback>(
                callback,
            )),
            userdata.cast::<c_void>(),
            code.as_mut_ptr(),
        )
    };

    status_to_result(status, ())
}

#[cfg(all(test, not(miri)))]
mod test {
    use core::ptr;

    use super::*;

    #[test]
    fn test_error_code_translation() {
        // Provoke a FFI_BAD_TYPEDEF by a bad `type_` tag.
        let mut bad_arg = ffi_type {
            size: 0,
            alignment: 0,
            type_: 255, // This type tag should not exist
            elements: ptr::null_mut(),
        };
        let mut cif = ffi_cif::default();

        // SAFETY:
        // * `cif` points to a mutable `ffi_cif`.
        // * `rtype` points to a `ffi_type`.
        // * Since `nargs` is 0, it is safe to set `atypes` to `NULL`.
        let result = unsafe {
            prep_cif(
                &raw mut cif,
                ffi_abi_FFI_DEFAULT_ABI,
                0,
                &raw mut bad_arg,
                ptr::null_mut(),
            )
        };

        assert_eq!(result, Err(Error::Typedef));

        // Provoke a FFI_BAD_ABI by a bad ABI value
        let mut cif = ffi_cif::default();

        // SAFETY:
        // * `cif` points to a mutable `ffi_cif`.
        // * `rtype` points to a `ffi_type`.
        // * Since `nargs` is 0, it is safe to set `atypes` to `NULL`.
        let result = unsafe {
            prep_cif(
                &raw mut cif,
                0xdead_beef,
                0,
                &raw mut types::void,
                ptr::null_mut(),
            )
        };

        assert_eq!(result, Err(Error::Abi));

        // Provoke a FFI_BAD_ARGTYPE by bad values to `ffi_prep_cif_var`.
        // Test case copied from:
        // https://github.com/libffi/libffi/blob/v3.4.7/testsuite/libffi.call/va_1.c#L75
        let mut s_type = ffi_type::default();
        let mut s_elements = [ptr::null_mut::<ffi_type>(); 3];

        s_type.size = 0;
        s_type.alignment = 0;
        s_type.type_ = type_tag::STRUCT;

        s_elements[0] = &raw mut types::uint8;
        s_elements[1] = &raw mut types::uint8;
        s_type.elements = s_elements.as_mut_ptr();

        let mut l_type = ffi_type::default();
        let mut l_elements = [ptr::null_mut::<ffi_type>(); 6];

        l_type.size = 0;
        l_type.alignment = 0;
        l_type.type_ = type_tag::STRUCT;

        l_elements[0] = &raw mut types::uint32;
        l_elements[1] = &raw mut types::uint32;
        l_elements[2] = &raw mut types::uint32;
        l_elements[3] = &raw mut types::uint32;
        l_elements[4] = &raw mut types::uint32;
        l_type.elements = l_elements.as_mut_ptr();

        let mut cif = ffi_cif::default();
        let mut arg_types = [
            &raw mut types::sint32,
            &raw mut s_type,
            &raw mut l_type,
            &raw mut s_type,
            &raw mut types::uint8,
            &raw mut types::sint8,
            &raw mut types::uint16,
            &raw mut types::sint16,
            &raw mut types::uint32,
            &raw mut types::sint32,
            &raw mut types::uint64,
            &raw mut types::sint64,
            &raw mut types::double,
            &raw mut types::double,
        ];

        // SAFETY:
        // `cif`, `rtype` and `atypes` points to valid, well-formed data.
        let result = unsafe {
            prep_cif_var(
                &raw mut cif,
                ffi_abi_FFI_DEFAULT_ABI,
                1,
                14,
                &raw mut types::sint32,
                (&raw mut arg_types).cast(),
            )
        };

        assert_eq!(result, Err(Error::ArgType));
    }

    #[repr(C)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct SmallStruct(u8, u16);
    #[repr(C)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct LargeStruct(u64, u64, u64, u64);

    extern "C" fn return_nothing() {}
    extern "C" fn return_i8(a: i8) -> i8 {
        a
    }
    extern "C" fn return_u8(a: u8) -> u8 {
        a
    }
    extern "C" fn return_i16(a: i16) -> i16 {
        a
    }
    extern "C" fn return_u16(a: u16) -> u16 {
        a
    }
    extern "C" fn return_i32(a: i32) -> i32 {
        a
    }
    extern "C" fn return_u32(a: u32) -> u32 {
        a
    }
    extern "C" fn return_i64(a: i64) -> i64 {
        a
    }
    extern "C" fn return_u64(a: u64) -> u64 {
        a
    }
    extern "C" fn return_pointer(a: *const c_void) -> *const c_void {
        a
    }
    extern "C" fn return_f32(a: f32) -> f32 {
        a
    }
    extern "C" fn return_f64(a: f64) -> f64 {
        a
    }
    extern "C" fn return_small_struct(a: SmallStruct) -> SmallStruct {
        a
    }
    extern "C" fn return_large_struct(a: LargeStruct) -> LargeStruct {
        a
    }

    macro_rules! test_return_value {
        ($ty:ty, $ffitype:expr, $val:expr, $fn:ident) => {
            #[allow(
                clippy::float_cmp,
                reason = "Comparing floats that are passed directly through a function in `assert_eq!`",
            )]
            {
                let mut cif = ffi_cif::default();
                let mut arg_ty_array = [&raw mut $ffitype];
                let mut arg: $ty = $val;
                let mut arg_array: [*mut c_void; 1] = [(&raw mut arg).cast()];

                // SAFETY:
                // `cif` points to a properly aligned `ffi_cif`.
                // The return value is a pointer to an `ffi_type`.
                // `arg_array` contains 1 pointer to an `ffi_type`.
                let result: $ty = unsafe {
                    prep_cif(
                        &raw mut cif,
                        ffi_abi_FFI_DEFAULT_ABI,
                        1,
                        &raw mut $ffitype,
                        arg_ty_array.as_mut_ptr(),
                    ).unwrap();

                    call(&mut cif, CodePtr($fn as *mut _), arg_array.as_mut_ptr())
                };

                assert_eq!(result, $val);
            }
        }
    }

    /// Test to ensure that values returned from functions called through libffi are correct.
    #[test]
    fn test_return_values() {
        // Test a function returning nothing.
        {
            let mut cif = ffi_cif::default();

            // SAFETY:
            // `cif` points to a properly aligned `ffi_cif`.
            // The return value is a pointer to an `ffi_type`.
            // `nargs` is 0, so argument and argument type array is never read.
            unsafe {
                prep_cif(
                    &raw mut cif,
                    ffi_abi_FFI_DEFAULT_ABI,
                    0,
                    &raw mut types::void,
                    ptr::null_mut(),
                )
                .unwrap();

                call::<()>(&mut cif, CodePtr(return_nothing as *mut _), ptr::null_mut());
            }
        }

        test_return_value!(i8, types::sint8, 0x55, return_i8);
        test_return_value!(u8, types::uint8, 0xAA, return_u8);
        test_return_value!(i16, types::sint16, 0x5555, return_i16);
        test_return_value!(u16, types::uint16, 0xAAAA, return_u16);
        test_return_value!(i32, types::sint32, 0x5555_5555, return_i32);
        test_return_value!(u32, types::uint32, 0xAAAA_AAAA, return_u32);
        test_return_value!(i64, types::sint64, 0x5555_5555_5555_5555, return_i64);
        test_return_value!(u64, types::uint64, 0xAAAA_AAAA_AAAA_AAAA, return_u64);
        test_return_value!(f32, types::float, core::f32::consts::E, return_f32);
        test_return_value!(f64, types::double, core::f64::consts::PI, return_f64);

        let mut dummy = 0;
        test_return_value!(
            *const c_void,
            types::pointer,
            (&raw mut dummy).cast(),
            return_pointer
        );

        let mut small_struct_elements = [
            &raw mut types::uint8,
            &raw mut types::uint16,
            ptr::null_mut(),
        ];
        let mut small_struct_type = ffi_type {
            type_: type_tag::STRUCT,
            elements: small_struct_elements.as_mut_ptr(),
            ..Default::default()
        };
        test_return_value!(
            SmallStruct,
            small_struct_type,
            SmallStruct(0xAA, 0x5555),
            return_small_struct
        );

        let mut large_struct_elements = [
            &raw mut types::uint64,
            &raw mut types::uint64,
            &raw mut types::uint64,
            &raw mut types::uint64,
            ptr::null_mut(),
        ];
        let mut large_struct_type = ffi_type {
            type_: type_tag::STRUCT,
            elements: large_struct_elements.as_mut_ptr(),
            ..Default::default()
        };
        test_return_value!(
            LargeStruct,
            large_struct_type,
            LargeStruct(
                0x1234_5678_9abc_def0,
                0x0fed_cba9_8765_4321,
                0x5555_5555_5555_5555,
                0xAAAA_AAAA_AAAA_AAAA,
            ),
            return_large_struct
        );
    }
}
