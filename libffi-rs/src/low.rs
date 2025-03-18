//! A low-level wrapping of libffi, this layer makes no attempts at safety, but tries to provide a
//! somewhat more idiomatic interface.
//!
//! This module also re-exports types and constants necessary for using the library, so it should
//! not be generally necessary to use the `raw` module. While this is a bit “Rustier” than
//! [`raw`], I’ve avoided drastic renaming in favor of hewing close to the libffi API.
//! See [`middle`](crate::middle) for an easier-to-use approach.

use core::{
    ffi::{c_uint, c_void},
    mem,
};

use crate::raw;

/// Errors reported by libffi.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Error {
    /// Given a bad or unsupported type representation.
    Typedef,
    /// Given a bad or unsupported ABI.
    Abi,
    /// Given invalid data structures to `ffi_prep_cif_var`.
    ///
    /// `ffi_prep_cif_var` only supports 64-bit floats (f64/double) and integers of at least `int`
    /// size.
    ArgType,
    /// An unrecognized error code, potentially a bug.
    Unknown(u32),
}

/// The [`core::result::Result`] type specialized for libffi [`Error`]s.
pub type Result<T> = core::result::Result<T, Error>;

// Converts the raw status type to a `Result`.
fn status_to_result<R>(status: ffi_status, good: R) -> Result<R> {
    match status {
        raw::ffi_status_FFI_OK => Ok(good),
        raw::ffi_status_FFI_BAD_TYPEDEF => Err(Error::Typedef),
        raw::ffi_status_FFI_BAD_ABI => Err(Error::Abi),
        raw::ffi_status_FFI_BAD_ARGTYPE => Err(Error::ArgType),
        _ => Err(Error::Unknown(status)),
    }
}

/// Wraps a function pointer of unknown type.
///
/// This is used to make the API a bit easier to understand, and as a simple type lint. As a
/// `repr(C)` struct of one element, it should be safe to transmute between `CodePtr` and
/// `*mut c_void`, or between collections thereof.
#[derive(Clone, Copy, Debug, Hash)]
#[repr(C)]
pub struct CodePtr(pub *mut c_void);

// How useful is this type? Does it need all the methods?
impl CodePtr {
    /// Initializes a code pointer from a function pointer.
    ///
    /// This is useful mainly for talking to C APIs that take untyped callbacks specified in the API
    /// as having type `void(*)()`.
    pub fn from_fun(fun: unsafe extern "C" fn()) -> Self {
        CodePtr(fun as *mut c_void)
    }

    /// Initializes a code pointer from a void pointer.
    ///
    /// This is the other common type used in APIs (or at least in libffi) for untyped callback
    /// arguments.
    pub fn from_ptr(fun: *const c_void) -> Self {
        CodePtr(fun.cast_mut())
    }

    /// Gets the code pointer typed as a C function pointer.
    ///
    /// This is useful mainly for talking to C APIs that take untyped callbacks specified in the
    /// API as having type `void(*)()`.
    ///
    /// # Safety
    ///
    /// There is no checking that the returned type reflects the actual parameter and return types
    /// of the function. Unless the C function actually has type `void(*)()`, it will need to be
    /// cast before it is called.
    ///
    /// You should also be sure that the `CodePtr` was properly initialized, as there is nothing
    /// preventing it from containing a NULL pointer.
    pub unsafe fn as_fun(&self) -> &unsafe extern "C" fn() {
        // SAFETY: See this functions' safety section.
        unsafe { self.as_any_ref_() }
    }

    /// Gets the code pointer typed as a "safe" C function pointer.
    ///
    /// This is useful mainly for talking to C APIs that take untyped callbacks specified in the
    /// API as having type `void(*)()`.
    ///
    /// # Safety
    ///
    /// There isn't necessarily anything actually safe about the resulting function pointer — it is
    /// up to the caller to know what they're doing within the unsafety boundary, or undefined
    /// behavior may result. In particular, there is no checking that the returned type reflects the
    /// actual parameter and return types of the function. Unless the C function actually has type
    /// `void(*)()`, it will need to be cast before it is called.
    ///
    /// You should also be sure that the `CodePtr` was properly initialized, as there is nothing
    /// preventing it from containing a NULL pointer.
    pub unsafe fn as_safe_fun(&self) -> &extern "C" fn() {
        // SAFETY: See this functions' safety section.
        unsafe { self.as_any_ref_() }
    }

    pub(crate) unsafe fn as_any_ref_<T>(&self) -> &T {
        // SAFETY: May attempt to create a reference from a NULL pointer, should probably be fixed.
        #[allow(
            clippy::ptr_as_ptr,
            clippy::borrow_as_ptr,
            clippy::ref_as_ptr,
            reason = "CodePtr should probably be reworked, not spending too much time making this prettier until then."
        )]
        unsafe {
            &*(&self.0 as *const _ as *const T)
        }
    }

    /// Gets the code pointer typed as a `const void*`.
    ///
    /// This is the other common type used in APIs (or at least in libffi) for untyped callback
    /// arguments.
    pub fn as_ptr(self) -> *const c_void {
        self.0
    }

    /// Gets the code pointer typed as a `void*`.
    ///
    /// This is the other common type used in APIs (or at least in libffi) for untyped callback
    /// arguments.
    pub fn as_mut_ptr(self) -> *mut c_void {
        self.0
    }
}

pub use raw::{
    ffi_abi, ffi_abi_FFI_DEFAULT_ABI, ffi_arg, ffi_cif, ffi_closure, ffi_sarg, ffi_status, ffi_type,
};

/// Re-exports the [`ffi_type`] objects used to describe the types of arguments and results.
///
/// These are from [the raw layer](crate::raw), but are renamed by removing the `ffi_type_` prefix.
/// For example, [`raw::ffi_type_void`] becomes [`types::void`].
pub mod types {
    #[cfg(feature = "complex")]
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64", target_env = "msvc")))]
    pub use crate::raw::ffi_type_complex_longdouble as complex_longdouble;
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
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

/// Type tags used in constructing and inspecting [`ffi_type`]s.
///
/// For atomic types this tag doesn’t matter because libffi predeclares
/// [an instance of each one](mod@types). However, for composite types (structs and complex
/// numbers), we need to create a new instance of the [`ffi_type`] struct. In particular, the
/// `type_` field contains a value that indicates what kind of type is represented, and we use these
/// values to indicate that that we are describing a struct or complex type.
///
/// # Examples
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
/// To pass it by value to a C function we can construct an
/// `ffi_type` as follows using `type_tag::STRUCT`:
///
/// ```
/// use std::ptr;
///
/// use libffi::low::{ffi_type, type_tag, types};
///
/// let mut elements = unsafe {
///     [
///         &raw mut types::uint16,
///         &raw mut types::uint64,
///         ptr::null_mut::<ffi_type>(),
///     ]
/// };
///
/// let my_struct: ffi_type = ffi_type {
///     type_: type_tag::STRUCT,
///     elements: elements.as_mut_ptr(),
///     ..Default::default()
/// };
/// ```
pub mod type_tag {
    use core::ffi::c_ushort;

    use crate::raw;

    /// Indicates a structure type.
    #[expect(
        clippy::cast_possible_truncation,
        reason = "TODO review whether this can be changed/use different data types"
    )]
    pub const STRUCT: c_ushort = raw::ffi_type_enum_STRUCT as c_ushort;

    /// Indicates a complex number type.
    ///
    /// This item is enabled by `#[cfg(feature = "complex")]`. It is not available when building for
    /// msvc.
    #[cfg(feature = "complex")]
    #[cfg(not(target_env = "msvc"))]
    #[expect(
        clippy::cast_possible_truncation,
        reason = "TODO review whether this can be changed/use different data types"
    )]
    pub const COMPLEX: c_ushort = raw::ffi_type_enum_COMPLEX as c_ushort;
}

/// Initalizes a CIF (Call Interface) with the given ABI
/// and types.
///
/// We need to initialize a CIF before we can use it to call a function or create a closure. This
/// function lets us specify the calling convention to use and the argument and result types. For
/// varargs CIF initialization, see [`prep_cif_var`].
///
///
/// # Safety
///
/// The CIF `cif` retains references to `rtype` and `atypes`, so if they are no longer live when the
/// CIF is used then the behavior is undefined.
///
/// # Arguments
///
/// - `cif` — the CIF to initialize
/// - `abi` — the calling convention to use
/// - `nargs` — the number of arguments
/// - `rtype` — the result type
/// - `atypes` — the argument types (length must be at least `nargs`)
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function returns an error if the underlying `ffi_prep_cif` returns an error. The following
/// error conditions are listed in `libffi`'s man pages:
///
/// * `cif` is `NULL`
/// * `rtype` or `atypes` are malformed
///   * This should not happen when passing types in [`types`].
/// * An invalid ABI is passed
///
/// # Examples
///
/// ```
/// use libffi::low::{ffi_abi_FFI_DEFAULT_ABI, ffi_cif, ffi_type, prep_cif, types};
///
/// let mut args = [&raw mut types::sint32, &raw mut types::uint64];
/// let mut cif = ffi_cif::default();
///
/// unsafe {
///     prep_cif(
///         &mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         2,
///         &raw mut types::pointer,
///         args.as_mut_ptr(),
///     )
/// }
/// .unwrap();
/// ```
pub unsafe fn prep_cif(
    cif: *mut ffi_cif,
    abi: ffi_abi,
    nargs: u32,
    rtype: *mut ffi_type,
    atypes: *mut *mut ffi_type,
) -> Result<()> {
    // SAFETY: It is up to the caller to make sure that `cif`, `rtype`, and `atypes` are valid
    // pointers and that `atypes` points to an array of (at least) `nargs` size.
    let status = unsafe { raw::ffi_prep_cif(cif, abi, nargs, rtype, atypes) };
    status_to_result(status, ())
}

/// Initalizes a CIF (Call Interface) for a varargs function.
///
/// We need to initialize a CIF before we can use it to call a function or create a closure. This
/// function lets us specify the calling convention to use and the argument and result types. For
/// non-varargs CIF initialization, see [`prep_cif`].
///
/// # Safety
///
/// The CIF `cif` retains references to `rtype` and `atypes`, so if they are no longer live when the
/// CIF is used then the behavior is undefined.
///
/// # Arguments
///
/// - `cif` — the CIF to initialize
/// - `abi` — the calling convention to use
/// - `nfixedargs` — the number of fixed arguments
/// - `ntotalargs` — the total number of arguments, including fixed and var args
/// - `rtype` — the result type
/// - `atypes` — the argument types (length must be at least `nargs`)
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function returns an error if the underlying `ffi_prep_cif` returns an error. The following
/// error conditions are listed in `libffi`'s man pages:
///
/// * `cif` is `NULL`
/// * `rtype` or `atypes` are malformed
///   * This should not happen when passing types in [`types`].
/// * An invalid ABI is passed
pub unsafe fn prep_cif_var(
    cif: *mut ffi_cif,
    abi: ffi_abi,
    nfixedargs: u32,
    ntotalargs: u32,
    rtype: *mut ffi_type,
    atypes: *mut *mut ffi_type,
) -> Result<()> {
    // SAFETY: It is up to the caller to make sure that `cif`, `rtype`, and `atypes` are valid
    // pointers and that `atypes` points to an array of (at least) `nargs` size.
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

/// Calls a C function as specified by a CIF.
///
/// # Arguments
///
/// * `cif` — describes the argument and result types and the calling convention
/// * `fun` — the function to call
/// * `args` — the arguments to pass to `fun`
///
/// # Result
///
/// The result of calling `fun` with `args`.
///
/// # Examples
///
/// ```
/// use std::{os::raw::c_void, ptr};
///
/// use libffi::low::{CodePtr, call, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, ffi_type, prep_cif, types};
///
/// extern "C" fn c_function(a: u64, b: u64) -> u64 {
///     a + b
/// }
///
/// let result = unsafe {
///     let mut args = [&raw mut types::uint64, &raw mut types::uint64];
///     let mut cif = ffi_cif::default();
///
///     prep_cif(
///         &raw mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         2,
///         &raw mut types::uint64,
///         args.as_mut_ptr(),
///     )
///     .unwrap();
///
///     call::<u64>(
///         &mut cif,
///         CodePtr(c_function as *mut _),
///         vec![
///             ptr::from_mut(&mut 4u64).cast(),
///             ptr::from_mut(&mut 5u64).cast(),
///         ]
///         .as_mut_ptr(),
///     )
/// };
///
/// assert_eq!(9, result);
/// ```
///
/// # Safety
/// libffi will read values from `args` based on the CIF, make sure that every pointer points to
/// correct data types that are properly aligned. Additionally, the ffi function may perform unsafe
/// actions on provided pointers.
pub unsafe fn call<R>(cif: *mut ffi_cif, fun: CodePtr, args: *mut *mut c_void) -> R {
    let mut result = mem::MaybeUninit::<R>::uninit();

    // SAFETY: It is up to the caller to ensure that the ffi_call is safe to perform.
    unsafe {
        raw::ffi_call(
            cif,
            Some(*fun.as_safe_fun()),
            result.as_mut_ptr().cast::<c_void>(),
            args,
        );

        result.assume_init()
    }
}

/// Allocates a closure.
///
/// Returns a pair of the writable closure object and the function pointer for calling it. The
/// former acts as a handle to the closure, and is used to configure and free it. The latter is the
/// code pointer used to invoke the closure. Before it can be invoked, it must be initialized with
/// [`prep_closure`] and [`prep_closure_mut`]. The closure must be deallocated using
/// [`closure_free`], after which point the code pointer should not be used.
///
/// # Examples
///
/// ```
/// use libffi::low::{closure_alloc, closure_free};
///
/// let (closure_handle, code_ptr) = closure_alloc();
///
/// // Use closure_alloc here
///
/// // Always be sure to call closure_free after use to free the closure's memory.
/// unsafe { closure_free(closure_handle) };
/// ```
pub fn closure_alloc() -> (*mut ffi_closure, CodePtr) {
    // SAFETY: Call `ffi_closure_alloc` with sufficient size for a `ffi_closure`. This writes back
    // a pointer to `code_pointer`, at which point it can be assumed to be initialized.
    unsafe {
        let mut code_pointer = mem::MaybeUninit::<*mut c_void>::uninit();
        let closure = raw::ffi_closure_alloc(size_of::<ffi_closure>(), code_pointer.as_mut_ptr());

        (
            closure.cast::<ffi_closure>(),
            CodePtr::from_ptr(code_pointer.assume_init()),
        )
    }
}

/// Frees a closure.
///
/// Closures allocated with [`closure_alloc`] must be deallocated with [`closure_free`].
///
/// # Examples
///
/// ```
/// use libffi::low::{closure_alloc, closure_free};
///
/// let (closure_handle, code_ptr) = closure_alloc();
///
/// // ...
///
/// unsafe {
///     closure_free(closure_handle);
/// }
/// ```
///
/// # Safety
/// This will free the provided pointer, make sure that it is only called on pointers returned from
/// [`closure_alloc`].
pub unsafe fn closure_free(closure: *mut ffi_closure) {
    // SAFETY: `ffi_closure_free` must be called to free any memory allocated by
    // `ffi_closure_alloc`.
    unsafe { raw::ffi_closure_free(closure.cast::<c_void>()) }
}

/// The type of function called by a closure.
///
/// `U` is the type of the user data captured by the closure and passed to the callback, and `R` is
/// the type of the result. The parameters are not typed, since they are passed as a C array of
/// `void*`.
pub type Callback<U, R> =
    unsafe extern "C" fn(cif: &ffi_cif, result: &mut R, args: *const *const c_void, userdata: &U);

/// The type of function called by a mutable closure.
///
/// `U` is the type of the user data captured by the closure and passed to the callback, and `R` is
/// the type of the result. The parameters are not typed, since they are passed as a C array of
/// `void*`.
pub type CallbackMut<U, R> = unsafe extern "C" fn(
    cif: &ffi_cif,
    result: &mut R,
    args: *const *const c_void,
    userdata: &mut U,
);

/// The callback type expected by [`raw::ffi_prep_closure_loc`].
pub type RawCallback = unsafe extern "C" fn(
    cif: *mut ffi_cif,
    result: *mut c_void,
    args: *mut *mut c_void,
    userdata: *mut c_void,
);

/// Initializes a closure with a callback function and userdata.
///
/// After allocating a closure with [`closure_alloc`], it needs to be initialized with a function
/// `callback` to call and a pointer `userdata` to pass to it. Invoking the closure’s code pointer
/// will then pass the provided arguments and the user data pointer to the callback.
///
/// For mutable userdata use [`prep_closure_mut`].
///
/// # Safety
///
/// The closure retains a reference to CIF `cif`, so that must still be live when the closure is
/// used lest undefined behavior result.
///
/// # Arguments
///
/// - `closure` — the closure to initialize
/// - `cif` — the calling convention and types for calling the closure
/// - `callback` — the function that the closure will invoke
/// - `userdata` — the closed-over value, stored in the closure and passed to the callback upon
///   invocation
/// - `code` — the closure’s code pointer, *i.e.*, the second component returned by
///   [`closure_alloc`].
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function will return an error if the `cif`'s ABI is invalid.
///
/// # Examples
///
/// ```
/// use std::{mem, os::raw::c_void};
///
/// use libffi::low::{
///     CodePtr, closure_alloc, closure_free, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif,
///     prep_closure, types,
/// };
///
/// unsafe extern "C" fn callback(
///     _cif: &ffi_cif,
///     result: &mut u64,
///     args: *const *const c_void,
///     userdata: &u64,
/// ) {
///     unsafe {
///         let args: *const *const u64 = args.cast();
///         *result = **args + *userdata;
///     }
/// }
///
/// fn twice(f: extern "C" fn(u64) -> u64, x: u64) -> u64 {
///     f(f(x))
/// }
///
/// unsafe {
///     let mut cif = ffi_cif::default();
///     let mut args = [(&raw mut types::uint64).cast()];
///     let mut userdata: u64 = 5;
///
///     prep_cif(
///         &mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         1,
///         &raw mut types::uint64,
///         args.as_mut_ptr(),
///     )
///     .unwrap();
///
///     let (closure, code) = closure_alloc();
///     let add5: extern "C" fn(u64) -> u64 = mem::transmute(code);
///
///     prep_closure(
///         closure,
///         &mut cif,
///         callback,
///         &raw mut userdata,
///         CodePtr(add5 as *mut _),
///     )
///     .unwrap();
///
///     assert_eq!(11, add5(6));
///     assert_eq!(12, add5(7));
///
///     assert_eq!(22, twice(add5, 12));
///
///     // Make sure to free the closure after we are finished with it.
///     unsafe { closure_free(closure) };
/// }
/// ```
pub unsafe fn prep_closure<U, R>(
    closure: *mut ffi_closure,
    cif: *mut ffi_cif,
    callback: Callback<U, R>,
    userdata: *const U,
    code: CodePtr,
) -> Result<()> {
    // SAFETY: Up to the caller, see this function's safety section.
    let status = unsafe {
        raw::ffi_prep_closure_loc(
            closure,
            cif,
            Some(mem::transmute::<Callback<U, R>, RawCallback>(callback)),
            userdata as *mut c_void,
            code.as_mut_ptr(),
        )
    };

    status_to_result(status, ())
}

/// Initializes a mutable closure with a callback function and (mutable) userdata.
///
/// After allocating a closure with [`closure_alloc`], it needs to be initialized with a function
/// `callback` to call and a pointer `userdata` to pass to it. Invoking the closure’s code pointer
/// will then pass the provided arguments and the user data pointer to the callback.
///
/// For immutable userdata use [`prep_closure`].
///
/// # Safety
///
/// The closure retains a reference to CIF `cif`, so that must still be live when the closure is
/// used lest undefined behavior result.
///
/// # Arguments
///
/// - `closure` — the closure to initialize
/// - `cif` — the calling convention and types for calling the closure
/// - `callback` — the function that the closure will invoke
/// - `userdata` — the closed-over value, stored in the closure and passed to the callback upon
///   invocation
/// - `code` — the closure’s code pointer, *i.e.*, the second component returned by
///   [`closure_alloc`].
///
/// # Result
///
/// `Ok(())` for success or `Err(e)` for failure.
///
/// # Errors
///
/// This function will return an error if the `cif`'s ABI is invalid.
///
/// # Examples
///
/// ```
/// use std::{mem, os::raw::c_void};
///
/// use libffi::low::{
///     CodePtr, closure_alloc, closure_free, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif,
///     prep_closure_mut, types,
/// };
///
/// unsafe extern "C" fn callback(
///     _cif: &ffi_cif,
///     result: &mut u64,
///     args: *const *const c_void,
///     userdata: &mut u64,
/// ) {
///     unsafe {
///         let args: *const *const u64 = args.cast();
///         *result = *userdata;
///         *userdata += **args;
///     }
/// }
///
/// fn twice(f: extern "C" fn(u64) -> u64, x: u64) -> u64 {
///     f(f(x))
/// }
///
/// unsafe {
///     let mut cif = ffi_cif::default();
///     let mut args = [(&raw mut types::uint64).cast()];
///     let mut userdata: u64 = 5;
///
///     prep_cif(
///         &mut cif,
///         ffi_abi_FFI_DEFAULT_ABI,
///         1,
///         &raw mut types::uint64,
///         args.as_mut_ptr(),
///     )
///     .unwrap();
///
///     let (closure, code) = closure_alloc();
///     let add5: extern "C" fn(u64) -> u64 = mem::transmute(code);
///
///     prep_closure_mut(
///         closure,
///         &mut cif,
///         callback,
///         &raw mut userdata,
///         CodePtr(add5 as *mut _),
///     )
///     .unwrap();
///
///     assert_eq!(5, add5(6));
///     assert_eq!(11, add5(7));
///
///     assert_eq!(19, twice(add5, 1));
///
///     // Make sure to free the closure after we are finished with it.
///     unsafe { closure_free(closure) };
/// }
/// ```
pub unsafe fn prep_closure_mut<U, R>(
    closure: *mut ffi_closure,
    cif: *mut ffi_cif,
    callback: CallbackMut<U, R>,
    userdata: *mut U,
    code: CodePtr,
) -> Result<()> {
    // SAFETY: Up to the caller, see this function's safety section.
    let status = unsafe {
        raw::ffi_prep_closure_loc(
            closure,
            cif,
            Some(mem::transmute::<CallbackMut<U, R>, RawCallback>(callback)),
            userdata.cast::<c_void>(),
            code.as_mut_ptr(),
        )
    };

    status_to_result(status, ())
}

#[cfg(all(test, not(miri)))]
mod test {
    use core::ptr;

    use libffi_sys::FFI_TYPE_STRUCT;

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

        // SAFETY: Both `bad_arg` and `cif` are pointers to valid data.
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

        // SAFETY: `cif` is a pointer to valid data.
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
        #[allow(
            clippy::cast_possible_truncation,
            reason = "Type tags are stored as u32 for some reason, however all fit in a u16"
        )]
        {
            s_type.type_ = FFI_TYPE_STRUCT as u16;
        }

        s_elements[0] = &raw mut types::uint8;
        s_elements[1] = &raw mut types::uint8;
        s_type.elements = s_elements.as_mut_ptr();

        let mut l_type = ffi_type::default();
        let mut l_elements = [ptr::null_mut::<ffi_type>(); 6];

        l_type.size = 0;
        l_type.alignment = 0;
        #[allow(
            clippy::cast_possible_truncation,
            reason = "Type tags are stored as u32 for some reason, however all fit in a u16"
        )]
        {
            l_type.type_ = FFI_TYPE_STRUCT as u16;
        }

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

        // SAFETY: Both `cif` and `args` are pointers to valid data.
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
}
