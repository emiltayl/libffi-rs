extern crate alloc;

use alloc::vec;
#[cfg(not(test))]
use alloc::vec::Vec;

use super::Error;
use super::types::Type;

/// Provides a builder-style API for constructing CIFs and closures.
///
/// To use a builder, first construct it using [`Builder::new`]. The default calling convention is
/// [`ffi_abi_FFI_DEFAULT_ABI`], and the default function type is `extern "C" fn()` (or in C,
/// `void(*)()`). Add argument types to the function type with the [`Builder::arg`] and [`args`]
/// methods. Set the result type with [`Builder::res`]. Change the calling convention, if
/// necessary, with [`Builder::abi`].
///
/// Once the builder is configured, construct a `Cif` with [`Builder::into_cif`] or a closure with
/// [`Builder::into_closure`], [`into_closure_mut`], [`into_closure_owned`], or
/// [`into_closure_owned_mut`].
///
/// # Examples
///
/// Calling an `extern` function:
///
/// ```
/// use libffi::middle::{Arg, Builder, CodePtr, Type, ffi_abi_FFI_DEFAULT_ABI};
///
/// # #[unsafe(no_mangle)]
/// # extern "C" fn foreign_mul(a: u64, b: u64) -> u64 { a * b }
/// unsafe extern "C" {
///     #[link_name = "foreign_mul"]
///     fn mul(a: u64, b: u64) -> u64;
/// }
///
/// # use libffi::middle::Error;
/// # fn main() -> Result<(), Error> {
/// let cif = Builder::new()
///     // The default ABI is set by default, so the `abi` call is not needed unless you need to
///     // function with a non-default ABI.
///     .abi(ffi_abi_FFI_DEFAULT_ABI)
///     .args(&[Type::U64, Type::U64])
///     .res(Some(Type::U64))
///     .into_cif()?;
///
/// // SAFETY: `mul` only accepts literal values and performs a multiplication, returning a `u64`.
/// let result: u64 = unsafe {
///     cif.call(
///         CodePtr(mul as *mut _),
///         &[Arg::borrowed(&3u64), Arg::borrowed(&5u64)],
///     )
/// }?;
///
/// assert_eq!(result, 3 * 5);
/// #   Ok(())
/// # }
/// ```
///
/// Building and calling a closure:
///
/// ```
/// use std::mem;
/// use std::os::raw::c_void;
///
/// use libffi::low;
/// use libffi::middle::{Builder, Type};
///
/// unsafe extern "C" fn lambda_callback<F: Fn(u64, u64) -> u64>(
///     _cif: &low::ffi_cif,
///     result: *mut mem::MaybeUninit<u64>,
///     args: *const *const c_void,
///     userdata: *const F,
/// ) {
///     // SAFETY: Callers of this function needs to make sure that `args` is an array with two
///     // pointers to `u64`s.
///     unsafe {
///         let args: *const &u64 = args.cast();
///         let arg_1 = **args.offset(0);
///         let arg_2 = **args.offset(1);
///
///         (*result).write((*userdata)(arg_1, arg_2));
///     }
/// }
///
/// # use libffi::middle::Error;
/// # fn main() -> Result<(), Error> {
/// let lambda = |x: u64, y: u64| x + y;
///
/// let closure = Builder::new()
///     .arg(Type::U64)
///     .arg(Type::U64)
///     .res(Some(Type::U64))
///     // In this case, a reference to the lambda `lambda` is the closure's `userdata`.
///     .into_closure(lambda_callback, &lambda)?;
///
/// // SAFETY: `lambda_callback` takes two `u64`s and returns a `u64`.
/// unsafe {
///     let fun: unsafe extern "C" fn(u64, u64) -> u64 = closure.instantiate_code_ptr();
///
///     assert_eq!(11, fun(5, 6));
///     assert_eq!(12, fun(5, 7));
/// }
/// #   Ok(())
/// # }
/// ```
///
/// [`args`]: `Builder::args`
/// [`ffi_abi_FFI_DEFAULT_ABI`]: `crate::low::ffi_abi_FFI_DEFAULT_ABI`
/// [`into_closure_mut`]: `Builder::into_closure_mut`
/// [`into_closure_owned`]: `Builder::into_closure_owned`
/// [`into_closure_owned_mut`]: `Builder::into_closure_owned_mut`
#[derive(Clone, Debug)]
pub struct Builder {
    args: Vec<Type>,
    res: Option<Type>,
    abi: super::FfiAbi,
}

impl Default for Builder {
    fn default() -> Self {
        Builder::new()
    }
}

impl Builder {
    /// Constructs a `Builder`.
    pub fn new() -> Self {
        Builder {
            args: vec![],
            res: None,
            abi: super::ffi_abi_FFI_DEFAULT_ABI,
        }
    }

    /// Adds a type to the argument type list.
    #[must_use]
    pub fn arg(mut self, type_: Type) -> Self {
        self.args.push(type_);
        self
    }

    /// Adds several types to the argument type list.
    #[must_use]
    pub fn args(mut self, types: &[Type]) -> Self {
        self.args.extend_from_slice(types);
        self
    }

    /// Sets the result type.
    #[must_use]
    pub fn res(mut self, type_: Option<Type>) -> Self {
        self.res = type_;
        self
    }

    /// Sets the calling convention.
    #[must_use]
    pub fn abi(mut self, abi: super::FfiAbi) -> Self {
        self.abi = abi;
        self
    }

    /// Builds a CIF.
    ///
    /// # Errors
    ///
    /// See [`Cif::new`](`crate::middle::Cif::new`) for possible error conditions.
    pub fn into_cif(self) -> Result<super::Cif, Error> {
        super::Cif::new_with_abi(&self.args, self.res, self.abi)
    }

    /// Builds an immutable closure.
    ///
    /// # Arguments
    ///
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the pointer to pass to `callback` along with the arguments when the closure
    ///   is called
    ///
    /// # Result
    ///
    /// The new closure.
    ///
    /// # Errors
    ///
    /// See [`Cif::new`](`crate::middle::Cif::new`) for possible error conditions.
    pub fn into_closure<U, R>(
        self,
        callback: super::Callback<U, R>,
        userdata: &U,
    ) -> Result<super::Closure<'_>, Error> {
        super::Closure::new(self.into_cif()?, callback, userdata)
    }

    /// Builds a mutable closure.
    ///
    /// # Arguments
    ///
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the pointer to pass to `callback` along with the arguments when the closure
    ///   is called
    ///
    /// # Result
    ///
    /// The new closure.
    ///
    /// # Errors
    ///
    /// See [`Cif::new`](`crate::middle::Cif::new`) for possible error conditions.
    pub fn into_closure_mut<U, R>(
        self,
        callback: super::CallbackMut<U, R>,
        userdata: &mut U,
    ) -> Result<super::Closure<'_>, Error> {
        super::Closure::new_mut(self.into_cif()?, callback, userdata)
    }

    /// Builds a closure that owns its `userdata`.
    ///
    /// # Arguments
    ///
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the object to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Result
    ///
    /// The new closure.
    ///
    /// # Errors
    ///
    /// See [`Cif::new`](`crate::middle::Cif::new`) for possible error conditions.
    pub fn into_closure_owned<U: 'static, R>(
        self,
        callback: super::Callback<U, R>,
        userdata: U,
    ) -> Result<super::ClosureOwned<U>, Error> {
        super::ClosureOwned::new(self.into_cif()?, callback, userdata)
    }

    /// Builds a closure that owns and can mutate its `userdata`.
    ///
    /// # Arguments
    ///
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the object to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Result
    ///
    /// The new closure.
    ///
    /// # Errors
    ///
    /// See [`Cif::new`](`crate::middle::Cif::new`) for possible error conditions.
    pub fn into_closure_owned_mut<U: 'static, R>(
        self,
        callback: super::CallbackMut<U, R>,
        userdata: U,
    ) -> Result<super::ClosureOwned<U>, Error> {
        super::ClosureOwned::new_mut(self.into_cif()?, callback, userdata)
    }
}

#[cfg(all(test, not(miri)))]
mod test {
    use core::ffi::c_void;
    use core::mem::MaybeUninit;

    use libffi_sys::ffi_abi_FFI_DEFAULT_ABI;

    use super::*;
    use crate::low::{CodePtr, ffi_cif};
    use crate::middle::Arg;

    unsafe extern "C" fn add_two_usizes(a: usize, b: usize) -> usize {
        a + b
    }

    unsafe extern "C" fn ref_lambda_callback<F: Fn(u64, u64) -> u64>(
        _cif: &ffi_cif,
        result: *mut MaybeUninit<u64>,
        args: *const *const c_void,
        userdata: *const F,
    ) {
        // SAFETY: Callers of this function needs to make sure that `args` is an array with two
        // pointers to `u64`s.
        unsafe {
            let args: *const &u64 = args.cast();
            let arg_1 = **args.offset(0);
            let arg_2 = **args.offset(1);

            (*result).write((*userdata)(arg_1, arg_2));
        }
    }

    unsafe extern "C" fn mut_ref_lambda_callback<F: Fn(u64, u64) -> u64>(
        _cif: &ffi_cif,
        result: *mut MaybeUninit<u64>,
        args: *const *const c_void,
        userdata: *mut F,
    ) {
        // SAFETY: Callers of this function needs to make sure that `args` is an array with two
        // pointers to `u64`s.
        unsafe {
            let args: *const &u64 = args.cast();
            let arg_1 = **args.offset(0);
            let arg_2 = **args.offset(1);

            (*result).write((*userdata)(arg_1, arg_2));
        }
    }

    #[test]
    fn test_add_two_usizes() {
        let a: usize = 0xABCD_EF01;
        let b: usize = 0x1234_5678;

        let cif = Builder::new()
            .arg(Type::Usize)
            .arg(Type::Usize)
            .res(Some(Type::Usize))
            .abi(ffi_abi_FFI_DEFAULT_ABI)
            .into_cif()
            .unwrap();

        // SAFETY:
        // `add_two_usizes` is an `extern "C"` function that accepts two `usize`s and returns one
        // `usize`.
        let result: usize = unsafe {
            cif.call(
                CodePtr(add_two_usizes as *mut _),
                &[Arg::borrowed(&a), Arg::borrowed(&b)],
            )
            .unwrap()
        };

        assert_eq!(a + b, result);
    }

    #[test]
    fn test_closure_variants() {
        // mut_ref
        let mut lambda = |x: u64, y: u64| x + y;
        let closure = Builder::new()
            .arg(Type::U64)
            .arg(Type::U64)
            .res(Some(Type::U64))
            .into_closure_mut(mut_ref_lambda_callback, &mut lambda)
            .unwrap();

        // SAFETY: `mut_ref_lambda_callback` takes two `u64`s and returns a `u64`.
        unsafe {
            let fun: unsafe extern "C" fn(u64, u64) -> u64 = closure.instantiate_code_ptr();

            assert_eq!(11, fun(5, 6));
            assert_eq!(12, fun(5, 7));
        }

        // owned
        let lambda = |x: u64, y: u64| x + y;
        let closure = Builder::new()
            .arg(Type::U64)
            .arg(Type::U64)
            .res(Some(Type::U64))
            .into_closure_owned(ref_lambda_callback, lambda)
            .unwrap();

        // SAFETY: `ref_lambda_callback` takes two `u64`s and returns a `u64`.
        unsafe {
            let fun: unsafe extern "C" fn(u64, u64) -> u64 = closure.instantiate_code_ptr();

            assert_eq!(11, fun(5, 6));
            assert_eq!(12, fun(5, 7));
        }

        // owned_mut
        let lambda = |x: u64, y: u64| x + y;
        let closure = Builder::new()
            .arg(Type::U64)
            .arg(Type::U64)
            .res(Some(Type::U64))
            .into_closure_owned_mut(mut_ref_lambda_callback, lambda)
            .unwrap();

        // SAFETY: `mut_ref_lambda_callback` takes two `u64`s and returns a `u64`.
        unsafe {
            let fun: unsafe extern "C" fn(u64, u64) -> u64 = closure.instantiate_code_ptr();

            assert_eq!(11, fun(5, 6));
            assert_eq!(12, fun(5, 7));
        }
    }
}
