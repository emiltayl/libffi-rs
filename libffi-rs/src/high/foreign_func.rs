use core::marker::PhantomData;

use crate::high::CodePtr;
use crate::high::types::{FfiArgs, FfiRet};
use crate::middle::{Cif, FfiAbi, ffi_abi_FFI_DEFAULT_ABI};

/// Wrapper around a FFI function where the signature of the function is known at compile-time. This
/// can for example be used to load plugin functionality from .dll/.so files that are loaded at
/// run-time.
///
/// Note that if you are using [`ForeignFunc`], you are likely able to just transmute pointers to
/// function pointers (`fn (argtype1, argtype2, ..., argtypeN) -> rettype`) directly and avoid the
/// entire libffi machinery.
///
/// # Example
///
/// ```
/// use libffi::high::{CodePtr, ForeignFunc};
///
/// extern "C" fn add(a: u32, b: u32) -> u32 {
///     a + b
/// }
///
/// extern "C" fn return_three() -> u32 {
///     3
/// }
///
/// extern "C" fn add_one_to_u32_ptr(a: *mut u32) {
///     unsafe {
///         *a += 1;
///     }
/// }
///
/// let add_func = ForeignFunc::<(u32, u32), u32>::new(CodePtr(add as *mut _));
/// // Note the extra parentheses in `ForeignFunc::call`, they are needed around the parameters.
/// let result = unsafe { add_func.call((3, 6)) };
///
/// assert_eq!(result, 9);
///
/// // If the function does not accept any parameters, set the first type parameter to ().
/// let return_three_func = ForeignFunc::<(), u32>::new(CodePtr(return_three as *mut _));
/// // `()` must also be provided to `ForeignFunc::call` if the function does not accept any
/// // parameters.
/// let three = unsafe { return_three_func.call(()) };
/// assert_eq!(three, 3);
///
/// let mut num: u32 = 4;
/// // () as the second type parameter signifies that the function does not return anything (void).
/// let add_one_to_u32_func =
///     ForeignFunc::<*mut u32, ()>::new(CodePtr(add_one_to_u32_ptr as *mut _));
/// // If the first type parameter is only a single type not in a tuple, extra parentheses are not
/// // needed for `ForeignFunc::call`.
/// unsafe {
///     add_one_to_u32_func.call(&raw mut num);
/// }
/// assert_eq!(num, 5);
/// ```
#[derive(Debug, Clone)]
pub struct ForeignFunc<ARGS, RET>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet,
{
    cif: Cif,
    fn_ptr: CodePtr,
    _signature: PhantomData<fn(ARGS) -> RET>,
}

impl<ARGS, RET> ForeignFunc<ARGS, RET>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet,
{
    /// Create a new [`ForeignFunc`] with the default ABI for the function stored at `fn_ptr`.
    ///
    /// # Example
    ///
    /// ```
    /// use libffi::high::{CodePtr, ForeignFunc};
    /// extern "C" fn void_fn_impl() {}
    /// extern "C" fn identity_fn_impl(a: u32) -> u32 {
    ///     a
    /// }
    /// extern "C" fn add_fn_impl(a: u32, b: u32) -> u32 {
    ///     a + b
    /// }
    ///
    /// let void_fn = ForeignFunc::<(), ()>::new(CodePtr(void_fn_impl as *mut _));
    /// // It is also possible to provide (u32,) as the first parameter to keep things consistent.
    /// let identity_fn = ForeignFunc::<u32, u32>::new(CodePtr(void_fn_impl as *mut _));
    /// let add_fn = ForeignFunc::<(u32, u32), u32>::new(CodePtr(add_fn_impl as *mut _));
    /// ```
    #[inline]
    pub fn new(fn_ptr: CodePtr) -> Self {
        Self::new_with_abi(fn_ptr, ffi_abi_FFI_DEFAULT_ABI)
    }

    /// Identical to [`ForeignFunc::new`] except that it accepts an `abi` parameter to specify which
    /// ABI should be used when calling the function.
    #[inline]
    pub fn new_with_abi(fn_ptr: CodePtr, abi: FfiAbi) -> Self {
        let cif = Cif::new_with_abi(
            <ARGS as FfiArgs>::as_type_array().as_ref(),
            <RET as FfiRet>::as_ffi_return_type(),
            abi,
        )
        // TODO document why unreachable
        .unwrap_or_else(|_| unreachable!());

        Self {
            cif,
            fn_ptr,
            _signature: PhantomData,
        }
    }

    /// Wrap `self` in a wrapper that is `Send` and `Sync`. It is up to the caller to make sure that
    /// the function provided when creating `self` can safely be sent to another thread and called
    /// from multiple threads simultaneously.
    ///
    /// # Safety
    ///
    /// The function must be safe to call from other threads. It must also be thread safe, making
    /// it safe to call the function from several threads simultaneously.
    pub unsafe fn send_sync(self) -> ForeignFuncSendSync<ARGS, RET> {
        ForeignFuncSendSync(self)
    }

    /// Call the function defined in the [`ForeignFunc`]
    ///
    /// # Safety
    ///
    /// * Make sure that the provided `fn_ptr` is callable when calling [`ForeignFunc::call`].
    /// * Make sure that the function signature of `fn_ptr` is identical to the signature provided
    ///   when creating `self`.
    /// * Make sure eventual safety requirements for calling the function pointed to by `fn_ptr` are
    ///   fulfilled.
    #[inline]
    #[allow(
        clippy::needless_pass_by_value,
        reason = "Stylistic choice, also makes it easy to guarantee that borrowed arguments are alive when fn_ptr is called."
    )]
    pub unsafe fn call(&self, args: ARGS) -> RET {
        let arg_ptrs = args.as_arg_array();

        // SAFETY: It is up to the caller to ensure that the safety requirements for `call` have
        // been fulfilled.
        unsafe {
            self.cif
                .call(self.fn_ptr, arg_ptrs.as_ref())
                // TODO document why unreachable
                .unwrap_or_else(|_| unreachable!())
        }
    }
}

/// A [`ForeignFunc`] that is safe to send to, and share with other threads. It must be safe to
/// send `fn_ptr` to another thread, and call it from multiple threads simultaneously.
///
/// Create a `ForeignFuncSendSync` by calling [`ForeignFunc::send_sync`] on a [`ForeignFunc`]
/// object.
///
/// See [`ForeignFunc`] for more details.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct ForeignFuncSendSync<ARGS, RET>(ForeignFunc<ARGS, RET>)
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet;

impl<ARGS, RET> ForeignFuncSendSync<ARGS, RET>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet,
{
    /// This function works identical to [`ForeignFunc::call`], see its documentation for more
    /// details.
    ///
    /// # Safety
    ///
    /// In addition to the requirements listed in
    /// [`ForeignFunc::call`'s safety documentation](ForeignFunc::call#safety), it must be safe to
    /// send `self` to other threads and execute `ForeignFuncSend::call` from multiple threads
    /// simultaneously.
    #[inline]
    pub unsafe fn call(&self, args: ARGS) -> RET {
        // SAFETY: It is up to the caller to ensure the safety requirements documented for this
        // function.
        unsafe { self.0.call(args) }
    }
}

// SAFETY: It is up to the creator of `ForeignFuncSendSync` to guarantee that the [`ForeignFunc`] is
// `Send`.
unsafe impl<ARGS, RET> Send for ForeignFuncSendSync<ARGS, RET>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet,
{
}

// SAFETY: It is up to the creator of `ForeignFuncSendSync` to guarantee that the [`ForeignFunc`] is
// `Sync`.
unsafe impl<ARGS, RET> Sync for ForeignFuncSendSync<ARGS, RET>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet,
{
}

#[cfg(all(test, not(miri)))]
mod test {
    use super::*;
    use crate::high::AsFfiType;
    use crate::middle::Type;

    #[repr(C)]
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct SmallFfiStruct {
        pub number: i32,
        pub tag: u8,
    }

    // SAFETY: SmallFfiStruct is `repr(C)` and contains an `i32` and a `u8`.
    unsafe impl AsFfiType for SmallFfiStruct {
        fn as_ffi_type() -> Type {
            Type::structure(&[Type::I32, Type::U8])
        }
    }

    #[repr(C)]
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct LargeFfiStruct {
        pub a: u64,
        pub b: u64,
        pub c: u64,
        pub d: u64,
    }

    // SAFETY: LargeFfiStruct is `repr(C)` and contains four `u64`s.
    unsafe impl AsFfiType for LargeFfiStruct {
        fn as_ffi_type() -> Type {
            Type::structure(&[Type::U64, Type::U64, Type::U64, Type::U64])
        }
    }

    /// Generate code to test calling `ForeignFunc` with an arbitrary number of arguments and
    /// optionally a result value.
    ///
    /// If the macro is called with a return value, it will be recursively call itself without the
    /// return value, but the same arguments. If the macro is called without a return value, it will
    /// recursively call itself with the first argument as the return value and one argument less.
    ///
    /// A return value is added as an optional prefix: `$retty:ty = $retval:expr =>`.
    ///
    /// Arguments are added on the following format: `$($name:ident: $ty:ty = $val:expr),+`.
    macro_rules! generate_foreign_func_test {
        () => {
            {
                extern "C" fn extern_fn() {}

                let foreign_func = ForeignFunc::<(), ()>::new(CodePtr(extern_fn as *mut _));
                // SAFETY:
                // * `extern_fn` is defined as a `extern "C"` function that does not accept any
                //   parameters and does not return anything.
                // * `extern_fn` does not do anything, and is therefore thread safe.
                unsafe {
                    foreign_func.call(());

                    let send_sync = foreign_func.send_sync();
                    send_sync.call(());
                }
            }
        };

        // Output type needs to be put first to allow for an arbitrary number of arguments.
        ($ty:ty = $val:expr => ()) => {
            {
                extern "C" fn extern_fn() -> $ty {
                    $val
                }

                let foreign_func = ForeignFunc::<(), $ty>::new(CodePtr(extern_fn as *mut _));
                // SAFETY:
                // * `extern_fn` is defined as a `extern "C"` function that does not accept any
                //   parameters and returns a value of the type `$ty`. perform
                // * `extern_fn` only returns a value, it does not perform any actions that are not
                //   thread safe.
                unsafe {
                    let result = foreign_func.call(());
                    assert_eq!(result, $val);

                    let send_sync = foreign_func.send_sync();
                    let result = send_sync.call(());
                    assert_eq!(result, $val);
                }
            }

            generate_foreign_func_test!();
        };

        ($name:ident: $ty:ty = $val:expr) => {
            {
                extern "C" fn extern_fn($name: $ty) {
                    assert_eq!($name, $val);
                }

                let foreign_func = ForeignFunc::<($ty,), ()>::new(CodePtr(extern_fn as *mut _));
                // SAFETY:
                // * `extern_fn` is defined as a `extern "C"` function that accepts one parameter of
                //   the value `$ty` and does not return anything.
                // * `extern_fn` only compares a parameter to its expected values, it does not
                //   perform any actions that are not thread safe.
                unsafe {
                    foreign_func.call(($val,));

                    let send_sync = foreign_func.send_sync();
                    send_sync.call(($val,));
                }
            }

            generate_foreign_func_test!($ty = $val => ());
        };

        ($retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr) => {
            {
                extern "C" fn extern_fn($name: $ty) -> $retty {
                    assert_eq!($name, $val);
                    $retval
                }

                let foreign_func = ForeignFunc::<($ty,), $retty>::new(CodePtr(extern_fn as *mut _));
                // SAFETY:
                // * `extern_fn` is defined as a `extern "C"` function that accepts a single
                //   parameter of the type `$ty` and returns a value of the type `$retty`.
                // * `extern_fn` only compares a parameter to its expected value and returns a
                //   value, it does not perform any actions that are not thread safe.
                unsafe {
                    let result = foreign_func.call(($val,));
                    assert_eq!(result, $retval);

                    let send_sync = foreign_func.send_sync();
                    let result = send_sync.call(($val,));
                    assert_eq!(result, $retval);
                }
            }

            generate_foreign_func_test!($name: $ty = $val);
        };

        ($name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                extern "C" fn extern_fn($name: $ty, $($restname: $restty),+) {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                }

                let foreign_func = ForeignFunc::<($ty, $($restty,)+), ()>::new(CodePtr(extern_fn as *mut _));
                // SAFETY:
                // * `extern_fn` is defined as a `extern "C"` function that accepts parameters of
                //   the types `($ty, $($restty,)+)` and does not return anything.
                // * `extern_fn` only compares parameters to their expected values, it does not
                //   perform any actions that are not thread safe.
                unsafe {
                    foreign_func.call(($val, $($restval),+));

                    let send_sync = foreign_func.send_sync();
                    send_sync.call(($val, $($restval),+));
                }
            }

            generate_foreign_func_test!($ty = $val => $($restname: $restty = $restval),+);
        };

        ($retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                extern "C" fn extern_fn($name: $ty, $($restname: $restty),+) -> $retty {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                    $retval
                }

                let foreign_func = ForeignFunc::<($ty, $($restty,)+), $retty>::new(CodePtr(extern_fn as *mut _));
                // SAFETY:
                // * `extern_fn` is defined as a `extern "C"` function that accepts parameters of
                //   the types `($ty, $($restty,)+)` and returns a value of the type `$retty`.
                // * `extern_fn` only compares parameters to their expected values and returns a
                //   value, it does not perform any actions that are not thread safe.
                unsafe {
                    let result = foreign_func.call(($val, $($restval),+));
                    assert_eq!(result, $retval);

                    let send_sync = foreign_func.send_sync();
                    let result = send_sync.call(($val, $($restval),+));
                    assert_eq!(result, $retval);
                }
            }

            generate_foreign_func_test!($name: $ty = $val, $($restname: $restty = $restval),+);
        };
    }

    #[expect(
        clippy::float_cmp,
        reason = "Direct comparison of floats that have not been modified."
    )]
    #[test]
    fn test_all_arg_and_ret_types() {
        generate_foreign_func_test!(
            i8 = 0x55 =>
            a: i8 = 0x55,
            b: u8 = 0xAA,
            c: i16 = 0x5555,
            d: u16 = 0xAAAA,
            e: i32 = 0x5555_5555,
            f: u32 = 0xAAAA_AAAA,
            g: i64 = 0x5555_5555_5555_5555,
            h: u64 = 0xAAAA_AAAA_AAAA_AAAA,
            i: isize = 0x5555_5555,
            j: usize = 0xAAAA_AAAA,
            k: f32 = std::f32::consts::PI,
            l: f64 = std::f64::consts::TAU,
            m: *const i32 = 0xDEAD_BEEF as *const i32,
            n: SmallFfiStruct = SmallFfiStruct { number: 0x5555_5555, tag: 0xAA },
            o: LargeFfiStruct = LargeFfiStruct {
                a: 0xAAAA_AAAA_AAAA_AAAA,
                b: 0xAAAA_AAAA_AAAA_AAAA,
                c: 0xAAAA_AAAA_AAAA_AAAA,
                d: 0xAAAA_AAAA_AAAA_AAAA,
            },
            p: u8 = 0
        );
    }
}
