extern crate alloc;

#[cfg(not(test))]
use alloc::boxed::Box;
use core::marker::PhantomData;
use core::sync::atomic::AtomicBool;

use super::{Closurable, ClosureMutable};
use crate::high::{FfiArgs, FfiRet};
use crate::middle::{Cif, ClosureOwned};

/// `Closure` accepts a Rust closure and creates a function pointer so that a function pointer to
/// the closure can be sent across FFI boundaries.
pub struct Closure<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: Closurable<ARGS, RET, FN>,
{
    inner: ClosureOwned<FN>,
    _phantom: PhantomData<(ARGS, RET)>,
}

impl<ARGS, RET, FN> Closure<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: Closurable<ARGS, RET, FN>,
{
    /// Creates a new [`Closure`]. Closures created with [`Closure::new`] aborts if the closure, or
    /// code called by the closure, panics.
    ///
    /// # Panics
    ///
    /// This function panics if libffi is unable to allocate memory for the closure.
    #[inline]
    pub fn new(func: FN) -> Self {
        let cif = Cif::new(
            <ARGS as FfiArgs>::as_type_array().as_ref(),
            <RET as FfiRet>::as_ffi_return_type(),
        );

        let inner = ClosureOwned::new(cif, FN::call_closure, func);

        Self {
            inner,
            _phantom: PhantomData,
        }
    }

    /// Creates a new [`Closure`]. Panics in closures created with [`Closure::new_unwindable`] can
    /// be caught with [`std::panic::catch_unwind`].
    ///
    /// # Panics
    ///
    /// This function panics if libffi is unable to allocate memory for the closure.
    pub fn new_unwindable(func: FN) -> Self {
        let cif = Cif::new(
            <ARGS as FfiArgs>::as_type_array().as_ref(),
            <RET as FfiRet>::as_ffi_return_type(),
        );

        let inner = ClosureOwned::new_unwindable(cif, FN::call_closure_unwindable, func);

        Self {
            inner,
            _phantom: PhantomData,
        }
    }

    /// Returns a function pointer that can be used to execute the closure. Note that the function
    /// pointer is only valid as long as `self` is alive. Calling the function pointer after `self`
    /// is dropped is undefined behavior.
    pub fn as_fn_ptr(&self) -> FN::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { FN::ptr_to_self(self.inner.code.0) }
    }

    /// Consumes and leaks the `Closure` using [`Box::leak`] See `Box`'s documentation for more
    /// details.
    ///
    /// Note that `FN` must outlive `'leak`, if a `'static` reference is needed, `FN` must also be
    /// 'static.
    pub fn leak<'leak>(self) -> &'leak Closure<ARGS, RET, FN> {
        Box::leak(Box::new(self))
    }
}

// SAFETY: If the closure `FN` is `Send`, `Closure` should also be `Send` as there is nothing else
// in `Closure` that cannot be sent to another thread.
unsafe impl<ARGS, RET, FN> Send for Closure<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: Closurable<ARGS, RET, FN> + Send,
{
}

// SAFETY: If the closure `FN` is `Sync`, `Closure` should also be `Sync` as there is nothing else
// in `Closure` that cannot be shared with another thread.
unsafe impl<ARGS, RET, FN> Sync for Closure<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: Closurable<ARGS, RET, FN> + Sync,
{
}

/// `ClosureMut` accepts a mutable Rust closure and creates a function pointer so that a function
/// pointer to the closure can be sent across FFI boundaries.
pub struct ClosureMut<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: ClosureMutable<ARGS, RET, FN>,
{
    inner: ClosureOwned<(FN, AtomicBool)>,
    _phantom: PhantomData<(ARGS, RET)>,
}

impl<ARGS, RET, FN> ClosureMut<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: ClosureMutable<ARGS, RET, FN>,
{
    /// Creates a new [`ClosureMut`]. Closures created with [`ClosureMut::new`] aborts if the
    /// closure, or code called by the closure, panics. Since [`ClosureMut`] takes `FnMut` closures,
    /// attempting to call the closure several times concurrently will also abort the process.
    ///
    /// If multiple concurrent calls is needed, it is recommended to use a `Closure` which calls a
    /// non-mut `Fn` and accesses shared data through a synchronization primitive such as a `Mutex`.
    ///
    /// # Panics
    ///
    /// This function panics if libffi is unable to allocate memory for the closure.
    pub fn new(func: FN) -> Self {
        let cif = Cif::new(
            <ARGS as FfiArgs>::as_type_array().as_ref(),
            <RET as FfiRet>::as_ffi_return_type(),
        );

        let inner = ClosureOwned::new_mut(cif, FN::call_closure, (func, AtomicBool::new(false)));

        Self {
            inner,
            _phantom: PhantomData,
        }
    }

    /// Creates a new [`ClosureMut`] with unwinding panics. This is only available for testing.
    ///
    /// # Panics
    ///
    /// This function panics if libffi is unable to allocate memory for the closure.
    #[cfg(test)]
    #[doc(hidden)]
    pub fn new_unwindable(func: FN) -> Self {
        let cif = Cif::new(
            <ARGS as FfiArgs>::as_type_array().as_ref(),
            <RET as FfiRet>::as_ffi_return_type(),
        );

        let inner = ClosureOwned::new_unwindable_mut(
            cif,
            FN::call_closure_unwindable,
            (func, AtomicBool::new(false)),
        );

        Self {
            inner,
            _phantom: PhantomData,
        }
    }

    /// Returns a function pointer that can be used to execute the closure. Note that the function
    /// pointer is only valid as long as `self` is alive. Calling the function pointer after `self`
    /// is dropped is undefined behavior.
    pub fn as_fn_ptr(&self) -> FN::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { FN::ptr_to_self(self.inner.code.0) }
    }

    /// Consumes and leaks the `Closure` using [`Box::leak`] See `Box`'s documentation for more
    /// details.
    ///
    /// Note that `FN` must outlive `'leak`, if a `'static` reference is needed, `FN` must also be
    /// 'static.
    pub fn leak<'leak>(self) -> &'leak ClosureMut<ARGS, RET, FN> {
        Box::leak(Box::new(self))
    }
}

// SAFETY: If the closure `FN` is `Send`, `ClosureMut` should also be `Send` as there is nothing
// else in `ClosureMut` that cannot be sent to another thread.
unsafe impl<ARGS, RET, FN> Send for ClosureMut<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: ClosureMutable<ARGS, RET, FN> + Send,
{
}

// SAFETY: If the closure `FN` is `Sync`, `ClosureMut` should also be `Sync` as `ClosureMut`
// utilizes atomics to ensure unique access to the closure when called. Note that `ClosureMut` will
// abort if called several times concurrently.
unsafe impl<ARGS, RET, FN> Sync for ClosureMut<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: ClosureMutable<ARGS, RET, FN> + Sync,
{
}

#[cfg(all(test, not(miri)))]
mod test {
    use core::hint::spin_loop;
    use core::sync::atomic::Ordering;
    use core::time::Duration;
    use std::time::Instant;

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

    macro_rules! test_identity_closures {
        ($ty:ty = $val:expr) => {{
            let original: $ty = $val;
            let closure = Closure::new(|val: $ty| val);
            assert_eq!((closure.as_fn_ptr())($val), original);

            let original: $ty = $val;
            let closure = ClosureMut::new(|val: $ty| val);
            assert_eq!((closure.as_fn_ptr())($val), original);
        }};
    }

    #[expect(
        clippy::float_cmp,
        reason = "Direct comparison of floats that have not been modified."
    )]
    #[test]
    fn test_identity_closures() {
        let mut num: i8 = 0;

        test_identity_closures!(i8 = 0x55);
        test_identity_closures!(u8 = 0xAA);
        test_identity_closures!(i16 = 0x5555);
        test_identity_closures!(u16 = 0xAAAA);
        test_identity_closures!(i32 = 0x5555_5555);
        test_identity_closures!(u32 = 0xAAAA_AAAA);
        test_identity_closures!(i64 = 0x5555_5555_5555_5555);
        test_identity_closures!(u64 = 0xAAAA_AAAA_AAAA_AAAA);
        test_identity_closures!(isize = 0x5555_5555);
        test_identity_closures!(usize = 0xAAAA_AAAA);
        test_identity_closures!(f32 = std::f32::consts::LN_2);
        test_identity_closures!(f64 = std::f64::consts::LN_10);
        test_identity_closures!(*const i8 = &raw const num);
        test_identity_closures!(*mut i8 = &raw mut num);
        test_identity_closures!(
            SmallFfiStruct = SmallFfiStruct {
                number: 0x5555_5555,
                tag: 0xAA
            }
        );
        test_identity_closures!(
            LargeFfiStruct = LargeFfiStruct {
                a: 0xAAAA_AAAA_AAAA_AAAA,
                b: 0xAAAA_AAAA_AAAA_AAAA,
                c: 0xAAAA_AAAA_AAAA_AAAA,
                d: 0xAAAA_AAAA_AAAA_AAAA,
            }
        );
    }

    #[test]
    fn closure_can_unwind() {
        let result = std::panic::catch_unwind(|| {
            #[expect(
                clippy::unused_unit,
                reason = "`Closure` is unable to find the correct trait implementation without `-> ()`"
            )]
            let closure = Closure::new_unwindable(|| -> () { panic!("Test") });

            (closure.as_fn_ptr())();
        });

        assert!(result.is_err());
    }

    /// Generate code to test calling closures with an arbitrary number of arguments and
    /// optionally a result value.
    ///
    /// If the macro is called with a return value, it will be recursively call itself without the
    /// return value, but the same arguments. If the macro is called without a return value, it will
    /// recursively call itself with the first argument as the return value and one argument less.
    ///
    /// A return value is added as an optional prefix: `$retty:ty = $retval:expr =>`.
    ///
    /// Arguments are added on the following format: `$($name:ident: $ty:ty = $val:expr),+`.
    macro_rules! generate_closure_test {
        () => {
            {
                let closure = Closure::new_unwindable(|| {});
                (closure.as_fn_ptr())();

                let closuremut = ClosureMut::new_unwindable(|| {});
                (closuremut.as_fn_ptr())();
            }
        };

        // Output type needs to be put first to allow for an arbitrary number of arguments.
        ($ty:ty = $val:expr => ()) => {
            {
                let closure = Closure::new_unwindable(|| -> $ty {$val});
                let result = (closure.as_fn_ptr())();
                assert_eq!(result, $val);

                let closuremut = ClosureMut::new_unwindable(|| -> $ty {$val});
                let result = (closuremut.as_fn_ptr())();
                assert_eq!(result, $val);
            }

            generate_closure_test!();
        };

        ($name:ident: $ty:ty = $val:expr) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty| {
                    assert_eq!($name, $val);
                });
                (closure.as_fn_ptr())($val);

                let closuremut = ClosureMut::new_unwindable(|$name: $ty| {
                    assert_eq!($name, $val);
                });
                (closuremut.as_fn_ptr())($val);
            }

            generate_closure_test!($ty = $val => ());
        };

        ($retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty| -> $retty {
                    assert_eq!($name, $val);
                    $retval
                });
                let result = (closure.as_fn_ptr())($val);
                assert_eq!(result, $retval);

                let closuremut = ClosureMut::new_unwindable(|$name: $ty| -> $retty {
                    assert_eq!($name, $val);
                    $retval
                });
                let result = (closuremut.as_fn_ptr())($val);
                assert_eq!(result, $retval);
            }

            generate_closure_test!($name: $ty = $val);
        };

        ($name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty, $($restname: $restty),+| {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                });
                (closure.as_fn_ptr())($val, $($restval),+);

                let closuremut = ClosureMut::new_unwindable(|$name: $ty, $($restname: $restty),+| {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                });
                (closuremut.as_fn_ptr())($val, $($restval),+);
            }

            generate_closure_test!($ty = $val => $($restname: $restty = $restval),+);
        };

        ($retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty, $($restname: $restty),+| -> $retty {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                    $retval
                });
                let result = (closure.as_fn_ptr())($val, $($restval),+);
                assert_eq!(result, $retval);

                let closuremut = ClosureMut::new_unwindable(|$name: $ty, $($restname: $restty),+| -> $retty {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                    $retval
                });
                let result = (closuremut.as_fn_ptr())($val, $($restval),+);
                assert_eq!(result, $retval);
            }

            generate_closure_test!($name: $ty = $val, $($restname: $restty = $restval),+);
        };
    }

    #[expect(
        clippy::float_cmp,
        reason = "Direct comparison of floats that have not been modified."
    )]
    #[test]
    fn test_all_arg_and_ret_types() {
        let num = 0;
        generate_closure_test!(
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
            m: *const i32 = &raw const num,
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

    #[test]
    fn test_mutating_closure() {
        let mut n = 0;

        {
            let closure = ClosureMut::new(|| {
                n += 1;
            });

            (closure.as_fn_ptr())();
        }

        assert_eq!(n, 1);
    }

    #[test]
    fn concurrent_closuremut_panics() {
        let lock = AtomicBool::new(false);
        let complete = AtomicBool::new(false);

        let closure = ClosureMut::new_unwindable(|| {
            let prev_lock = lock.swap(true, Ordering::Release);
            // Panic if `lock` was already set. This should be a distinct panic message from
            // when a `ClosureMut` is called concurrently.
            assert!(!prev_lock);

            let start = Instant::now();

            while !complete.load(Ordering::Acquire) && start.elapsed() < Duration::from_secs(30) {
                spin_loop();
            }

            assert!(
                start.elapsed() <= Duration::from_secs(30),
                "Thread timed out."
            );
        });

        std::thread::scope(|s| {
            // The first thread will set `lock` to true and wait for either `complete` or to time
            // out after 30 seconds.
            let thread_1 = s.spawn(|| {
                (closure.as_fn_ptr())();
            });

            // Wait for `thread_1` to set `lock` to signal that no other threads should be able to
            // call `closure.`
            while !lock.load(Ordering::Acquire) {
                spin_loop();
            }

            // Start `thread_2`, which should panic causing `thread_2.join()` to return an `Err`.
            let thread_2 = s.spawn(|| {
                (closure.as_fn_ptr())();
            });

            let thread_2_result = thread_2.join();
            // After `thread_2` returns, we can signal to `thread_1` that it can also return.
            complete.store(true, Ordering::Release);

            if let Err(panic_box) = thread_2_result {
                if let Some(panic_msg) = panic_box.downcast_ref::<String>() {
                    assert!(
                        panic_msg.contains(
                            "Attempt to call mutable closure several times concurrently."
                        ),
                        "`thread_2` did not exit with the expected panic message"
                    );

                    // `thread_1` should return successfully without panicking.
                    assert!(thread_1.join().is_ok());
                } else {
                    panic!("Panic message from `thread_2` not a `String`: \"{panic_box:?}\".")
                }
            } else {
                panic!("`thread_2` did not panic, but was able to execute `ClosureMut`.")
            }
        });
    }
}

#[cfg(all(test, miri))]
mod miritest {
    use core::ffi::c_void;
    use core::mem::MaybeUninit;

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

    /// Generate code to test calling closures with an arbitrary number of arguments and
    /// optionally a result value.
    ///
    /// `generate_miri_closure_test` is a prime candidate for macro refactoring.
    ///
    /// If the macro is called with a return value, it will be recursively call itself without the
    /// return value, but the same arguments. If the macro is called without a return value, it will
    /// recursively call itself with the first argument as the return value and one argument less.
    ///
    /// A return value is added as an optional prefix: `$retty:ty = $retval:expr =>`.
    ///
    /// Arguments are added on the following format: `$($name:ident: $ty:ty = $val:expr),+`.
    macro_rules! generate_miri_closure_test_for_ty {
        ($closurety:ty) => {
            {
                let closure = <$closurety>::new_unwindable(|| {});
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let fun = (*closure.inner.alloc).fun.unwrap();
                    fun(
                        (*closure.inner.alloc).cif,
                        core::ptr::null_mut::<c_void>(),
                        core::ptr::null_mut::<*mut c_void>(),
                        (*closure.inner.alloc).user_data,
                    );
                }
            }
        };

        // Output type needs to be put first to allow for an arbitrary number of arguments.
        ($closurety:ty, $ty:ty = $val:expr => ()) => {
            {
                let closure = <$closurety>::new_unwindable(|| -> $ty {$val});
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let fun = (*closure.inner.alloc).fun.unwrap();

                    let result = if size_of::<$ty>() < size_of::<usize>() {
                        let mut result = MaybeUninit::<usize>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            core::ptr::null_mut::<*mut c_void>(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.as_ptr().cast::<$ty>().read()
                    } else {
                        let mut result = MaybeUninit::<$ty>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            core::ptr::null_mut::<*mut c_void>(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.assume_init()
                    };

                    assert_eq!(result, $val);
                }
            }

            generate_miri_closure_test_for_ty!($closurety);
        };

        ($closurety:ty, $name:ident: $ty:ty = $val:expr) => {
            {
                let closure = <$closurety>::new_unwindable(|$name: $ty| {
                    assert_eq!($name, $val);
                });
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut $name: $ty = $val;
                    let mut arg_ptrs = [(&raw mut $name).cast::<c_void>()];

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    fun(
                        (*closure.inner.alloc).cif,
                        core::ptr::null_mut::<c_void>(),
                        arg_ptrs.as_mut_ptr(),
                        (*closure.inner.alloc).user_data,
                    );
                }
            }

            generate_miri_closure_test_for_ty!($closurety, $ty = $val => ());
        };

        ($closurety:ty, $retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr) => {
            {
                let closure = <$closurety>::new_unwindable(|$name: $ty| -> $retty {
                    assert_eq!($name, $val);
                    $retval
                });
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut $name: $ty = $val;
                    let mut arg_ptrs = [(&raw mut $name).cast::<c_void>()];

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    let result = if size_of::<$retty>() < size_of::<usize>() {
                        let mut result = MaybeUninit::<usize>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            (&raw mut arg_ptrs).cast(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.as_ptr().cast::<$retty>().read()
                    } else {
                        let mut result = MaybeUninit::<$retty>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            (&raw mut arg_ptrs).cast(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.assume_init()
                    };

                    assert_eq!(result, $retval);
                }
            }

            generate_miri_closure_test_for_ty!($closurety, $name: $ty = $val);
        };

        ($closurety:ty, $name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                let closure = <$closurety>::new_unwindable(|$name: $ty, $($restname: $restty),+| {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                });
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut $name: $ty = $val;
                    $(let mut $restname: $restty = $restval;)+
                    let mut arg_ptrs = [
                        (&raw mut $name).cast::<c_void>(),
                        $((&raw mut $restname).cast::<c_void>(),)+
                    ];

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    fun(
                        (*closure.inner.alloc).cif,
                        core::ptr::null_mut::<c_void>(),
                        arg_ptrs.as_mut_ptr(),
                        (*closure.inner.alloc).user_data,
                    );
                }
            }

            generate_miri_closure_test_for_ty!($closurety, $ty = $val => $($restname: $restty = $restval),+);
        };

        ($closurety:ty, $retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                let closure = <$closurety>::new_unwindable(|$name: $ty, $($restname: $restty),+| -> $retty {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                    $retval
                });
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut $name: $ty = $val;
                    $(let mut $restname: $restty = $restval;)+
                    let mut arg_ptrs = [
                        (&raw mut $name).cast::<c_void>(),
                        $((&raw mut $restname).cast::<c_void>(),)+
                    ];

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    let result = if size_of::<$retty>() < size_of::<usize>() {
                        let mut result = MaybeUninit::<usize>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            (&raw mut arg_ptrs).cast(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.as_ptr().cast::<$retty>().read()
                    } else {
                        let mut result = MaybeUninit::<$retty>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            (&raw mut arg_ptrs).cast(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.assume_init()
                    };

                    assert_eq!(result, $retval);
                }
            }

            generate_miri_closure_test_for_ty!($closurety, $name: $ty = $val, $($restname: $restty = $restval),+);
        };
    }

    #[test]
    fn verify_closure_behavior() {
        let num = 0;
        generate_miri_closure_test_for_ty!(
            Closure<_, _, _>,
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
            m: *const i32 = &raw const num,
            n: SmallFfiStruct = SmallFfiStruct { number: 0x5555_5555, tag: 0xAA },
            o: LargeFfiStruct = LargeFfiStruct {
                a: 0xAAAA_AAAA_AAAA_AAAA,
                b: 0xAAAA_AAAA_AAAA_AAAA,
                c: 0xAAAA_AAAA_AAAA_AAAA,
                d: 0xAAAA_AAAA_AAAA_AAAA,
            },
            p: u8 = 0
        );

        generate_miri_closure_test_for_ty!(
            ClosureMut<_, _, _>,
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
            m: *const i32 = &raw const num,
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
