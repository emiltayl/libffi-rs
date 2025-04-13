use core::any::TypeId;
use core::ffi::c_void;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicBool, Ordering};

use crate::high::{AsFfiType, FfiArgs, FfiRet};
use crate::low::ffi_cif;

mod private {
    pub trait ClosurableSuper<ARGS, RET, FN> {}
    pub trait ClosureMutableSuper<ARGS, RET, FN> {}
}

/// Trait for all immutable closures that can be made into a function pointer using libffi. This
/// trait is implemented for all eligible closures, and cannot be implemented manually.
///
/// TODO more text here
///
/// # Examples
///
/// Using a closure as the comparator to C's standard library `qsort`.
///
/// ```
/// use libffi::high::Closure;
///
/// unsafe extern "C" {
///     fn qsort(
///         base: *mut i32,
///         elements: usize,
///         element_size: usize,
///         comparator: extern "C" fn(*const i32, *const i32) -> i32,
///     );
/// }
///
/// let mut array: [i32; 10] = [i32::MAX, 3, 7, 1000, 5, 0, 9, 13, 2, i32::MIN];
///
/// let closure = Closure::new(|a: *const i32, b: *const i32| -> i32 {
///     // SAFETY: This assumes that qsort is called with an array with a correct number of `i32`s.
///     let order = unsafe { (*a).cmp(&*b) };
///
///     match order {
///         std::cmp::Ordering::Less => -1,
///         std::cmp::Ordering::Equal => 0,
///         std::cmp::Ordering::Greater => 1,
///     }
/// });
///
/// // SAFETY:
/// // * `array` is a valid, mut array with 10 elements of size `size_of::<i32>()`
/// // * `closure.as_ptr()` returns a pointer to a function that compares the pointers of two `i32s`
/// unsafe {
///     qsort(
///         array.as_mut_ptr(),
///         10,
///         size_of::<i32>(),
///         closure.as_fn_ptr(),
///     );
/// }
///
/// assert!(array.is_sorted());
/// ```
pub trait Closurable<ARGS, RET, FN>: private::ClosurableSuper<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: Closurable<ARGS, RET, FN>,
{
    /// The type of the function created by libffi. Used to return a fn pointer of the correct type
    /// in `ptr_to_self`.
    type FnPointer;

    /// Utility function used to convert raw pointers to properly typed function pointers. This
    /// function should not be called directly, but through a [`Closure`].
    ///
    /// # Safety
    ///
    /// Should only be called with pointers from a [`Closure`] with identical type parameters.
    #[doc(hidden)]
    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer;

    /// The actual implementation of what goes on in `call_closure` / `call_closure_unwindable`.
    /// See [`Closurable::call_closure`] and [`Closurable::call_closure_unwindable`] for
    /// documentation.
    ///
    /// # Safety
    ///
    /// See [`Closurable::call_closure`] and [`Closurable::call_closure_unwindable`].
    #[doc(hidden)]
    unsafe fn call_closure_impl(
        cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        args: *const *const c_void,
        closure: *const FN,
    );

    /// Closure handle function called by libffi, which in turn reads the provided arguments and
    /// passes them along to the stored closure. If the closure, or any code called by the closure,
    /// panics, `call_closure` will abort the process, the panic may not be caught.
    ///
    /// # Safety
    ///
    /// This function should **NOT** be called manually, but is only provided as a function pointer
    /// to libffi to handle sending the correct arguments to the closure and providing the return
    /// value.
    ///
    /// * `cif` must be a reference to a `ffi_cif` that accurately describes the layout of the
    ///   arguments passed to the closure and the expected return type.
    /// * `result_space` must point to properly aligned memory that can store at least an `usize` or
    ///   a `RET`, whichever is larger.
    /// * `args` must be a pointer to an array of pointers to arguments with a layout identical to
    ///   the one described by the `cif`.
    /// * `closure` must be an immutable closure with arguments and return values as described by
    ///   the `cif`.
    unsafe extern "C" fn call_closure(
        cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        args: *const *const c_void,
        closure: *const FN,
    ) {
        // SAFETY: See this function's Safety section.
        unsafe {
            Self::call_closure_impl(cif, result_space, args, closure);
        }
    }

    /// Closure handle function called by libffi, which in turn reads the provided arguments and
    /// passes them along to the stored closure. Panics thrown by the closures, or code called from
    /// it, can be caught with [`std::panic::catch_unwind`].
    ///
    /// # Safety
    ///
    /// This function should **NOT** be called manually, but is only provided as a function pointer
    /// to libffi to handle sending the correct arguments to the closure and providing the return
    /// value.
    ///
    /// * `cif` must be a reference to a `ffi_cif` that accurately describes the layout of the
    ///   arguments passed to the closure and the expected return type.
    /// * `result_space` must point to properly aligned memory that can store at least an `usize` or
    ///   a `RET`, whichever is larger.
    /// * `args` must be a pointer to an array of pointers to arguments with a layout identical to
    ///   the one described by the `cif`.
    /// * `closure` must be an immutable closure with arguments and return values as described by
    ///   the `cif`.
    unsafe extern "C-unwind" fn call_closure_unwindable(
        cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        args: *const *const c_void,
        closure: *const FN,
    ) {
        // SAFETY: See this function's Safety section.
        unsafe {
            Self::call_closure_impl(cif, result_space, args, closure);
        }
    }
}

impl<FN> private::ClosurableSuper<(), (), FN> for FN where FN: Fn() {}

impl<FN> Closurable<(), (), FN> for FN
where
    FN: Fn(),
{
    type FnPointer = extern "C" fn();

    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { core::mem::transmute(ptr) }
    }

    unsafe fn call_closure_impl(
        _cif: &ffi_cif,
        _result_space: *mut MaybeUninit<()>,
        _args: *const *const c_void,
        closure: *const FN,
    ) {
        // SAFETY: It is up to the caller to assure that `closure` points to a valid closure.
        unsafe {
            (*closure)();
        }
    }
}

impl<RET, FN> private::ClosurableSuper<(), RET, FN> for FN
where
    RET: AsFfiType + 'static,
    FN: Fn() -> RET,
{
}

impl<RET, FN> Closurable<(), RET, FN> for FN
where
    RET: AsFfiType + 'static,
    FN: Fn() -> RET,
{
    type FnPointer = extern "C" fn() -> RET;

    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { core::mem::transmute(ptr) }
    }

    unsafe fn call_closure_impl(
        _cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        _args: *const *const c_void,
        closure: *const FN,
    ) {
        // SAFETY: It is up to the caller to assure that `closure` points to a valid closure.
        let result = unsafe { (*closure)() };

        // SAFETY:
        // * `cif`'s layout is determined by the `AsFfiType` implementations.
        // * `result_space` is a pointer to a sufficiently large space from libffi.
        // * `args` are correctly provided if the caller has provided correctly typed arguments.
        // * `closure` is the closure stored by [`Closure`] using Rust's type system to provide
        //   guarantees for its signature.
        unsafe {
            closure_write_result(result, result_space);
        }
    }
}

macro_rules! impl_closurable_for_arguments {
    ($($var:ident: $ty:ident),+ $(,)?) => {
        impl<$($ty,)+ FN> private::ClosurableSuper<($($ty,)+), (), FN> for FN
        where
            $($ty: AsFfiType,)+
            FN: Fn($($ty,)+),
        {}

        impl<$($ty,)+ FN> Closurable<($($ty,)+), (), FN> for FN
        where
            $($ty: AsFfiType,)+
            FN: Fn($($ty,)+),
        {
            type FnPointer = extern "C" fn($($ty),+);

            unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
                // SAFETY: The type parameters should ensure that the function pointer type is correct.
                unsafe { core::mem::transmute(ptr) }
            }

            unsafe fn call_closure_impl(
                _cif: &ffi_cif,
                _result_space: *mut MaybeUninit<()>,
                args: *const *const c_void,
                closure: *const FN,
            ) {
                let mut idx = 0;
                $(
                    // Workaround until https://github.com/emiltayl/libffi-rs/issues/29 is fixed
                    #[cfg(all(target_arch = "x86", target_os = "windows", target_env = "gnu"))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { ((*(args.add(idx))).cast::<$ty>()).read_unaligned() };
                    #[cfg(not(all(target_arch = "x86", target_os = "windows", target_env = "gnu")))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { *((*(args.add(idx))).cast::<$ty>()) };

                    idx += 1;
                )+

                // Nonsensical line to make the linter happy.
                let _ = idx;

                // SAFETY: It is up to the caller to assure that `closure` points to a valid
                // closure.
                unsafe { (*closure)($($var),+); }
            }
        }

        impl<$($ty,)+ RET, FN> private::ClosurableSuper<($($ty,)+), RET, FN> for FN
        where
            $($ty: AsFfiType,)+
            RET: AsFfiType + 'static,
            FN: Fn($($ty,)+) -> RET,
        {}

        impl<$($ty,)+ RET, FN> Closurable<($($ty,)+), RET, FN> for FN
        where
            $($ty: AsFfiType,)+
            RET: AsFfiType + 'static,
            FN: Fn($($ty,)+) -> RET,
        {
            type FnPointer = extern "C" fn($($ty),+) -> RET;

            unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
                // SAFETY: The type parameters should ensure that the function pointer type is correct.
                unsafe { core::mem::transmute(ptr) }
            }

            unsafe fn call_closure_impl(
                _cif: &ffi_cif,
                result_space: *mut MaybeUninit<RET>,
                args: *const *const c_void,
                closure: *const FN,
            ) {
                let mut idx = 0;
                $(
                    // Workaround until https://github.com/emiltayl/libffi-rs/issues/29 is fixed
                    #[cfg(all(target_arch = "x86", target_os = "windows", target_env = "gnu"))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { ((*(args.add(idx))).cast::<$ty>()).read_unaligned() };
                    #[cfg(not(all(target_arch = "x86", target_os = "windows", target_env = "gnu")))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { *((*(args.add(idx))).cast::<$ty>()) };

                    idx += 1;
                )+

                // Nonsensical line to make the linter happy.
                let _ = idx;


                // SAFETY: It is up to the caller to assure that `closure` points to a valid
                // closure.
                let result = unsafe { (*closure)($($var),+) };

                // SAFETY:
                // * `cif`'s layout is determined by the `AsFfiType` implementations.
                // * `result_space` is a pointer to a sufficiently large space from libffi.
                // * `args` are correctly provided if the caller has provided correctly typed arguments.
                // * `closure` is the closure stored by [`Closure`] using Rust's type system to provide
                //   guarantees for its signature.
                unsafe {
                    closure_write_result(result, result_space);
                }
            }
        }
    }
}

impl_closurable_for_arguments!(a: A);
impl_closurable_for_arguments!(a: A, b: B);
impl_closurable_for_arguments!(a: A, b: B, c: C);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
impl_closurable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);

/// Trait for all mutable closures that can be made into a function pointer using libffi. This trait
/// is implemented for all eligible closures, and cannot be implemented manually.
///
/// TODO more text here
///
/// # Examples
///
/// TODO
pub trait ClosureMutable<ARGS, RET, FN>: private::ClosureMutableSuper<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    FN: ClosureMutable<ARGS, RET, FN>,
{
    /// The type of the function created by libffi. Used to return a fn pointer of the correct type
    /// in `ptr_to_self`.
    type FnPointer;

    /// Utility function used to convert raw pointers to properly typed function pointers. This
    /// function should not be called directly, but through a [`ClosureMut`].
    ///
    /// # Safety
    ///
    /// Should only be called with pointers from a [`Closure`] with identical type parameters.
    #[doc(hidden)]
    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer;

    /// The actual implementation of what goes on in `call_closure`. See
    /// [`ClosureMutable::call_closure`] for documentation.
    ///
    /// # Safety
    ///
    /// See [`ClosureMutable::call_closure`].
    #[doc(hidden)]
    unsafe fn call_closure_impl(
        cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        args: *const *const c_void,
        closure: *mut FN,
    );

    /// Closure handle function called by libffi, which in turn reads the provided arguments and
    /// passes them along to the stored closure. Since `ClosureMutable` calls `FnMut`s, the closure
    /// may only be called once concurrently. If an attempt is made to call the closure several
    /// times concurrently, `call_closure` panics, which will lead to the process aborting as
    /// unwinding panics is not supported from `extern "C"` functions.
    ///
    /// If multiple concurrent calls is needed, it is recommended to use a `Closure` which calls a
    /// non-mut `Fn` and accesses shared data through a synchronization primitive such as a `Mutex`.
    ///
    /// # Panics
    ///
    /// As mentioned, this function panics if called multiple times concurrently. It is not possible
    /// to catch the panic.
    ///
    /// # Safety
    ///
    /// This function should **NOT** be called manually, but is only provided as a function pointer
    /// to libffi to handle sending the correct arguments to the closure and providing the return
    /// value.
    ///
    /// * `cif` must be a reference to a `ffi_cif` that accurately describes the layout of the
    ///   arguments passed to the closure and the expected return type.
    /// * `result_space` must point to properly aligned memory that can store at least an `usize` or
    ///   a `RET`, whichever is larger.
    /// * `args` must be a pointer to an array of pointers to arguments with a layout identical to
    ///   the one described by the `cif`.
    /// * `closure` must be an immutable closure with arguments and return values as described by
    ///   the `cif`.
    unsafe extern "C" fn call_closure(
        cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        args: *const *const c_void,
        closure_data: *mut (FN, AtomicBool),
    ) {
        // SAFETY: It is up to the caller to assure that `closure_data` points to a
        // `(FN, AtomicBool)` tuple. For further reference, see this function's Safety section.
        unsafe {
            Self::lock(&(*closure_data).1);

            Self::call_closure_impl(cif, result_space, args, &raw mut (*closure_data).0);

            Self::unlock(&(*closure_data).1);
        }
    }

    /// Unwindable version of call_closure for mutable closures. Only used for testing. See
    /// [`ClosureMutable::call_closure`] for documentation.
    #[cfg(test)]
    #[doc(hidden)]
    unsafe extern "C-unwind" fn call_closure_unwindable(
        cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        args: *const *const c_void,
        closure_data: *mut (FN, AtomicBool),
    ) {
        // SAFETY: It is up to the caller to assure that `closure_data` points to a
        // `(FN, AtomicBool)` tuple. For further reference, see this function's Safety section.
        unsafe {
            Self::lock(&(*closure_data).1);

            Self::call_closure_impl(cif, result_space, args, &raw mut (*closure_data).0);

            Self::unlock(&(*closure_data).1);
        }
    }

    /// Helper function that will "lock" the `AtomicBool`. Only for internal usage.
    ///
    /// # Panics
    ///
    /// This function panics if `flag` is already true.
    #[doc(hidden)]
    fn lock(flag: &AtomicBool) {
        flag.compare_exchange(false, true, Ordering::AcqRel, Ordering::Relaxed)
            .expect("Attempt to call mutable closure several times concurrently.");
    }

    /// Helper function that will "unlock" the `AtomicBool`. Only for internal usage.
    #[doc(hidden)]
    fn unlock(flag: &AtomicBool) {
        flag.store(false, Ordering::Release);
    }
}

impl<FN> private::ClosureMutableSuper<(), (), FN> for FN where FN: FnMut() {}

impl<FN> ClosureMutable<(), (), FN> for FN
where
    FN: FnMut(),
{
    type FnPointer = extern "C" fn();

    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { core::mem::transmute(ptr) }
    }

    unsafe fn call_closure_impl(
        _cif: &ffi_cif,
        _result_space: *mut MaybeUninit<()>,
        _args: *const *const c_void,
        closure: *mut FN,
    ) {
        // SAFETY: It is up to the caller to assure that `closure` points to a valid closure.
        unsafe {
            (*closure)();
        }
    }
}

impl<RET, FN> private::ClosureMutableSuper<(), RET, FN> for FN
where
    RET: AsFfiType + 'static,
    FN: FnMut() -> RET,
{
}

impl<RET, FN> ClosureMutable<(), RET, FN> for FN
where
    RET: AsFfiType + 'static,
    FN: FnMut() -> RET,
{
    type FnPointer = extern "C" fn() -> RET;

    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { core::mem::transmute(ptr) }
    }

    unsafe fn call_closure_impl(
        _cif: &ffi_cif,
        result_space: *mut MaybeUninit<RET>,
        _args: *const *const c_void,
        closure: *mut FN,
    ) {
        // SAFETY: It is up to the caller to assure that `closure` points to a valid closure.
        let result = unsafe { (*closure)() };

        // SAFETY:
        // * `cif`'s layout is determined by the `AsFfiType` implementations.
        // * `result_space` is a pointer to a sufficiently large space from libffi.
        // * `args` are correctly provided if the caller has provided correctly typed arguments.
        // * `closure` is the closure stored by [`Closure`] using Rust's type system to provide
        //   guarantees for its signature.
        unsafe {
            closure_write_result(result, result_space);
        }
    }
}

macro_rules! impl_closuremutable_for_arguments {
    ($($var:ident: $ty:ident),+ $(,)?) => {
        impl<$($ty,)+ FN> private::ClosureMutableSuper<($($ty,)+), (), FN> for FN
        where
            $($ty: AsFfiType,)+
            FN: FnMut($($ty,)+),
        {}

        impl<$($ty,)+ FN> ClosureMutable<($($ty,)+), (), FN> for FN
        where
            $($ty: AsFfiType,)+
            FN: FnMut($($ty,)+),
        {
            type FnPointer = extern "C" fn($($ty),+);

            unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
                // SAFETY: The type parameters should ensure that the function pointer type is correct.
                unsafe { core::mem::transmute(ptr) }
            }

            unsafe fn call_closure_impl(
                _cif: &ffi_cif,
                _result_space: *mut MaybeUninit<()>,
                args: *const *const c_void,
                closure: *mut FN,
            ) {
                let mut idx = 0;
                $(
                    // Workaround until https://github.com/emiltayl/libffi-rs/issues/29 is fixed
                    #[cfg(all(target_arch = "x86", target_os = "windows", target_env = "gnu"))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { ((*(args.add(idx))).cast::<$ty>()).read_unaligned() };
                    #[cfg(not(all(target_arch = "x86", target_os = "windows", target_env = "gnu")))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { *((*(args.add(idx))).cast::<$ty>()) };

                    idx += 1;
                )+

                // Nonsensical line to make the linter happy.
                let _ = idx;

                // SAFETY: It is up to the caller to assure that `closure` points to a valid closure.
                unsafe { (*closure)($($var),+); }
            }
        }

        impl<$($ty,)+ RET, FN> private::ClosureMutableSuper<($($ty,)+), RET, FN> for FN
        where
            $($ty: AsFfiType,)+
            RET: AsFfiType + 'static,
            FN: FnMut($($ty,)+) -> RET,
        {}

        impl<$($ty,)+ RET, FN> ClosureMutable<($($ty,)+), RET, FN> for FN
        where
            $($ty: AsFfiType,)+
            RET: AsFfiType + 'static,
            FN: FnMut($($ty,)+) -> RET,
        {
            type FnPointer = extern "C" fn($($ty),+) -> RET;

            unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
                // SAFETY: The type parameters should ensure that the function pointer type is correct.
                unsafe { core::mem::transmute(ptr) }
            }

            unsafe fn call_closure_impl(
                _cif: &ffi_cif,
                result_space: *mut MaybeUninit<RET>,
                args: *const *const c_void,
                closure: *mut FN,
            ) {
                let mut idx = 0;
                $(
                    // Workaround until https://github.com/emiltayl/libffi-rs/issues/29 is fixed
                    #[cfg(all(target_arch = "x86", target_os = "windows", target_env = "gnu"))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { ((*(args.add(idx))).cast::<$ty>()).read_unaligned() };
                    #[cfg(not(all(target_arch = "x86", target_os = "windows", target_env = "gnu")))]
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { *((*(args.add(idx))).cast::<$ty>()) };

                    idx += 1;
                )+

                // Nonsensical line to make the linter happy.
                let _ = idx;


                // SAFETY: It is up to the caller to assure that `closure` points to a valid
                // closure.
                let result = unsafe { (*closure)($($var),+) };

                // SAFETY:
                // * `cif`'s layout is determined by the `AsFfiType` implementations.
                // * `result_space` is a pointer to a sufficiently large space from libffi.
                // * `args` are correctly provided if the caller has provided correctly typed arguments.
                // * `closure` is the closure stored by [`Closure`] using Rust's type system to provide
                //   guarantees for its signature.
                unsafe {
                    closure_write_result(result, result_space);
                }
            }
        }
    }
}

impl_closuremutable_for_arguments!(a: A);
impl_closuremutable_for_arguments!(a: A, b: B);
impl_closuremutable_for_arguments!(a: A, b: B, c: C);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
impl_closuremutable_for_arguments!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);

/// Helper function to ensure that the result is written correctly for all sizes of `RET`.
///
/// # Safety
///
/// * `result_space` must point to properly aligned writable memory that can store at least a
///   `usize` or `RET`, whichever is larger.
#[expect(
    clippy::collapsible_else_if,
    reason = "Stylistic choice, using one block for little endian, and one for big endian architectures."
)]
unsafe fn closure_write_result<RET>(result: RET, result_space: *mut MaybeUninit<RET>)
where
    RET: FfiRet + 'static,
{
    if cfg!(target_endian = "little") {
        // SAFETY: `result_space` should be allocated to be at least `mem::size_of<usize>`
        // bytes wide by libffi.
        unsafe {
            // libffi closures will always return at least a full register's width. If `RET` is
            // smaller than a register, we zero out the return space to avoid leaking other
            // values from the stack.
            if size_of::<RET>() < size_of::<usize>() {
                let write_ptr = result_space.cast::<MaybeUninit<usize>>();
                (*write_ptr).write(0);
            }

            (*result_space).write(result);
        }
    } else {
        if size_of::<RET>() < size_of::<usize>() {
            // SAFETY: `result_space` should be allocated to be at least `mem::size_of<usize>`
            // bytes wide by libffi.
            unsafe {
                let write_ptr = (*result_space).as_mut_ptr();
                write_ptr.cast::<usize>().write(0);

                // `f32` should be put at `result_space`'s address. This was determined by
                // tests.
                if TypeId::of::<RET>() == TypeId::of::<f32>() {
                    (*result_space).write(result);
                } else {
                    let result_offset_ptr =
                        write_ptr.add(size_of::<usize>() / size_of::<RET>() - 1);
                    result_offset_ptr.write(result);
                }
            }
        } else {
            // SAFETY: `result_space` should be allocated to be at least `mem::size_of<usize>`
            // bytes wide by libffi.
            unsafe {
                (*result_space).write(result);
            }
        }
    }
}
