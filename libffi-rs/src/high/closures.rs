extern crate alloc;

#[cfg(not(test))]
use alloc::boxed::Box;
use core::{any::TypeId, ffi::c_void, marker::PhantomData, mem::MaybeUninit};

use libffi_sys::ffi_cif;

use super::{AsFfiType, FfiArgs, FfiRet};
use crate::middle::{Cif, ClosureOwned};

mod private {
    pub struct Token;
}

/// Trait for all immutable closures that can be made into a function pointer using libffi. This
/// trait is implemented for all eligible closures, and cannot be implemented manually.
///
/// TODO more text here
/// TODO mut?
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
pub trait Closurable<ARGS, RET, FN>
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
        closure: &FN,
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
        closure: &FN,
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
        closure: &FN,
    ) {
        // SAFETY: See this function's Safety section.
        unsafe {
            Self::call_closure_impl(cif, result_space, args, closure);
        }
    }

    /// Helper function to ensure that the result is written correctly for all sizes of `RET`.
    ///
    /// # Safety
    ///
    /// * `result_space` must point to properly aligned writable memory that can store at least a
    ///   `usize` or `RET`, whichever is larger.
    #[doc(hidden)]
    #[expect(
        clippy::collapsible_else_if,
        reason = "Stylistic choice, using one block for little endian, and one for big endian architectures."
    )]
    #[inline]
    unsafe fn write_result(result: RET, result_space: *mut MaybeUninit<RET>) -> private::Token {
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

        private::Token
    }
}

impl<FN> Closurable<(), (), FN> for FN
where
    FN: Fn(),
{
    type FnPointer = extern "C" fn();

    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
        // SAFETY:
        unsafe { core::mem::transmute(ptr) }
    }

    unsafe fn call_closure_impl(
        _cif: &ffi_cif,
        _result_space: *mut MaybeUninit<()>,
        _args: *const *const c_void,
        closure: &FN,
    ) {
        closure();
    }
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
        closure: &FN,
    ) {
        let result = closure();

        // SAFETY:
        // * `cif`'s layout is determined by the `AsFfiType` implementations.
        // * `result_space` is a pointer to a sufficiently large space from libffi.
        // * `args` are correctly provided if the caller has provided correctly typed arguments.
        // * `closure` is the closure stored by [`Closure`] using Rust's type system to provide
        //   guarantees for its signature.
        unsafe {
            Self::write_result(result, result_space);
        }
    }
}

macro_rules! impl_closurable_for_arguments {
    ($($var:ident: $ty:ident),+ $(,)?) => {
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
                closure: &FN,
            ) {
                let mut idx = 0;
                $(
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { *((*(args.add(idx))).cast::<$ty>()) };
                    idx += 1;
                )+

                // Nonsensical line to make the linter happy.
                let _ = idx;

                closure($($var),+);
            }
        }

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
                closure: &FN,
            ) {
                let mut idx = 0;
                $(
                    // SAFETY: It is up to the caller to provide the correct number of arguments
                    // with the right types.
                    let $var: $ty = unsafe { *((*(args.add(idx))).cast::<$ty>()) };
                    idx += 1;
                )+

                // Nonsensical line to make the linter happy.
                let _ = idx;


                let result = closure($($var),+);

                // SAFETY:
                // * `cif`'s layout is determined by the `AsFfiType` implementations.
                // * `result_space` is a pointer to a sufficiently large space from libffi.
                // * `args` are correctly provided if the caller has provided correctly typed arguments.
                // * `closure` is the closure stored by [`Closure`] using Rust's type system to provide
                //   guarantees for its signature.
                unsafe {
                    Self::write_result(result, result_space);
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

    /// Returns a function reference that can be used to call the closure from Rust. See
    /// [`ClosureOwned::code_ptr`] for more information. It is recommended to use this function
    /// if calling the closure from Rust to ensure that `self` is alive when calling the closure.
    pub fn code_ptr(&self) -> &FN::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { self.inner.instantiate_code_ptr() }
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

#[cfg(all(test, not(miri)))]
mod test {
    use super::*;
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

    macro_rules! test_identity_closure {
        ($ty:ty = $val:expr) => {{
            let original: $ty = $val;
            let closure = Closure::new(|val: $ty| val);
            assert_eq!((closure.code_ptr())($val), original);
        }};
    }

    #[expect(
        clippy::float_cmp,
        reason = "Direct comparison of floats that have not been modified."
    )]
    #[test]
    fn test_identity_closures() {
        let mut num: i8 = 0;

        test_identity_closure!(i8 = 0x55);
        test_identity_closure!(u8 = 0xAA);
        test_identity_closure!(i16 = 0x5555);
        test_identity_closure!(u16 = 0xAAAA);
        test_identity_closure!(i32 = 0x5555_5555);
        test_identity_closure!(u32 = 0xAAAA_AAAA);
        test_identity_closure!(i64 = 0x5555_5555_5555_5555);
        test_identity_closure!(u64 = 0xAAAA_AAAA_AAAA_AAAA);
        test_identity_closure!(isize = 0x5555_5555);
        test_identity_closure!(usize = 0xAAAA_AAAA);
        test_identity_closure!(f32 = std::f32::consts::LN_2);
        test_identity_closure!(f64 = std::f64::consts::LN_10);
        test_identity_closure!(*const i8 = &raw const num);
        test_identity_closure!(*mut i8 = &raw mut num);
        test_identity_closure!(
            SmallFfiStruct = SmallFfiStruct {
                number: 0x5555_5555,
                tag: 0xAA
            }
        );
        test_identity_closure!(
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

            (closure.code_ptr())();
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
                (closure.code_ptr())();
            }
        };

        // Output type needs to be put first to allow for an arbitrary number of arguments.
        ($ty:ty = $val:expr => ()) => {
            {
                let closure = Closure::new_unwindable(|| -> $ty {$val});
                let result = (closure.code_ptr())();
                assert_eq!(result, $val);
            }

            generate_closure_test!();
        };

        ($name:ident: $ty:ty = $val:expr) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty| {
                    assert_eq!($name, $val);
                });
                (closure.code_ptr())($val);
            }

            generate_closure_test!($ty = $val => ());
        };

        ($retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty| -> $retty {
                    assert_eq!($name, $val);
                    $retval
                });
                let result = (closure.code_ptr())($val);
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
                (closure.code_ptr())($val, $($restval),+);
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
                let result = (closure.code_ptr())($val, $($restval),+);
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
}

#[cfg(all(test, miri))]
mod miritest {
    use super::*;
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
    macro_rules! generate_miri_closure_test {
        () => {
            {
                let closure = Closure::new_unwindable(|| {});
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut null = core::ptr::null_mut::<c_void>();

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    fun(
                        (*closure.inner.alloc).cif,
                        (&raw mut null).cast(),
                        (&raw mut null).cast(),
                        (*closure.inner.alloc).user_data,
                    );
                }
            }
        };

        // Output type needs to be put first to allow for an arbitrary number of arguments.
        ($ty:ty = $val:expr => ()) => {
            {
                let closure = Closure::new_unwindable(|| -> $ty {$val});
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let fun = (*closure.inner.alloc).fun.unwrap();
                    let mut arg_ptrs = core::ptr::null_mut::<c_void>();

                    let result = if size_of::<$ty>() < size_of::<usize>() {
                        let mut result = MaybeUninit::<usize>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            (&raw mut arg_ptrs).cast(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.as_ptr().cast::<$ty>().read()
                    } else {
                        let mut result = MaybeUninit::<$ty>::uninit();
                        fun(
                            (*closure.inner.alloc).cif,
                            result.as_mut_ptr().cast(),
                            (&raw mut arg_ptrs).cast(),
                            (*closure.inner.alloc).user_data,
                        );

                        result.assume_init()
                    };

                    assert_eq!(result, $val);
                }
            }

            generate_miri_closure_test!();
        };

        ($name:ident: $ty:ty = $val:expr) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty| {
                    assert_eq!($name, $val);
                });
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut null = core::ptr::null_mut::<c_void>();
                    let mut $name: $ty = $val;
                    let mut arg_ptrs = [(&raw mut $name).cast::<c_void>()];

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    fun(
                        (*closure.inner.alloc).cif,
                        (&raw mut null).cast(),
                        arg_ptrs.as_mut_ptr(),
                        (*closure.inner.alloc).user_data,
                    );
                }
            }

            generate_miri_closure_test!($ty = $val => ());
        };

        ($retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty| -> $retty {
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

            generate_miri_closure_test!($name: $ty = $val);
        };

        ($name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty, $($restname: $restty),+| {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                });
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut null = core::ptr::null_mut::<c_void>();
                    let mut $name: $ty = $val;
                    $(let mut $restname: $restty = $restval;)+
                    let mut arg_ptrs = [
                        (&raw mut $name).cast::<c_void>(),
                        $((&raw mut $restname).cast::<c_void>(),)+
                    ];

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    fun(
                        (*closure.inner.alloc).cif,
                        (&raw mut null).cast(),
                        arg_ptrs.as_mut_ptr(),
                        (*closure.inner.alloc).user_data,
                    );
                }
            }

            generate_miri_closure_test!($ty = $val => $($restname: $restty = $restval),+);
        };

        ($retty:ty = $retval:expr => $name:ident: $ty:ty = $val:expr, $($restname:ident: $restty:ty = $restval:expr),+) => {
            {
                let closure = Closure::new_unwindable(|$name: $ty, $($restname: $restty),+| -> $retty {
                    assert_eq!($name, $val);
                    $(assert_eq!($restname, $restval);)+
                    $retval
                });
                // SAFETY: `Closure::new` should initialize well-formed struct for the closure.
                unsafe {
                    let mut null = core::ptr::null_mut::<c_void>();
                    let mut $name: $ty = $val;
                    $(let mut $restname: $restty = $restval;)+
                    let mut arg_ptrs = [
                        (&raw mut $name).cast::<c_void>(),
                        $((&raw mut $restname).cast::<c_void>(),)+
                    ];

                    let fun = (*closure.inner.alloc).fun.unwrap();
                    fun(
                        (*closure.inner.alloc).cif,
                        (&raw mut null).cast(),
                        arg_ptrs.as_mut_ptr(),
                        (*closure.inner.alloc).user_data,
                    );
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

            generate_miri_closure_test!($name: $ty = $val, $($restname: $restty = $restval),+);
        };
    }

    #[test]
    #[rustfmt::skip]
    fn verify_closure_initialization() {
        let num = 0;
        generate_miri_closure_test!(
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
