use core::{any::TypeId, ffi::c_void, marker::PhantomData, mem::MaybeUninit};

use libffi_sys::ffi_cif;

use super::{AsFfiType, FfiArgs, FfiRet};
use crate::middle::{Cif, ClosureOwned};

mod private {
    pub struct Token;
}

/// Trait for all closures that can be made into a function pointer using libffi.
///
/// TODO more text here
/// TODO mut?
///
/// # Examples
///
/// TODO
pub trait Closurable<ARGS, RET, FN>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    Self: Sized,
{
    /// The type of the function created by libffi. Used to return a fn pointer of the correct type
    /// in `ptr_to_self`.
    type FnPointer;

    /// Function that creates a [`Closure`] from a Rust closure.
    ///
    /// # Example
    ///
    /// TODO
    fn to_ffi_closure(self) -> Closure<ARGS, RET, FN, Self>;

    /// Utility function used to convert raw pointers to properly typed function pointers. This
    /// function should not be called directly, but through a [`Closure`].
    ///
    /// # Safety
    ///
    /// Should only be called with pointers from a [`Closure`] with identical type parameters.
    #[doc(hidden)]
    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer;

    /// Closure handle function called by libffi, which in turn reads the provided arguments and
    /// passes them along to the stored closure.
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
        result_space: &mut MaybeUninit<RET>,
        args: *const *const c_void,
        closure: &FN,
    );

    /// Helper function to ensure that the result is written correctly for all sizes of `RET`.
    ///
    /// # Safety
    ///
    /// * `result_space` must point to properly aligned writable memory that can store at least a
    ///   `usize` or `RET`, whichever is larger.
    #[inline]
    #[expect(
        clippy::collapsible_else_if,
        reason = "Stylistic choice, using one block for little endian, and one for big endian architectures."
    )]
    unsafe fn write_result(result: RET, result_space: &mut MaybeUninit<RET>) -> private::Token {
        if cfg!(target_endian = "little") {
            // libffi closures will always return at least a full register's width. If `RET` is
            // smaller than a register, we zero out the return space to avoid leaking other values
            // from the stack.
            if size_of::<RET>() < size_of::<usize>() {
                let write_ptr = result_space.as_mut_ptr();
                // SAFETY: `result_space` should be allocated to be at least `mem::size_of<usize>`
                // bytes wide by libffi.
                unsafe {
                    write_ptr.cast::<usize>().write(0);
                }
            }

            result_space.write(result);
        } else {
            if size_of::<RET>() < size_of::<usize>() {
                let write_ptr = result_space.as_mut_ptr();
                // SAFETY: `result_space` should be allocated to be at least `mem::size_of<usize>`
                // bytes wide by libffi.
                unsafe {
                    write_ptr.cast::<usize>().write(0);
                }

                // `f32` should be put at `result_space`'s address. This was determined by tests.
                if TypeId::of::<RET>() == TypeId::of::<f32>() {
                    result_space.write(result);
                } else {
                    // Write the result at the correct offset for big endian architectures.
                    // SAFETY: `result_space` should be allocated to be at least
                    // `mem::size_of<usize>` bytes wide by libffi.
                    unsafe {
                        let result_offset_ptr =
                            write_ptr.add(size_of::<usize>() / size_of::<RET>() - 1);
                        result_offset_ptr.write(result);
                    }
                }
            } else {
                result_space.write(result);
            }
        }

        private::Token
    }
}

impl<FN> Closurable<(), (), FN> for FN
where
    FN: Fn(),
    Self: Sized,
{
    type FnPointer = extern "C" fn();

    fn to_ffi_closure(self) -> Closure<(), (), FN, Self> {
        Closure::new(self)
    }

    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
        // SAFETY:
        unsafe { core::mem::transmute(ptr) }
    }

    unsafe extern "C" fn call_closure(
        _cif: &ffi_cif,
        _result_space: &mut MaybeUninit<()>,
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

    fn to_ffi_closure(self) -> Closure<(), RET, FN, Self> {
        Closure::new(self)
    }

    unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { core::mem::transmute(ptr) }
    }

    unsafe extern "C" fn call_closure(
        _cif: &ffi_cif,
        result_space: &mut MaybeUninit<RET>,
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

            fn to_ffi_closure(self) -> Closure<($($ty,)+), (), FN, Self> {
                Closure::new(self)
            }

            unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
                // SAFETY: The type parameters should ensure that the function pointer type is correct.
                unsafe { core::mem::transmute(ptr) }
            }

            unsafe extern "C" fn call_closure(
                _cif: &ffi_cif,
                _result_space: &mut MaybeUninit<()>,
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

            fn to_ffi_closure(self) -> Closure<($($ty,)+), RET, FN, Self> {
                Closure::new(self)
            }

            unsafe fn ptr_to_self(ptr: *mut c_void) -> Self::FnPointer {
                // SAFETY: The type parameters should ensure that the function pointer type is correct.
                unsafe { core::mem::transmute(ptr) }
            }

            unsafe extern "C" fn call_closure(
                _cif: &ffi_cif,
                result_space: &mut MaybeUninit<RET>,
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
pub struct Closure<ARGS, RET, FN, CLOSURABLE>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    CLOSURABLE: Closurable<ARGS, RET, FN>,
{
    inner: ClosureOwned<FN>,
    _phantom: PhantomData<(ARGS, RET, CLOSURABLE)>,
}

impl<ARGS, RET, FN, CLOSURABLE> Closure<ARGS, RET, FN, CLOSURABLE>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet + 'static,
    CLOSURABLE: Closurable<ARGS, RET, FN>,
{
    /// Creates a new [`Closure`].
    pub fn new(func: FN) -> Self {
        let cif = Cif::new(
            <ARGS as FfiArgs>::as_type_array().as_ref(),
            <RET as FfiRet>::as_ffi_return_type(),
        );

        let inner = ClosureOwned::new(cif, CLOSURABLE::call_closure, func);

        Self {
            inner,
            _phantom: PhantomData,
        }
    }

    /// Returns a function pointer that can be used to call the closure from Rust. See
    /// [`ClosureOwned::code_ptr`] for more information.
    pub fn code_ptr(&self) -> &unsafe extern "C" fn() {
        self.inner.code_ptr()
    }

    /// Returns a function pointer that can be used to execute the closure. Note that the function
    /// pointer is only valid as long as `self` is alive. Calling the function pointer after `self`
    /// is dropped is undefined behavior.
    pub fn as_fn_ptr(&self) -> CLOSURABLE::FnPointer {
        // SAFETY: The type parameters should ensure that the function pointer type is correct.
        unsafe { CLOSURABLE::ptr_to_self(self.inner.code.0) }
    }
}
