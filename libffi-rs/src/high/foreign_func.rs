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

    /// Wrap `self` in a wrapper that is `Send`. It is up to the caller to make sure that the
    /// function provided when creating `self` can safely be sent to another thread and called from
    /// multiple threads simultaneously.
    pub fn send(self) -> ForeignFuncSend<ARGS, RET> {
        ForeignFuncSend(self)
    }

    /// Wrap `self` in a wrapper that is `Sync`. It is up to the caller to make sure that the
    /// function provided when creating `self` can safely be called from multiple threads
    /// simultaneously.
    pub fn sync(self) -> ForeignFuncSync<ARGS, RET> {
        ForeignFuncSync(self)
    }

    /// Wrap `self` in a wrapper that is `Send` and `Sync`. It is up to the caller to make sure that
    /// the function provided when creating `self` can safely be sent to another thread and called
    /// from multiple threads simultaneously.
    pub fn send_sync(self) -> ForeignFuncSendSync<ARGS, RET> {
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

/// A [`ForeignFunc`] that is safe to send to other threads. It must be safe to send `fn_ptr` to
/// another thread, and call it from multiple threads simultaneously as `ForeignFunc` is `Clone`.
///
/// Create a `ForeignFuncSend` by calling [`ForeignFunc::send`] on a [`ForeignFunc`] object.
///
/// See [`ForeignFunc`] for more details.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct ForeignFuncSend<ARGS, RET>(ForeignFunc<ARGS, RET>)
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet;

impl<ARGS, RET> ForeignFuncSend<ARGS, RET>
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

// SAFETY: It is up to the creator of `ForeignFuncSend` to guarantee that the [`ForeignFunc`] is
// `Send`.
unsafe impl<ARGS, RET> Send for ForeignFuncSend<ARGS, RET>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet,
{
}

/// A [`ForeignFunc`] that is safe to share with other threads. It must be safe to call it from
/// multiple threads simultaneously.
///
/// Create a `ForeignFuncSync` by calling [`ForeignFunc::sync`] on a [`ForeignFunc`] object.
///
/// See [`ForeignFunc`] for more details.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct ForeignFuncSync<ARGS, RET>(ForeignFunc<ARGS, RET>)
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet;

impl<ARGS, RET> ForeignFuncSync<ARGS, RET>
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
    /// execute `ForeignFuncSend::call` from multiple threads simultaneously.
    #[inline]
    pub unsafe fn call(&self, args: ARGS) -> RET {
        // SAFETY: It is up to the caller to ensure the safety requirements documented for this
        // function.
        unsafe { self.0.call(args) }
    }
}

// SAFETY: It is up to the creator of `ForeignFuncSync` to guarantee that the [`ForeignFunc`] is
// `Sync`.
unsafe impl<ARGS, RET> Sync for ForeignFuncSync<ARGS, RET>
where
    ARGS: for<'args> FfiArgs<'args>,
    RET: FfiRet,
{
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
