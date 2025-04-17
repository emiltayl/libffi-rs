extern crate alloc;
#[cfg(not(test))]
use alloc::boxed::Box;
use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::{AtomicBool, Ordering};

#[cfg(miri)]
use miri::{
    closure_alloc, closure_free, prep_closure, prep_closure_mut, prep_closure_unwindable,
    prep_closure_unwindable_mut,
};

use crate::low::ffi_closure;
#[cfg(not(miri))]
use crate::low::{
    closure_alloc, closure_free, prep_closure, prep_closure_mut, prep_closure_unwindable,
    prep_closure_unwindable_mut,
};
use crate::middle::{
    Callback, CallbackMut, CallbackUnwindable, CallbackUnwindableMut, Cif, CodePtr, Error,
};

/// Represents a closure callable from C that borrows `userdata`.
///
/// A libffi closure captures a `void*` ("userdata") and passes it to a callback when the code
/// pointer (obtained via [`Closure::code_ptr`]) is invoked. Lifetype parameter `'closure` ensures
/// that the closure does not outlive the userdata.
///
/// Construct with [`Closure::new`] and [`Closure::new_mut`].
///
/// # Examples
///
/// In this example we turn a Rust lambda into a C function. We first define function
/// `lambda_callback`, which will be called by libffi when the closure is called. The callback
/// function takes four arguments: a CIF describing its arguments, a pointer for where to store its
/// result, a pointer to an array of pointers to its arguments, and a userdata pointer. In this
/// case, the Rust closure value `lambda` is passed as userdata to `lambda_callback`, which then
/// invokes it.
///
/// ```
/// use std::mem;
/// use std::os::raw::c_void;
///
/// use libffi::low;
/// use libffi::middle::{Cif, Closure, Type};
///
/// unsafe extern "C" fn lambda_callback<F: Fn(u64, u64) -> u64>(
///     _cif: &low::ffi_cif,
///     result: *mut mem::MaybeUninit<u64>,
///     args: *const *const c_void,
///     userdata: *const F,
/// ) {
///     let args: *const *const u64 = args.cast();
///     unsafe {
///         let arg_1 = **args.offset(0);
///         let arg_2 = **args.offset(1);
///         (*result).write((*userdata)(arg_1, arg_2));
///     }
/// }
///
/// # use libffi::middle::Error;
/// # fn main() -> Result<(), Error> {
/// let cif = Cif::new(&[Type::U64, Type::U64], Some(Type::U64))?;
/// let lambda = |x: u64, y: u64| x + y;
/// let closure = Closure::new(cif, lambda_callback, &lambda)?;
///
/// // If calling lambda callback with valid input parameters was potentially unsafe, `fun` wouild
/// // have to be typed as `&unsafe extern "C"...`.
/// let fun: &extern "C" fn(u64, u64) -> u64 = unsafe { closure.instantiate_code_ptr() };
///
/// assert_eq!(11, fun(5, 6));
/// assert_eq!(12, fun(5, 7));
/// #   Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct Closure<'closure> {
    _cif: Cif,
    alloc: *mut ffi_closure,
    code: CodePtr,
    _marker: PhantomData<&'closure ()>,
}

impl<'closure> Closure<'closure> {
    /// Creates a new closure that borrows `userdata` immutably.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the pointer to pass to `callback` along with the arguments when the closure
    ///   is called
    ///
    /// # Errors
    ///
    /// This function returns an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new<U, R>(
        cif: Cif,
        callback: Callback<U, R>,
        userdata: &'closure U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_closure` call.
        unsafe {
            prep_closure(alloc, cif.cif, callback, ptr::from_ref(userdata), code)?;
        }

        Ok(Closure {
            _cif: cif,
            alloc,
            code,
            _marker: PhantomData,
        })
    }

    /// Creates a new closure that borrows `userdata` immutably. Use this if you need to support
    /// unwinding the stack in case of a panic.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the pointer to pass to `callback` along with the arguments when the closure
    ///   is called
    ///
    /// # Errors
    ///
    /// This function returns an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_unwindable<U, R>(
        cif: Cif,
        callback: CallbackUnwindable<U, R>,
        userdata: &'closure U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_closure` call.
        unsafe {
            prep_closure_unwindable(alloc, cif.cif, callback, ptr::from_ref(userdata), code)?;
        }

        Ok(Closure {
            _cif: cif,
            alloc,
            code,
            _marker: PhantomData,
        })
    }

    /// Creates a new closure that borrows a mutable reference to `userdata`.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the pointer to pass to `callback` along with the arguments when the closure
    ///   is called
    ///
    /// # Errors
    ///
    /// This function will return an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_mut<U, R>(
        cif: Cif,
        callback: CallbackMut<U, R>,
        userdata: &'closure mut U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_mut(alloc, cif.cif, callback, ptr::from_mut(userdata), code)?;
        }

        Ok(Closure {
            _cif: cif,
            alloc,
            code,
            _marker: PhantomData,
        })
    }

    /// Creates a new closure that borrows a mutable reference to `userdata`. Use this if you need
    /// to support unwinding the stack in case of a panic.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the pointer to pass to `callback` along with the arguments when the closure
    ///   is called
    ///
    /// # Errors
    ///
    /// This function will return an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_unwindable_mut<U, R>(
        cif: Cif,
        callback: CallbackUnwindableMut<U, R>,
        userdata: &'closure mut U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_unwindable_mut(alloc, cif.cif, callback, ptr::from_mut(userdata), code)?;
        }

        Ok(Closure {
            _cif: cif,
            alloc,
            code,
            _marker: PhantomData,
        })
    }

    /// Obtains the callable code pointer for a closure.
    ///
    /// The result needs to be transmuted to the correct type before it can be called. If the type
    /// is wrong, calling the result of `code_ptr` will result in undefined behavior.
    pub fn code_ptr(&self) -> &unsafe extern "C" fn() {
        // SAFETY: This may create a reference from a NULL pointer, should probably be fixed.
        unsafe { self.code.as_fun() }
    }

    /// Transmutes the callable code pointer for a closure to a reference to any type. This is
    /// intended to be used to transmute it to its correct function type in order to call it.
    ///
    /// # Safety
    ///
    /// This method allows transmuting to a reference to *any* sized type, and cannot check whether
    /// the code pointer actually has that type. If the type is wrong using the reference will
    /// result in undefined behavior.
    pub unsafe fn instantiate_code_ptr<T>(&self) -> &T {
        // SAFETY: See this function's safety section.
        unsafe { self.code.as_any_ref_() }
    }
}

impl Drop for Closure<'_> {
    fn drop(&mut self) {
        // SAFETY: `self.alloc` is allocated using `low::closure_alloc` and should therefore be
        // freed by `low::closure_free` and only that function.
        unsafe {
            closure_free(self.alloc);
        }
    }
}

/// Represents a closure callable from C that owns its own `userdata`.
///
/// This works similar to [`Closure`], except that [`ClosureOwned`] owns its own `userdata` which
/// will be dropped when [`ClosureOwned`] is dropped.
#[derive(Debug)]
pub struct ClosureOwned<U> {
    pub(crate) alloc: *mut ffi_closure,
    pub(crate) code: CodePtr,
    _cif: Cif,
    userdata: *mut U,
}

impl<U> Drop for ClosureOwned<U> {
    fn drop(&mut self) {
        // SAFETY: `self.alloc` is allocated using `low::closure_alloc` and should therefore be
        // freed by `low::closure_free` and only that function.
        unsafe {
            closure_free(self.alloc);
        }

        // SAFETY: `self.userdata` is a pointer created by `Box::into_raw` owned and managed by
        // `self`.
        unsafe {
            drop(Box::from_raw(self.userdata));
        }
    }
}

impl<U> ClosureOwned<U> {
    /// Creates a new closure with owned userdata and a callback that accesses `userdata` immutably.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the value to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Errors
    ///
    /// This function returns an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new<R>(cif: Cif, callback: Callback<U, R>, userdata: U) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        let userdata = Box::into_raw(Box::new(userdata));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure(alloc, cif.cif, callback, userdata, code)?;
        }

        Ok(ClosureOwned {
            alloc,
            code,
            _cif: cif,
            userdata,
        })
    }

    /// Creates a new closure with owned userdata and a callback that accesses `userdata` immutably.
    /// Use this if you need to support unwinding the stack in case of a panic.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the value to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Errors
    ///
    /// This function will return an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_unwindable<R>(
        cif: Cif,
        callback: CallbackUnwindable<U, R>,
        userdata: U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        let userdata = Box::into_raw(Box::new(userdata));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_unwindable(alloc, cif.cif, callback, userdata, code)?;
        }

        Ok(ClosureOwned {
            alloc,
            code,
            _cif: cif,
            userdata,
        })
    }

    /// Creates a new closure with owned userdata and a callback that can mutate `userdata`.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the value to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Errors
    ///
    /// This function returns an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_mut<R>(cif: Cif, callback: CallbackMut<U, R>, userdata: U) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        let userdata = Box::into_raw(Box::new(userdata));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_mut(alloc, cif.cif, callback, userdata, code)?;
        }

        Ok(ClosureOwned {
            alloc,
            code,
            _cif: cif,
            userdata,
        })
    }

    /// Creates a new closure with owned userdata and a callback that can mutate `userdata`. Use
    /// this if you need to support unwinding the stack in case of a panic.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the value to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Errors
    ///
    /// This function returns an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_unwindable_mut<R>(
        cif: Cif,
        callback: CallbackUnwindableMut<U, R>,
        userdata: U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        let userdata = Box::into_raw(Box::new(userdata));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_unwindable_mut(alloc, cif.cif, callback, userdata, code)?;
        }

        Ok(ClosureOwned {
            alloc,
            code,
            _cif: cif,
            userdata,
        })
    }

    /// Obtains the callable code pointer for a closure.
    ///
    /// The result needs to be transmuted to the correct type before it can be called. If the type
    /// is wrong then undefined behavior will result.
    pub fn code_ptr(&self) -> &unsafe extern "C" fn() {
        // SAFETY: This may create a reference from a NULL pointer, should probably be fixed.
        unsafe { self.code.as_fun() }
    }

    /// Transmutes the callable code pointer for a closure to a reference to any type. This is
    /// intended to be used to transmute it to its correct function type in order to call it.
    ///
    /// # Safety
    ///
    /// This method allows transmuting to a reference to *any* sized type, and cannot check whether
    /// the code pointer actually has that type. If the type is wrong then undefined behavior will
    /// result.
    pub unsafe fn instantiate_code_ptr<T>(&self) -> &T {
        // SAFETY: See this function's safety section.
        // Note that this may create a reference from a NULL pointer, should probably be fixed.
        unsafe { self.code.as_any_ref_() }
    }
}

/// Represents the data owned by `ClosureOnce<U>` that can only be retrieved once.
///
/// This is only meant to be used to implement `high::ClosureOnce` and is therefore not exposed to
/// external crates.
#[derive(Debug)]
pub(crate) struct OnceData<U> {
    userdata: *mut U,
    has_been_acquired: AtomicBool,
}

impl<U> Drop for OnceData<U> {
    fn drop(&mut self) {
        // If self has **NOT** been acquired, we drop the userdata.
        if !self.has_been_acquired.swap(true, Ordering::AcqRel) {
            // SAFETY: `self.userdata` is a pointer created by `Box::into_raw` owned and managed by
            // `self`. Since `self.has_been_acquired` was false, self.userdata has not been dropped.
            unsafe {
                drop(Box::from_raw(self.userdata));
            }
        }
    }
}

impl<U> OnceData<U> {
    pub fn new(userdata: U) -> Self {
        let userdata = Box::into_raw(Box::new(userdata));
        let has_been_acquired = AtomicBool::new(false);

        Self {
            userdata,
            has_been_acquired,
        }
    }

    /// Acquire the userdata, setting the `has_been_acquired` flag and returning `Some(Box<U>)`
    /// with the `userdata` if the flag had not already been set.
    ///
    /// If the flag already had been set, `None` is returned.
    ///
    /// If you acquire the `userdata`, you are responsible for dropping it.
    pub fn acquire(&self) -> Option<Box<U>> {
        // If the flag was already set, we return None
        if self.has_been_acquired.swap(true, Ordering::AcqRel) {
            None
        } else {
            // SAFETY: The flag has not been set previously, so nobody should have touched
            // `userdata`.
            let userdata = unsafe { Box::from_raw(self.userdata) };

            Some(userdata)
        }
    }
}

/// Represents a closure callable from C that owns its own `userdata`.
///
/// This is only meant to be used to implement `high::ClosureOnce` and is therefore not exposed to
/// external crates.
#[derive(Debug)]
pub(crate) struct ClosureOnce<U> {
    pub(crate) alloc: *mut ffi_closure,
    pub(crate) code: CodePtr,
    _cif: Cif,
    userdata: *mut OnceData<U>,
}

impl<U> Drop for ClosureOnce<U> {
    fn drop(&mut self) {
        // SAFETY: `self.alloc` is allocated using `low::closure_alloc` and should therefore be
        // freed by `low::closure_free` and only that function.
        unsafe {
            closure_free(self.alloc);
        }

        // SAFETY: `self.userdata` is created from `Box::into_raw` and `self` owns it.
        unsafe {
            drop(Box::from_raw(self.userdata));
        }
    }
}

impl<U> ClosureOnce<U> {
    /// Creates a new closure and a callback that can mutate `userdata`.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the value to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Errors
    ///
    /// This function returns an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_mut<R>(
        cif: Cif,
        callback: CallbackMut<OnceData<U>, R>,
        userdata: U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        let userdata = Box::into_raw(Box::new(OnceData::new(userdata)));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_mut(alloc, cif.cif, callback, userdata, code)?;
        }

        Ok(ClosureOnce {
            alloc,
            code,
            _cif: cif,
            userdata,
        })
    }

    /// Creates a new closure that can mutate `userdata`. Only used for testing purposes where
    /// unwinding is needed to prevent aborting the test process.
    ///
    /// # Arguments
    ///
    /// - `cif` — describes the calling convention and argument and result types
    /// - `callback` — the function to call when the closure is invoked
    /// - `userdata` — the value to pass to `callback` along with the arguments when the closure is
    ///   called
    ///
    /// # Errors
    ///
    /// This function returns an error if libffi was unable to allocate memory in
    /// `ffi_closure_alloc`.
    ///
    /// It will also return an error if `low::prep_closure_mut` fails to create the CIF. This is
    /// likely caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    #[cfg(test)]
    pub fn new_unwindable_mut<R>(
        cif: Cif,
        callback: CallbackUnwindableMut<OnceData<U>, R>,
        userdata: U,
    ) -> Result<Self, Error> {
        let (alloc, code) = closure_alloc();

        if alloc.is_null() {
            return Err(Error::AllocFailed);
        }

        let userdata = Box::into_raw(Box::new(OnceData::new(userdata)));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_unwindable_mut(alloc, cif.cif, callback, userdata, code)?;
        }

        Ok(ClosureOnce {
            alloc,
            code,
            _cif: cif,
            userdata,
        })
    }
}

#[cfg(all(test, not(miri)))]
mod test {
    use core::ffi::c_void;
    use core::mem::MaybeUninit;

    use super::*;
    use crate::low::ffi_cif;
    use crate::middle::Type;

    #[test]
    fn closure() {
        let cif = Cif::new(&[Type::U64], Some(Type::U64)).unwrap();
        let env: u64 = 5;

        {
            let closure = Closure::new(cif.clone(), callback, &env).unwrap();

            // SAFETY: `callback` expects one u64 and returns a u64.
            let fun: &extern "C" fn(u64) -> u64 = unsafe { closure.instantiate_code_ptr() };

            assert_eq!(11, fun(6));
            assert_eq!(12, fun(7));
        }

        {
            let closure = ClosureOwned::new(cif, callback, env).unwrap();

            // SAFETY: `callback` expects one u64 and returns a u64.
            let fun: &extern "C" fn(u64) -> u64 = unsafe { closure.instantiate_code_ptr() };

            assert_eq!(11, fun(6));
            assert_eq!(12, fun(7));
        }
    }

    unsafe extern "C" fn callback(
        _cif: &ffi_cif,
        result: *mut MaybeUninit<u64>,
        args: *const *const c_void,
        userdata: *const u64,
    ) {
        let args = args.cast::<*const u64>();
        // SAFETY: `callback` receives a pointer to an array with pointers to the provided
        // arguments. This derefs a the pointer to the first argument, which should be a pointer to
        // a u64.
        unsafe {
            (*result).write(**args + *userdata);
        }
    }

    #[test]
    fn rust_lambda() {
        let cif = Cif::new(&[Type::U64, Type::U64], Some(Type::U64)).unwrap();
        let env = |x: u64, y: u64| x + y;

        {
            let closure = Closure::new(cif.clone(), callback2, &env).unwrap();

            // SAFETY: `callback2` expects two u64 arguments and returns a u64.
            let fun: &extern "C" fn(u64, u64) -> u64 = unsafe { closure.instantiate_code_ptr() };

            assert_eq!(11, fun(5, 6));
        }

        {
            let closure = ClosureOwned::new(cif, callback2, env).unwrap();

            // SAFETY: `callback2` expects two u64 arguments and returns a u64.
            let fun: &extern "C" fn(u64, u64) -> u64 = unsafe { closure.instantiate_code_ptr() };

            assert_eq!(11, fun(5, 6));
        }
    }

    unsafe extern "C" fn callback2<F: Fn(u64, u64) -> u64>(
        _cif: &ffi_cif,
        result: *mut MaybeUninit<u64>,
        args: *const *const c_void,
        userdata: *const F,
    ) {
        let args = args.cast::<*const u64>();

        // SAFETY: `callback2` receives a pointer to an array with pointers to the provided
        // arguments. This derefs a the pointer to the first argument, which should be a pointer to
        // a u64.
        let first_arg = unsafe { **args.offset(0) };
        // SAFETY: `callback2` receives a pointer to an array with pointers to the provided
        // arguments. This derefs a the pointer to the second argument, which should be a pointer to
        // a u64.
        let second_arg = unsafe { **args.offset(1) };

        // SAFETY: result points to a `MaybeUninit<u64>` in `rust_lambda`.
        unsafe {
            (*result).write((*userdata)(first_arg, second_arg));
        }
    }

    #[test]
    fn test_closures_unwind() {
        let cif = Cif::new(&[], None).unwrap();

        let closure_1 = std::panic::catch_unwind(|| {
            let closure = Closure::new_unwindable(cif.clone(), do_panic, &()).unwrap();
            // SAFETY: `closure` refers to a "C-unwind" function that does not take any parameters
            // or return any values that does not perform any unsafe actions.
            let fun: &extern "C-unwind" fn() = unsafe { closure.instantiate_code_ptr() };
            fun();
        });
        assert!(closure_1.is_err());

        let closure_2 = std::panic::catch_unwind(|| {
            let mut void = ();
            let closure =
                Closure::new_unwindable_mut(cif.clone(), do_panic_mut, &mut void).unwrap();
            // SAFETY: `closure` refers to a "C-unwind" function that does not take any parameters
            // or return any values that does not perform any unsafe actions.
            let fun: &extern "C-unwind" fn() = unsafe { closure.instantiate_code_ptr() };
            fun();
        });
        assert!(closure_2.is_err());

        let closure_3 = std::panic::catch_unwind(|| {
            let closure = ClosureOwned::new_unwindable(cif.clone(), do_panic, ()).unwrap();
            // SAFETY: `closure` refers to a "C-unwind" function that does not take any parameters
            // or return any values that does not perform any unsafe actions.
            let fun: &extern "C-unwind" fn() = unsafe { closure.instantiate_code_ptr() };
            fun();
        });
        assert!(closure_3.is_err());

        let closure_4 = std::panic::catch_unwind(|| {
            let closure = ClosureOwned::new_unwindable_mut(cif.clone(), do_panic_mut, ()).unwrap();
            // SAFETY: `closure` refers to a "C-unwind" function that does not take any parameters
            // or return any values that does not perform any unsafe actions.
            let fun: &extern "C-unwind" fn() = unsafe { closure.instantiate_code_ptr() };
            fun();
        });
        assert!(closure_4.is_err());
    }

    extern "C-unwind" fn do_panic(
        _cif: &ffi_cif,
        _result: *mut MaybeUninit<()>,
        _args: *const *const c_void,
        _userdata: *const (),
    ) {
        panic!();
    }

    extern "C-unwind" fn do_panic_mut(
        _cif: &ffi_cif,
        _result: *mut MaybeUninit<()>,
        _args: *const *const c_void,
        _userdata: *mut (),
    ) {
        panic!();
    }
}

/// Tests to ensure that the memory management for closures is correct.
#[cfg(test)]
mod miritest {
    use core::ffi::c_void;
    use core::mem::MaybeUninit;

    use super::*;
    use crate::low::ffi_cif;

    unsafe extern "C" fn dummy_callback(
        _cif: &ffi_cif,
        _result: *mut MaybeUninit<u32>,
        _args: *const *const c_void,
        _userdata: *const u32,
    ) {
    }

    unsafe extern "C" fn dummy_callback_mut(
        _cif: &ffi_cif,
        _result: *mut MaybeUninit<u32>,
        _args: *const *const c_void,
        _userdata: *mut u32,
    ) {
    }

    unsafe extern "C" fn dummy_callback_once(
        _cif: &ffi_cif,
        _result: *mut MaybeUninit<u32>,
        _args: *const *const c_void,
        _userdata: *mut OnceData<u32>,
    ) {
    }

    #[test]
    fn create_closures() {
        let cif = Cif::new(&[], None).unwrap();

        let state = 0u32;
        let mut mut_state = 0u32;

        let _closure = Closure::new(cif.clone(), dummy_callback, &state);
        let _closure2 = Closure::new_mut(cif.clone(), dummy_callback_mut, &mut mut_state);
        let _closure3 = Closure::new(cif.clone(), dummy_callback, &state);
        let _closure4 = ClosureOwned::new(cif.clone(), dummy_callback, 0u32);
        let _closure5 = ClosureOwned::new_mut(cif.clone(), dummy_callback_mut, 0u32);
        let _closure6 = ClosureOnce::new_mut(cif, dummy_callback_once, 0u32);
    }

    struct PanicDropper;
    impl Drop for PanicDropper {
        fn drop(&mut self) {
            panic!("self dropped!");
        }
    }

    unsafe extern "C" fn dummy_panic_dropper_callback_mut(
        _cif: &ffi_cif,
        _result: *mut MaybeUninit<u32>,
        _args: *const *const c_void,
        _userdata: *mut OnceData<PanicDropper>,
    ) {
    }

    #[test]
    fn do_not_drop_acquired_closureonce() {
        let cif = Cif::new(&[], None).unwrap();
        let closure =
            ClosureOnce::new_mut(cif, dummy_panic_dropper_callback_mut, PanicDropper).unwrap();

        // SAFETY: `userdata` is owned and managed by `self`.
        let once_data = unsafe { &*closure.userdata };

        if let Some(userdata) = once_data.acquire() {
            std::mem::forget(userdata);
        } else {
            panic!("Closure was already acquired?");
        }
    }
}

#[cfg(miri)]
mod miri {
    use super::*;
    use crate::low::{RawCallback, ffi_cif};

    pub(super) fn closure_alloc() -> (*mut ffi_closure, CodePtr) {
        let closure = Box::into_raw(Box::new(ffi_closure::default()));

        (closure, CodePtr(ptr::null_mut()))
    }

    pub(super) unsafe fn closure_free(closure: *mut ffi_closure) {
        // SAFETY: This function assumes `closure` was created by `Box::into_raw`.
        unsafe { drop(Box::from_raw(closure)) }
    }

    pub(super) unsafe fn prep_closure<U, R>(
        closure: *mut ffi_closure,
        cif: *mut ffi_cif,
        callback: Callback<U, R>,
        userdata: *const U,
        _code: CodePtr,
    ) -> Result<(), crate::low::Error> {
        // SAFETY: This function assumes all pointers are valid.
        unsafe {
            (*closure).cif = cif;
            (*closure).fun = Some(core::mem::transmute::<Callback<U, R>, RawCallback>(
                callback,
            ));
            (*closure).user_data = userdata.cast_mut().cast();
        }

        Ok(())
    }

    pub(super) unsafe fn prep_closure_unwindable<U, R>(
        closure: *mut ffi_closure,
        cif: *mut ffi_cif,
        callback: CallbackUnwindable<U, R>,
        userdata: *const U,
        _code: CodePtr,
    ) -> Result<(), crate::low::Error> {
        // SAFETY: This function assumes all pointers are valid.
        unsafe {
            (*closure).cif = cif;
            (*closure).fun =
                Some(core::mem::transmute::<CallbackUnwindable<U, R>, RawCallback>(callback));
            (*closure).user_data = userdata.cast_mut().cast();
        }

        Ok(())
    }

    pub(super) unsafe fn prep_closure_mut<U, R>(
        closure: *mut ffi_closure,
        cif: *mut ffi_cif,
        callback: CallbackMut<U, R>,
        userdata: *mut U,
        _code: CodePtr,
    ) -> Result<(), crate::low::Error> {
        // SAFETY: This function assumes all pointers are valid.
        unsafe {
            (*closure).cif = cif;
            (*closure).fun = Some(core::mem::transmute::<CallbackMut<U, R>, RawCallback>(
                callback,
            ));
            (*closure).user_data = userdata.cast();
        }

        Ok(())
    }

    pub(super) unsafe fn prep_closure_unwindable_mut<U, R>(
        closure: *mut ffi_closure,
        cif: *mut ffi_cif,
        callback: CallbackUnwindableMut<U, R>,
        userdata: *mut U,
        _code: CodePtr,
    ) -> Result<(), crate::low::Error> {
        // SAFETY: This function assumes all pointers are valid.
        unsafe {
            (*closure).cif = cif;
            (*closure).fun = Some(core::mem::transmute::<
                CallbackUnwindableMut<U, R>,
                RawCallback,
            >(callback));
            (*closure).user_data = userdata.cast();
        }

        Ok(())
    }
}
