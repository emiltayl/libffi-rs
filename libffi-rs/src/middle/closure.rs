extern crate alloc;
#[cfg(not(test))]
use alloc::boxed::Box;
use core::{marker::PhantomData, ptr};

#[cfg(miri)]
use miri::{closure_alloc, closure_free, prep_closure, prep_closure_mut};

#[cfg(not(miri))]
use crate::low::{closure_alloc, closure_free, prep_closure, prep_closure_mut};
use crate::{
    low::ffi_closure,
    middle::{Callback, CallbackMut, Cif, CodePtr},
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
/// use std::{mem, os::raw::c_void};
///
/// use libffi::{low, middle::*};
///
/// unsafe extern "C" fn lambda_callback<F: Fn(u64, u64) -> u64>(
///     _cif: &low::ffi_cif,
///     result: &mut u64,
///     args: *const *const c_void,
///     userdata: &F,
/// ) {
///     let args = args as *const &u64;
///     unsafe {
///         let arg1 = **args.offset(0);
///         let arg2 = **args.offset(1);
///         *result = userdata(arg1, arg2);
///     }
/// }
///
/// let cif = Cif::new(&[Type::U64, Type::U64], Some(Type::U64));
/// let lambda = |x: u64, y: u64| x + y;
/// let closure = Closure::new(cif, lambda_callback, &lambda);
///
/// let fun: &extern "C" fn(u64, u64) -> u64 = unsafe { closure.instantiate_code_ptr() };
///
/// assert_eq!(11, fun(5, 6));
/// assert_eq!(12, fun(5, 7));
/// ```
#[derive(Debug)]
pub struct Closure<'closure> {
    _cif: Cif,
    alloc: *mut ffi_closure,
    code: CodePtr,
    _marker: PhantomData<&'closure ()>,
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
    /// # Panics
    ///
    /// This function panics if libffi was unable to allocate memory in `ffi_closure_alloc`.
    ///
    /// It may also panic if `low::prep_closure_mut` fails to create the CIF. This is likely caused
    /// by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new<U, R>(cif: Cif, callback: Callback<U, R>, userdata: &'closure U) -> Self {
        let (alloc, code) = closure_alloc();

        assert!(!alloc.is_null(), "closure_alloc: returned null");

        // Safety: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_closure` call.
        unsafe {
            prep_closure(alloc, cif.cif, callback, ptr::from_ref(userdata), code).unwrap();
        }

        Closure {
            _cif: cif,
            alloc,
            code,
            _marker: PhantomData,
        }
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
    /// # Panics
    ///
    /// This function panics if libffi was unable to allocate memory in `ffi_closure_alloc`.
    ///
    /// It may also panic if `low::prep_closure_mut` fails to create the CIF. This is likely caused
    /// by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_mut<U, R>(cif: Cif, callback: CallbackMut<U, R>, userdata: &'closure mut U) -> Self {
        let (alloc, code) = closure_alloc();

        assert!(!alloc.is_null(), "closure_alloc: returned null");

        // Safety: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_mut(alloc, cif.cif, callback, ptr::from_mut(userdata), code).unwrap();
        }

        Closure {
            _cif: cif,
            alloc,
            code,
            _marker: PhantomData,
        }
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

/// Represents a closure callable from C that owns its own `userdata`.
///
/// This works similar to [`Closure`], except that [`ClosureOwned`] owns its own `userdata` which
/// will be dropped when [`ClosureOwned`] is dropped.
#[derive(Debug)]
pub struct ClosureOwned<U>
where
    U: 'static,
{
    alloc: *mut ffi_closure,
    code: CodePtr,
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
    /// # Panics
    ///
    /// This function panics if libffi was unable to allocate memory in `ffi_closure_alloc`.
    ///
    /// It may also panic if `low::prep_closure_mut` fails to create the CIF. This is likely caused
    /// by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new<R>(cif: Cif, callback: Callback<U, R>, userdata: U) -> Self {
        let (alloc, code) = closure_alloc();

        assert!(!alloc.is_null(), "closure_alloc: returned null");

        let userdata = Box::into_raw(Box::new(userdata));

        // Safety: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure(alloc, cif.cif, callback, userdata, code).unwrap();
        }

        ClosureOwned {
            alloc,
            code,
            _cif: cif,
            userdata,
        }
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
    /// # Panics
    ///
    /// This function panics if libffi was unable to allocate memory in `ffi_closure_alloc`.
    ///
    /// It may also panic if `low::prep_closure_mut` fails to create the CIF. This is likely caused
    /// by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_mut<R>(cif: Cif, callback: CallbackMut<U, R>, userdata: U) -> Self {
        let (alloc, code) = closure_alloc();

        assert!(!alloc.is_null(), "closure_alloc: returned null");

        let userdata = Box::into_raw(Box::new(userdata));

        // Safety: `Type` should ensure that no input to this function can cause safety issues
        // in the `low::prep_closure_mut` call.
        unsafe {
            prep_closure_mut(alloc, cif.cif, callback, userdata, code).unwrap();
        }

        ClosureOwned {
            alloc,
            code,
            _cif: cif,
            userdata,
        }
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

#[cfg(all(test, not(miri)))]
mod test {
    use core::ffi::c_void;

    use super::*;
    use crate::{low::ffi_cif, middle::Type};

    #[test]
    fn closure() {
        let cif = Cif::new(&[Type::U64], Some(Type::U64));
        let env: u64 = 5;
        let closure = Closure::new(cif, callback, &env);

        // SAFETY: `callback` expects one u64 and returns a u64.
        let fun: &extern "C" fn(u64) -> u64 = unsafe { closure.instantiate_code_ptr() };

        assert_eq!(11, fun(6));
        assert_eq!(12, fun(7));
    }

    unsafe extern "C" fn callback(
        _cif: &ffi_cif,
        result: &mut u64,
        args: *const *const c_void,
        userdata: &u64,
    ) {
        let args = args.cast::<*const u64>();
        // SAFETY: `callback` receives a pointer to an array with pointers to the provided
        // arguments. This derefs a the pointer to the first argument, which should be a pointer to
        // a u64.
        *result = unsafe { **args } + *userdata;
    }

    #[test]
    fn rust_lambda() {
        let cif = Cif::new(&[Type::U64, Type::U64], Some(Type::U64));
        let env = |x: u64, y: u64| x + y;
        let closure = Closure::new(cif, callback2, &env);

        // SAFETY: `callback2` expects two u64 arguments and returns a u64.
        let fun: &extern "C" fn(u64, u64) -> u64 = unsafe { closure.instantiate_code_ptr() };

        assert_eq!(11, fun(5, 6));
    }

    unsafe extern "C" fn callback2<F: Fn(u64, u64) -> u64>(
        _cif: &ffi_cif,
        result: &mut u64,
        args: *const *const c_void,
        userdata: &F,
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

        *result = userdata(first_arg, second_arg);
    }
}

/// Tests to ensure that the memory management for closures is correct.
#[cfg(test)]
mod miritest {
    use core::ffi::c_void;

    use super::*;
    use crate::low::ffi_cif;

    unsafe extern "C" fn dummy_callback(
        _cif: &ffi_cif,
        _result: &mut u32,
        _args: *const *const c_void,
        _userdata: &u32,
    ) {
    }

    #[test]
    fn create_closures() {
        let cif = Cif::new(&[], None);
        let cif2 = cif.clone();

        let state = 0u32;

        let _closure = Closure::new(cif, dummy_callback, &state);
        let _closure2 = ClosureOwned::new(cif2, dummy_callback, 0u32);
    }
}

#[cfg(miri)]
mod miri {
    use super::*;
    use crate::low::{RawCallback, Result, ffi_cif};

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
    ) -> Result<()> {
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

    pub(super) unsafe fn prep_closure_mut<U, R>(
        closure: *mut ffi_closure,
        cif: *mut ffi_cif,
        callback: CallbackMut<U, R>,
        userdata: *mut U,
        _code: CodePtr,
    ) -> Result<()> {
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
}
