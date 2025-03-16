//! Middle layer providing a somewhat safer (but still quite unsafe)
//! API.
//!
//! The main idea of the middle layer is to wrap types [`low::ffi_cif`]
//! and [`low::ffi_closure`] as [`Cif`] and [`Closure`], respectively,
//! so that their resources are managed properly. However, calling a
//! function via a CIF or closure is still unsafe because argument types
//! aren’t checked.

extern crate alloc;
#[cfg(not(test))]
use alloc::boxed::Box;
use core::{any::Any, ffi::c_void, marker::PhantomData, ptr};

#[cfg(miri)]
use miri::{call, prep_cif};

pub use crate::low::{Callback, CallbackMut, CodePtr, ffi_abi as FfiAbi, ffi_abi_FFI_DEFAULT_ABI};
#[cfg(not(miri))]
use crate::low::{call, prep_cif};
use crate::low::{
    closure_alloc, closure_free, ffi_cif, ffi_closure, prep_closure, prep_closure_mut,
    types as low_types,
};

mod types;
pub use types::Type;

mod builder;
pub use builder::Builder;

/// Contains an untyped pointer to a function argument.
///
/// When calling a function via a [CIF](Cif), each argument must be passed as a C `void*`. Wrapping
/// the argument in the [`Arg`] struct accomplishes the necessary coercion.
#[derive(Clone, Debug)]
#[repr(C)]
pub struct Arg(*mut c_void);

impl Arg {
    /// Coerces an argument reference into the [`Arg`] type.
    ///
    /// This is used to wrap each argument pointer before passing them to [`Cif::call`].
    pub fn new<T>(r: &T) -> Self {
        Arg(ptr::from_ref(r) as *mut c_void)
    }
}

/// Coerces an argument reference into the [`Arg`] type.
///
/// This is used to wrap each argument pointer before passing them to [`Cif::call`]. (This is the
/// same as [`Arg::new`]).
pub fn arg<T>(r: &T) -> Arg {
    Arg::new(r)
}

/// Describes the calling convention and types for calling a function.
///
/// This is the middle layer’s wrapping of the [`low`](crate::low) and [`raw`](crate::raw) layers’
/// [`low::ffi_cif`]. An initialized CIF contains references to an array of argument types and a
/// result type, each of which may be allocated on the heap. `Cif` manages the memory of those
/// referenced objects.
///
/// Construct with [`Cif::new`].
///
/// # Examples
///
/// ```
/// extern "C" fn add(x: f64, y: &f64) -> f64 {
///     x + y
/// }
///
/// use libffi::middle::*;
///
/// let args = [Type::F64, Type::Pointer];
/// let cif = Cif::new(&args, Some(Type::F64));
///
/// let n = unsafe { cif.call(CodePtr(add as *mut _), &[arg(&5f64), arg(&&6f64)]) };
/// assert_eq!(11f64, n);
/// ```
pub struct Cif {
    cif: *mut ffi_cif,
    args: *mut [types::RawType],
    result: types::RawType,
}

impl Cif {
    /// Creates a new [CIF](Cif) for the given argument and result types. A `void` return type is
    /// defined in the `Cif` if `result` is `None`.
    ///
    /// [`Cif`] defaults to the platform’s default calling convention; use [`Cif::new_with_abi`] to
    /// create a Cif for a given ABI.
    ///
    /// # Panics
    ///
    /// See [`Cif::new_with_abi`] for possible panic scenarios.
    pub fn new(args: &[Type], result: Option<Type>) -> Self {
        Self::new_with_abi(args, result, ffi_abi_FFI_DEFAULT_ABI)
    }

    /// Creates a new [`Cif`] for the given argument and result types, and ABI. A `void` return type
    /// is defined in the `Cif` if `result` is `None`.
    ///
    /// # Panics
    ///
    /// This function panics if `args` contains 2^32 or more elements or if `low::prep_cif` fails to
    /// create the CIF. The latter is probably caused by a bug in this crate and should be reported.
    pub fn new_with_abi(args: &[Type], result: Option<Type>, abi: FfiAbi) -> Self {
        let n_args = args.len();

        let args: Box<[types::RawType]> = args.iter().map(Type::as_raw).collect();
        let args = Box::into_raw(args);

        let result = match result {
            Some(result) => result.as_raw(),
            None => types::RawType(&raw mut low_types::void),
        };

        let cif = Box::into_raw(Box::new(ffi_cif::default()));

        // Safety: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_cif` call.
        unsafe {
            prep_cif(
                cif,
                abi,
                n_args.try_into().unwrap(),
                result.0,
                (*args).as_mut_ptr().cast(),
            )
        }
        .expect("low::prep_cif");

        // Note that cif retains references to args and result, which is why we hold onto them here.
        Cif { cif, args, result }
    }

    /// Calls a function with the given arguments.
    ///
    /// In particular, this method invokes function `fun` passing it arguments `args`, and returns
    /// the result.
    ///
    /// # Safety
    ///
    /// There is no checking that the calling convention and types in the `Cif` match the actual
    /// calling convention and types of `fun`, nor that they match the types of `args`.
    ///
    /// # Panics
    ///
    /// This function will panic if `args` does not contain exactly as many arguments as defined in
    /// [`Cif::new`].
    pub unsafe fn call<R>(&self, fun: CodePtr, args: &[Arg]) -> R {
        // SAFETY: `self.cif` is a pointer to `low::ffi_cif` owned and managed by `self`.
        unsafe {
            assert_eq!(
                (*self.cif).nargs as usize,
                args.len(),
                "Cif::call: passed wrong number of arguments"
            );
        }

        // SAFETY: This is inherently unsafe and it is up to the caller of this function to uphold
        // all required safety guarantees.
        unsafe { call::<R>(self.cif, fun, args.as_ptr() as *mut *mut c_void) }
    }
}

impl Clone for Cif {
    fn clone(&self) -> Self {
        // SAFETY: `self.cif` is a pointer to a `low::ffi_cif` owned and managed by `self`.
        let mut cif = unsafe { Box::new(*self.cif) };
        // SAFETY: `self.args` is a pointer to `[RawType]` owned and managed by `self`.
        let args_clone = unsafe {
            (*self.args)
                .iter()
                .cloned()
                .collect::<Box<[types::RawType]>>()
        };
        let args_clone = Box::into_raw(args_clone.clone());

        let result = self.result.clone();

        // SAFETY: `args_clone` is a pointer to the new `[RawType]` for the cloned `Cif`.
        cif.arg_types = unsafe { (*args_clone).as_mut_ptr().cast() };
        cif.rtype = result.0;

        Self {
            cif: Box::into_raw(cif),
            args: args_clone,
            result,
        }
    }
}

impl core::fmt::Debug for Cif {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // SAFETY: `self.args` is a pointer to `[RawType]` owned and managed by `self`.
        let args_ref = unsafe { &*self.args };

        f.debug_struct("Cif")
            // SAFETY: `self.cif` is a pointer to a `low::ffi_cif` owned and managed by `self`.
            .field("cif", unsafe { &*self.cif })
            .field("args", &args_ref)
            .field("result", &self.result)
            .finish()
    }
}

impl Drop for Cif {
    fn drop(&mut self) {
        // SAFETY: `self.cif` and `self.args` are a pointers created by `Box::into_raw` owned and
        // managed by `self`.
        unsafe {
            drop(Box::from_raw(self.cif));
            drop(Box::from_raw(self.args));
        }
    }
}

/// Represents a closure callable from C.
///
/// A libffi closure captures a `void*` (“userdata”) and passes it to a callback when the code
/// pointer (obtained via [`Closure::code_ptr`]) is invoked. Lifetype parameter `'a` ensures that
/// the closure does not outlive the userdata.
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
pub struct Closure<'a> {
    _cif: Cif,
    alloc: *mut ffi_closure,
    code: CodePtr,
    _marker: PhantomData<&'a ()>,
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

impl<'a> Closure<'a> {
    /// Creates a new closure with immutable userdata.
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
    /// This function panics if `low::prep_closure` fails to create the CIF. This is probably caused
    /// by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new<U, R>(cif: Cif, callback: Callback<U, R>, userdata: &'a U) -> Self {
        let (alloc, code) = closure_alloc();

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

    /// Creates a new closure with mutable userdata.
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
    /// This function panics if `low::prep_closure_mute` fails to create the CIF. This is probably
    /// caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new_mut<U, R>(cif: Cif, callback: CallbackMut<U, R>, userdata: &'a mut U) -> Self {
        let (alloc, code) = closure_alloc();

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

/// The type of callback invoked by a [`ClosureOnce`].
pub type CallbackOnce<U, R> = CallbackMut<Option<U>, R>;

/// A closure that owns needs-drop data.
///
/// This allows the closure’s callback to take ownership of the data, in which case the userdata
/// will be gone if called again.
#[derive(Debug)]
pub struct ClosureOnce {
    alloc: *mut ffi_closure,
    code: CodePtr,
    _cif: Cif,
    _userdata: Box<dyn Any>,
}

impl Drop for ClosureOnce {
    fn drop(&mut self) {
        // SAFETY: `self.alloc` is allocated using `low::closure_alloc` and should therefore be
        // freed by `low::closure_free` and only that function.
        unsafe {
            closure_free(self.alloc);
        }
    }
}

impl ClosureOnce {
    /// Creates a new closure with owned userdata.
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
    /// This function panics if `low::prep_closure_mut` fails to create the CIF. This is probably
    /// caused by a bug in this crate and should be reported.
    ///
    /// # Result
    ///
    /// The new closure.
    pub fn new<U: Any, R>(cif: Cif, callback: CallbackOnce<U, R>, userdata: U) -> Self {
        let userdata = Box::new(Some(userdata)) as Box<dyn Any>;
        let (alloc, code) = closure_alloc();

        assert!(!alloc.is_null(), "closure_alloc: returned null");

        {
            let borrow = userdata.downcast_ref::<Option<U>>().unwrap();
            // Safety: `Type` should ensure that no input to this function can cause safety issues
            // in the `low::prep_closure_mut` call.
            unsafe {
                prep_closure_mut(
                    alloc,
                    cif.cif,
                    callback,
                    ptr::from_ref(borrow).cast_mut(),
                    code,
                )
                .unwrap();
            }
        }

        ClosureOnce {
            alloc,
            code,
            _cif: cif,
            _userdata: userdata,
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
    use super::*;

    #[test]
    fn call() {
        let cif = Cif::new(&[Type::I64, Type::I64], Some(Type::I64));
        let f = |m: i64, n: i64| -> i64 {
            // SAFETY: the cif is properly defined and `add_it`` does not perform any unsafe
            // actions.
            unsafe { cif.call(CodePtr(add_it as *mut c_void), &[arg(&m), arg(&n)]) }
        };

        assert_eq!(12, f(5, 7));
        assert_eq!(13, f(6, 7));
        assert_eq!(15, f(8, 7));
    }

    extern "C" fn add_it(n: i64, m: i64) -> i64 {
        n + m
    }

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

    #[test]
    fn clone_cif() {
        let cif = Cif::new(
            &[
                Type::structure(&[
                    Type::structure(&[Type::U64, Type::U8, Type::F64]),
                    Type::I8,
                    Type::I64,
                ]),
                Type::U64,
            ],
            Some(Type::U64),
        );
        let clone_cif = cif.clone();

        // SAFETY: `std::slice::from_raw_parts` is used to create slices on data created in Rust
        // that should be non-null and properly aligned.
        unsafe {
            let args = std::slice::from_raw_parts((*cif.cif).arg_types, (*cif.cif).nargs as usize);
            let struct_arg = args
                .first()
                .expect("CIF arguments slice was empty")
                .as_ref()
                .expect("CIF first argument was null");
            // Get slice of length 1 to get the first element
            let struct_size = struct_arg.size;
            let struct_parts = std::slice::from_raw_parts(struct_arg.elements, 1);
            let substruct_size = struct_parts
                .first()
                .expect("CIF struct argument's elements slice was empty")
                .as_ref()
                .expect("CIF struct argument's first element was null")
                .size;

            let clone_args = std::slice::from_raw_parts(
                (*clone_cif.cif).arg_types,
                (*clone_cif.cif).nargs as usize,
            );
            let clone_struct_arg = clone_args
                .first()
                .expect("CIF arguments slice was empty")
                .as_ref()
                .expect("CIF first argument was null");
            // Get slice of length 1 to get the first element
            let clone_struct_size = clone_struct_arg.size;
            let clone_struct_parts = std::slice::from_raw_parts(clone_struct_arg.elements, 1);
            let clone_substruct_size = clone_struct_parts
                .first()
                .expect("Cloned CIF struct argument's elements slice was empty")
                .as_ref()
                .expect("Cloned CIF struct argument's first element was null")
                .size;

            assert_eq!(struct_size, clone_struct_size);
            assert_eq!(substruct_size, clone_substruct_size);
        }
    }
}

/// Tests to ensure that memory management for `middle` structs is correct.
#[cfg(test)]
mod miritest {
    use super::*;

    extern "C" fn dummy_function(
        _: i8,
        _: u16,
        _: i32,
        _: u64,
        _: *const c_void,
        _: f32,
        _: f64,
        _: u8,
    ) -> u32 {
        0
    }

    #[test]
    fn create_cifs_clone_then_call() {
        let cif = Cif::new(
            &[
                Type::I8,
                Type::U16,
                Type::I32,
                Type::U64,
                Type::Pointer,
                Type::F32,
                Type::F64,
                Type::structure(&[Type::U8]),
            ],
            Some(Type::U32),
        );

        let cif_1 = cif.clone();
        drop(cif);
        let cif = cif_1.clone();
        let cif_2 = cif.clone();
        let cif_3 = cif_2.clone();
        drop(cif);

        let arguments = [
            arg(&1i8),
            arg(&2u16),
            arg(&3i32),
            arg(&4u64),
            arg(&ptr::null::<c_void>()),
            arg(&6f32),
            arg(&7f64),
            arg(&8u8),
        ];

        // SAFETY: [`Cif::call`] is called with the correct number of arguments with (mostly) the
        // correct type. A struct with no members cannot be read anyways?
        unsafe {
            cif_1.call::<u32>(CodePtr(dummy_function as *mut _), &arguments);
            cif_2.call::<u32>(CodePtr(dummy_function as *mut _), &arguments);
            drop(cif_2);
            cif_3.call::<u32>(CodePtr(dummy_function as *mut _), &arguments);
        }
    }
}

#[cfg(miri)]
mod miri {
    use core::ffi::c_void;

    use crate::{
        low::{CodePtr, ffi_abi, ffi_cif, ffi_type},
        raw::{
            FFI_TYPE_DOUBLE, FFI_TYPE_FLOAT, FFI_TYPE_POINTER, FFI_TYPE_SINT8, FFI_TYPE_SINT16,
            FFI_TYPE_SINT32, FFI_TYPE_SINT64, FFI_TYPE_STRUCT, FFI_TYPE_UINT8, FFI_TYPE_UINT16,
            FFI_TYPE_UINT32, FFI_TYPE_UINT64,
        },
    };

    /// Helper function to write to values in ffi_type to make sure that possible memory writes are
    /// checked.
    ///
    /// # Safety
    ///
    /// Writes to `t`, make sure that it is a well-formed [`ffi_type`].
    unsafe fn write_to_ffi_type(t: *mut ffi_type) {
        // SAFETY: It is up to the caller of this function to ensure that `t` can be written to.
        unsafe {
            (*t).alignment += 1;
            (*t).size += 1;

            if !(*t).elements.is_null() {
                let mut child = (*t).elements;
                while !(*child).is_null() {
                    write_to_ffi_type(*child);
                    child = child.add(1);
                }
            }
        }
    }

    /// Replaces [`low::prep_cif`] for tests with miri. Note that this function can not be used to
    /// prepare an actual [`middle::Cif`] for use with libffi.
    ///
    /// This function will write to `cif`, `rtype`, and `atypes` as that is something libffi may do.
    ///
    /// # Safety
    ///
    /// This function will write to the pointers provided to this function. As long as they point to
    /// valid memory, nothing unsafe should happen.
    pub(super) unsafe fn prep_cif(
        cif: *mut ffi_cif,
        abi: ffi_abi,
        nargs: u32,
        rtype: *mut ffi_type,
        atypes: *mut *mut ffi_type,
    ) -> crate::low::Result<()> {
        // SAFETY: It is assumed that `cif`, `rtype`, and `atypes` are valid pointers that can be
        // written to and that `artypes` points to an array of `nargs` length.
        unsafe {
            write_to_ffi_type(rtype);

            let nargs_usize = usize::try_from(nargs).unwrap();

            for argument_index in 0..nargs_usize {
                write_to_ffi_type(*(atypes.add(argument_index)));
            }

            (*cif).abi = abi;
            (*cif).nargs = nargs;
            (*cif).rtype = rtype;
            (*cif).arg_types = atypes;
        }

        Ok(())
    }

    /// Helper function that dereferences a pointer to a type based on its `type_tag`. This function
    /// does not currently support dereferencing structs.
    ///
    /// # Safety
    ///
    /// This function assumes that `ptr` points to valid memory of a type that corresponds to
    /// `type_tag`.
    unsafe fn deref_argument(type_tag: u16, ptr: *const c_void) {
        // SAFETY: See this function's safety section.
        unsafe {
            match u32::from(type_tag) {
                FFI_TYPE_SINT8 => {
                    core::ptr::read_volatile::<i8>(ptr.cast());
                }
                FFI_TYPE_UINT8 => {
                    core::ptr::read_volatile::<u8>(ptr.cast());
                }
                FFI_TYPE_SINT16 => {
                    core::ptr::read_volatile::<i16>(ptr.cast());
                }
                FFI_TYPE_UINT16 => {
                    core::ptr::read_volatile::<u16>(ptr.cast());
                }
                FFI_TYPE_SINT32 => {
                    core::ptr::read_volatile::<i32>(ptr.cast());
                }
                FFI_TYPE_UINT32 => {
                    core::ptr::read_volatile::<u32>(ptr.cast());
                }
                FFI_TYPE_SINT64 => {
                    core::ptr::read_volatile::<i64>(ptr.cast());
                }
                FFI_TYPE_UINT64 => {
                    core::ptr::read_volatile::<u64>(ptr.cast());
                }
                FFI_TYPE_POINTER => {
                    core::ptr::read_volatile::<*const c_void>(ptr.cast());
                }
                FFI_TYPE_FLOAT => {
                    core::ptr::read_volatile::<f32>(ptr.cast());
                }
                FFI_TYPE_DOUBLE => {
                    core::ptr::read_volatile::<f64>(ptr.cast());
                }
                // No test for dereferencing custom structs as of now.
                FFI_TYPE_STRUCT => assert!(!ptr.is_null()),
                _ => panic!("Unknown type tag {type_tag} detected."),
            }
        }
    }

    /// Replaces [`low::call`] for tests with miri. Note that this function will not actually call
    /// `fun`.
    ///
    /// # Safety
    ///
    /// This function uses `mem::zeroed` to return value. This may cause undefined behavior if all
    /// zeroes is not a valid bit pattern for `R`.
    ///
    /// It also attempts to read all `args` values based on the types defined in `cif`.
    pub(super) unsafe fn call<R>(cif: *mut ffi_cif, _fun: CodePtr, args: *mut *mut c_void) -> R {
        // SAFETY: See this function's safety section.
        unsafe {
            for arg_index in 0..usize::try_from((*cif).nargs).unwrap() {
                let type_tag = (**(*cif).arg_types.add(arg_index)).type_;
                let arg_ptr = *args.add(arg_index);

                deref_argument(type_tag, arg_ptr);
            }

            core::mem::zeroed::<R>()
        }
    }
}
