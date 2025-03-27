//! Middle layer providing a somewhat safer (but still quite unsafe) API.
//!
//! The main idea of the middle layer is to wrap types [`low::ffi_cif`] and [`low::ffi_closure`] as
//! [`Cif`] and [`Closure`], respectively, so that their resources are managed properly. However,
//! calling a function via a CIF or closure is still unsafe because argument types aren’t checked
//! and the function may perform actions that are unsafe or unsound.
//!
//! [`low::ffi_cif`]: `crate::low::ffi_cif`
//! [`low::ffi_closure`]: `crate::low::ffi_closure`

extern crate alloc;
#[cfg(not(test))]
use alloc::boxed::Box;
use core::{ffi::c_void, marker::PhantomData, ptr};

#[cfg(miri)]
use miri::{call, prep_cif};

use crate::low::ffi_cif;
pub use crate::low::{
    Callback, CallbackMut, CallbackUnwindable, CallbackUnwindableMut, CodePtr, ffi_abi as FfiAbi,
    ffi_abi_FFI_DEFAULT_ABI,
};
#[cfg(not(miri))]
use crate::low::{call, prep_cif};

mod closure;
pub use closure::{Closure, ClosureOwned};

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
pub struct Arg<'arg>(*mut c_void, PhantomData<&'arg c_void>);

impl Arg<'_> {
    /// Coerces an argument reference into the [`Arg`] type.
    ///
    /// This is used to wrap each argument pointer before passing them to [`Cif::call`].
    pub fn new<T>(r: &T) -> Self {
        Arg(ptr::from_ref(r) as *mut c_void, PhantomData)
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
/// extern "C" fn add(x: u64, y: &u64) -> u64 {
///     x + y
/// }
///
/// use libffi::middle::{Cif, CodePtr, Type, arg};
///
/// let args = [Type::U64, Type::Pointer];
/// let cif = Cif::new(&args, Some(Type::U64));
///
/// let n: u64 = unsafe { cif.call(CodePtr(add as *mut _), &[arg(&5u64), arg(&&6u64)]) };
/// assert_eq!(11, n);
/// ```
///
/// [`low::ffi_cif`]: [`crate::low::ffi_cif`]
#[allow(
    clippy::struct_field_names,
    reason = "`cif` properly describes what is stored in the field (the cif)."
)]
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
            None => types::RawType::VOID,
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
        unsafe { call::<R>(self.cif, fun, args.as_ptr().cast_mut().cast()) }
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

// SAFETY: It is safe to send a `Cif` to another thread, after it has been created `Cif` is not
// modified until it is dropped.
unsafe impl Send for Cif {}
// SAFETY: It is safe to send a `Cif` to another thread, after it has been created `Cif` is not
// modified until it is dropped.
unsafe impl Sync for Cif {}

#[cfg(all(test, not(miri)))]
mod test {
    use super::*;

    extern "C" fn add_it(n: i64, m: i64) -> i64 {
        n + m
    }

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

    #[test]
    #[should_panic = "Cif::call: passed wrong number of arguments"]
    fn cif_call_panics_on_invalid_number_of_arguments() {
        let cif = Cif::new(&[Type::I64, Type::I64], Some(Type::I64));
        // SAFETY: This should panic before any potential unsafe action happens.
        let _result: i64 = unsafe { cif.call(CodePtr(add_it as *mut c_void), &[arg(&0u64)]) };
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

    /// Verify that [`Cif`]'s `Debug` impl does not misbehave.
    #[test]
    fn verify_cif_debug_behavior() {
        let cif = Cif::new(
            &[Type::I8, Type::Pointer, Type::structure(&[Type::F64])],
            Some(Type::U64),
        );

        // Invoke `cif`'s debug impl.
        let _ = format!("{cif:?}");
    }
}

#[cfg(miri)]
mod miri {
    use core::ffi::c_void;

    use crate::low::{CodePtr, ffi_abi, ffi_cif, ffi_type, type_tag};

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
            match type_tag {
                type_tag::SINT8 => {
                    core::ptr::read::<i8>(ptr.cast());
                }
                type_tag::UINT8 => {
                    core::ptr::read::<u8>(ptr.cast());
                }
                type_tag::SINT16 => {
                    core::ptr::read::<i16>(ptr.cast());
                }
                type_tag::UINT16 => {
                    core::ptr::read::<u16>(ptr.cast());
                }
                type_tag::SINT32 => {
                    core::ptr::read::<i32>(ptr.cast());
                }
                type_tag::UINT32 => {
                    core::ptr::read::<u32>(ptr.cast());
                }
                type_tag::SINT64 => {
                    core::ptr::read::<i64>(ptr.cast());
                }
                type_tag::UINT64 => {
                    core::ptr::read::<u64>(ptr.cast());
                }
                type_tag::POINTER => {
                    core::ptr::read::<*const c_void>(ptr.cast());
                }
                type_tag::FLOAT => {
                    core::ptr::read::<f32>(ptr.cast());
                }
                type_tag::DOUBLE => {
                    core::ptr::read::<f64>(ptr.cast());
                }
                // No test for dereferencing custom structs as of now.
                type_tag::STRUCT => assert!(!ptr.is_null()),
                _ => panic!("Unknown type tag {type_tag} detected."),
            }
        }
    }

    /// Replaces [`low::call`] for tests with miri. Note that this function will not actually call
    /// `_fun`.
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
