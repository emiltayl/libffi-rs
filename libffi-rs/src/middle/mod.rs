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
use alloc::{boxed::Box, vec::Vec};
use core::borrow::Borrow;
use core::ffi::c_void;

#[cfg(miri)]
use miri::{call, prep_cif, prep_cif_var};

use crate::low::ffi_cif;
pub use crate::low::{
    Callback, CallbackMut, CallbackUnwindable, CallbackUnwindableMut, CodePtr, ffi_abi as FfiAbi,
    ffi_abi_FFI_DEFAULT_ABI,
};
#[cfg(not(miri))]
use crate::low::{call, prep_cif, prep_cif_var};

mod arg;
#[expect(deprecated, reason = "Re-export of deprecated function.")]
pub use arg::arg;
pub use arg::{Arg, OwnedArg};

mod closure;
pub(crate) use closure::internal::{ClosureOnce, OnceData};
pub use closure::{Closure, ClosureOwned};

mod types;
pub use types::Type;

mod builder;
pub use builder::Builder;

/// Errors that may be returned by functions in the `middle` module.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Error {
    /// An error from the underlying libffi library.
    Libffi(crate::low::Error),
    /// Returned if [`Cif::call`] is called with fewer or more arguments than the number of
    /// arguments provided when creating the `Cif`.
    InvalidArgCount {
        /// Number of arguments given when creating the `Cif`.
        expected: usize,
        /// Number of arguments provided to [`Cif::call`].
        provided: usize,
    },
    /// Returned if the number of arguments provided when creating a Cif exceeds `u32::MAX`.
    TooManyArguments(usize),
}

impl From<crate::low::Error> for Error {
    fn from(error: crate::low::Error) -> Self {
        Self::Libffi(error)
    }
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
/// use libffi::middle::{Arg, Cif, CodePtr, Type};
///
/// # use libffi::middle::Error;
/// # fn main() -> Result<(), Error> {
/// let args = [Type::U64, Type::Pointer];
/// let cif = Cif::new(&args, Some(Type::U64))?;
///
/// let n: u64 = unsafe {
///     cif.call(
///         CodePtr(add as *mut _),
///         &[Arg::borrowed(&5u64), Arg::borrowed(&&6u64)],
///     )
/// }?;
/// assert_eq!(11, n);
/// #
/// #   Ok(())
/// # }
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
    /// # Errors
    ///
    /// See [`Cif::new_with_abi`] for possible error scenarios.
    #[inline]
    pub fn new(args: &[Type], result: Option<Type>) -> Result<Self, Error> {
        Self::new_with_abi(args, result, ffi_abi_FFI_DEFAULT_ABI)
    }

    /// Creates a new [`Cif`] for the given argument and result types, and ABI. A `void` return type
    /// is defined in the `Cif` if `result` is `None`.
    ///
    /// # Errors
    ///
    /// This function returns an error if `args` contains `u32::MAX` or more elements, or if
    /// `low::prep_cif` fails to create the CIF. The latter is probably caused by a bug in this
    /// crate and should be reported.
    #[inline]
    pub fn new_with_abi(args: &[Type], result: Option<Type>, abi: FfiAbi) -> Result<Self, Error> {
        let n_args = args.len();

        let args: Box<[types::RawType]> = args.iter().map(Type::as_raw).collect();
        let args = Box::into_raw(args);

        let result = match result {
            Some(result) => result.as_raw(),
            None => types::RawType::VOID,
        };

        let cif = Box::into_raw(Box::new(ffi_cif::default()));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_cif` call.
        unsafe {
            prep_cif(
                cif,
                abi,
                n_args
                    .try_into()
                    .map_err(|_| Error::TooManyArguments(n_args))?,
                result.0,
                (*args).as_mut_ptr().cast(),
            )
        }?;

        // Note that cif retains references to args and result, which is why we hold onto them here.
        Ok(Cif { cif, args, result })
    }

    /// Creates a new variadic [CIF](Cif) for the given argument and result types. When calling a
    /// function using a `Cif` created by this function, all arguments should be passed in the order
    /// they were provided with the `fixed_args` coming first, followed by the `var_args`.
    ///
    /// # Arguments
    ///
    /// * `fixed_args` is an iterator over the [`Type`]s of the fixed arguments that are always
    ///   provided to the function. All integer arguments must be at least 32 bits wide.
    /// * `var_args` is an iterator over the [`Type`]s that of the varargs provided to the function.
    ///   Note that if a different number of varargs or different types are required, a new [`Cif`]
    ///   must be created. All integer arguments must be at least 32 bits wide.
    /// * `result` is either `None` if the function does not return a value or `Some(Type)` with the
    ///   return type.
    ///
    /// # Errors
    ///
    /// This function returns an error if `args` contains `u32::Max` or more elements, or if
    /// `low::prep_cif` fails to create the CIF. The latter is probably caused by a bug in this
    /// crate and should be reported.
    ///
    /// If any of the argument types are 8- or 16-bit integers, or 32-bit floats.
    ///
    /// # Examples
    /// todo
    pub fn new_variadic<I, J>(
        fixed_args: I,
        var_args: J,
        result: Option<Type>,
    ) -> Result<Self, Error>
    where
        I: IntoIterator,
        I::Item: Borrow<Type>,
        J: IntoIterator,
        J::Item: Borrow<Type>,
    {
        Self::new_variadic_with_abi(fixed_args, var_args, result, ffi_abi_FFI_DEFAULT_ABI)
    }

    /// Creates a new variadic [CIF](Cif) for the given argument and result types for the specified
    /// ABI. When calling a function using a `Cif` created by this function, all arguments should be
    /// passed in the order they were provided with the `fixed_args` coming first, followed by the
    /// `var_args`.
    ///
    /// # Arguments
    ///
    /// * `fixed_args` is an iterator over the [`Type`]s of the fixed arguments that are always
    ///   provided to the function. All integer arguments must be at least 32 bits wide.
    /// * `var_args` is an iterator over the [`Type`]s that of the varargs provided to the function.
    ///   Note that if a different number of varargs or different types are required, a new [`Cif`]
    ///   must be created. All integer arguments must be at least 32 bits wide.
    /// * `result` is either `None` if the function does not return a value or `Some(Type)` with the
    ///   return type.
    /// * `abi` is the Abi of the target function.
    ///
    /// # Errors
    ///
    /// This function returns an error if `args` contains `u32::Max` or more elements, or if
    /// `low::prep_cif` fails to create the CIF. The latter is probably caused by a bug in this
    /// crate and should be reported.
    ///
    /// If any of the argument types are 8- or 16-bit integers, or 32-bit floats.
    ///
    /// # Examples
    /// todo
    pub fn new_variadic_with_abi<I, J>(
        fixed_args: I,
        var_args: J,
        result: Option<Type>,
        abi: FfiAbi,
    ) -> Result<Self, Error>
    where
        I: IntoIterator,
        I::Item: Borrow<Type>,
        J: IntoIterator,
        J::Item: Borrow<Type>,
    {
        let mut args: Vec<types::RawType> = fixed_args
            .into_iter()
            .map(|ty| ty.borrow().as_raw())
            .collect();

        let n_fixed_args: u32 = args
            .len()
            .try_into()
            .map_err(|_| Error::TooManyArguments(args.len()))?;

        args.extend(var_args.into_iter().map(|ty| ty.borrow().as_raw()));

        let n_total_args: u32 = args
            .len()
            .try_into()
            .map_err(|_| Error::TooManyArguments(args.len()))?;

        let args = args.into_boxed_slice();
        let args = Box::into_raw(args);

        let result = match result {
            Some(result) => result.as_raw(),
            None => types::RawType::VOID,
        };

        let cif = Box::into_raw(Box::new(ffi_cif::default()));

        // SAFETY: `Type` should ensure that no input to this function can cause safety issues in
        // the `low::prep_cif` call.
        unsafe {
            prep_cif_var(
                cif,
                abi,
                n_fixed_args,
                n_total_args,
                result.0,
                (*args).as_mut_ptr().cast(),
            )
        }?;

        // Note that cif retains references to args and result, which is why we hold onto them here.
        Ok(Cif { cif, args, result })
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
    /// # Errors
    ///
    /// This function will return an error if `args` does not contain exactly as many arguments as
    /// defined in when creating the Cif or more than `usize::MAX` arguments are provided.
    #[inline]
    pub unsafe fn call<R>(&self, fun: CodePtr, args: &[Arg]) -> Result<R, Error> {
        // SAFETY: `self.cif` is a pointer to `low::ffi_cif` owned and managed by `self`.
        unsafe {
            let n_args: usize = (*self.cif)
                .nargs
                .try_into()
                .map_err(|_| Error::TooManyArguments(usize::MAX))?;

            if n_args != args.len() {
                return Err(Error::InvalidArgCount {
                    expected: n_args,
                    provided: args.len(),
                });
            }
        }

        let mut args: Box<[*mut c_void]> = args.iter().map(Arg::as_ptr).collect();

        // SAFETY: This is inherently unsafe and it is up to the caller of this function to uphold
        // all required safety guarantees.
        unsafe { Ok(call::<R>(self.cif, fun, args.as_mut_ptr().cast())) }
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
    use core::f64;
    #[cfg(not(target_env = "msvc"))]
    use core::ffi::c_char;
    use std::f32;

    use super::*;

    extern "C" fn add_it(n: i64, m: i64) -> i64 {
        n + m
    }

    #[test]
    fn call() {
        let cif = Cif::new(&[Type::I64, Type::I64], Some(Type::I64)).unwrap();
        let f = |m: i64, n: i64| -> i64 {
            // SAFETY: the cif is properly defined and `add_it`` does not perform any unsafe
            // actions.
            unsafe {
                cif.call(
                    CodePtr(add_it as *mut c_void),
                    &[Arg::borrowed(&m), Arg::borrowed(&n)],
                )
                .unwrap()
            }
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
        )
        .unwrap();
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
    #[should_panic = "called `Result::unwrap()` on an `Err` value: InvalidArgCount { expected: 2, provided: 1 }"]
    fn cif_call_panics_on_invalid_number_of_arguments() {
        let cif = Cif::new(&[Type::I64, Type::I64], Some(Type::I64)).unwrap();
        // SAFETY: This should panic before any potential unsafe action happens.
        let _result: i64 = unsafe {
            cif.call(CodePtr(add_it as *mut c_void), &[Arg::borrowed(&0u64)])
                .unwrap()
        };
    }

    #[repr(C)]
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct SmallFfiStruct {
        pub number: i32,
        pub tag: u8,
    }

    #[repr(C)]
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct LargeFfiStruct {
        pub a: u64,
        pub b: u64,
        pub c: u64,
        pub d: u64,
    }

    extern "C" fn identity_i8(arg: i8) -> i8 {
        arg
    }
    extern "C" fn identity_u8(arg: u8) -> u8 {
        arg
    }
    extern "C" fn identity_i16(arg: i16) -> i16 {
        arg
    }
    extern "C" fn identity_u16(arg: u16) -> u16 {
        arg
    }
    extern "C" fn identity_i32(arg: i32) -> i32 {
        arg
    }
    extern "C" fn identity_u32(arg: u32) -> u32 {
        arg
    }
    extern "C" fn identity_i64(arg: i64) -> i64 {
        arg
    }
    extern "C" fn identity_u64(arg: u64) -> u64 {
        arg
    }
    extern "C" fn identity_isize(arg: isize) -> isize {
        arg
    }
    extern "C" fn identity_usize(arg: usize) -> usize {
        arg
    }
    extern "C" fn identity_f32(arg: f32) -> f32 {
        arg
    }
    extern "C" fn identity_f64(arg: f64) -> f64 {
        arg
    }
    extern "C" fn identity_const_ptr(arg: *const i32) -> *const i32 {
        arg
    }
    extern "C" fn identity_mut_ptr(arg: *mut i32) -> *mut i32 {
        arg
    }
    extern "C" fn identity_small_ffi_struct(arg: SmallFfiStruct) -> SmallFfiStruct {
        arg
    }
    extern "C" fn identity_large_ffi_struct(arg: LargeFfiStruct) -> LargeFfiStruct {
        arg
    }

    macro_rules! gen_identity_fn_test {
        ($fn:ident($ty:ty = $val:expr, $ffity:expr)) => {{
            let cif = Cif::new(&[$ffity], Some($ffity)).unwrap();
            let orig: $ty = $val;
            // SAFETY: It is assumed that $fn is a valid function accepting $ty and returning $ty.
            let result: $ty = unsafe {
                cif.call(CodePtr($fn as *mut _), &[Arg::borrowed(&orig)])
                    .unwrap()
            };
            assert_eq!(orig, result);
        }};
    }

    #[expect(
        clippy::float_cmp,
        reason = "Direct comparison of floats that have not been modified."
    )]
    #[test]
    fn test_identity_functions() {
        let mut num: i32 = 0;

        let small_struct = Type::structure(&[Type::I32, Type::U8]);
        let large_struct = Type::structure(&[Type::U64, Type::U64, Type::U64, Type::U64]);

        gen_identity_fn_test!(identity_i8(i8 = 0x55, Type::I8));
        gen_identity_fn_test!(identity_u8(u8 = 0xAA, Type::U8));
        gen_identity_fn_test!(identity_i16(i16 = 0x5544, Type::I16));
        gen_identity_fn_test!(identity_u16(u16 = 0xAABB, Type::U16));
        gen_identity_fn_test!(identity_i32(i32 = 0x5544_3322, Type::I32));
        gen_identity_fn_test!(identity_u32(u32 = 0xAABB_CCDD, Type::U32));
        gen_identity_fn_test!(identity_i64(i64 = 0x5544_3322_1100_AABB, Type::I64));
        gen_identity_fn_test!(identity_u64(u64 = 0xAABB_CCDD_EEFF_0011, Type::U64));
        gen_identity_fn_test!(identity_isize(isize = 0x5544_3322, Type::Isize));
        gen_identity_fn_test!(identity_usize(usize = 0xAABB_CCDD, Type::Usize));
        gen_identity_fn_test!(identity_f32(f32 = f32::consts::PI, Type::F32));
        gen_identity_fn_test!(identity_f64(f64 = f64::consts::TAU, Type::F64));
        gen_identity_fn_test!(identity_const_ptr(*const i32 = &raw const num, Type::Pointer));
        gen_identity_fn_test!(identity_mut_ptr(*mut i32 = &raw mut num, Type::Pointer));
        gen_identity_fn_test!(identity_small_ffi_struct(
            SmallFfiStruct = SmallFfiStruct {
                number: 0x5544_3322,
                tag: 0xAA
            },
            small_struct.clone()
        ));
        gen_identity_fn_test!(identity_large_ffi_struct(
            LargeFfiStruct = LargeFfiStruct {
                a: 0x1234_5678_9ABC_DEF0,
                b: 0x0FED_CBA9_8765_4321,
                c: 0xABBA_CDDC_EFFE_0110,
                d: 0x192A_3B4C_5D6E_7F80,
            },
            large_struct.clone()
        ));
    }

    macro_rules! gen_owned_arg_identity_fn_test {
        ($fn:ident($ty:ty = $val:expr, $ffity:expr)) => {{
            let cif = Cif::new(&[$ffity], Some($ffity)).unwrap();
            let orig: $ty = $val;
            // SAFETY: It is assumed that $fn is a valid function accepting $ty and returning $ty.
            let result: $ty = unsafe {
                cif.call(CodePtr($fn as *mut _), &[Arg::owned(orig)])
                    .unwrap()
            };
            assert_eq!(orig, result);
        }};
    }

    #[expect(
        clippy::float_cmp,
        reason = "Direct comparison of floats that have not been modified."
    )]
    #[test]
    fn test_owned_arg_identity_functions() {
        let mut num: i32 = 0;

        gen_owned_arg_identity_fn_test!(identity_i8(i8 = 0x55, Type::I8));
        gen_owned_arg_identity_fn_test!(identity_u8(u8 = 0xAA, Type::U8));
        gen_owned_arg_identity_fn_test!(identity_i16(i16 = 0x5544, Type::I16));
        gen_owned_arg_identity_fn_test!(identity_u16(u16 = 0xAABB, Type::U16));
        gen_owned_arg_identity_fn_test!(identity_i32(i32 = 0x5544_3322, Type::I32));
        gen_owned_arg_identity_fn_test!(identity_u32(u32 = 0xAABB_CCDD, Type::U32));
        gen_owned_arg_identity_fn_test!(identity_i64(i64 = 0x5544_3322_1100_AABB, Type::I64));
        gen_owned_arg_identity_fn_test!(identity_u64(u64 = 0xAABB_CCDD_EEFF_0011, Type::U64));
        gen_owned_arg_identity_fn_test!(identity_isize(isize = 0x5544_3322, Type::Isize));
        gen_owned_arg_identity_fn_test!(identity_usize(usize = 0xAABB_CCDD, Type::Usize));
        gen_owned_arg_identity_fn_test!(identity_f32(f32 = f32::consts::PI, Type::F32));
        gen_owned_arg_identity_fn_test!(identity_f64(f64 = f64::consts::TAU, Type::F64));
        gen_owned_arg_identity_fn_test!(identity_const_ptr(*const i32 = &raw const num, Type::Pointer));
        gen_owned_arg_identity_fn_test!(identity_mut_ptr(*mut i32 = &raw mut num, Type::Pointer));
    }

    /// Test variadic cifs by calling `snprintf`. I could not seem to figure out how to get
    /// _snprintf linked with msvc, so I am leaving it out for now.
    #[cfg(not(target_env = "msvc"))]
    #[test]
    fn call_snprintf() {
        unsafe extern "C" {
            unsafe fn snprintf(s: *mut c_char, n: usize, format: *const c_char, ...) -> i32;
        }

        let mut output_buffer = [0u8; 50];

        let expected = c"num: 123, pi: 3.14, This is a &Cstr";

        let format_str = c"num: %d, pi: %.2f, %s";

        let num = 123;
        let pi = f64::consts::PI;
        let cstr = c"This is a &Cstr";

        let cif = Cif::new_variadic(
            [Type::Pointer, Type::Usize, Type::Pointer],
            [Type::I32, Type::F64, Type::Pointer],
            Some(Type::I32),
        )
        .unwrap();

        // Safety:
        // * snprintf is a vararg function that will not write outside the length of the output
        //   buffer.
        // * The output buffer is mutable.
        // * The proper length of the output buffer is given and len() returns an usize.
        // * There is room for the NULL-byte at the end of the buffer as well.
        // * The format string points to a well-formed C-string.
        // * The first argument is a signed 32-bit int.
        // * The second argument is a 32-bit float.
        // * The third arguments is a pointer to a well-formed C-string.
        let result: i32 = unsafe {
            cif.call(
                CodePtr(snprintf as *mut _),
                &[
                    Arg::borrowed(&output_buffer.as_mut_ptr()),
                    Arg::borrowed(&output_buffer.len()),
                    Arg::borrowed(&format_str.as_ptr()),
                    Arg::borrowed(&num),
                    Arg::borrowed(&pi),
                    Arg::borrowed(&cstr.as_ptr()),
                ],
            )
            .unwrap()
        };

        assert_eq!(result, expected.count_bytes().try_into().unwrap());
    }
}

/// Tests to ensure that memory management for `middle` structs is correct.
#[cfg(test)]
mod miritest {
    use core::ptr;

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
        )
        .unwrap();

        let cif_1 = cif.clone();
        drop(cif);
        let cif = cif_1.clone();
        let cif_2 = cif.clone();
        let cif_3 = cif_2.clone();
        let cif_4 = cif_2.clone();
        drop(cif);

        // Test with `Arg::Borrowed`.
        {
            let arguments = [
                Arg::borrowed(&1i8),
                Arg::borrowed(&2u16),
                Arg::borrowed(&3i32),
                Arg::borrowed(&4u64),
                Arg::borrowed(&ptr::null::<c_void>()),
                Arg::borrowed(&6f32),
                Arg::borrowed(&7f64),
                Arg::borrowed(&8u8),
            ];

            // SAFETY: [`Cif::call`] is called with the correct number of arguments with (mostly)
            // the correct type. A struct with no members cannot be read anyways?
            unsafe {
                cif_1
                    .call::<u32>(CodePtr(dummy_function as *mut _), &arguments)
                    .unwrap();
                cif_2
                    .call::<u32>(CodePtr(dummy_function as *mut _), &arguments)
                    .unwrap();
                drop(cif_2);
                cif_3
                    .call::<u32>(CodePtr(dummy_function as *mut _), &arguments)
                    .unwrap();
            }
        }

        // Test with `Arg::Owned`.
        {
            let arguments = [
                Arg::owned(1i8),
                Arg::owned(2u16),
                Arg::owned(3i32),
                Arg::owned(4u64),
                Arg::owned(ptr::null::<c_void>()),
                Arg::owned(6f32),
                Arg::owned(7f64),
                Arg::owned(8u8),
            ];

            // SAFETY: [`Cif::call`] is called with the correct number of arguments with (mostly)
            // the correct type. A struct with no members cannot be read anyways?
            unsafe {
                cif_1
                    .call::<u32>(CodePtr(dummy_function as *mut _), &arguments)
                    .unwrap();
                cif_4
                    .call::<u32>(CodePtr(dummy_function as *mut _), &arguments)
                    .unwrap();
                drop(cif_4);
                cif_3
                    .call::<u32>(CodePtr(dummy_function as *mut _), &arguments)
                    .unwrap();
            }
        }
    }

    /// Verify that [`Cif`]'s `Debug` impl does not misbehave.
    #[test]
    fn verify_cif_debug_behavior() {
        let cif = Cif::new(
            &[Type::I8, Type::Pointer, Type::structure(&[Type::F64])],
            Some(Type::U64),
        )
        .unwrap();

        // Invoke `cif`'s debug impl.
        let _ = format!("{cif:?}");
    }

    // Verify that `Ciff::new_variadic` is able to count how many arguments it receives.
    #[test]
    fn verify_var_cif_count() {
        for n_fixed_args in 0..5 {
            for n_var_args in 0..5 {
                let fixed_args = vec![Type::U32; n_fixed_args];
                let var_args = vec![Type::U32; n_var_args];

                let cif = Cif::new_variadic(fixed_args, var_args, None).unwrap();

                // Safety: The `ffi_cif` should be properly initialized and readable.
                unsafe {
                    assert_eq!(
                        (*cif.cif).nargs,
                        u32::try_from(n_fixed_args + n_var_args).unwrap()
                    );
                }
            }
        }
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
    ) -> Result<(), crate::low::Error> {
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

    /// Replaces [`low::prep_cif_var`] for tests with miri. Note that this function can not be used
    /// to prepare an actual [`middle::Cif`] for use with libffi.
    ///
    /// This function will write to `cif`, `rtype`, and `atypes` as that is something libffi may do.
    ///
    /// # Safety
    ///
    /// This function will write to the pointers provided to this function. As long as they point to
    /// valid memory, nothing unsafe should happen.
    pub(super) unsafe fn prep_cif_var(
        cif: *mut ffi_cif,
        abi: ffi_abi,
        nfixedargs: u32,
        ntotalargs: u32,
        rtype: *mut ffi_type,
        atypes: *mut *mut ffi_type,
    ) -> Result<(), crate::low::Error> {
        // SAFETY: It is assumed that `cif`, `rtype`, and `atypes` are valid pointers that can be
        // written to and that `artypes` points to an array of `nargs` length.
        unsafe {
            write_to_ffi_type(rtype);

            let nfixedargs_usize = usize::try_from(nfixedargs).unwrap();
            let nargs_usize = usize::try_from(ntotalargs).unwrap();

            assert!(nfixedargs_usize <= nargs_usize);

            for argument_index in 0..nargs_usize {
                write_to_ffi_type(*(atypes.add(argument_index)));
            }

            (*cif).abi = abi;
            (*cif).nargs = ntotalargs;
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
