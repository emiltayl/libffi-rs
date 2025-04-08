//! Module defining traits used to more ergonomically define argument and return types used by
//! functions called through libffi.

use core::ffi::c_void;

use crate::middle::{Arg, Type};

/// A trait used to signal that a type can be passed to ffi functions. All functions sent to and
/// received from ffi boundaries must be `Copy` and `Clone`.
///
/// # Safety
///
/// The `as_ffi_type` function is used to create a `Type` which is used to describe the type to
/// libffi. Libffi reads and writes data based on this information, so it is important that it is
/// correct to avoid libffi reading or writing out-of-bounds.
///
/// In addition, the types `AsFfiType` is implemented for should be safe for sending across ffi
/// boundaries, typically `#[repr(C)]` or `#[repr(transparent)]` with a ffi-safe type. See
/// [The Rustonomicon][rustonomicon-reprc] for more details.
///
/// # Example
///
/// Implementing `AsFfiType` for a `#[repr(C)]` struct.
///
/// ```
/// use libffi::high::{AsFfiType, CodePtr, ForeignFunc};
/// use libffi::middle::Type;
///
/// // The struct must be `Copy` to implement `AsFfiType`.
/// #[repr(C)]
/// #[derive(Copy, Clone)]
/// struct FfiStruct {
///     number: i32,
///     tag: u8,
/// }
///
/// extern "C-unwind" fn accepts_ffi_struct(ffi_struct: FfiStruct) {
///     assert_eq!(ffi_struct.number, 11);
///     assert_eq!(ffi_struct.tag, 22);
/// }
///
/// unsafe impl AsFfiType for FfiStruct {
///     fn as_ffi_type() -> Type {
///         Type::structure(&[Type::I32, Type::U8])
///     }
/// }
///
/// let ffi_struct_instance = FfiStruct {
///     number: 11,
///     tag: 22,
/// };
///
/// let accepts_ffi_struct_fn =
///     ForeignFunc::<FfiStruct, ()>::new(CodePtr(accepts_ffi_struct as *mut _));
/// unsafe {
///     accepts_ffi_struct_fn.call(ffi_struct_instance);
/// }
/// ```
///
/// [rustonomicon-reprc]: https://doc.rust-lang.org/nomicon/other-reprs.html#reprc
pub unsafe trait AsFfiType: Copy {
    /// Return a `Type` representing the layout of `Self`.
    fn as_ffi_type() -> Type;
}

// SAFETY: `i8` has the same layout as libffi's sint8.
unsafe impl AsFfiType for i8 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::I8
    }
}

// SAFETY: `u8` has the same layout as libffi's uint8.
unsafe impl AsFfiType for u8 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::U8
    }
}

// SAFETY: `i16` has the same layout as libffi's sint16.
unsafe impl AsFfiType for i16 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::I16
    }
}

// SAFETY: `u16` has the same layout as libffi's uint16.
unsafe impl AsFfiType for u16 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::U16
    }
}

// SAFETY: `i32` has the same layout as libffi's sint32.
unsafe impl AsFfiType for i32 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::I32
    }
}

// SAFETY: `u32` has the same layout as libffi's uint32.
unsafe impl AsFfiType for u32 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::U32
    }
}

// SAFETY: `i64` has the same layout as libffi's sint64.
unsafe impl AsFfiType for i64 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::I64
    }
}

// SAFETY: `u64` has the same layout as libffi's uint64.
unsafe impl AsFfiType for u64 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::U64
    }
}

// SAFETY: `isize` is converted to an `i(16|32|64)` as needed based on `target_pointer_width`.
unsafe impl AsFfiType for isize {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::Isize
    }
}

// SAFETY: `usize` is converted to an `u(16|32|64)` as needed based on `target_pointer_width`.
unsafe impl AsFfiType for usize {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::Usize
    }
}

// SAFETY: `f32` has the same layout as libffi's float.
unsafe impl AsFfiType for f32 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::F32
    }
}

// SAFETY: `f64` has the same layout as libffi's double.
unsafe impl AsFfiType for f64 {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::F64
    }
}

// SAFETY: *const T denotes a pointer.
unsafe impl<T> AsFfiType for *const T {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::Pointer
    }
}

// SAFETY: *mut T denotes a pointer.
unsafe impl<T> AsFfiType for *mut T {
    #[inline]
    fn as_ffi_type() -> Type {
        Type::Pointer
    }
}

/// Private module used to create traits that cannot be named by other crates.
mod private {
    /// Supertrait used to prevent other crates from implementing [`FfiArgs`].
    pub trait FfiArgsSuper {}
    /// Supertrait used to prevent other crates from implementing [`FfiRet`].
    pub trait FfiRetSuper {}
}

/// A trait representing the types of the arguments to a ffi function. This trait cannot be
/// implemented manually, but is instead implemented for `()` (no arguments), a single
/// `T: AsFfiType`, or a tuple (of up to 16 types) with types that implement [`AsFfiType`].
///
/// # Safety
///
/// This tuple is used to create a [`Cif`], so its contents need accurately describe the number of
/// arguments and their memory layout.
pub unsafe trait FfiArgs<'arg>: private::FfiArgsSuper {
    /// The array of `Arg`s returned by [`FfiArgs::as_arg_array`]. This is `[Arg<'arg>; N]` where
    /// `N` is the number of arguments in the trait implementation.
    type ArgsType: AsRef<[Arg<'arg>]>;
    /// The array of `Type`s returned by [`FfiArgs::as_type_array`]. This is `[Type; N]` where
    /// `N` is the number of arguments in the trait implementation.
    type TypesType: AsRef<[Type]>;

    // If it ever gets stabilized, it would be nice to be able to have the trait with the following
    // signature: const SIZE: usize;
    // fn as_type_array() -> [Type; Self::SIZE];
    // fn as_arg_array() -> [Arg; Self::SIZE];

    /// Return a `Vec` with the [`Type`]s that will be passed as parameters when calling a
    /// [`crate::high::ForeignFunc`].
    fn as_type_array() -> Self::TypesType;

    /// Return a `Vec` with `Arg`s corresponding to the types implementing `FfiArgs`.
    fn as_arg_array(&'arg self) -> Self::ArgsType;

    /// Convert arguments incoming to a ffi closure to a tuple with the arguments. This function
    /// reads raw pointers and is therefore considered to be unsafe.
    ///
    /// # Safety
    /// Make sure that `ptr` points to an array of pointers to value that contains as many arguments
    /// as there are values in `Self`, and that the layout of each value is correctly defined.
    unsafe fn from_libffi_args(ptr: *const *const c_void) -> Self;
}

impl private::FfiArgsSuper for () {}
// SAFETY: `SIZE` is 0, no arguments.
unsafe impl<'arg> FfiArgs<'arg> for () {
    type ArgsType = [Arg<'arg>; 0];
    type TypesType = [Type; 0];

    #[inline]
    fn as_type_array() -> Self::TypesType {
        []
    }

    #[inline]
    fn as_arg_array(&'arg self) -> Self::ArgsType {
        []
    }

    #[inline]
    unsafe fn from_libffi_args(_ptr: *const *const c_void) -> Self {}
}

impl<T> private::FfiArgsSuper for T where T: AsFfiType {}

// SAFETY: This assumes all `AsFfiType` implementation are safe.
unsafe impl<'arg, T> FfiArgs<'arg> for T
where
    T: AsFfiType,
{
    type ArgsType = [Arg<'arg>; 1];
    type TypesType = [Type; 1];

    #[inline]
    fn as_type_array() -> Self::TypesType {
        [<T as AsFfiType>::as_ffi_type()]
    }

    #[inline]
    fn as_arg_array(&'arg self) -> Self::ArgsType {
        [Arg::borrowed(self)]
    }

    #[inline]
    unsafe fn from_libffi_args(ptr: *const *const c_void) -> Self {
        // SAFETY: `FfiArgs` should guarantee that `ptr` receives the correct amount of pointers to
        // values, and that all types are correctly defined.
        unsafe { (*ptr).cast::<Self>().read() }
    }
}

/// Macro to implement `FfiArgs` for a tuple (0: A, 1: B, 2: C, ...) of types.
macro_rules! implement_as_ffi_args_for_tuple {
    ($count:literal, $( $index:tt: $name:ident ),+ ) => {
        impl<$($name,)+> private::FfiArgsSuper for ($($name,)+) {}

        // SAFETY: It is assumed the types implement AsFfiType correctly. Tests verify that a
        // correct number of argument types is provided.
        unsafe impl<'arg, $($name,)+> FfiArgs<'arg> for ($($name,)+)
        where
            $($name: AsFfiType),+
        {
            type ArgsType = [Arg<'arg>; $count];
            type TypesType = [Type; $count];

            #[inline]
            fn as_type_array() -> Self::TypesType {
                [$(<$name as AsFfiType>::as_ffi_type()),+]
            }

            #[inline]
            fn as_arg_array(&'arg self) -> Self::ArgsType {
                [$(Arg::borrowed(&self.$index)),+]
            }

            #[inline]
            unsafe fn from_libffi_args(ptr: *const *const c_void) -> Self {
                // SAFETY: `FfiArgs` should guarantee that `ptr` receives the correct amount of
                // pointers to values, and that all types are correctly defined.
                unsafe {(
                    $(((*(ptr.add($index))).cast::<$name>()).read(),)+
                )}
            }
        }
    };
}

// Implement FffiArgs for tuples from 1 to 16 elements.
implement_as_ffi_args_for_tuple!(1, 0: A);
implement_as_ffi_args_for_tuple!(2, 0: A, 1: B);
implement_as_ffi_args_for_tuple!(3, 0: A, 1: B, 2: C);
implement_as_ffi_args_for_tuple!(4, 0: A, 1: B, 2: C, 3: D);
implement_as_ffi_args_for_tuple!(5, 0: A, 1: B, 2: C, 3: D, 4: E);
implement_as_ffi_args_for_tuple!(6, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F);
implement_as_ffi_args_for_tuple!(7, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G);
implement_as_ffi_args_for_tuple!(8, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H);
implement_as_ffi_args_for_tuple!(9, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I);
implement_as_ffi_args_for_tuple!(10, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J);
implement_as_ffi_args_for_tuple!(11, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K);
implement_as_ffi_args_for_tuple!(12, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K, 11: L);
implement_as_ffi_args_for_tuple!(13, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K, 11: L, 12: M);
implement_as_ffi_args_for_tuple!(14, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K, 11: L, 12: M, 13: N);
implement_as_ffi_args_for_tuple!(15, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K, 11: L, 12: M, 13: N, 14: O);
implement_as_ffi_args_for_tuple!(16, 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K, 11: L, 12: M, 13: N, 14: O, 15: P);

/// A trait representing the return type of a ffi function. This trait cannot be implemented
/// manually, but is instead implemented for `()` (no return value) or a single type
/// `T: AsFfiType`.
///
/// # Safety
///
/// This tuple is used to create a [`Cif`], so its contents need accurately describe the memory
/// layout of the return value.
pub unsafe trait FfiRet: private::FfiRetSuper {
    /// Returns either `None` for `void` functions, or `Some(type)` for a function returning a
    /// value.
    fn as_ffi_return_type() -> Option<Type>;
}

impl private::FfiRetSuper for () {}

// SAFETY: () signifies no return value.
unsafe impl FfiRet for () {
    #[inline]
    fn as_ffi_return_type() -> Option<Type> {
        None
    }
}

impl<T> private::FfiRetSuper for T where T: AsFfiType {}

// SAFETY: This assumes all `AsFfiType` implementation are safe.
unsafe impl<T> FfiRet for T
where
    T: AsFfiType,
{
    #[inline]
    fn as_ffi_return_type() -> Option<Type> {
        Some(<T as AsFfiType>::as_ffi_type())
    }
}

#[cfg(test)]
mod test {
    use core::ptr;

    use super::*;

    #[test]
    #[rustfmt::skip]
    fn verify_ffi_args_impl() {
        assert_eq!(<() as FfiArgs>::as_type_array().len(), 0);
        assert_eq!(<i8 as FfiArgs>::as_type_array(), [Type::I8]);
        assert_eq!(<(i8, u8) as FfiArgs>::as_type_array(), [Type::I8, Type::U8]);
        assert_eq!(<(i8, u8, i16) as FfiArgs>::as_type_array(), [Type::I8, Type::U8, Type::I16]);
        assert_eq!(
            <(i8, u8, i16, u16) as FfiArgs>::as_type_array(),
            [Type::I8, Type::U8, Type::I16, Type::U16]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32) as FfiArgs>::as_type_array(),
            [Type::I8, Type::U8, Type::I16, Type::U16, Type::I32]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32) as FfiArgs>::as_type_array(),
            [Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64) as FfiArgs>::as_type_array(),
            [Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64) as FfiArgs>::as_type_array(),
            [Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32
            ]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32, Type::F64
            ]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64, *const i8) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32, Type::F64,
                Type::Pointer
            ]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64, *const i8, *mut u8) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32, Type::F64,
                Type::Pointer, Type::Pointer
            ]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64, *const i8, *mut u8, u8) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32, Type::F64,
                Type::Pointer, Type::Pointer, Type::U8
            ]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64, *const i8, *mut u8, u8, u8) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32, Type::F64,
                Type::Pointer, Type::Pointer, Type::U8, Type::U8
            ]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64, *const i8, *mut u8, u8, u8, u8) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32, Type::F64,
                Type::Pointer, Type::Pointer, Type::U8, Type::U8, Type::U8
            ]
        );
        assert_eq!(
            <(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64, *const i8, *mut u8, u8, u8, u8, u8) as FfiArgs>::as_type_array(),
            [
                Type::I8, Type::U8, Type::I16, Type::U16, Type::I32, Type::U32, Type::I64, Type::U64, Type::F32, Type::F64,
                Type::Pointer, Type::Pointer, Type::U8, Type::U8, Type::U8, Type::U8
            ]
        );
    }

    #[test]
    fn verify_ffi_ret_impl() {
        assert_eq!(<() as FfiRet>::as_ffi_return_type(), None);
        assert_eq!(<i8 as FfiRet>::as_ffi_return_type(), Some(Type::I8));
        assert_eq!(<u8 as FfiRet>::as_ffi_return_type(), Some(Type::U8));
        assert_eq!(<i16 as FfiRet>::as_ffi_return_type(), Some(Type::I16));
        assert_eq!(<u16 as FfiRet>::as_ffi_return_type(), Some(Type::U16));
        assert_eq!(<i32 as FfiRet>::as_ffi_return_type(), Some(Type::I32));
        assert_eq!(<u32 as FfiRet>::as_ffi_return_type(), Some(Type::U32));
        assert_eq!(<i64 as FfiRet>::as_ffi_return_type(), Some(Type::I64));
        assert_eq!(<u64 as FfiRet>::as_ffi_return_type(), Some(Type::U64));
        assert_eq!(<f32 as FfiRet>::as_ffi_return_type(), Some(Type::F32));
        assert_eq!(<f64 as FfiRet>::as_ffi_return_type(), Some(Type::F64));
        assert_eq!(
            <*const u8 as FfiRet>::as_ffi_return_type(),
            Some(Type::Pointer)
        );
        assert_eq!(
            <*mut u8 as FfiRet>::as_ffi_return_type(),
            Some(Type::Pointer)
        );
    }

    macro_rules! verify_tuple_as_arg_array {
        (($($name:ident: $ty:ty),+ $(,)?)) => {
            {
                let tuple = ($($name),+ ,);
                let arg_vec = tuple.as_arg_array();
                // SAFETY: `arg_vec` items should only point to valid memory.
                unsafe {
                    verify_tuple_generate_asserts!(arg_vec, 0usize, ($($name: $ty),+));
                }
            }
        };
    }

    macro_rules! verify_tuple_generate_asserts {
        ($arg_vec:ident, $idx:expr, ($name:ident: $ty:ty $(,)?)) => {
            assert_eq!(*($arg_vec[$idx].as_ptr().cast::<$ty>()), $name);
        };

        ($arg_vec:ident, $idx:expr, ($name:ident: $ty:ty, $($restname:ident: $restty:ty),+ $(,)?)) => {
            assert_eq!(*($arg_vec[$idx].as_ptr().cast::<$ty>()), $name);
            verify_tuple_generate_asserts!($arg_vec, $idx+1, ($($restname: $restty),+));
        };
    }

    #[test]
    #[allow(
        clippy::float_cmp,
        reason = "Comparing floats that should be bitwise identical"
    )]
    fn verify_ffi_as_ptr_impl() {
        let nothing = ();
        assert_eq!(nothing.as_arg_array().len(), 0);

        let val_0: i8 = 0;
        let mut val_1: u8 = 1;
        let val_2: i16 = 2;
        let val_3: u16 = 2;
        let val_4: i32 = 3;
        let val_5: u32 = 4;
        let val_6: i64 = 5;
        let val_7: u64 = 6;
        let val_8: isize = 7;
        let val_9: usize = 8;
        let val_a: f32 = 9.;
        let val_b: f64 = 10.;
        let val_c: *const i8 = &raw const val_0;
        let val_d: *mut u8 = &raw mut val_1;
        let val_e: i8 = 13;
        let val_f: u8 = 14;

        let arg_vec = val_0.as_arg_array();
        // SAFETY: `arg_vec` items should only point to valid memory.
        unsafe {
            assert_eq!(*(arg_vec[0].as_ptr().cast::<i8>()), val_0);
        }

        verify_tuple_as_arg_array!((val_0: i8,));
        verify_tuple_as_arg_array!((val_0: i8, val_1: u8));
        verify_tuple_as_arg_array!((val_0: i8, val_1: u8, val_2: i16));
        verify_tuple_as_arg_array!((val_0: i8, val_1: u8, val_2: i16, val_3: u16));
        verify_tuple_as_arg_array!((val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize, val_9: usize
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize, val_9: usize, val_a: f32
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize, val_9: usize, val_a: f32, val_b: f64
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize, val_9: usize, val_a: f32, val_b: f64, val_c: *const i8
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize, val_9: usize, val_a: f32, val_b: f64, val_c: *const i8,
            val_d: *mut u8
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize, val_9: usize, val_a: f32, val_b: f64, val_c: *const i8,
            val_d: *mut u8, val_e: i8
        ));
        verify_tuple_as_arg_array!((
            val_0: i8, val_1: u8, val_2: i16, val_3: u16, val_4: i32, val_5: u32, val_6: i64,
            val_7: u64, val_8: isize, val_9: usize, val_a: f32, val_b: f64, val_c: *const i8,
            val_d: *mut u8, val_e: i8, val_f: u8
        ));
    }

    macro_rules! verify_from_libffi_args {
        ($orig_val: expr, ($($idx:tt: $ty:ty),+ $(,)?)) => {
            {
                let val: ($($ty,)+) = $orig_val;
                let val_ptrs = [$((&raw const val.$idx).cast::<c_void>()),+];
                // SAFETY: This should be all valid pointers. If not, it should be caught in miri
                // tests.
                let val_from_libffi_args = unsafe {
                    <($($ty,)+) as FfiArgs>::from_libffi_args(val_ptrs.as_ptr())
                };

                // `Debug` and `Eq` are only defined for tuples of up to 12 items, so we need to
                // compare each item individually.
                $(assert_eq!(val.$idx, val_from_libffi_args.$idx);)+
            }
        };
    }

    #[test]
    #[allow(
        clippy::float_cmp,
        reason = "Comparing floats that should be bitwise identical"
    )]
    fn verify_from_libffi_args_impl() {
        let mut ptr_target: i32 = 0;

        // SAFETY: This _SHOULD NOT_ dereference the pointer.
        unsafe {
            <() as FfiArgs>::from_libffi_args(ptr::null());
        }

        let val: i32 = 0x5555_5555;
        let val_ptr = (&raw const val).cast::<c_void>();
        // SAFETY: `val_ptr` is a valid pointer to an `i32`.
        let val_from_libffi_args =
            unsafe { <i32 as FfiArgs>::from_libffi_args(&raw const val_ptr) };
        assert_eq!(val, val_from_libffi_args);

        verify_from_libffi_args!((0x5555_5555,), (0: i32));
        verify_from_libffi_args!((0x5555_5555, 0xAAAA_AAAA), (0: i32, 1: u32));
        verify_from_libffi_args!((0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555), (0: i32, 1: u32, 2: i64));
        verify_from_libffi_args!(
            (0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA),
            (0: i32, 1: u32, 2: i64, 3: u64)
        );
        verify_from_libffi_args!(
            (0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567),
            (0: i32, 1: u32, 2: i64, 3: u64, 4: f32)
        );
        verify_from_libffi_args!(
            (0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210),
            (0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64)
        );
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555
            ),
            (0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16)
        );
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA
            ),
            (0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16)
        );
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55
            ),
            (0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8)
        );
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55, 0xAA
            ),
            (0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8, 9: u8)
        );
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55, 0xAA, &raw const ptr_target
            ),(
                0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8, 9: u8, 10: *const i32
        ));
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55, 0xAA, &raw const ptr_target, &raw mut ptr_target,
            ),(
                0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8, 9: u8, 10: *const i32,
                11: *mut i32
        ));
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55, 0xAA, &raw const ptr_target, &raw mut ptr_target, 0x5555_5555
            ),(
                0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8, 9: u8, 10: *const i32,
                11: *mut i32, 12: isize
        ));
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55, 0xAA, &raw const ptr_target, &raw mut ptr_target, 0x5555_5555, 0xAAAA_AAAA
            ),(
                0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8, 9: u8, 10: *const i32,
                11: *mut i32, 12: isize, 13: usize
        ));
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55, 0xAA, &raw const ptr_target, &raw mut ptr_target, 0x5555_5555, 0xAAAA_AAAA, 0x13,
            ),(
                0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8, 9: u8, 10: *const i32,
                11: *mut i32, 12: isize, 13: usize, 14: i8
        ));
        verify_from_libffi_args!(
            (
                0x5555_5555, 0xAAAA_AAAA, 0x5555_5555_5555_5555, 0xAAAA_AAAA_AAAA_AAAA, 1.234_567, 9.876_543_210,
                0x5555, 0xAAAA, 0x55, 0xAA, &raw const ptr_target, &raw mut ptr_target, 0x5555_5555, 0xAAAA_AAAA, 0x13, 0x37,
            ),(
                0: i32, 1: u32, 2: i64, 3: u64, 4: f32, 5: f64, 6: i16, 7: u16, 8: i8, 9: u8, 10: *const i32,
                11: *mut i32, 12: isize, 13: usize, 14: i8, 15: u8
        ));
    }
}
