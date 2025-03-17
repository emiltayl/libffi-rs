#![expect(clippy::doc_markdown, reason = "False positive")]
//! Representations of C types and structs.
//!
//! These are used to describe the types of the arguments and results of functions. When a
//! [CIF](super::Cif) is created, a sequence of argument types and a result type is provided, and
//! libffi uses this to figure out how to set up a call to a function with those types.
//!
//! *[CIF]: Call InterFace
use core::{mem, slice};

extern crate alloc;
#[cfg(not(test))]
use alloc::boxed::Box;

#[cfg(miri)]
use miri::{
    double, float, pointer, sint8, sint16, sint32, sint64, uint8, uint16, uint32, uint64, void,
};

#[cfg(all(feature = "complex", not(target_env = "msvc")))]
use crate::low::types::complex_double;
#[cfg(all(feature = "complex", not(target_env = "msvc")))]
use crate::low::types::complex_float;
#[cfg(all(
    feature = "complex",
    not(any(target_env = "msvc", target_arch = "arm", target_arch = "aarch64"))
))]
use crate::low::types::complex_longdouble;
#[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
use crate::low::types::longdouble;
#[cfg(not(miri))]
use crate::low::types::{
    double, float, pointer, sint8, sint16, sint32, sint64, uint8, uint16, uint32, uint64, void,
};
use crate::low::{ffi_type, type_tag};

/// This represents a C type that libffi can pass to, and return from functions.
#[derive(Clone, Debug)]
pub enum Type {
    /// Represents a `i8`
    I8,
    /// Represents a `u8`
    U8,
    /// Represents a `i16`
    I16,
    /// Represents a `u16`
    U16,
    /// Represents a `i32`
    I32,
    /// Represents a `u32`
    U32,
    /// Represents a `i64`
    I64,
    /// Represents a `u64`
    U64,
    /// Represents a `isize`
    Isize,
    /// Represents a `usize`
    Usize,
    /// Represents a `f32`
    F32,
    /// Represents a `f64`
    F64,
    /// Represents a pointer
    Pointer,
    /// Represents a `long double`. Not available for ARM.
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    LongDouble,
    /// Returns the C `_Complex float` type.
    ///
    /// This item is enabled by `#[cfg(feature = "complex")]`. It is not available when building for
    /// msvc.
    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    ComplexFloat,
    /// Returns the C `_Complex double` type.
    ///
    /// This item is enabled by `#[cfg(feature = "complex")]`. It is not available when building for
    /// msvc.
    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    ComplexDouble,
    /// Returns the C `_Complex double` type.
    ///
    /// This item is enabled by `#[cfg(feature = "complex")]`. It is not available when building for
    /// msvc or for ARM.
    #[cfg(all(
        feature = "complex",
        not(any(target_env = "msvc", target_arch = "arm", target_arch = "aarch64"))
    ))]
    ComplexLongDouble,
    /// Represents a `repr(C)` structure.
    Structure(Box<[Type]>),
}

const fn signed_data_to_scalar_type<T: Sized>() -> Type {
    match size_of::<T>() {
        1 => Type::I8,
        2 => Type::I16,
        4 => Type::I32,
        8 => Type::I64,
        _ => panic!("Unsupported int size"),
    }
}

const fn unsigned_data_to_scalar_type<T: Sized>() -> Type {
    match size_of::<T>() {
        1 => Type::U8,
        2 => Type::U16,
        4 => Type::U32,
        8 => Type::U64,
        _ => panic!("Unsupported int size"),
    }
}

impl Type {
    /// Returns the signed 8-bit numeric type.
    #[deprecated = "Refer to `Type::I8` directly. This function will be removed in a future version."]
    pub const fn i8() -> Self {
        Self::I8
    }

    /// Returns the unsigned 8-bit numeric type.
    #[deprecated = "Refer to `Type::U8` directly. This function will be removed in a future version."]
    pub const fn u8() -> Self {
        Self::U8
    }

    /// Returns the signed 16-bit numeric type.
    #[deprecated = "Refer to `Type::I16` directly. This function will be removed in a future version."]
    pub const fn i16() -> Self {
        Self::I16
    }

    /// Returns the unsigned 16-bit numeric type.
    #[deprecated = "Refer to `Type::U16` directly. This function will be removed in a future version."]
    pub const fn u16() -> Self {
        Self::U16
    }

    /// Returns the signed 32-bit numeric type.
    #[deprecated = "Refer to `Type::I32` directly. This function will be removed in a future version."]
    pub const fn i32() -> Self {
        Self::I32
    }

    /// Returns the unsigned 32-bit numeric type.
    #[deprecated = "Refer to `Type::U32` directly. This function will be removed in a future version."]
    pub const fn u32() -> Self {
        Self::U32
    }
    /// Returns the signed 64-bit numeric type.
    #[deprecated = "Refer to `Type::I64` directly. This function will be removed in a future version."]
    pub const fn i64() -> Self {
        Self::I64
    }

    /// Returns the unsigned 64-bit numeric type.
    #[deprecated = "Refer to `Type::U64` directly. This function will be removed in a future version."]
    pub const fn u64() -> Self {
        Self::U64
    }

    /// Returns the C equivalent of Rust `isize` (`i64`).
    #[deprecated = "Refer to `Type::Isize` directly. This function will be removed in a future version."]
    pub const fn isize() -> Self {
        Self::Isize
    }

    /// Returns the C equivalent of Rust `usize` (`u64`).
    #[deprecated = "Refer to `Type::Usize` directly. This function will be removed in a future version."]
    pub const fn usize() -> Self {
        Self::Usize
    }

    /// Returns the C `signed char` type.
    pub const fn c_schar() -> Self {
        signed_data_to_scalar_type::<core::ffi::c_schar>()
    }

    /// Returns the C `unsigned char` type.
    pub const fn c_uchar() -> Self {
        unsigned_data_to_scalar_type::<core::ffi::c_uchar>()
    }

    /// Returns the C `short` type.
    pub const fn c_short() -> Self {
        signed_data_to_scalar_type::<core::ffi::c_short>()
    }

    /// Returns the C `unsigned short` type.
    pub const fn c_ushort() -> Self {
        unsigned_data_to_scalar_type::<core::ffi::c_ushort>()
    }

    /// Returns the C `int` type.
    pub const fn c_int() -> Self {
        signed_data_to_scalar_type::<core::ffi::c_int>()
    }

    /// Returns the C `unsigned int` type.
    pub const fn c_uint() -> Self {
        unsigned_data_to_scalar_type::<core::ffi::c_uint>()
    }

    /// Returns the C `long` type.
    pub const fn c_long() -> Self {
        signed_data_to_scalar_type::<core::ffi::c_long>()
    }

    /// Returns the C `unsigned long` type.
    pub const fn c_ulong() -> Self {
        unsigned_data_to_scalar_type::<core::ffi::c_ulong>()
    }

    /// Returns the C `longlong` type.
    pub const fn c_longlong() -> Self {
        signed_data_to_scalar_type::<core::ffi::c_longlong>()
    }

    /// Returns the C `unsigned longlong` type.
    pub const fn c_ulonglong() -> Self {
        unsigned_data_to_scalar_type::<core::ffi::c_ulonglong>()
    }

    /// Returns the C `float` (32-bit floating point) type.
    #[deprecated = "Refer to `Type::F32` directly. This function will be removed in a future version."]
    pub const fn f32() -> Self {
        Self::F32
    }

    /// Returns the C `double` (64-bit floating point) type.
    #[deprecated = "Refer to `Type::F64` directly. This function will be removed in a future version."]
    pub const fn f64() -> Self {
        Self::F64
    }

    /// Returns the C `void*` type, for passing any kind of pointer.
    #[deprecated = "Refer to `Type::Pointer` directly. This function will be removed in a future version."]
    pub const fn pointer() -> Self {
        Self::Pointer
    }

    /// Returns the C `long double` (extended-precision floating point) type.
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    #[deprecated = "Refer to `Type::LongDouble` directly. This function will be removed in a future version."]
    pub const fn longdouble() -> Self {
        Self::LongDouble
    }

    /// Returns the C `_Complex float` type.
    ///
    /// This item is enabled by `#[cfg(feature = "complex")]`. It is not available when building for
    /// msvc.
    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    #[deprecated = "Refer to `Type::ComplexFloat` directly. This function will be removed in a future version."]
    pub const fn c32() -> Self {
        Self::ComplexFloat
    }

    /// Returns the C `_Complex double` type.
    ///
    /// This item is enabled by `#[cfg(feature = "complex")]`. It is not available when building for
    /// msvc.
    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    #[deprecated = "Refer to `Type::ComplexDouble` directly. This function will be removed in a future version."]
    pub const fn c64() -> Self {
        Self::ComplexDouble
    }

    /// Returns the C `_Complex long double` type.
    ///
    /// This item is enabled by `#[cfg(feature = "complex")]`. It is not available when building for
    /// msvc or the arm arch.
    #[cfg(all(
        feature = "complex",
        not(any(target_env = "msvc", target_arch = "arm", target_arch = "aarch64"))
    ))]
    #[deprecated = "Refer to `Type::ComplexLongDouble` directly. This function will be removed in a future version."]
    pub const fn complex_longdouble() -> Self {
        Self::ComplexLongDouble
    }

    /// Constructs a structure type whose fields have the given types.
    pub fn structure(fields: &[Type]) -> Self {
        Self::Structure(fields.iter().cloned().collect())
    }

    /// Used by [`crate::middle::Cif`] to get a pointer to [`ffi_type`] that can be passed
    /// directly to libffi.
    pub(crate) fn as_raw(&self) -> RawType {
        match self {
            Type::I8 => RawType(&raw mut sint8),
            Type::U8 => RawType(&raw mut uint8),
            Type::I16 => RawType(&raw mut sint16),
            Type::U16 => RawType(&raw mut uint16),
            Type::I32 => RawType(&raw mut sint32),
            Type::U32 => RawType(&raw mut uint32),
            Type::I64 => RawType(&raw mut sint64),
            Type::U64 => RawType(&raw mut uint64),
            #[cfg(target_pointer_width = "16")]
            Type::Isize => RawType(&raw mut sint16),
            #[cfg(target_pointer_width = "16")]
            Type::Usize => RawType(&raw mut uint16),
            #[cfg(target_pointer_width = "32")]
            Type::Isize => RawType(&raw mut sint32),
            #[cfg(target_pointer_width = "32")]
            Type::Usize => RawType(&raw mut uint32),
            #[cfg(target_pointer_width = "64")]
            Type::Isize => RawType(&raw mut sint64),
            #[cfg(target_pointer_width = "64")]
            Type::Usize => RawType(&raw mut uint64),
            Type::F32 => RawType(&raw mut float),
            Type::F64 => RawType(&raw mut double),
            Type::Pointer => RawType(&raw mut pointer),
            #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
            Type::LongDouble => RawType(&raw mut longdouble),
            #[cfg(all(feature = "complex", not(target_env = "msvc")))]
            Type::ComplexFloat => RawType(&raw mut complex_float),
            #[cfg(all(feature = "complex", not(target_env = "msvc")))]
            Type::ComplexDouble => RawType(&raw mut complex_double),
            #[cfg(all(
                feature = "complex",
                not(any(target_env = "msvc", target_arch = "arm", target_arch = "aarch64"))
            ))]
            Type::ComplexLongDouble => RawType(&raw mut complex_longdouble),
            Type::Structure(items) => Self::struct_as_raw(items),
        }
    }

    /// Allocate memory for `ffi_type` as needed. Be sure to run tests with miri whenever
    /// changing this code to avoid potential problems when playing with raw pointers.
    fn struct_as_raw(items: &[Type]) -> RawType {
        // We need to allocate memory for the `elements` field in `ffi_type` to ensure that
        // we get pointers that will not change for libffi to read the type definitions.
        let elements_box = items
            .iter()
            // Recursively convert children to `RawType`.
            .map(Type::as_raw)
            // According to https://www.chiark.greenend.org.uk/doc/libffi-dev/html/Structures.html
            // the last element in the `elements` array should be NULL to signal that there are no
            // more elements.
            .chain(core::iter::once(RawType(core::ptr::null_mut())))
            .collect::<Box<[RawType]>>();

        // `Box::into_raw` takes ownership of the `Box` and returns a pointer to its contents to
        // ensure it will not be deallocated until a new `Box` is constructed using `Box::from_raw`
        // and that `Box` is dropped.
        //
        // The pointer is then cast from `*mut [RawType]` to `*mut *mut ffi_type`. This should
        // be okay since `RawType` is `#[repr(transparent)]` with a `*mut ffi_type`.
        let elements_ptr = Box::into_raw(elements_box).cast::<*mut ffi_type>();

        // According to https://www.chiark.greenend.org.uk/doc/libffi-dev/html/Structures.html
        // `size` and `alignment` should be initialized to 0.
        let ffi_type = Box::new(ffi_type {
            size: 0,
            alignment: 0,
            type_: type_tag::STRUCT,
            elements: elements_ptr,
        });

        // Finally, we convert `ffi_type` to a raw pointer to prevent deallocation until the
        // `RawType` is dropped.
        RawType(Box::into_raw(ffi_type))
    }
}

/// Container for the pointer to a type that will be passed to `prep_cif`.
#[repr(transparent)]
pub(crate) struct RawType(pub(crate) *mut ffi_type);

impl core::fmt::Debug for RawType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.0.is_null() {
            write!(f, "RawType(NULL)")
        } else {
            // SAFETY: The pointer is not 0, so it _should_ only point to a `ffi_type` allocated by
            // libffi or created from `Type`.
            unsafe { (*self.0).fmt(f) }
        }
    }
}

impl RawType {
    /// Used to create a [`RawType`] for void.
    pub(super) const VOID: Self = RawType(&raw mut void);
}

/// `RawType` requires custom clone logic due to all the "forgotten" `Box`es. A lot of pointer magic
/// is happening here, so be sure to test with miri whenever making changes to this code.
impl Clone for RawType {
    #[expect(
        clippy::undocumented_unsafe_blocks,
        reason = "It is assumed that RawType only operates on well-formed memory allocated by `Type::as_raw`"
    )]
    fn clone(&self) -> Self {
        if self.0.is_null() {
            // RawType(NULL).clone() == RawType(NULL)
            return Self(core::ptr::null_mut());
        }

        let this_type_tag = unsafe { (*self.0).type_ };
        if this_type_tag != type_tag::STRUCT {
            // For built-in types we can simply return a new RawType pointing at that type since
            // we will not deallocate it when dropped.
            return Self(self.0);
        }

        // The size is initialized to 1 to account for the extra sentinel NULL at the end of the
        // array, which is not counted in the following loop.
        let mut n_elements: usize = 1;
        let mut elements_array_ptr = unsafe { (*(self.0)).elements };

        unsafe {
            while !(*elements_array_ptr).is_null() {
                n_elements += 1;
                elements_array_ptr = elements_array_ptr.add(1);
            }
        }

        // Reconstruct the `Box<[RawType]>` so the `RawType`s can be cloned recursively and then
        // forget the `Box<[RawType]>` to avoid deallocating it.
        let elements_boxed_slice = unsafe {
            Box::<[RawType]>::from_raw(slice::from_raw_parts_mut(
                // Casting from `*mut *mut ffi_type` to `*mut RawType`.
                (*(self.0)).elements.cast::<RawType>(),
                n_elements,
            ))
        };

        let cloned_elements_boxed_slice = elements_boxed_slice.clone();
        mem::forget(elements_boxed_slice);

        // Reconstruct the `Box<RawType>` so it can be cloned, and then forget it to avoid
        // deallocating it.
        let original_box = unsafe { Box::from_raw(self.0) };
        let mut cloned_box = original_box.clone();
        mem::forget(original_box);

        cloned_box.elements = Box::into_raw(cloned_elements_boxed_slice).cast::<*mut ffi_type>();

        RawType(Box::into_raw(cloned_box))
    }
}

/// This is used to ensure that all memory allocated for `RawType` is freed. A lot of pointer magic
/// is happening here, so be sure to test with miri whenever making changes to this code.
impl Drop for RawType {
    #[expect(
        clippy::undocumented_unsafe_blocks,
        reason = "It is assumed that RawType only operates on well-formed memory allocated by `Type::as_raw`"
    )]
    fn drop(&mut self) {
        if self.0.is_null() {
            // If self is referring to the last item in a `elements` array, we do not need to do
            // anything.
            return;
        }

        let this_type_tag = unsafe { (*self.0).type_ };
        if this_type_tag != type_tag::STRUCT {
            // If self is not a struct, this crate has not allocated any memory for the `RawType`
            // and we do not need to do anything.
            return;
        }

        // The size is initialized to 1 to account for the extra sentinel NULL at the end of the
        // array, which is not counted in the following loop.
        let mut n_elements: usize = 1;
        let mut elements_array_ptr = unsafe { (*(self.0)).elements };

        unsafe {
            while !(*elements_array_ptr).is_null() {
                n_elements += 1;
                elements_array_ptr = elements_array_ptr.add(1);
            }
        }

        // Reconstruct the `Box<[RawType]>` so the `RawType`s can be dropped recursively and then
        // drop the `Box<[RawType]>`.
        let elements_boxed_slice = unsafe {
            Box::<[RawType]>::from_raw(slice::from_raw_parts_mut(
                // Casting from `*mut *mut ffi_type` to `*mut RawType`.
                (*(self.0)).elements.cast::<RawType>(),
                n_elements,
            ))
        };
        drop(elements_boxed_slice);

        // Finally we can drop the `Box` for this `ffi_type`.
        unsafe { drop(Box::from_raw(self.0)) }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::raw::{
        FFI_TYPE_SINT8, FFI_TYPE_SINT16, FFI_TYPE_SINT32, FFI_TYPE_UINT8, FFI_TYPE_UINT16,
        FFI_TYPE_UINT32,
    };

    #[test]
    fn verify_raw_type_layout() {
        let ffi_struct = Type::structure(&[
            // First struct, containing a struct, i8, and u8
            Type::structure(&[
                // Second struct, containing a i16, struct, and u16
                Type::I16,
                Type::structure(&[
                    // Third struct, containing a i32, u32 and struct
                    Type::I32,
                    Type::U32,
                    Type::structure(&[
                        // Fourth struct, only a struct
                        Type::structure(&[
                            // Fifth and final struct, no members
                        ]),
                    ]),
                ]),
                Type::U16,
            ]),
            Type::I8,
            Type::U8,
        ]);

        let raw = ffi_struct.as_raw();
        verify_struct_layout(&raw);

        let clone1 = raw.clone();
        verify_struct_layout(&raw);
        verify_struct_layout(&clone1);

        let clone2 = raw.clone();
        verify_struct_layout(&raw);
        verify_struct_layout(&clone1);
        verify_struct_layout(&clone2);

        let clone3 = clone1.clone();
        verify_struct_layout(&raw);
        verify_struct_layout(&clone1);
        verify_struct_layout(&clone2);
        verify_struct_layout(&clone3);

        drop(clone2);
        verify_struct_layout(&raw);
        verify_struct_layout(&clone1);
        verify_struct_layout(&clone3);

        drop(raw);
        verify_struct_layout(&clone1);
        verify_struct_layout(&clone3);
    }

    #[expect(
        clippy::undocumented_unsafe_blocks,
        reason = "This test is only operating on assumed well-formed memory created in this module."
    )]
    fn verify_struct_layout(raw_type: &RawType) {
        // First struct: struct, i8, u8
        let struct_1 = unsafe { &*raw_type.0 };
        assert_eq!(struct_1.size, 0);
        assert_eq!(struct_1.alignment, 0);
        assert_eq!(struct_1.type_, type_tag::STRUCT);

        assert_eq!(unsafe { (**struct_1.elements).type_ }, type_tag::STRUCT);
        assert_eq!(
            u32::from(unsafe { (**struct_1.elements.add(1)).type_ }),
            FFI_TYPE_SINT8
        );
        assert_eq!(
            u32::from(unsafe { (**struct_1.elements.add(2)).type_ }),
            FFI_TYPE_UINT8
        );
        assert!(unsafe { (*struct_1.elements.add(3)).is_null() });

        // Second struct: i16, struct, u16
        let struct_2 = unsafe { &**struct_1.elements };
        assert_eq!(struct_2.size, 0);
        assert_eq!(struct_2.alignment, 0);
        assert_eq!(struct_2.type_, type_tag::STRUCT);

        assert_eq!(
            u32::from(unsafe { (**struct_2.elements).type_ }),
            FFI_TYPE_SINT16
        );
        assert_eq!(
            unsafe { (**struct_2.elements.add(1)).type_ },
            type_tag::STRUCT
        );
        assert_eq!(
            u32::from(unsafe { (**struct_2.elements.add(2)).type_ }),
            FFI_TYPE_UINT16
        );
        assert!(unsafe { (*struct_2.elements.add(3)).is_null() });

        // Third struct: i8, u8, struct
        let struct_3 = unsafe { &**(struct_2.elements.add(1)) };
        assert_eq!(struct_3.size, 0);
        assert_eq!(struct_3.alignment, 0);
        assert_eq!(struct_3.type_, type_tag::STRUCT);

        assert_eq!(
            u32::from(unsafe { (**struct_3.elements).type_ }),
            FFI_TYPE_SINT32
        );
        assert_eq!(
            u32::from(unsafe { (**struct_3.elements.add(1)).type_ }),
            FFI_TYPE_UINT32
        );
        assert_eq!(
            unsafe { (**struct_3.elements.add(2)).type_ },
            type_tag::STRUCT
        );
        assert!(unsafe { (*struct_3.elements.add(3)).is_null() });

        // Fourth struct: struct
        let struct_4 = unsafe { &**(struct_3.elements.add(2)) };
        assert_eq!(struct_4.size, 0);
        assert_eq!(struct_4.alignment, 0);
        assert_eq!(struct_4.type_, type_tag::STRUCT);

        assert_eq!(unsafe { (**struct_4.elements).type_ }, type_tag::STRUCT);
        assert!(unsafe { (*struct_4.elements.add(1)).is_null() });

        // Fifth and final struct: nothing
        let struct_5 = unsafe { &**(struct_4.elements) };
        assert_eq!(struct_5.size, 0);
        assert_eq!(struct_5.alignment, 0);
        assert_eq!(struct_5.type_, type_tag::STRUCT);

        assert!(unsafe { (*struct_5.elements).is_null() });
    }
}

#[cfg(miri)]
#[expect(
    non_upper_case_globals,
    reason = "Copying names from `crate::low::types`"
)]
#[expect(
    clippy::cast_possible_truncation,
    reason = "libffi-sys-rs currently exposes type tags as u32, however, all fit in a u16"
)]
mod miri {
    use crate::{
        low::ffi_type,
        raw::{
            FFI_TYPE_DOUBLE, FFI_TYPE_FLOAT, FFI_TYPE_POINTER, FFI_TYPE_SINT8, FFI_TYPE_SINT16,
            FFI_TYPE_SINT32, FFI_TYPE_SINT64, FFI_TYPE_UINT8, FFI_TYPE_UINT16, FFI_TYPE_UINT32,
            FFI_TYPE_UINT64, FFI_TYPE_VOID,
        },
    };

    // Redefining static muts so this module can be tested with miri
    pub(super) static mut sint8: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_SINT8 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut uint8: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_UINT8 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut sint16: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_SINT16 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut uint16: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_UINT16 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut sint32: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_SINT32 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut uint32: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_UINT32 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut sint64: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_SINT64 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut uint64: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_UINT64 as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut pointer: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_POINTER as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut float: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_FLOAT as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut double: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_DOUBLE as u16,
        elements: core::ptr::null_mut(),
    };

    pub(super) static mut void: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FFI_TYPE_VOID as u16,
        elements: core::ptr::null_mut(),
    };
}
