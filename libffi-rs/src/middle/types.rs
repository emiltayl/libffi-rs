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
mod imports {
    #[cfg(all(
        feature = "complex",
        not(any(target_env = "msvc", target_arch = "arm", target_arch = "aarch64"))
    ))]
    pub use super::miri::complex_longdouble;
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    pub use super::miri::longdouble;
    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    pub use super::miri::{complex_double, complex_float};
    pub use super::miri::{
        double, float, pointer, sint8, sint16, sint32, sint64, uint8, uint16, uint32, uint64, void,
    };
}

#[cfg(not(miri))]
mod imports {
    #[cfg(all(
        feature = "complex",
        not(any(target_env = "msvc", target_arch = "arm", target_arch = "aarch64"))
    ))]
    pub use crate::low::types::complex_longdouble;
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    pub use crate::low::types::longdouble;
    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    pub use crate::low::types::{complex_double, complex_float};
    pub use crate::low::types::{
        double, float, pointer, sint8, sint16, sint32, sint64, uint8, uint16, uint32, uint64, void,
    };
}

#[allow(
    clippy::wildcard_imports,
    reason = "Hack to organize imports in normal and custom miri implementations"
)]
use imports::*;

use crate::low::{ffi_type, type_tag};

/// This represents a C type that libffi can pass to, and return from functions.
#[derive(Clone, Debug, PartialEq, Eq)]
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
    #[inline]
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

            // LongDoubles are allocated in its own block to prevent potential race conditions.
            #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
            Type::LongDouble => {
                // SAFETY: When using the `middle` module, `longdouble` will never be overwritten.
                // Care needs to be taken if `low` and `middle` modules are mixed on PowerPC.
                // TODO document above in `low`
                let type_box = unsafe {
                    // `ffi_type` is `copy`.
                    Box::new(longdouble)
                };

                RawType(Box::into_raw(type_box))
            }

            #[cfg(all(feature = "complex", not(target_env = "msvc")))]
            Type::ComplexFloat => {
                // SAFETY: `complex_float` should never change according to libffi.
                let type_box = unsafe {
                    // `ffi_type` is `copy`.
                    Box::new(complex_float)
                };

                RawType(Box::into_raw(type_box))
            }

            #[cfg(all(feature = "complex", not(target_env = "msvc")))]
            Type::ComplexDouble => {
                // SAFETY: `complex_double` should never change according to libffi.
                let type_box = unsafe {
                    // `ffi_type` is `copy`.
                    Box::new(complex_double)
                };

                RawType(Box::into_raw(type_box))
            }

            #[cfg(all(
                feature = "complex",
                not(any(target_env = "msvc", target_arch = "arm", target_arch = "aarch64"))
            ))]
            Type::ComplexLongDouble => {
                // SAFETY: When using the `middle` module, `complex_longdouble` will never be
                // overwritten. Care needs to be taken if `low` and `middle` modules are mixed on
                // PowerPC.
                // TODO document above in `low`
                let type_box = unsafe {
                    // `ffi_type` is `copy`.
                    Box::new(complex_longdouble)
                };

                RawType(Box::into_raw(type_box))
            }

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

impl RawType {
    /// Used to create a [`RawType`] for void.
    pub(super) const VOID: Self = RawType(&raw mut void);
}

/// `RawType` requires custom clone logic due to all the "forgotten" `Box`es. A lot of pointer magic
/// is happening here, so be sure to test with miri whenever making changes to this code.
impl Clone for RawType {
    // TODO Remove expect and document unsafe blocks
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

        match this_type_tag {
            // for `long double` and complex type we clone the objects to avoid potential issues
            // with different cifs overwriting `static mut`s even though it is not needed. it is
            // only documented to be needed on powerpc when using `long double` with different
            // abis.
            //
            // see https://www.chiark.greenend.org.uk/doc/libffi-dev/html/thread-safety.html for
            // more details on thread safety.
            type_tag::LONGDOUBLE | type_tag::COMPLEX => {
                let cif_clone = unsafe { Box::new(*self.0) };

                Self(Box::into_raw(cif_clone))
            }

            type_tag::STRUCT => {
                // The size is initialized to 1 to account for the extra sentinel NULL at the end of
                // the array, which is not counted in the following loop.
                let mut n_elements: usize = 1;
                let mut elements_array_ptr = unsafe { (*(self.0)).elements };

                unsafe {
                    while !(*elements_array_ptr).is_null() {
                        n_elements += 1;
                        elements_array_ptr = elements_array_ptr.add(1);
                    }
                }

                // Reconstruct the `Box<[RawType]>` so the `RawType`s can be cloned recursively and
                // then forget the `Box<[RawType]>` to avoid deallocating it.
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

                cloned_box.elements =
                    Box::into_raw(cloned_elements_boxed_slice).cast::<*mut ffi_type>();

                RawType(Box::into_raw(cloned_box))
            }

            // For the rest of the types, we can just send a pointer to the static ffi_types
            // created by libffi.
            _ => Self(self.0),
        }
    }
}

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

        match this_type_tag {
            // `long double` and complex types are allocated by `RawType` to avoid potential race
            // conditions.
            type_tag::LONGDOUBLE | type_tag::COMPLEX => unsafe { drop(Box::from_raw(self.0)) },

            // Structs are also allocated by `RawType` and need to be de-allocated manually.
            type_tag::STRUCT => {
                // The size is initialized to 1 to account for the extra sentinel NULL at the end of
                // the array, which is not counted in the following loop.
                let mut n_elements: usize = 1;
                let mut elements_array_ptr = unsafe { (*(self.0)).elements };

                unsafe {
                    while !(*elements_array_ptr).is_null() {
                        n_elements += 1;
                        elements_array_ptr = elements_array_ptr.add(1);
                    }
                }

                // Reconstruct the `Box<[RawType]>` so the `RawType`s can be dropped recursively and
                // then drop the `Box<[RawType]>`.
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

            // The remaining types do not need to be de-allocated.
            _ => (),
        }
    }
}

// SAFETY: It is safe to send a `RawType` to another thread, after it has been created `RawType` is
// not modified until it is dropped.
unsafe impl Send for RawType {}
// SAFETY: It is safe to send a `&RawType` to another thread, after it has been created `RawType` is
// not modified until it is dropped.
unsafe impl Sync for RawType {}

#[cfg(test)]
mod test {
    use super::*;
    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    use crate::low::type_tag::COMPLEX;
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    use crate::low::type_tag::LONGDOUBLE;
    use crate::low::type_tag::{SINT8, SINT16, SINT32, STRUCT, UINT8, UINT16, UINT32};

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
        assert_eq!(struct_1.type_, STRUCT);

        assert_eq!(unsafe { (**struct_1.elements).type_ }, STRUCT);
        assert_eq!(unsafe { (**struct_1.elements.add(1)).type_ }, SINT8);
        assert_eq!(unsafe { (**struct_1.elements.add(2)).type_ }, UINT8);
        assert!(unsafe { (*struct_1.elements.add(3)).is_null() });

        // Second struct: i16, struct, u16
        let struct_2 = unsafe { &**struct_1.elements };
        assert_eq!(struct_2.size, 0);
        assert_eq!(struct_2.alignment, 0);
        assert_eq!(struct_2.type_, STRUCT);

        assert_eq!(unsafe { (**struct_2.elements).type_ }, SINT16);
        assert_eq!(unsafe { (**struct_2.elements.add(1)).type_ }, STRUCT);
        assert_eq!(unsafe { (**struct_2.elements.add(2)).type_ }, UINT16);
        assert!(unsafe { (*struct_2.elements.add(3)).is_null() });

        // Third struct: i8, u8, struct
        let struct_3 = unsafe { &**(struct_2.elements.add(1)) };
        assert_eq!(struct_3.size, 0);
        assert_eq!(struct_3.alignment, 0);
        assert_eq!(struct_3.type_, STRUCT);

        assert_eq!(unsafe { (**struct_3.elements).type_ }, SINT32);
        assert_eq!(unsafe { (**struct_3.elements.add(1)).type_ }, UINT32);
        assert_eq!(unsafe { (**struct_3.elements.add(2)).type_ }, STRUCT);
        assert!(unsafe { (*struct_3.elements.add(3)).is_null() });

        // Fourth struct: struct
        let struct_4 = unsafe { &**(struct_3.elements.add(2)) };
        assert_eq!(struct_4.size, 0);
        assert_eq!(struct_4.alignment, 0);
        assert_eq!(struct_4.type_, STRUCT);

        assert_eq!(unsafe { (**struct_4.elements).type_ }, STRUCT);
        assert!(unsafe { (*struct_4.elements.add(1)).is_null() });

        // Fifth and final struct: nothing
        let struct_5 = unsafe { &**(struct_4.elements) };
        assert_eq!(struct_5.size, 0);
        assert_eq!(struct_5.alignment, 0);
        assert_eq!(struct_5.type_, STRUCT);

        assert!(unsafe { (*struct_5.elements).is_null() });
    }

    /// Verify that [`RawType`]'s `Debug` impl does not misbehave.
    #[test]
    fn verify_rawtype_debug_behavior() {
        let null_rawtype = RawType(core::ptr::null_mut());
        let _ = format!("{null_rawtype:?}");

        let struct_rawtype = Type::structure(&[
            Type::U16,
            Type::F32,
            Type::structure(&[Type::I32, Type::structure(&[])]),
            Type::Pointer,
        ])
        .as_raw();

        let _ = format!("{struct_rawtype:?}");
    }

    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    #[test]
    fn verify_longdouble_allocations() {
        let raw_type = Type::LongDouble.as_raw();
        let raw_type_clone = raw_type.clone().clone();
        drop(raw_type);

        // SAFETY: raw_type_clone should be a properly initialized `RawType`.
        unsafe {
            assert_eq!((*raw_type_clone.0).type_, LONGDOUBLE);
        }

        let raw_long_double_struct =
            Type::structure(&[Type::LongDouble, Type::LongDouble]).as_raw();
        let raw_long_double_struct_clone = raw_long_double_struct.clone().clone();
        drop(raw_long_double_struct);

        // SAFETY: raw_long_double_struct should be a properly initialized `RawType` with 2
        // elements.
        unsafe {
            let elements_ptr = (*raw_long_double_struct_clone.0).elements;
            let element_1 = *elements_ptr;
            assert_eq!((*element_1).type_, LONGDOUBLE);
            let element_2 = *elements_ptr.add(1);
            assert_eq!((*element_2).type_, LONGDOUBLE);
        }
    }

    #[cfg(all(feature = "complex", not(target_env = "msvc")))]
    #[test]
    #[expect(
        clippy::deref_addrof,
        reason = "Workaround for accessing static muts that are not actually changing."
    )]
    fn verify_complex_allocations() {
        let raw_complex_float = Type::ComplexFloat.as_raw();
        let raw_complex_float_clone = raw_complex_float.clone().clone();
        drop(raw_complex_float);

        // SAFETY: raw_complex_float_clone should be a properly initialized `RawType`.
        unsafe {
            assert_eq!((*raw_complex_float_clone.0).type_, COMPLEX);
            assert_eq!(
                (*raw_complex_float_clone.0).elements,
                (*(&raw const complex_float)).elements
            );
        }

        let raw_complex_double = Type::ComplexDouble.as_raw();
        let raw_complex_double_clone = raw_complex_double.clone().clone();
        drop(raw_complex_double);

        // SAFETY: raw_complex_double_clone should be a properly initialized `RawType`.
        unsafe {
            assert_eq!((*raw_complex_double_clone.0).type_, COMPLEX);
            assert_eq!(
                (*raw_complex_double_clone.0).elements,
                (*(&raw const complex_double)).elements
            );
        }

        #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
        {
            let raw_complex_longdouble = Type::ComplexLongDouble.as_raw();
            let raw_complex_longdouble_clone = raw_complex_longdouble.clone().clone();
            drop(raw_complex_longdouble);

            // SAFETY: raw_complex_longdouble_clone should be a properly initialized `RawType`.
            unsafe {
                assert_eq!((*raw_complex_longdouble_clone.0).type_, COMPLEX);
                assert_eq!(
                    (*raw_complex_longdouble_clone.0).elements,
                    (*(&raw const complex_longdouble)).elements
                );
            }

            let raw_struct_elements = [
                Type::ComplexFloat,
                Type::ComplexDouble,
                #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
                Type::ComplexLongDouble,
            ];
            let raw_struct = Type::structure(&raw_struct_elements).as_raw();
            let raw_struct_clone = raw_struct.clone().clone();
            drop(raw_struct);

            // SAFETY: raw_struct should be a properly initialized `RawType` with 2 or 3 elements.
            unsafe {
                let elements_ptr = (*raw_struct_clone.0).elements;
                let element_1 = *elements_ptr;
                assert_eq!((*element_1).type_, COMPLEX);
                assert_eq!(
                    (*element_1).elements,
                    (*(&raw const complex_float)).elements
                );

                let element_2 = *elements_ptr.add(1);
                assert_eq!((*element_2).type_, COMPLEX);
                assert_eq!(
                    (*element_2).elements,
                    (*(&raw const complex_double)).elements
                );

                #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
                {
                    let element_3 = *elements_ptr.add(2);
                    assert_eq!((*element_3).type_, COMPLEX);
                    assert_eq!(
                        (*element_3).elements,
                        (*(&raw const complex_longdouble)).elements
                    );
                }
            }
        }
    }
}

#[cfg(miri)]
#[expect(
    non_upper_case_globals,
    reason = "Copying names from `crate::low::types`"
)]
mod miri {
    use crate::low::{
        ffi_type,
        type_tag::{
            COMPLEX, DOUBLE, FLOAT, LONGDOUBLE, POINTER, SINT8, SINT16, SINT32, SINT64, UINT8,
            UINT16, UINT32, UINT64, VOID,
        },
    };

    // Redefining static muts so this module can be tested with miri
    pub static mut sint8: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: SINT8,
        elements: core::ptr::null_mut(),
    };

    pub static mut uint8: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: UINT8,
        elements: core::ptr::null_mut(),
    };

    pub static mut sint16: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: SINT16,
        elements: core::ptr::null_mut(),
    };

    pub static mut uint16: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: UINT16,
        elements: core::ptr::null_mut(),
    };

    pub static mut sint32: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: SINT32,
        elements: core::ptr::null_mut(),
    };

    pub static mut uint32: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: UINT32,
        elements: core::ptr::null_mut(),
    };

    pub static mut sint64: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: SINT64,
        elements: core::ptr::null_mut(),
    };

    pub static mut uint64: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: UINT64,
        elements: core::ptr::null_mut(),
    };

    pub static mut pointer: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: POINTER,
        elements: core::ptr::null_mut(),
    };

    pub static mut float: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: FLOAT,
        elements: core::ptr::null_mut(),
    };

    pub static mut double: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: DOUBLE,
        elements: core::ptr::null_mut(),
    };

    #[allow(
        dead_code,
        reason = "Implemented for all targets for simplicity even though it may remain unused"
    )]
    pub static mut longdouble: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: LONGDOUBLE,
        elements: core::ptr::null_mut(),
    };

    #[allow(
        dead_code,
        reason = "Implemented for all targets for simplicity even though it may remain unused"
    )]
    pub static mut complex_float: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: COMPLEX,
        // `elements` is used to distinguish the complexes in miri tests.
        elements: core::ptr::null_mut(),
    };

    #[allow(
        dead_code,
        reason = "Implemented for all targets for simplicity even though it may remain unused"
    )]
    pub static mut complex_double: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: COMPLEX,
        // `elements` is used to distinguish the complexes in miri tests.
        elements: 8usize as *mut *mut ffi_type,
    };

    #[allow(
        dead_code,
        reason = "Implemented for all targets for simplicity even though it may remain unused"
    )]
    pub static mut complex_longdouble: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: COMPLEX,
        // `elements` is used to distinguish the complexes in miri tests.
        elements: 16usize as *mut *mut ffi_type,
    };

    pub static mut void: ffi_type = ffi_type {
        size: 0,
        alignment: 0,
        type_: VOID,
        elements: core::ptr::null_mut(),
    };
}
