use core::ffi::c_void;
use core::marker::PhantomData;
use core::ptr;

/// Contains an untyped pointer to a function argument.
///
/// When calling a function via a [CIF](Cif), each argument must be passed as a C `void*`. Wrapping
/// the argument in the [`Arg`] struct accomplishes the necessary coercion.
///
/// # Example
/// ```
/// use libffi::middle::{Arg, Cif, CodePtr, Type};
/// extern "C" fn add(a: u32, b: u32) -> u32 {
///     a + b
/// }
///
/// let cif = Cif::new(&[Type::U32, Type::U32], Some(Type::U32));
///
/// // First with borrowed args
/// let a: u32 = 3;
/// let b: u32 = 4;
///
/// let result = unsafe {
///     cif.call::<u32>(
///         CodePtr(add as *mut _),
///         &[Arg::borrowed(&a), Arg::borrowed(&b)],
///     )
/// };
///
/// assert_eq!(result, 7);
///
/// // Then with owned args
/// let result = unsafe {
///     cif.call::<u32>(
///         CodePtr(add as *mut _),
///         &[Arg::owned(3u32), Arg::owned(4u32)],
///     )
/// };
///
/// assert_eq!(result, 7);
/// ```
#[derive(Debug)]
#[repr(C)]
pub enum Arg<'arg> {
    /// A argument of a borrowed value that must remain valid as long as `Arg` is alive.
    Borrowed(*mut c_void, PhantomData<&'arg c_void>),
    /// A owned argument that is dropped with `Arg`.
    Owned(OwnedArg),
}

impl<'arg> Arg<'arg> {
    /// Creates a borrowed `Arg` pointing to the argument provided in `arg`.
    pub fn borrowed<T>(arg: &'arg T) -> Self {
        Arg::Borrowed(ptr::from_ref(arg) as *mut c_void, PhantomData)
    }

    /// Creates a owned `Arg`.
    pub fn owned<T>(arg: T) -> Self
    where
        T: Into<OwnedArg>,
    {
        Arg::Owned(arg.into())
    }

    #[inline]
    pub(crate) fn as_ptr(&self) -> *mut c_void {
        match self {
            Self::Borrowed(ptr, _) => *ptr,
            Self::Owned(value) => value.as_ptr(),
        }
    }
}

/// Owned values used as arguments for functions.
#[derive(Debug)]
pub enum OwnedArg {
    /// A owned `i8`
    I8(i8),
    /// A owned `u8`
    U8(u8),
    /// A owned `i16`
    I16(i16),
    /// A owned `u16`
    U16(u16),
    /// A owned `i32`
    I32(i32),
    /// A owned `u32`
    U32(u32),
    /// A owned `i64`
    I64(i64),
    /// A owned `u64`
    U64(u64),
    /// A owned `isize`
    Isize(isize),
    /// A owned `usize`
    Usize(usize),
    /// A owned `f32`
    F32(f32),
    /// A owned `f64`
    F64(f64),
    /// A owned pointe
    Pointer(*mut c_void),
}

impl OwnedArg {
    pub(super) fn as_ptr(&self) -> *mut c_void {
        match self {
            OwnedArg::I8(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::U8(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::I16(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::U16(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::I32(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::U32(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::I64(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::U64(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::Isize(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::Usize(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::F32(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::F64(val) => ptr::from_ref(val).cast_mut().cast(),
            OwnedArg::Pointer(val) => ptr::from_ref(val).cast_mut().cast(),
        }
    }
}

impl From<i8> for OwnedArg {
    fn from(value: i8) -> Self {
        OwnedArg::I8(value)
    }
}

impl From<u8> for OwnedArg {
    fn from(value: u8) -> Self {
        OwnedArg::U8(value)
    }
}

impl From<i16> for OwnedArg {
    fn from(value: i16) -> Self {
        OwnedArg::I16(value)
    }
}

impl From<u16> for OwnedArg {
    fn from(value: u16) -> Self {
        OwnedArg::U16(value)
    }
}

impl From<i32> for OwnedArg {
    fn from(value: i32) -> Self {
        OwnedArg::I32(value)
    }
}

impl From<u32> for OwnedArg {
    fn from(value: u32) -> Self {
        OwnedArg::U32(value)
    }
}

impl From<i64> for OwnedArg {
    fn from(value: i64) -> Self {
        OwnedArg::I64(value)
    }
}

impl From<u64> for OwnedArg {
    fn from(value: u64) -> Self {
        OwnedArg::U64(value)
    }
}

impl From<isize> for OwnedArg {
    fn from(value: isize) -> Self {
        OwnedArg::Isize(value)
    }
}

impl From<usize> for OwnedArg {
    fn from(value: usize) -> Self {
        OwnedArg::Usize(value)
    }
}

impl From<f32> for OwnedArg {
    fn from(value: f32) -> Self {
        OwnedArg::F32(value)
    }
}

impl From<f64> for OwnedArg {
    fn from(value: f64) -> Self {
        OwnedArg::F64(value)
    }
}

impl<T> From<*const T> for OwnedArg {
    fn from(value: *const T) -> Self {
        OwnedArg::Pointer(value.cast_mut().cast())
    }
}

impl<T> From<*mut T> for OwnedArg {
    fn from(value: *mut T) -> Self {
        OwnedArg::Pointer(value.cast())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! verify_arg_type {
        ( $type:ty, $val:expr ) => {{
            let val: $type = $val;
            let owned_arg = OwnedArg::from(val);
            let owned_ptr = owned_arg.as_ptr().cast::<$type>();
            let borrowed_arg = Arg::borrowed(&val);
            let borrowed_ptr = borrowed_arg.as_ptr().cast::<$type>();

            #[allow(
                clippy::float_cmp,
                reason = "Comparing floats that should be bitwise identical"
            )]
            // SAFETY: `owned_arg` should live as long as `owned_ptr` and should point to valid
            // `$type` memory.
            unsafe {
                assert_eq!(*owned_ptr, val);
                assert_eq!(*borrowed_ptr, val);
            }
        }};
    }

    #[test]
    fn verify_all_arg_types() {
        verify_arg_type!(i8, 0x55);
        verify_arg_type!(u8, 0xAA);
        verify_arg_type!(i16, 0x5555);
        verify_arg_type!(u16, 0xAAAA);
        verify_arg_type!(i32, 0x5555_5555);
        verify_arg_type!(u32, 0xAAAA_AAAA);
        verify_arg_type!(i64, 0x5555_5555_5555_5555);
        verify_arg_type!(u64, 0xAAAA_AAAA_AAAA_AAAA);
        verify_arg_type!(isize, 0x5555_5555);
        verify_arg_type!(usize, 0xAAAA_AAAA);
        verify_arg_type!(f32, 1.234_567);
        verify_arg_type!(f64, 9.876_543_21);

        let mut var: i32 = 123;
        verify_arg_type!(*const i32, &raw const var);
        verify_arg_type!(*mut i32, &raw mut var);
    }
}
