//! Representations of C types and arrays thereof.

use std::{mem, ptr};
use libc;

use c;
use low;

type FfiType_      = *mut low::ffi_type;
type FfiTypeArray_ = *mut FfiType_;
type Owned<T>      = T;

#[derive(Debug)]
pub struct FfiType(FfiType_);

#[derive(Debug)]
pub struct FfiTypeArray(FfiTypeArray_);

/// Computes the length of a raw `FfiTypeArray_` by searching for the
/// null terminator.
unsafe fn ffi_type_array_len(mut array: FfiTypeArray_) -> usize {
    let mut count   = 0;
    while !(*array).is_null() {
        count += 1;
        array = array.offset(1);
    }
    count
}

/// Creates an empty `FfiTypeArray_` with null terminator.
unsafe fn ffi_type_array_create_empty(len: usize) -> Owned<FfiTypeArray_> {
    let array = libc::malloc((len + 1) * mem::size_of::<FfiType_>())
                    as FfiTypeArray_;
    assert!(!array.is_null());
    *array.offset(len as isize) = ptr::null::<low::ffi_type>() as FfiType_;
    array
}

/// Creates a null-terminated array of FfiType_. Takes ownership of
/// the elements.
unsafe fn ffi_type_array_create(elements: Vec<FfiType>)
    -> Owned<FfiTypeArray_>
{
    let size = elements.len();
    let new  = ffi_type_array_create_empty(size);
    for i in 0 .. size {
        *new.offset(i as isize) = elements[i].0;
    }

    for t in elements {
        mem::forget(t);
    }

    println!("ffi_type_array_create(...) = {:?}", new);

    new
}

/// Creates a struct type from a raw array of element types.
unsafe fn ffi_type_struct_create_raw(elements: FfiTypeArray_)
    -> Owned<FfiType_>
{
    let new = libc::malloc(mem::size_of::<low::ffi_type>()) as FfiType_;
    assert!(!new.is_null());

    (*new).size      = 0;
    (*new).alignment = 0;
    (*new).type_     = c::ffi_type_enum::STRUCT as ::libc::c_ushort;
    (*new).elements  = elements;

    println!("ffi_type_struct_create_raw({:?}) = {:?}", elements, new);

    new
}

/// Creates a struct ffi_type with the given elements. Takes ownership
/// of the elements.
unsafe fn ffi_type_struct_create(elements: Vec<FfiType>) -> Owned<FfiType_> {
    println!("ffi_type_array_create({:?})", elements);
    ffi_type_struct_create_raw(ffi_type_array_create(elements))
}

/// Makes a copy of a type array.
unsafe fn ffi_type_array_clone(old: FfiTypeArray_) -> Owned<FfiTypeArray_> {
    let size = ffi_type_array_len(old);
    let new  = ffi_type_array_create_empty(size);

    for i in 0 .. size {
        *new.offset(i as isize) = ffi_type_clone(*old.offset(i as isize));
    }

    new
}

/// Makes a copy of a type.
unsafe fn ffi_type_clone(old: FfiType_) -> Owned<FfiType_> {
    if (*old).type_ == c::ffi_type_enum::STRUCT as u16 {
        ffi_type_struct_create_raw(ffi_type_array_clone((*old).elements))
    } else {
        old
    }
}

/// Destroys an array of FfiType_ and all of its elements.
unsafe fn ffi_type_array_destroy(victim: Owned<FfiTypeArray_>) {
    println!("ffi_type_array_destroy({:?})", victim);
    let mut current = victim;
    while !(*current).is_null() {
        ffi_type_destroy(*current);
        current = current.offset(1);
    }

    libc::free(victim as *mut libc::c_void);
}

/// Destroys an FfiType_ if it was dynamically allocated.
unsafe fn ffi_type_destroy(victim: Owned<FfiType_>) {
    println!("ffi_type_destroy({:?})", victim);
    if (*victim).type_ == c::ffi_type_enum::STRUCT as u16 {
        ffi_type_array_destroy((*victim).elements);
        libc::free(victim as *mut libc::c_void);
    }
}

impl Drop for FfiType {
    fn drop(&mut self) {
        unsafe { ffi_type_destroy(self.0) }
    }
}

impl Drop for FfiTypeArray {
    fn drop(&mut self) {
        unsafe { ffi_type_array_destroy(self.0) }
    }
}

impl Clone for FfiType {
    fn clone(&self) -> Self {
        unsafe { FfiType(ffi_type_clone(self.0)) }
    }
}

impl Clone for FfiTypeArray {
    fn clone(&self) -> Self {
        unsafe { FfiTypeArray(ffi_type_array_clone(self.0)) }
    }
}

impl FfiType {
    pub fn void() -> Self {
        FfiType(unsafe { &mut low::ffi_type_void })
    }

    pub fn uint8() -> Self {
        FfiType(unsafe { &mut low::ffi_type_uint8 })
    }

    pub fn sint8() -> Self {
        FfiType(unsafe { &mut low::ffi_type_sint8 })
    }

    pub fn uint16() -> Self {
        FfiType(unsafe { &mut low::ffi_type_uint16 })
    }

    pub fn sint16() -> Self {
        FfiType(unsafe { &mut low::ffi_type_sint16 })
    }

    pub fn uint32() -> Self {
        FfiType(unsafe { &mut low::ffi_type_uint32 })
    }

    pub fn sint32() -> Self {
        FfiType(unsafe { &mut low::ffi_type_sint32 })
    }

    pub fn uint64() -> Self {
        FfiType(unsafe { &mut low::ffi_type_uint64 })
    }

    pub fn sint64() -> Self {
        FfiType(unsafe { &mut low::ffi_type_sint64 })
    }

    pub fn float() -> Self {
        FfiType(unsafe { &mut low::ffi_type_float })
    }

    pub fn double() -> Self {
        FfiType(unsafe { &mut low::ffi_type_double })
    }

    pub fn pointer() -> Self {
        FfiType(unsafe { &mut low::ffi_type_pointer })
    }

    pub fn longdouble() -> Self {
        FfiType(unsafe { &mut low::ffi_type_longdouble })
    }

    pub fn complex_float() -> Self {
        FfiType(unsafe { &mut low::ffi_type_complex_float })
    }

    pub fn complex_double() -> Self {
        FfiType(unsafe { &mut low::ffi_type_complex_double })
    }

    pub fn complex_longdouble() -> Self {
        FfiType(unsafe { &mut low::ffi_type_complex_longdouble })
    }

    pub fn structure(fields: Vec<FfiType>) -> Self {
        println!("FfiType::structure({:?})", fields);
        unsafe {
            FfiType(ffi_type_struct_create(fields))
        }
    }

    pub fn as_raw_ptr(&self) -> *mut low::ffi_type {
        self.0
    }
}

impl FfiTypeArray {
    pub fn new(elements: Vec<FfiType>) -> Self {
        unsafe { FfiTypeArray(ffi_type_array_create(elements)) }
    }

    pub fn len(&self) -> usize {
        unsafe { ffi_type_array_len(self.0) }
    }

    pub fn as_raw_ptr(&self) -> *mut *mut low::ffi_type {
        self.0
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn create_uint64() {
        FfiType::uint64();
    }

    #[test]
    fn create_struct() {
        FfiType::structure(vec![FfiType::sint64(),
                                FfiType::sint64(),
                                FfiType::uint64()]);
    }

}