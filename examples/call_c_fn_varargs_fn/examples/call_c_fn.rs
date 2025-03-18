//! Sample binary that loads functions implemented in C.

use std::{ffi::CString, ptr};

unsafe extern "C" {
    unsafe fn vararg_sum(n_numbers: u32, ...) -> u32;
    unsafe fn ascii_to_upper(str: *mut i8);
}

use libffi::{
    low::{call, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif_var, types},
    middle::{Cif, CodePtr, Type, arg},
};

fn main() {
    let mut sum_5_numbers_cif = ffi_cif::default();
    // SAFETY: Create a `ffi_cif` that can be used to call a vararg function that accepts one fixed
    // `u32` and varargs. This specific CIF can be used to provide exactly 5 varargs to the
    // function.
    unsafe {
        prep_cif_var(
            &raw mut sum_5_numbers_cif,
            ffi_abi_FFI_DEFAULT_ABI,
            1,
            6,
            &raw mut types::uint32,
            [
                &raw mut types::uint32,
                &raw mut types::uint32,
                &raw mut types::uint32,
                &raw mut types::uint32,
                &raw mut types::uint32,
                &raw mut types::uint32,
            ]
            .as_mut_ptr(),
        )
        .expect("Got error while calling `ffi_prep_cif_var`.");

        let result: u32 = call(
            &raw mut sum_5_numbers_cif,
            CodePtr(vararg_sum as *mut _),
            [
                ptr::from_mut(&mut 5u32).cast(),
                ptr::from_mut(&mut 1u32).cast(),
                ptr::from_mut(&mut 2u32).cast(),
                ptr::from_mut(&mut 3u32).cast(),
                ptr::from_mut(&mut 4u32).cast(),
                ptr::from_mut(&mut 5u32).cast(),
            ]
            .as_mut_ptr(),
        );

        assert_eq!(result, 15);
    }

    let ascii_to_upper_cif = Cif::new(&[Type::Pointer], None);

    let original_string = "thIs STriNg, should be UPPERcased?";
    let uppercase_string = original_string.to_ascii_uppercase();

    let lowercase_string_ptr = CString::new(original_string).unwrap().into_raw();
    // SAFETY: CString ensures that the string is NULL-terminated, so ascii_to_upper should not read
    // out of bounds.
    unsafe {
        ascii_to_upper_cif.call::<()>(
            CodePtr(ascii_to_upper as *mut _),
            &[arg(&lowercase_string_ptr)],
        );
    }
    // SAFETY: `lowercase_string_ptr` was created by `CString` and is still NULL-terminated.
    let modified_string = unsafe {
        CString::from_raw(lowercase_string_ptr)
            .into_string()
            .unwrap()
    };

    assert_eq!(&modified_string, &uppercase_string);
}
