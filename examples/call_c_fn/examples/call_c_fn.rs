//! Sample binary that loads functions implemented in C.

use std::ffi::CString;

use call_c_fn::{add, ascii_to_upper};
use libffi::middle::{Cif, CodePtr, Type, arg};

fn main() {
    let add_cif = Cif::new(&[Type::U32, Type::U32], Some(Type::U32));

    // SAFETY: add is a safe function.
    let result: u32 = unsafe { add_cif.call(CodePtr(add as *mut _), &[arg(&3u32), arg(&2u32)]) };

    assert_eq!(result, 5);

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
