//! Example binary that loads functions implemented in C.

use std::ffi::CString;
use std::ptr;

use call_c_fn_varargs_fn::{ascii_to_upper, call_do_panic, vararg_sum};
use libffi::low::{call, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif_var, types};
use libffi::middle::{Arg, Cif, CodePtr, Type};

/// Demonstrating calling the vararg `vararg_sum` function.
fn call_vararg_sum() {
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
}

/// Demonstrating passing a `CString` to a function implemented in C.
fn call_ascii_to_upper() {
    let ascii_to_upper_cif = Cif::new(&[Type::Pointer], None);

    let original_string = "thIs STriNg, should be UPPERcased?";
    let uppercase_string = original_string.to_ascii_uppercase();

    let lowercase_string_ptr = CString::new(original_string).unwrap().into_raw();
    // SAFETY: CString ensures that the string is NULL-terminated, so ascii_to_upper should not read
    // out of bounds.
    unsafe {
        ascii_to_upper_cif.call::<()>(
            CodePtr(ascii_to_upper as *mut _),
            &[Arg::borrowed(&lowercase_string_ptr)],
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

/// Demonstrating unwinding a panic from an extern function.
fn catch_extern_panic() {
    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {
        // Do nothing, to avoid printing the panic
    }));

    let catch_unwind_result = std::panic::catch_unwind(|| {
        let do_panic_cif = Cif::new(&[], None);

        // SAFETY: Call a valid function that does not take any arguments or return any values.
        unsafe { do_panic_cif.call::<()>(CodePtr(call_do_panic as *mut _), &[]) }
    });

    // Reset to the previous panic hook
    std::panic::set_hook(old_hook);

    // Check that code in the catch_unwind closure actually panicked, which results in an `Err`.
    assert!(catch_unwind_result.is_err());
}

fn main() {
    call_vararg_sum();
    call_ascii_to_upper();

    // Unwinding panics fail on these platforms. See https://github.com/emiltayl/libffi-rs/issues/28
    #[cfg(not(any(target_arch = "arm", target_arch = "riscv64")))]
    catch_extern_panic();
}
