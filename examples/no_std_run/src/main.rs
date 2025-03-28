#![no_std]
#![no_main]

extern crate alloc;

use core::panic::PanicInfo;

use libffi::middle::{Arg, Cif, CodePtr, Type};

#[global_allocator]
static GLOBAL: dlmalloc::GlobalDlmalloc = dlmalloc::GlobalDlmalloc;

#[cfg(target_os = "windows")]
mod native {
    unsafe extern "C" {
        unsafe fn _exit(exit_code: i32) -> !;
        unsafe fn _cputs(s: *const i8) -> i32;
    }

    pub fn exit_process(exit_code: i32) -> ! {
        unsafe { _exit(exit_code) }
    }

    pub unsafe fn cstring_print(s: &core::ffi::CStr) -> i32 {
        unsafe { _cputs(s.as_ptr()) }
    }
}
#[cfg(not(target_os = "windows"))]
mod native {
    unsafe extern "C" {
        unsafe fn exit(exit_code: i32) -> !;
        unsafe fn puts(s: *const i8) -> i32;
    }

    pub fn exit_process(exit_code: i32) -> ! {
        unsafe { exit(exit_code) }
    }

    pub unsafe fn cstring_print(s: &core::ffi::CStr) -> i32 {
        unsafe { puts(s.as_ptr()) }
    }
}

use native::*;

// Needed to make code compile on Linux.
// Copied from https://github.com/rust-lang/rust/issues/106864#issuecomment-1858861750
#[unsafe(no_mangle)]
extern "C" fn rust_eh_personality() {}

#[allow(non_snake_case, reason = "Needed to make example compile")]
#[unsafe(no_mangle)]
extern "C" fn _Unwind_Resume() {}

#[panic_handler]
fn panic(panic_info: &PanicInfo) -> ! {
    let string = alloc::format!("{panic_info}\n");
    let cstring = alloc::ffi::CString::new(string).unwrap_or_else(|_| {
        let bytes = b"Unable to convert panic message to CString!\n\0";
        unsafe { alloc::ffi::CString::from_vec_with_nul_unchecked(alloc::vec::Vec::from(bytes)) }
    });

    unsafe {
        cstring_print(&cstring);
    }
    exit_process(1)
}

extern "C" fn empty() {}
extern "C" fn add(a: u32, b: u32) -> u32 {
    a + b
}

#[unsafe(no_mangle)]
pub extern "C" fn main() -> ! {
    let empty_cif = Cif::new(&[], None);
    let add_cif = Cif::new(&[Type::U32, Type::U32], Some(Type::U32));

    unsafe {
        empty_cif.call::<()>(CodePtr(empty as *mut _), &[]);
        let add_result: u32 = add_cif.call(
            CodePtr(add as *mut _),
            &[Arg::borrowed(&4u32), Arg::borrowed(&5u32)],
        );
        assert_eq!(add_result, 9);
    }

    exit_process(0)
}
