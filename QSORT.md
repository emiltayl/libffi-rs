TODO Describe
* Calling qsort with a comparator from Rust, in plain Rust and using each of the three modules

# Plain Rust

TODO

# `high` module

TODO

# `middle` module

TODO

# `low` module

```rust
use libffi::low::{
    call, CodePtr, closure_alloc, closure_free, Error, ffi_abi_FFI_DEFAULT_ABI, ffi_cif, prep_cif,
    prep_closure, types,
};
use std::ffi::c_void;
use std::mem;

unsafe extern "C" {
    // Note that while this function could be called directly, we instead create a CIF in order
    // to demonstrate how to use `libffi`
    unsafe fn qsort(
        ptr: *mut c_void,
        count: usize,
        size: usize,
        cmp_fn: extern "C" fn(cmp_a: *const c_void, cmp_b: *const c_void) -> i32
    );
}

// The function provided to `qsort` to compare two `i32`s
unsafe extern "C" fn compare_i32s(
    _cif: &ffi_cif,
    result: *mut mem::MaybeUninit<i32>,
    args: *const *const c_void,
    userdata: *const (),
) {
    // This function accepts a two pointers to `i32`s and returns a `i32`.
    unsafe {
        let args: *const *const *const i32 = args.cast();
        let arg_a = **args; // a pointer to the first `i32` to compare.
        // We need to add 1 to get the next pointer in the argument array.
        let arg_b = *((*args).add(1)); // a pointer to the second `i32` to compare.

        (*result).write(match (*arg_a).cmp(&*arg_b) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        });
    }
}

fn main() -> Result<(), Error> {
    // First, prepare the cif for `qsort`
    let mut qsort_cif = ffi_cif::default();
    let mut qsort_atypes = [
        // Array base address
        &raw mut types::pointer,
        // The number of elements
        // This should be `usize` / `size_t`, but that type is not built-in to libffi
        &raw mut types::pointer,
        // The size of each element
        // This should be `usize` / `size_t`, but that type is not built-in to libffi
        &raw mut types::pointer,
        // The address of the comparison function 
        &raw mut types::pointer,
    ];

    // SAFETY:
    // * `cif` points to a mutable `ffi_cif`.
    // * `rtype` points to a `ffi_type`.
    // * `atypes` points to an array of `ffi_types` with 4 elements.
    unsafe {
        prep_cif(
            &mut qsort_cif,
            ffi_abi_FFI_DEFAULT_ABI,
            4,
            &raw mut types::void,
            qsort_atypes.as_mut_ptr(),
        )?;
    }

    let mut cmp_cif = ffi_cif::default();
    let mut cmp_args = [(&raw mut types::pointer).cast(), (&raw mut types::pointer).cast()];

    // SAFETY:
    // * `cif` points to a mutable `ffi_cif`.
    // * `rtype` points to a `ffi_type`.
    // * `atypes` points to an array of `ffi_types` with one element.
    unsafe {
        prep_cif(
            &mut cmp_cif,
            ffi_abi_FFI_DEFAULT_ABI,
            1,
            &raw mut types::sint32,
            cmp_args.as_mut_ptr(),
        )?;
    }

    let (closure, code) = closure_alloc()?;

    // SAFETY:
    // * `closure` and `code` point to memory from the same call to `closure_alloc`.
    // * `closure_alloc` returned successfully as we have not returned early yet.
    // * `cif` points to memory that live until the end of this function, at which point `closure`
    //   will have been freed.
    unsafe {
        prep_closure(
            closure,
            &mut cmp_cif,
            compare_i32s,
            &(),
            code,
        )?;
    }

    // Now we are ready to sort
    let mut array: [i32; 7] = [37, 0, i32::MAX, i32::MIN, -1, 1, 7];
    let mut array_ptr = array.as_mut_ptr();
    let mut num_elements = array.len();
    let mut element_size = mem::size_of::<i32>();
    // SAFETY:
    // * `cif` and `callback` both describe a function that accepts two `const i32`s and return a
    //   `i32`.
    // * `code` contains a function pointer that will be used to execute `callback`.
    let mut cmp_fn: extern "C" fn(*const i32, *const i32) -> i32 = unsafe { mem::transmute(code) };

    let mut arg_array: [*mut c_void; 4] = [
        (&raw mut array_ptr).cast(),
        (&raw mut num_elements).cast(),
        (&raw mut element_size).cast(),
        (&raw mut cmp_fn).cast(),
    ];

    // SAFETY:
    // * `qsort_cif` is a pointer to an initialized `ffi_cif` to a function with the "C" ABI.
    // * `qsort_atypes` is still readable.
    // * `qsort` points to an `extern "C"` function that accepts two `*const i32`s and returns a
    //   `i32`.
    // * `qsort` should stay within the bounds of `array`.
    // * `arg_array` contains an array with the pointer to the array to sort, the number of
    //   elements, the size of each element, and a pointer to the comparison function.
    unsafe {
        call::<()>(
            &mut qsort_cif,
            CodePtr(qsort as *mut _),
            arg_array.as_mut_ptr(),
        );
    }

    // By now, the array should be sorted.
    assert!(array.is_sorted());

    // Make sure to free the closure after we are finished with it.
    // SAFETY:
    // * `closure` is a valid `ffi_closure` that has not been freed yet.
    // * `code` / `qsort_cmp` is not called beyond this point.
    unsafe { closure_free(closure) };
   Ok(())
}
```
