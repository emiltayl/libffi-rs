//! Example binary that calls `qsort` with a Rust closure as the comparator.

use libffi::high::Closure;

unsafe extern "C" {
    fn qsort(
        base: *mut i32,
        elements: usize,
        element_size: usize,
        comparator: extern "C" fn(*const i32, *const i32) -> i32,
    );
}

fn main() {
    let mut array: [i32; 10] = [i32::MAX, 3, 7, 1000, 5, 0, 9, 13, 2, i32::MIN];

    let closure = Closure::new(|a: *const i32, b: *const i32| -> i32 {
        // SAFETY: This assumes that qsort is called with an array with a correct number of `i32`s.
        let order = unsafe { (*a).cmp(&*b) };

        match order {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        }
    });

    // SAFETY:
    // * `array` is a valid, mut array with 10 elements of size `size_of::<i32>()`
    // * `closure.as_ptr()` returns a pointer to a function that compares the pointers of two `i32s`
    unsafe {
        qsort(
            array.as_mut_ptr(),
            10,
            size_of::<i32>(),
            closure.as_fn_ptr(),
        );
    }

    assert!(array.is_sorted());
}
