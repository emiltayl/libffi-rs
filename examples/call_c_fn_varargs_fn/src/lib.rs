//! Functions used by `call_c_fn` example.

/// A function that always panics. Since this is the function that panics, it must be declared
/// "C-unwind" to allow unwinding the stack. Note that other functions called do not need to be
/// declared "C-unwind", but can instead be declared just "C". Unwinding will happens as long as the
/// panicking function is "C-unwind".
///
/// # Panics
///
/// Always
#[unsafe(no_mangle)]
pub extern "C-unwind" fn do_panic() {
    panic!("panic!");
}

unsafe extern "C" {
    /// Vararg function that calculates the sum the values it is called with.
    pub unsafe fn vararg_sum(n_numbers: u32, ...) -> u32;
    /// Convert a C ascii string to uppercase.
    pub unsafe fn ascii_to_upper(str: *mut i8);
    /// A function that calls [`do_panic`].
    pub unsafe fn call_do_panic();
}
