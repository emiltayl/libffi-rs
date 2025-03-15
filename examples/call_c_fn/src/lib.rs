//! Re-exporting symbols from the C file for convenience.

unsafe extern "C" {
    /// Adds two u32's, returning a u32 with the sum.
    pub safe fn add(a: u32, b: u32) -> u32;
    /// Converts an ascii string to uppercase.
    pub unsafe fn ascii_to_upper(s: *mut u8);
}
