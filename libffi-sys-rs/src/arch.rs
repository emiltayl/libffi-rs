//! This module defines the different [`ffi_abi`] values for each platform.
//!
//! This module is set-up to define all the constants for each platform, but only export those which
//! are actually relevant to the target arch. This is done as a compile check to ensure the code
//! paths in less utilized architectures largely continue to compile.

#![allow(unused, reason = "Values are re-exported.")]

/// From libffi:src/x86/ffitarget.h.
/// See: <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/x86/ffitarget.h#L83>
mod x86_family {
    pub mod x86 {
        use crate::ffi_abi;

        pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
        pub const ffi_abi_FFI_SYSV: ffi_abi = 1;
        pub const ffi_abi_FFI_THISCALL: ffi_abi = 3;
        pub const ffi_abi_FFI_FASTCALL: ffi_abi = 4;
        pub const ffi_abi_FFI_STDCALL: ffi_abi = 5;
        pub const ffi_abi_FFI_PASCAL: ffi_abi = 6;
        pub const ffi_abi_FFI_REGISTER: ffi_abi = 7;
        pub const ffi_abi_FFI_MS_CDECL: ffi_abi = 8;
        pub const ffi_abi_FFI_LAST_ABI: ffi_abi = 9;
        pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_SYSV;

        // See: https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/x86/ffitarget.h#L149
        pub const FFI_TRAMPOLINE_SIZE: usize = 16;
        pub const FFI_NATIVE_RAW_API: u32 = 1;
    }

    pub mod x86_64 {
        use crate::ffi_abi;

        pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 1;
        pub const ffi_abi_FFI_UNIX64: ffi_abi = 2;
        pub const ffi_abi_FFI_WIN64: ffi_abi = 3;
        pub const ffi_abi_FFI_EFI64: ffi_abi = ffi_abi_FFI_WIN64;
        pub const ffi_abi_FFI_GNUW64: ffi_abi = 4;
        pub const ffi_abi_FFI_LAST_ABI: ffi_abi = 5;
        pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_UNIX64;

        // See: https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/x86/ffitarget.h#L140
        pub const FFI_TRAMPOLINE_SIZE: usize = 32;
        pub const FFI_NATIVE_RAW_API: u32 = 0;
    }

    pub mod x86_win32 {
        use crate::ffi_abi;

        pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
        pub const ffi_abi_FFI_SYSV: ffi_abi = 1;
        pub const ffi_abi_FFI_STDCALL: ffi_abi = 2;
        pub const ffi_abi_FFI_THISCALL: ffi_abi = 3;
        pub const ffi_abi_FFI_FASTCALL: ffi_abi = 4;
        pub const ffi_abi_FFI_MS_CDECL: ffi_abi = 5;
        pub const ffi_abi_FFI_PASCAL: ffi_abi = 6;
        pub const ffi_abi_FFI_REGISTER: ffi_abi = 7;
        pub const ffi_abi_FFI_LAST_ABI: ffi_abi = 8;
        pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_MS_CDECL;

        // See: https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/x86/ffitarget.h#L149
        pub const FFI_TRAMPOLINE_SIZE: usize = 16;
        pub const FFI_NATIVE_RAW_API: u32 = 1;
    }

    pub mod x86_win64 {
        use crate::ffi_abi;

        pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
        pub const ffi_abi_FFI_WIN64: ffi_abi = 1;
        pub const ffi_abi_FFI_GNUW64: ffi_abi = 2;
        pub const ffi_abi_FFI_LAST_ABI: ffi_abi = 3;

        mod gnu {
            pub const ffi_abi_FFI_DEFAULT_ABI: crate::ffi_abi = super::ffi_abi_FFI_GNUW64;
        }

        mod msvc {
            pub const ffi_abi_FFI_DEFAULT_ABI: crate::ffi_abi = super::ffi_abi_FFI_WIN64;
        }

        #[cfg(target_env = "gnu")]
        pub use gnu::*;
        #[cfg(target_env = "msvc")]
        pub use msvc::*;

        // See: https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/x86/ffitarget.h#L140
        pub const FFI_TRAMPOLINE_SIZE: usize = 32;
        pub const FFI_NATIVE_RAW_API: u32 = 0;
    }

    pub const FFI_GO_CLOSURES: u32 = 1;
}

#[cfg(all(target_arch = "x86", unix))]
pub use x86_family::x86::*;
#[cfg(all(target_arch = "x86_64", unix))]
pub use x86_family::x86_64::*;
#[cfg(all(target_arch = "x86", windows))]
pub use x86_family::x86_win32::*;
#[cfg(all(target_arch = "x86_64", windows))]
pub use x86_family::x86_win64::*;

/// From libffi:src/arm/ffitarget.h.
/// See: <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/arm/ffitarget.h>
mod arm {
    use crate::ffi_abi;

    pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
    pub const ffi_abi_FFI_SYSV: ffi_abi = 1;
    pub const ffi_abi_FFI_VFP: ffi_abi = 2;
    pub const ffi_abi_FFI_LAST_ABI: ffi_abi = 3;

    // On systems with a hard(ware) float ("hf"), ffi_abi_FFI_VPF is the default ABI.
    #[cfg(target_abi = "eabihf")]
    pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_VFP;
    #[cfg(not(target_abi = "eabihf"))]
    pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_SYSV;

    // See: <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/arm/ffitarget.h#L84>
    pub const FFI_GO_CLOSURES: u32 = 1;
    pub const FFI_TRAMPOLINE_SIZE: usize = 12;
    pub const FFI_NATIVE_RAW_API: u32 = 0;
}

#[cfg(target_arch = "arm")]
pub use arm::*;

/// From libffi:src/aarch64/ffitarget.h.
/// See: <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/aarch64/ffitarget.h#L44>
mod aarch64 {
    use crate::ffi_abi;

    pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
    pub const ffi_abi_FFI_SYSV: ffi_abi = 1;
    pub const ffi_abi_FFI_WIN64: ffi_abi = 2;
    pub const ffi_abi_FFI_LAST_ABI: ffi_abi = 3;

    #[cfg(unix)]
    pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_SYSV;
    #[cfg(windows)]
    pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_WIN64;

    pub const FFI_NATIVE_RAW_API: u32 = 0;

    #[cfg(target_vendor = "apple")]
    pub const FFI_TRAMPOLINE_SIZE: usize = 16;

    #[cfg(not(target_vendor = "apple"))]
    pub const FFI_TRAMPOLINE_SIZE: usize = 24;

    // No GO_CLOSURES on iOS or Windows
    #[cfg(not(any(target_os = "windows", target_vendor = "apple")))]
    pub const FFI_GO_CLOSURES: u32 = 1;
}

#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

/// From libffi:src/powerpc/ffitarget.h.
/// See: <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/powerpc/ffitarget.h#L60>
#[expect(
    unexpected_cfgs,
    reason = "Support for non-standard target powerpc-unknown-linux-gnuspe?"
)]
mod powerpc_family {
    pub mod powerpc {
        use crate::ffi_abi;

        pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
        pub const ffi_abi_FFI_SYSV_SOFT_FLOAT: ffi_abi = 0b00_0001;
        pub const ffi_abi_FFI_SYSV_STRUCT_RET: ffi_abi = 0b00_0010;
        pub const ffi_abi_FFI_SYSV_IBM_LONG_DOUBLE: ffi_abi = 0b00_0100;
        pub const ffi_abi_FFI_SYSV: ffi_abi = 0b00_1000;
        pub const ffi_abi_FFI_SYSV_LONG_DOUBLE_128: ffi_abi = 0b01_0000;

        mod fprs {
            pub const SOFT_FLOAT_FLAG: crate::ffi_abi = 0b0;
        }

        mod no_fprs {
            pub const SOFT_FLOAT_FLAG: crate::ffi_abi = super::ffi_abi_FFI_SYSV_SOFT_FLOAT;
        }

        #[cfg(not(target_env = "gnuspe"))]
        use fprs::SOFT_FLOAT_FLAG;
        #[cfg(target_env = "gnuspe")]
        use no_fprs::SOFT_FLOAT_FLAG;

        mod struct_ret {
            pub const STRUCT_RET_FLAG: crate::ffi_abi = super::ffi_abi_FFI_SYSV_STRUCT_RET;
        }

        mod no_struct_ret {
            pub const STRUCT_RET_FLAG: crate::ffi_abi = 0b0;
        }

        #[cfg(not(target_os = "netbsd"))]
        use no_struct_ret::STRUCT_RET_FLAG;
        #[cfg(target_os = "netbsd")]
        use struct_ret::STRUCT_RET_FLAG;

        mod long_double_64 {
            pub const LONG_DOUBLE_128_FLAG: crate::ffi_abi = 0b0;
        }

        mod long_double_128 {
            pub const LONG_DOUBLE_128_FLAG: crate::ffi_abi =
                super::ffi_abi_FFI_SYSV_LONG_DOUBLE_128;
        }

        // IEEE128 is not supported on BSD or when targeting musl:
        // https://github.com/rust-lang/llvm-project/blob/cb7f903994646c5b9223e0bb6cee3792190991f7/clang/lib/Basic/Targets/PPC.h#L379

        #[cfg(any(target_os = "netbsd", target_os = "freebsd", target_env = "musl"))]
        use long_double_64::LONG_DOUBLE_128_FLAG;
        #[cfg(not(any(target_os = "netbsd", target_os = "freebsd", target_env = "musl")))]
        use long_double_128::LONG_DOUBLE_128_FLAG;

        pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_SYSV
            | ffi_abi_FFI_SYSV_IBM_LONG_DOUBLE
            | SOFT_FLOAT_FLAG
            | STRUCT_RET_FLAG
            | LONG_DOUBLE_128_FLAG;

        pub const FFI_TRAMPOLINE_SIZE: usize = 40;
        pub const FFI_NATIVE_RAW_API: u32 = 0;
        pub const FFI_GO_CLOSURES: u32 = 1;
    }

    pub mod powerpc64 {
        use crate::ffi_abi;

        pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
        pub const ffi_abi_FFI_LINUX_STRUCT_ALIGN: ffi_abi = 0b00_0001;
        pub const ffi_abi_FFI_LINUX_LONG_DOUBLE_128: ffi_abi = 0b00_0010;
        pub const ffi_abi_FFI_LINUX_LONG_DOUBLE_IEEE128: ffi_abi = 0b00_0100;
        pub const ffi_abi_FFI_LINUX: ffi_abi = 0b00_1000;

        mod elfv1 {
            pub const FFI_TRAMPOLINE_SIZE: usize = 24;
        }

        mod elfv2 {
            pub const FFI_TRAMPOLINE_SIZE: usize = 32;
        }

        // I think this should be something like `target_abi = "elf_v2"`, but that's not yet
        // supported.
        // Discussion: https://github.com/rust-lang/rust/issues/60617
        // RFC: https://github.com/rust-lang/rfcs/pull/2992
        //
        // Instead, this is based on the current defaults at the time of this writing:
        // https://github.com/rust-lang/rust/blob/50d2c3abd59af8cbed7e001b5b4e2f6a9a011112/src/librustc_target/abi/call/powerpc64.rs#L122

        #[cfg(any(
            // ELFv1 is the used for powerpc64 when not targeting musl
            all(target_arch = "powerpc64", target_endian="big", not(target_env = "musl")),
            // Use empty flags when targeting a non-PowerPC target, too, just so code compiles.
            not(all(target_arch = "powerpc64", target_endian="little"))
        ))]
        mod elf {
            pub use super::elfv1::*;
        }

        // ELFv2 is used for Little-Endian powerpc64 and with musl
        #[cfg(any(
            all(target_arch = "powerpc64", target_endian = "big", target_env = "musl"),
            all(target_arch = "powerpc64", target_endian = "little")
        ))]
        mod elf {
            pub use super::elfv2::*;
        }

        pub use elf::FFI_TRAMPOLINE_SIZE;

        mod long_double_64 {
            pub const LONG_DOUBLE_128_FLAG: crate::ffi_abi = 0b0;
        }

        mod long_double_128 {
            pub const LONG_DOUBLE_128_FLAG: crate::ffi_abi =
                super::ffi_abi_FFI_LINUX_LONG_DOUBLE_128;
        }

        // IEEE128 is not supported on BSD or when targeting musl:
        // https://github.com/rust-lang/llvm-project/blob/cb7f903994646c5b9223e0bb6cee3792190991f7/clang/lib/Basic/Targets/PPC.h#L417

        #[cfg(any(target_os = "netbsd", target_os = "freebsd", target_env = "musl"))]
        use long_double_64::LONG_DOUBLE_128_FLAG;
        #[cfg(not(any(target_os = "netbsd", target_os = "freebsd", target_env = "musl")))]
        use long_double_128::LONG_DOUBLE_128_FLAG;

        pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi =
            ffi_abi_FFI_LINUX | ffi_abi_FFI_LINUX_STRUCT_ALIGN | LONG_DOUBLE_128_FLAG;

        pub const FFI_NATIVE_RAW_API: u32 = 0;
        pub const FFI_GO_CLOSURES: u32 = 1;
    }
}

#[cfg(target_arch = "powerpc")]
pub use powerpc_family::powerpc::*;
#[cfg(target_arch = "powerpc64")]
pub use powerpc_family::powerpc64::*;

/// From libffi:src/riscv/ffitarget.h
/// See: <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/riscv/ffitarget.h>
mod riscv {
    use crate::ffi_abi;

    pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
    pub const ffi_abi_FFI_SYSV: ffi_abi = 1;
    pub const ffi_abi_FFI_UNUSED_1: ffi_abi = 2;
    pub const ffi_abi_FFI_UNUSED_2: ffi_abi = 3;
    pub const ffi_abi_FFI_UNUSED_3: ffi_abi = 4;
    pub const ffi_abi_LAST_ABI: ffi_abi = 5;
    pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_SYSV;

    // See: <https://github.com/libffi/libffi/blob/4cb776bc8075332d2f3e59f51785d621fcda48f6/src/riscv/ffitarget.h#L63>
    pub const FFI_GO_CLOSURES: u32 = 1;
    pub const FFI_TRAMPOLINE_SIZE: usize = 24;
    pub const FFI_NATIVE_RAW_API: u32 = 0;
}

#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
pub use riscv::*;

/// From libffi:src/s390/ffitarget.h
/// See: <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/s390/ffitarget.h>
mod s390x {
    use crate::ffi_abi;

    pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
    pub const ffi_abi_FFI_SYSV: ffi_abi = 1;
    pub const ffi_abi_LAST_ABI: ffi_abi = 2;
    pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_SYSV;

    pub const FFI_GO_CLOSURES: u32 = 1;
    pub const FFI_TRAMPOLINE_SIZE: usize = 32;
    pub const FFI_NATIVE_RAW_API: u32 = 0;
}

#[cfg(target_arch = "s390x")]
pub use s390x::*;

/// From libffi:src/sparc/ffitarget.h
/// See <https://github.com/libffi/libffi/blob/bfb5b005a08239c751db667f68a67aeb72a9b9ff/src/sparc/ffitarget.h#L47>
mod sparc64 {
    use crate::ffi_abi;

    pub const ffi_abi_FFI_FIRST_ABI: ffi_abi = 0;
    pub const ffi_abi_FFI_V9: ffi_abi = 1;
    pub const ffi_abi_LAST_ABI: ffi_abi = 2;
    pub const ffi_abi_FFI_DEFAULT_ABI: ffi_abi = ffi_abi_FFI_V9;

    pub const FFI_GO_CLOSURES: u32 = 1;
    pub const FFI_TRAMPOLINE_SIZE: usize = 24;
    pub const FFI_NATIVE_RAW_API: u32 = 0;
}

#[cfg(target_arch = "sparc64")]
pub use sparc64::*;

#[cfg(all(test, not(miri)))]
mod test {
    use core::ffi::c_uint;

    use super::*;

    // Disable test when performing dynamic linking to libffi until version 3.5.0 is required by
    // libffi-rs.
    #[cfg(not(feature = "system"))]
    #[test]
    fn verify_default_abi() {
        unsafe extern "C" {
            safe fn ffi_get_default_abi() -> c_uint;
        }

        assert_eq!(ffi_abi_FFI_DEFAULT_ABI, ffi_get_default_abi())
    }
}
