//! The test image of the clean of data cache lines to the point of
//! unification on QEMU virt: `cache::clean_code_to_pou` runs at EL1 over a
//! range whose ends lie inside data cache lines, returns without an
//! exception, and the data reads back unchanged.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The image fills a page-aligned buffer of 4 KiB with a pattern and cleans
//! [`BYTES`] bytes from byte [`OFFSET`]. The range crosses the boundary of
//! 2 KiB in the middle of the buffer, so it touches at least two lines of
//! any data cache line size up to 2 KiB, and both of its ends lie inside a
//! line of any size from 4 bytes up. The self-check holds the ends and the
//! lines against the line size of `CTR_EL0.DminLine` and the buffer against
//! the pattern. The MMU and the caches stay off, as QEMU leaves them. On the
//! host it is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::{asm, global_asm};
    use core::ptr;

    use crate::common;
    use krepi_arch::cache;
    use krepi_arch::exception::Frame;
    use krepi_qemu_virt::uart;

    /// The bytes of the buffer, one page.
    const SIZE: usize = 4096;
    /// The offset of the range in the buffer: 101 bytes below its middle.
    const OFFSET: usize = 1947;
    /// The length of the range.
    const BYTES: u64 = 200;

    /// A page-aligned page of bytes.
    #[repr(C, align(4096))]
    struct Page([u8; SIZE]);

    /// The buffer whose range the image cleans.
    static mut DATA: Page = Page([0; SIZE]);

    // The entry of the image, the cold entry.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        b _start
        .size krepi_test_entry, . - krepi_test_entry
        "#
    );

    /// The cache type register `CTR_EL0`.
    fn cache_type() -> u64 {
        let value: u64;
        // SAFETY: EL1 reads `CTR_EL0` on QEMU virt, which has no EL2 to trap
        // it. The read has no side effect and touches no memory, the stack or
        // the condition flags.
        unsafe {
            asm!("mrs {}, ctr_el0", out(reg) value, options(nomem, nostack, preserves_flags))
        };
        value
    }

    /// The byte of the pattern at `index`.
    fn pattern(index: usize) -> u8 {
        (index as u8) ^ 0x5a
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("clean-code-to-pou");
        let base = (&raw mut DATA).cast::<u8>();
        for index in 0..SIZE {
            // SAFETY: `index` is below the size of `DATA`, a static of this
            // image that only this code accesses, on CPU 0 alone.
            unsafe { ptr::write_volatile(base.add(index), pattern(index)) };
        }
        let line = 4_u64 << ((cache_type() >> 16) & 15);
        let start = base as u64 + OFFSET as u64;
        let end = start + BYTES;
        cache::clean_code_to_pou(start, BYTES);
        let unchanged = (0..SIZE).all(|index| {
            // SAFETY: as for the writes above.
            unsafe { ptr::read_volatile(base.add(index)) == pattern(index) }
        });
        common::check(
            "clean-keeps-data",
            &[
                !start.is_multiple_of(line),
                !end.is_multiple_of(line),
                (end - 1) / line > start / line,
                unchanged,
            ],
        );
        common::finish()
    }

    /// The exception dispatch of the image: every exception is reported and
    /// halts, as in the default image, and fails the case.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        uart::report_fatal(frame)
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
