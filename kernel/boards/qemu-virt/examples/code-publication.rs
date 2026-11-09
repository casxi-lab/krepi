//! The test image of the publication of code on QEMU virt: the image
//! writes two instructions across the boundary of two instruction cache
//! lines, publishes them with `cache::clean_code_to_pou` and
//! `cache::invalidate_code_to_pou`, and calls them; then it writes other
//! instructions at the same address, publishes them and calls them again.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The code is `MOVZ W0, #value` and `RET` in a page-aligned buffer of
//! 4 KiB, with the first instruction in the last word of the first line of
//! the size that `CTR_EL0.IminLine` reports and the second in the first
//! word of the next line. With the MMU off, QEMU fetches the instructions
//! from that RAM as Normal memory that the image may execute. The first
//! call returns [`FIRST`]; the second, after the instructions that already
//! ran are overwritten, must return [`SECOND`]. The self-check holds the
//! placement and both results. On the host it is an empty program.

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

    /// The words of the buffer, one page.
    const WORDS: usize = 1024;
    /// The largest instruction cache line whose boundary the buffer holds
    /// with a word on each side: its middle.
    const LARGEST_LINE: u64 = 2048;
    /// The value that the first code returns.
    const FIRST: u32 = 0x2a;
    /// The value that the code written over it returns.
    const SECOND: u32 = 0x55;
    /// `MOVZ W0, #0` without its immediate, which bits 5 to 20 hold.
    const MOVZ_W0: u32 = 0x5280_0000;
    /// `RET`, a return through `x30`.
    const RET: u32 = 0xd65f_03c0;

    /// A page-aligned page of instruction words.
    #[repr(C, align(4096))]
    struct Code([u32; WORDS]);

    /// The buffer that holds the published code.
    static mut CODE: Code = Code([0; WORDS]);

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

    /// Writes `MOVZ W0, #value` and `RET` at `code`, publishes them and
    /// calls them: the value that the code returns.
    fn publish_and_call(code: *mut u32, value: u32) -> u32 {
        // SAFETY: `code` and the word after it lie in `CODE`, a static of
        // this image that only this code accesses, on CPU 0 alone.
        unsafe {
            ptr::write_volatile(code, MOVZ_W0 | (value << 5));
            ptr::write_volatile(code.add(1), RET);
        }
        cache::clean_code_to_pou(code as u64, 8);
        cache::invalidate_code_to_pou(code as u64, 8);
        // SAFETY: the two words at `code` are `MOVZ W0, #value` and `RET`,
        // which the clean and the invalidation of their range have published
        // on this CPU, the only one that runs, and the last `ISB` of the
        // invalidation has synchronized its instruction stream. With the MMU
        // off, stage 1 permits the execution of every address below the
        // implemented physical address size, and `CODE` lies in RAM. The
        // code writes only `w0`, which holds the result in the procedure
        // call standard, and returns through `x30`; it touches no memory or
        // the stack.
        let function = unsafe { core::mem::transmute::<*mut u32, extern "C" fn() -> u32>(code) };
        function()
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("code-publication");
        let line = 4_u64 << (cache_type() & 15);
        let offset = line.min(LARGEST_LINE) / 4 - 1;
        let code = (&raw mut CODE).cast::<u32>().wrapping_add(offset as usize);
        let first = publish_and_call(code, FIRST);
        let second = publish_and_call(code, SECOND);
        common::check(
            "published-code-runs",
            &[
                (code as u64 + 4).is_multiple_of(line),
                first == FIRST,
                second == SECOND,
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
