//! The test image of the boot memory on QEMU virt: it runs the boot wiring
//! of the board and writes what the wiring found and built, as counts that
//! are the same at every cold boot of the image.
//!
//! Feature: krepi.platform.device-tree
//! Feature: krepi.kernel.kernel-memory
//!
//! After its start record, written with the MMU off, the image runs the
//! boot wiring, which reads the device tree, builds the boot memory map,
//! the page ownership table and the kernel tables and turns the MMU on with
//! the caches off. It then writes two count records, in decimal: `CASXI_MEMORY
//! tree=<bytes> ram=<n> reserved=<n> boot=<n> managed=<n> usable=<n>`, the
//! `totalsize` of the tree and the numbers of RAM banks, firmware
//! reservations, spans of boot storage, managed banks and usable ranges of
//! the boot memory map; and `CASXI_TABLES lower=<tables>,<blocks>,<pages>
//! direct=<tables>,<blocks>,<pages>`, the tables in use, the root and one
//! for each table that a plan zeroed, and the block and page descriptors
//! that the plans of the lower kernel set and of the direct map wrote. The
//! self-check `stack-depth` holds that the stack reached at most 48 KiB:
//! the cold entry clears the whole stack, so the lowest word that is not
//! zero marks the deepest point that the image used. Then `CASXI_RESUMED`.
//! On the host the image is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod memory;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::{asm, global_asm};

    use crate::{common, memory};
    use krepi_arch::exception::Frame;
    use krepi_qemu_virt::uart;

    /// The deepest use of the stack that the self-check admits: 48 KiB of
    /// its 64 KiB.
    const STACK_LIMIT: u64 = 48 * 1024;

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

    /// The bytes of the stack `[bottom, top)` that the image used: from the
    /// lowest word that is not zero to the top, or 0 when every word is zero.
    fn stack_depth(bottom: u64, top: u64) -> u64 {
        let mut word = bottom;
        while word < top {
            let value: u64;
            // SAFETY: `word` is an aligned word of the stack of the image,
            // which the lower kernel set maps `ReadWrite` at its address; the
            // load reads it without a Rust reference and changes nothing,
            // and only this code runs on the CPU, which takes no exception
            // here.
            unsafe {
                asm!(
                    "ldr {value}, [{word}]",
                    value = out(reg) value,
                    word = in(reg) word,
                    options(nostack, readonly, preserves_flags)
                )
            };
            if value != 0 {
                return top - word;
            }
            word += 8;
        }
        0
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("boot-memory");
        let wired = memory::wire();
        let map = wired.memory;
        let mut usable = 0;
        let mut ranges = map.available_ranges();
        while ranges.next().is_some() {
            usable += 1;
        }
        uart::print(format_args!(
            "CASXI_MEMORY tree={} ram={} reserved={} boot={} managed={} usable={usable}\n",
            wired.tree.size,
            map.ram().len(),
            map.firmware_ranges().len(),
            map.boot_ranges().len(),
            map.managed_banks().len(),
        ));
        let (lower, direct) = (wired.lower, wired.direct);
        uart::print(format_args!(
            "CASXI_TABLES lower={},{},{} direct={},{},{}\n",
            lower.tables, lower.blocks, lower.pages, direct.tables, direct.blocks, direct.pages,
        ));
        let depth = stack_depth(wired.image.stack_bottom, wired.image.image_end);
        common::check("stack-depth", &[depth != 0, depth <= STACK_LIMIT]);
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
