//! The test image of the TLB invalidation of one page on QEMU virt: with
//! translation tables of its own and the MMU on, the image reads a page
//! through a first frame, replaces the entry of the page by
//! break-before-make with `cache::invalidate_tlb_page` between the invalid
//! and the new entry, and reads the page through the new frame.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The tables use the 4 KiB granule and 39-bit virtual addresses, so the
//! walk starts at level 1. The level 1 table maps the first GiB, with the
//! PL011 and the GICv2, as Device-nGnRnE memory and the second GiB, with the
//! RAM of the image, as Normal Non-cacheable memory, each with a block that
//! maps it to itself; its entry of [`PAGE`] points to a level 2 table,
//! whose entry points to a level 3 table, whose entry maps [`PAGE`] to the
//! frame `FRAME_A`. With the MMU off, the image writes the tables and the
//! first words of `FRAME_A` and `FRAME_B`, invalidates the TLB of the CPU,
//! sets `MAIR_EL1`, `TCR_EL1` and `TTBR0_EL1` and turns the MMU on with the
//! data and instruction caches off. It then reads [`PAGE`], which fills the
//! TLB, writes an invalid entry in the place of the page's entry, calls
//! `invalidate_tlb_page`, writes the entry of `FRAME_B` with `DSB ISH` and
//! `ISB` after it, as the SMP design rules require for a new entry, and
//! reads [`PAGE`] again. The self-check holds that the MMU is on, that the
//! first read gave the word of `FRAME_A` and the second that of `FRAME_B`,
//! and that both frames still hold their words. The image ends with the MMU
//! on and writes its records through the Device block. On the host it is an
//! empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::{asm, global_asm};
    use core::ptr;

    use crate::common;
    use krepi_arch::exception::Frame;
    use krepi_arch::{cache, cpu};
    use krepi_qemu_virt::uart;

    /// The virtual address of the page whose entry the image replaces: 256
    /// GiB, entry 256 of the level 1 table, far from the blocks of the first
    /// two GiB. By its implementation, QEMU flushes its whole software TLB
    /// when an invalidated address falls in the region of the blocks that
    /// it has used, so a wrong operand of the invalidation that lands there
    /// goes unnoticed; a page next to the blocks would hide an operand that
    /// is off by a factor of two.
    const PAGE: u64 = 0x40_0000_0000;
    /// The first word of `FRAME_A`.
    const WORD_A: u64 = 0x4652_414d_455f_4131;
    /// The first word of `FRAME_B`.
    const WORD_B: u64 = 0x4652_414d_455f_4232;
    /// The index of the entry of [`PAGE`] in the level 1 table: bits 30 to
    /// 38 of the address.
    const LEVEL1_INDEX: usize = ((PAGE >> 30) & 511) as usize;
    /// Its index in the level 2 table: bits 21 to 29.
    const LEVEL2_INDEX: usize = ((PAGE >> 21) & 511) as usize;
    /// Its index in the level 3 table: bits 12 to 20.
    const LEVEL3_INDEX: usize = ((PAGE >> 12) & 511) as usize;

    /// Bits 1 and 0 of a block entry at level 1.
    const BLOCK: u64 = 0b01;
    /// Bits 1 and 0 of a table entry at levels 1 and 2 and of a page entry
    /// at level 3.
    const TABLE_OR_PAGE: u64 = 0b11;
    /// `AttrIndx`, bits 2 to 4, of the Device-nGnRnE memory of `Attr0` of
    /// [`MAIR`]: 0.
    const DEVICE: u64 = 0;
    /// `AttrIndx` of the Normal Non-cacheable memory of `Attr1`.
    const NORMAL: u64 = 1 << 2;
    /// `SH`, bits 8 and 9: Inner Shareable.
    const INNER_SHAREABLE: u64 = 0b11 << 8;
    /// The access flag `AF`, bit 10, so that the first access does not
    /// fault. `AP`, bits 6 and 7, stays 0: read and write at EL1, no access
    /// at EL0.
    const ACCESSED: u64 = 1 << 10;
    /// `UXN`, bit 54: no execution at EL0.
    const NO_EL0_EXECUTE: u64 = 1 << 54;
    /// `PXN`, bit 53, and `UXN`: no execution at all.
    const NO_EXECUTE: u64 = (1 << 53) | NO_EL0_EXECUTE;

    /// `MAIR_EL1`: `Attr0` `0x00`, Device-nGnRnE memory, and `Attr1`
    /// `0x44`, Normal memory Inner and Outer Non-cacheable.
    const MAIR: u64 = 0x44 << 8;
    /// `TCR_EL1`: `T0SZ` 25, 39-bit virtual addresses whose walk starts at
    /// level 1 with the 4 KiB granule of `TG0` `0b00`; table walks
    /// Non-cacheable, `IRGN0` and `ORGN0` 0, and Inner Shareable, `SH0`
    /// `0b11`; no walk for `TTBR1_EL1`, `EPD1` 1, with `T1SZ` 25 and the
    /// 4 KiB granule of `TG1` `0b10`; and `IPS` `0b000`, 32-bit physical
    /// addresses, which hold the RAM and the devices that the image uses.
    const TCR: u64 = 25 | (0b11 << 12) | (25 << 16) | (1 << 23) | (0b10 << 30);
    /// The bit of `SCTLR_EL1` that the image sets: the MMU, `M`, bit 0.
    const MMU: u64 = 1 << 0;
    /// The bits of `SCTLR_EL1` that it clears: the alignment check, `A`,
    /// bit 1; the data cache, `C`, bit 2; the instruction cache, `I`, bit
    /// 12; and write implies execute-never, `WXN`, bit 19.
    const CLEARED: u64 = (1 << 1) | (1 << 2) | (1 << 12) | (1 << 19);

    /// A page-aligned page of 512 words: a translation table or a frame.
    #[repr(C, align(4096))]
    struct Page([u64; 512]);

    /// The level 1 table, the root in `TTBR0_EL1`.
    static mut LEVEL1: Page = Page([0; 512]);
    /// The level 2 table of the GiB of [`PAGE`].
    static mut LEVEL2: Page = Page([0; 512]);
    /// The level 3 table of the 2 MiB of [`PAGE`].
    static mut LEVEL3: Page = Page([0; 512]);
    /// The frame that [`PAGE`] maps to first.
    static mut FRAME_A: Page = Page([0; 512]);
    /// The frame that [`PAGE`] maps to after the change.
    static mut FRAME_B: Page = Page([0; 512]);

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

    /// The address of `page`, its physical address, which the identity
    /// block keeps after the MMU is on.
    fn address(page: *const Page) -> u64 {
        page as u64
    }

    /// Writes `value` into word `index` of `page`.
    fn store(page: *mut Page, index: usize, value: u64) {
        // SAFETY: `page` is a page of this image, `index` is below 512, and
        // only this code, on CPU 0, accesses the pages.
        unsafe { ptr::write_volatile(page.cast::<u64>().add(index), value) }
    }

    /// Reads word `index` of `page`.
    fn load(page: *const Page, index: usize) -> u64 {
        // SAFETY: as in `store`.
        unsafe { ptr::read_volatile(page.cast::<u64>().add(index)) }
    }

    /// The level 3 entry that maps a page to `frame`: Normal memory, Inner
    /// Shareable, accessed, read and write at EL1, not executable.
    fn page_entry(frame: *const Page) -> u64 {
        address(frame) | TABLE_OR_PAGE | NORMAL | INNER_SHAREABLE | ACCESSED | NO_EXECUTE
    }

    /// Writes the tables and the words of the frames.
    fn build_tables() {
        let level1 = &raw mut LEVEL1;
        store(level1, 0, BLOCK | DEVICE | ACCESSED | NO_EXECUTE);
        store(
            level1,
            1,
            0x4000_0000 | BLOCK | NORMAL | INNER_SHAREABLE | ACCESSED | NO_EL0_EXECUTE,
        );
        store(
            level1,
            LEVEL1_INDEX,
            address(&raw const LEVEL2) | TABLE_OR_PAGE,
        );
        store(
            &raw mut LEVEL2,
            LEVEL2_INDEX,
            address(&raw const LEVEL3) | TABLE_OR_PAGE,
        );
        store(
            &raw mut LEVEL3,
            LEVEL3_INDEX,
            page_entry(&raw const FRAME_A),
        );
        store(&raw mut FRAME_A, 0, WORD_A);
        store(&raw mut FRAME_B, 0, WORD_B);
    }

    /// Turns the MMU on with the tables of [`build_tables`], [`MAIR`] and
    /// [`TCR`], and the data and instruction caches off.
    fn enable_mmu() {
        let control = (cpu::system_control() | MMU) & !CLEARED;
        // SAFETY: EL1 owns these registers of CPU 0, the only CPU that runs.
        // The first `DSB ISH` completes the writes of the tables before a
        // walk can read them; `TLBI VMALLE1` removes any entry that the TLB
        // of the CPU holds from before, and the next `DSB ISH` and `ISB`
        // complete it. The tables map the image, its stack and the PL011
        // and the GICv2 each to its own address, so every address that the
        // image uses keeps its meaning, and the instruction after the write
        // of `SCTLR_EL1` is fetched from the same address. The asm touches
        // no stack or flags, and it is not `nomem`, so that the writes of
        // the tables stay before it.
        unsafe {
            asm!(
                "dsb ish",
                "tlbi vmalle1",
                "dsb ish",
                "isb",
                "msr mair_el1, {mair}",
                "msr tcr_el1, {tcr}",
                "msr ttbr0_el1, {table}",
                "isb",
                "msr sctlr_el1, {control}",
                "isb",
                mair = in(reg) MAIR,
                tcr = in(reg) TCR,
                table = in(reg) address(&raw const LEVEL1),
                control = in(reg) control,
                options(nostack, preserves_flags)
            )
        };
    }

    /// Completes the write of a valid entry where the entry was invalid:
    /// `DSB ISH`, then `ISB`.
    fn complete_new_entry() {
        // SAFETY: the barriers change no memory, the stack or the flags; the
        // asm is not `nomem`, so that the write of the entry stays before it.
        unsafe { asm!("dsb ish", "isb", options(nostack, preserves_flags)) };
    }

    /// Reads the first word of [`PAGE`].
    fn read_page() -> u64 {
        // SAFETY: with the MMU on, [`PAGE`] is mapped by the level 3 entry,
        // as Normal memory that EL1 may read, to `FRAME_A` or `FRAME_B`,
        // pages of this image that only this code accesses.
        unsafe { ptr::read_volatile(PAGE as *const u64) }
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("invalidate-tlb-page");
        build_tables();
        enable_mmu();
        let first = read_page();
        let level3 = &raw mut LEVEL3;
        store(level3, LEVEL3_INDEX, 0);
        cache::invalidate_tlb_page(PAGE);
        store(level3, LEVEL3_INDEX, page_entry(&raw const FRAME_B));
        complete_new_entry();
        let second = read_page();
        common::check(
            "remap-reads-new-frame",
            &[
                cpu::system_control() & MMU != 0,
                first == WORD_A,
                second == WORD_B,
                load(&raw const FRAME_A, 0) == WORD_A && load(&raw const FRAME_B, 0) == WORD_B,
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
