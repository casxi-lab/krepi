//! The cache and TLB maintenance of the executing CPU by address: the clean
//! of data cache lines to the point of unification, the invalidation of
//! data cache lines to the point of coherency, the invalidation of the TLB
//! entries of one page and the invalidation of instruction cache lines, each
//! with the barriers that complete it.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! A CPU calls each function for its own maintenance. The instructions act
//! on the shareability domain that each function states, and its barriers
//! wait for them there, but the final `ISB`, where there is one,
//! synchronizes only the CPU that executes it. Maintenance on behalf of
//! another CPU, with its acknowledgement, is not provided here. The range
//! functions walk the lines of a range with [`cache_range::data_lines`] or
//! [`cache_range::instruction_lines`], at the smallest line size that
//! `CTR_EL0` reports, and refuse a range that is empty, wraps or is longer
//! than [`cache_range::MAX_RANGE_BYTES`] before any maintenance. No function
//! reports a result: an address that a data cache function cannot
//! translate makes its instruction raise a Data Abort, which the vectors
//! report, the instruction cache invalidation may raise one, and the TLB
//! invalidation never raises one.
//!
//! The asm of the maintenance instructions is not `nomem`, so that the
//! compiler keeps the memory accesses before a call, such as the stores of
//! code or of translation table entries, before its instructions. The
//! module is compiled only for the bare-metal target.

use core::arch::asm;

use crate::cache_range;

/// The cache type register `CTR_EL0`, which holds the smallest data cache
/// line, `DminLine` in bits 16 to 19, and the smallest instruction cache
/// line, `IminLine` in bits 0 to 3, each as the base-2 logarithm of its
/// count of 4-byte words.
fn ctr() -> u64 {
    let value: u64;
    // SAFETY: EL1 reads `CTR_EL0` unless EL2 traps the read with
    // `HCR_EL2.TID2` or a fine-grained trap of FEAT_FGT; no entry of krepi
    // sets `TID2`, and the Cortex-A76 lacks FEAT_FGT. The read has no side
    // effect and touches no memory, the stack or the condition flags.
    unsafe { asm!("mrs {}, ctr_el0", out(reg) value, options(nomem, nostack, preserves_flags)) };
    value
}

/// Cleans the data cache lines of `[start, start + bytes)` to the point of
/// unification and waits for the cleans: `DC CVAU` on each line that the
/// range touches, at the smallest data cache line size, `CTR_EL0.DminLine`,
/// then `DSB ISH`. It is the first step of the publication of code that the
/// CPU wrote, which [`invalidate_code_to_pou`] of the same range completes.
///
/// Shareability: for an address of Inner or Outer Shareable memory, the
/// clean reaches the data caches of every CPU in the inner-shareable domain
/// of the executing CPU; for Non-shareable memory, only those of the
/// executing CPU. With the MMU off, every data access is to Device memory,
/// which is treated as Outer Shareable. `DSB ISH` waits for the cleans in
/// the inner-shareable domain. A CPU calls it for code that it wrote
/// itself.
///
/// With the MMU off, every address below the implemented physical address
/// size is mapped, and a larger one makes the clean raise an Address size
/// fault; with the MMU on, an address that the current translation does not
/// map makes it raise a Translation fault, and an entry whose access flag is
/// 0 may make it raise an Access flag fault. Each is taken as a Data Abort.
///
/// # Panics
///
/// Panics with `bounded code cache walk`, before any maintenance, when the
/// range is empty, wraps or is longer than
/// [`cache_range::MAX_RANGE_BYTES`].
pub fn clean_code_to_pou(start: u64, bytes: u64) {
    let lines = cache_range::data_lines(ctr(), start, bytes).expect("bounded code cache walk");
    for line in lines {
        // SAFETY: a clean writes a modified line back towards the point of
        // unification and leaves its data in place, as the CPU may do with
        // any line at any time, so no later access reads another value; a
        // byte of the checked range lies in `line`. A fault of the address
        // is taken as a Data Abort, which the vectors report. The
        // instruction touches no stack or flags.
        unsafe { asm!("dc cvau, {}", in(reg) line, options(nostack, preserves_flags)) };
    }
    // SAFETY: `DSB ISH` waits for the cleans and the earlier memory accesses
    // in the inner-shareable domain; it changes no memory, the stack or the
    // flags.
    unsafe { asm!("dsb ish", options(nostack, preserves_flags)) };
}

/// Invalidates the data cache lines of `[start, start + bytes)` to the point
/// of coherency, and then the instruction caches of the executing CPU:
/// `DSB SY`, `DC IVAC` on each line that the range touches, at the smallest
/// data cache line size, `CTR_EL0.DminLine`, `DSB SY`, `IC IALLU`, `DSB SY`
/// and `ISB`.
///
/// Shareability: the first `DSB SY` completes the earlier memory accesses of
/// the CPU for the whole system. Each `DC IVAC` invalidates its line in the
/// data caches, up to the point of coherency, of every CPU in the
/// shareability domain of the address: the Outer Shareable domain of the
/// executing CPU for Device memory and for Non-cacheable or Write-Through
/// memory, which includes every data access with the MMU off, and for other
/// Normal memory the domain of its Shareability attribute. `DSB SY` waits
/// for the invalidations in the whole system. `IC IALLU` invalidates the
/// instruction caches of the executing CPU only, and `ISB` synchronizes only
/// that CPU. A CPU calls it for itself.
///
/// With the MMU off, every address below the implemented physical address
/// size is mapped and writable, and a larger one makes the invalidation
/// raise an Address size fault; with the MMU on, an address that the current
/// translation does not map makes it raise a Translation fault, an address
/// that it maps without write permission a Permission fault, and an entry
/// whose access flag is 0 may make it raise an Access flag fault. Each is
/// taken as a Data Abort.
///
/// # Safety
///
/// An invalidation discards the data of a line, also data that was written
/// and not yet cleaned, and it may act on as much as a cache writeback
/// granule, `CTR_EL0.CWG`, at most 2 KiB, around the line. The caller owns
/// every naturally aligned 2 KiB block that the range touches, not only the
/// bytes of the range, and no cache may hold data of those blocks that must
/// be kept, as when no write has gone through the data cache since the
/// reset.
///
/// # Panics
///
/// Panics with `bounded cache walk`, before any maintenance, when the range
/// is empty, wraps or is longer than [`cache_range::MAX_RANGE_BYTES`].
pub unsafe fn invalidate_to_poc(start: u64, bytes: u64) {
    let lines = cache_range::data_lines(ctr(), start, bytes).expect("bounded cache walk");
    // SAFETY: `DSB SY` completes the earlier memory accesses of the CPU, so
    // that the data that they wrote is not in flight when the lines are
    // invalidated; it changes no memory, the stack or the flags.
    unsafe { asm!("dsb sy", options(nostack, preserves_flags)) };
    for line in lines {
        // SAFETY: the caller owns every block that the invalidation of
        // `line` may discard and vouches that none holds data that must be
        // kept, as the `# Safety` section requires; a byte of the checked
        // range lies in `line`. A fault of the address, such as one that
        // cannot be translated or lacks write permission, is taken as a Data
        // Abort, which the vectors report. The instruction touches no stack
        // or flags.
        unsafe { asm!("dc ivac, {}", in(reg) line, options(nostack, preserves_flags)) };
    }
    // SAFETY: `DSB SY` waits for the invalidations; `IC IALLU` discards only
    // copies of memory in the instruction caches of this CPU, `DSB SY` waits
    // for it and `ISB` makes this CPU fetch the instructions after it anew.
    // None changes memory, the stack or the flags.
    unsafe {
        asm!(
            "dsb sy",
            "ic iallu",
            "dsb sy",
            "isb",
            options(nostack, preserves_flags)
        )
    };
}

/// Invalidates the TLB entries of the page that holds `address` and waits
/// for the invalidation: `DSB ISH`, `TLBI VAAE1IS` with bits 12 to 55 of
/// `address`, `DSB ISH` and `ISB`.
///
/// Shareability: the first `DSB ISH` completes the earlier writes of the
/// CPU, such as a changed translation table entry, for the observers of the
/// inner-shareable domain, the table walks included. `TLBI VAAE1IS`
/// invalidates, on every CPU of the inner-shareable domain of the executing
/// CPU, the cached entries of the EL1&0 translation regime that translate
/// the address, with any ASID and from any level of the walk; it completes
/// once the memory accesses that used those entries have completed, and the
/// second `DSB ISH` waits for that. `ISB` synchronizes only the executing
/// CPU. A CPU calls it for a translation that it changed; the order of the
/// change, such as break-before-make, is the caller's. The bits of `address`
/// below the translation granule are ignored, and the instruction never
/// raises an abort.
pub fn invalidate_tlb_page(address: u64) {
    let page = (address >> 12) & ((1 << 44) - 1);
    // SAFETY: the barriers change no memory, and the invalidation removes
    // only cached copies of translation table entries, which the CPU may
    // drop at any time: it brings about a behaviour that the architecture
    // already permits, in which a later access translates through the
    // entries that the tables hold, and the code that wrote the tables
    // carries their obligations. A TLB invalidation never raises an abort.
    // The instructions touch no stack or flags.
    unsafe {
        asm!(
            "dsb ish",
            "tlbi vaae1is, {page}",
            "dsb ish",
            "isb",
            page = in(reg) page,
            options(nostack, preserves_flags)
        )
    };
}

/// Invalidates the instruction cache lines of `[start, start + bytes)` to
/// the point of unification and synchronizes the instruction stream of the
/// executing CPU: `IC IVAU` on each line that the range touches, at the
/// smallest instruction cache line size, `CTR_EL0.IminLine`, then `DSB ISH`
/// and `ISB`. It completes the publication of code after
/// [`clean_code_to_pou`] of the same range; it is needed also for
/// Non-cacheable memory and with the caches off, as instruction fetches can
/// be held in an instruction cache all the same.
///
/// Shareability: for an address of Inner or Outer Shareable memory, which
/// includes Non-cacheable memory and every instruction fetch with the MMU
/// off, the invalidation reaches the instruction caches of every CPU in the
/// inner-shareable domain of the executing CPU; for Non-shareable memory,
/// only those of the executing CPU. `DSB ISH` waits for the invalidations
/// there. `ISB` synchronizes only the executing CPU: another CPU that is to
/// execute the code executes its own `ISB`, or another context
/// synchronization event, first. A CPU calls it for code that it published
/// itself.
///
/// With the MMU off, every address below the implemented physical address
/// size is mapped, and a larger one may make the invalidation fault; with
/// the MMU on, an address that the current translation does not map, or an
/// entry whose access flag is 0, may make it raise a Translation or Access
/// flag fault, as the implementation defines. Such a fault is taken as a
/// Data Abort.
///
/// # Panics
///
/// Panics with `bounded code cache walk`, before any maintenance, when the
/// range is empty, wraps or is longer than
/// [`cache_range::MAX_RANGE_BYTES`].
pub fn invalidate_code_to_pou(start: u64, bytes: u64) {
    let lines =
        cache_range::instruction_lines(ctr(), start, bytes).expect("bounded code cache walk");
    for line in lines {
        // SAFETY: an instruction cache invalidation discards only copies of
        // memory, which the CPU may discard at any time: it brings about a
        // behaviour that the architecture already permits, in which later
        // fetches read memory, and the code that wrote the instructions
        // carries their obligations; a byte of the checked range lies in
        // `line`. A fault that the instruction may raise for the address is
        // taken as a Data Abort, which the vectors report. The instruction
        // touches no stack or flags.
        unsafe { asm!("ic ivau, {}", in(reg) line, options(nostack, preserves_flags)) };
    }
    // SAFETY: `DSB ISH` waits for the invalidations in the inner-shareable
    // domain and `ISB` makes this CPU fetch the instructions after it anew;
    // neither changes memory, the stack or the flags.
    unsafe { asm!("dsb ish", "isb", options(nostack, preserves_flags)) };
}
