//! The adapter of the page tables: the execution of the write plans of the
//! core on the pool of a table set, the registers that turn the MMU on, the
//! zeroing of frames through the direct map and the physical address size
//! of the CPU.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The rules are those of the contract of the page tables,
//! `docs/domains/memory/page-tables/contract.md`. The core checks every rule
//! of an entry and returns its write as a plan of steps; `apply` carries out
//! a whole plan, given through the trait [`Plan`], on the pool of its set,
//! which a `Pool` names: it zeroes the new tables and stores the descriptors
//! with volatile stores, and executes the barriers and the invalidations,
//! each step completing before it asks the plan for the next. `enable`
//! invalidates the TLB entries of the executing CPU and writes `MAIR_EL1`,
//! `TCR_EL1`, `TTBR0_EL1`, `TTBR1_EL1` and `SCTLR_EL1` with the values of
//! the contract, for the caches on or off. `zero_frames` writes zeros into
//! a physical range through the direct map, and `physical_width` reads the
//! physical address size from `ID_AA64MMFR0_EL1`.
//!
//! Each function acts for the CPU that executes it. The caller holds the
//! token of a set from the entry that gave its plan to the last step of the
//! plan, as the contract requires, so the module adds no lock. The trait,
//! the cursor [`WriteSteps`] over a plan of at most seven steps and the
//! implementations of the trait for the plan iterators of the core are plain
//! code, and private functions compute the register values, which the host
//! tests check; `Pool`, `apply`, `enable`, `zero_frames` and
//! `physical_width` are compiled only for the bare-metal target.

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
use core::arch::asm;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
use core::ptr;

use krepi_kernel::page_tables::{ClonePlan, DirectMapPlan, KernelMapPlan, Step, WritePlan};
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
use krepi_kernel::page_tables::{ENTRIES, PhysRange, direct_address};

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
use crate::{cache, cpu};

#[cfg(test)]
mod tests;

/// A write plan of a set of `N` tables, as `apply` takes it: its steps in
/// order, one at each call, and then none.
pub trait Plan<const N: usize> {
    /// The next step of the plan, or none after its last.
    fn next_step(&mut self) -> Option<Step>;
}

impl<const N: usize> Plan<N> for KernelMapPlan<'_, N> {
    fn next_step(&mut self) -> Option<Step> {
        self.next()
    }
}

impl<const N: usize> Plan<N> for DirectMapPlan<'_, N> {
    fn next_step(&mut self) -> Option<Step> {
        self.next()
    }
}

impl<const N: usize, const UPPER: bool> Plan<N> for ClonePlan<'_, N, UPPER> {
    fn next_step(&mut self) -> Option<Step> {
        self.next()
    }
}

/// The steps of a [`WritePlan`] of a set of `N` tables, the plan of
/// `map_page`, `map_block`, `unmap_page` or `reset`: `Zero(0)` to
/// `Zero(zero_tables - 1)`, then the first `len` of `steps`, at most all
/// seven of them, and then none.
pub struct WriteSteps<const N: usize> {
    /// The plan.
    plan: WritePlan,
    /// The tables given as `Zero` so far.
    zeroed: usize,
    /// The steps of `steps` given so far.
    given: usize,
}

impl<const N: usize> WriteSteps<N> {
    /// The steps of `plan`, from the first.
    pub fn new(plan: WritePlan) -> WriteSteps<N> {
        WriteSteps {
            plan,
            zeroed: 0,
            given: 0,
        }
    }
}

impl<const N: usize> Plan<N> for WriteSteps<N> {
    fn next_step(&mut self) -> Option<Step> {
        if self.zeroed < self.plan.zero_tables {
            self.zeroed += 1;
            return Some(Step::Zero(self.zeroed - 1));
        }
        if self.given < self.plan.len
            && let Some(&step) = self.plan.steps.get(self.given)
        {
            self.given += 1;
            return Some(step);
        }
        None
    }
}

/// The pool of a table set of `N` tables, `[base, base + 4096 N)`, at the
/// addresses at which the executing CPU reaches it: the handle through which
/// `apply` writes the set. The caller of `Pool::new` makes one value for a
/// set, which is neither `Clone` nor `Copy`.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub struct Pool<const N: usize> {
    /// The address of table 0.
    base: u64,
}

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
impl<const N: usize> Pool<N> {
    /// The pool of `N` tables whose table 0 is at `base`.
    ///
    /// # Safety
    ///
    /// `[base, base + 4096 N)` is the pool of one table set of `N` tables, with
    /// `base` a multiple of 4 KiB, which the executing CPU reaches at these
    /// addresses as memory that it may write: at their physical addresses with
    /// the MMU off, and with the MMU on through the mapping of the image for
    /// the pools of the kernel tables and through the direct map for a pool of
    /// held pages. The pool is the storage of that set, whose provenance has
    /// been exposed, as `<*mut T>::expose_provenance` does, so that the stores
    /// of `apply` may take it. Only the plans of that set write the pool,
    /// through this value alone, while the caller holds the token of the set.
    /// No Rust reference to the set that exists when a step of a plan writes an
    /// entry accesses that entry afterwards: the borrow that a plan of the core
    /// holds reads an entry only before the plan's own steps write it, and a
    /// later access forms a new reference from the storage of the set.
    pub const unsafe fn new(base: u64) -> Pool<N> {
        Pool { base }
    }
}

/// Executes the whole plan `plan` on `pool`, the pool of its set, each step
/// completing before the plan gives the next: `Zero(t)` by `zero_table`,
/// `Store(t, i, d)` by `store_descriptor`, `Fence` and `Sync` by
/// `synchronize`, and `Invalidate(v)` by
/// [`cache::invalidate_tlb_page`]. The check of the entry that gave the
/// plan fixed every step, so the function returns nothing and does not
/// fail.
///
/// # Panics
///
/// Panics with `a step outside its pool`, before the step writes, at a step
/// whose table is not below `N` or whose entry is not below 512. No plan that
/// the check of an entry fixed on a set of `N` tables names one, so the
/// check only keeps a plan of another set from writing outside the pool.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub fn apply<const N: usize, P: Plan<N>>(pool: &mut Pool<N>, mut plan: P) {
    while let Some(step) = plan.next_step() {
        match step {
            Step::Zero(table) => zero_table(pool, table),
            Step::Store(table, entry, descriptor) => {
                store_descriptor(pool, table, entry, descriptor)
            }
            Step::Fence => synchronize(Barrier::Fence),
            Step::Sync => synchronize(Barrier::Sync),
            Step::Invalidate(address) => cache::invalidate_tlb_page(address),
        }
    }
}

/// Writes `descriptor` into entry `entry` of table `table` of `pool`, with
/// one volatile store of 8 bytes.
///
/// # Panics
///
/// Panics with `a step outside its pool`, before the store, when `table` is
/// not below `N` or `entry` not below 512.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
fn store_descriptor<const N: usize>(
    pool: &mut Pool<N>,
    table: usize,
    entry: usize,
    descriptor: u64,
) {
    assert!(table < N && entry < ENTRIES, "a step outside its pool");
    let address = pool.base + 4096 * table as u64 + 8 * entry as u64;
    // SAFETY: the entry lies in the pool that the caller of `Pool::new`
    // vouched for, which the executing CPU reaches at this address and may
    // write, 8-byte aligned as the pool is 4 KiB aligned; the check above
    // keeps it inside the pool. An aligned store of 8 bytes is single-copy
    // atomic, so a table walk sees the old or the new descriptor whole. The
    // pointer takes the exposed provenance of the storage of the set, and
    // `apply`, which holds the only `Pool` of the set mutably, is its only
    // writer while the caller holds the token of the set. The plan that
    // gives the step borrows the set through a shared reference reborrowed
    // from the caller's reference to the storage, and reads an entry only
    // before a step of its own writes it, the entries of a slot at the first
    // step of the slot; so no reference reads this entry after the store,
    // which holds location by location, as Tree Borrows checks accesses.
    // Under Stacked Borrows, where an earlier store into another entry would
    // invalidate a helper of the plan that reborrows the whole pool, the
    // argument is not shown; the open obligations of this module leave that
    // question to the proof of their unsafe sites.
    unsafe { ptr::with_exposed_provenance_mut::<u64>(address as usize).write_volatile(descriptor) };
}

/// Writes 0 into the 512 entries of table `table` of `pool`, with volatile
/// stores of 8 bytes in the order of the entries.
///
/// # Panics
///
/// Panics with `a step outside its pool`, before any store, when `table` is
/// not below `N`.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
fn zero_table<const N: usize>(pool: &mut Pool<N>, table: usize) {
    assert!(table < N, "a step outside its pool");
    let start = pool.base + 4096 * table as u64;
    for entry in 0..ENTRIES as u64 {
        // SAFETY: each entry lies in table `table`, inside the pool by the
        // check above, at an 8-byte aligned address that the executing CPU
        // reaches and may write, as the caller of `Pool::new` vouched for.
        // The pointer takes the exposed provenance of the storage of the
        // set, and `apply`, which holds the only `Pool` of the set mutably,
        // is its only writer while the caller holds the token of the set. A
        // plan zeroes only tables that no reference of its own reads: the
        // new tables of `kernel_map` and `direct_map`, which their plans
        // only write, and the tables of `reset` and of the target of a copy,
        // which their plans do not borrow; so no reference reads these
        // entries after the stores, which holds location by location, as
        // Tree Borrows checks accesses. Under Stacked Borrows the argument is
        // not shown, as for `store_descriptor`. No table walk reaches a new
        // table before a later step stores its table descriptor.
        unsafe {
            ptr::with_exposed_provenance_mut::<u64>((start + 8 * entry) as usize).write_volatile(0)
        };
    }
}

/// A barrier that `synchronize` executes.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
enum Barrier {
    /// `DMB ISHST`: the stores before it reach the observers of the
    /// inner-shareable domain, the table walks among them, before the stores
    /// after it.
    Fence,
    /// `DSB ISH`, then `ISB`: the stores before it complete for the
    /// inner-shareable domain, and the CPU fetches the instructions after it
    /// anew.
    Sync,
    /// `TLBI VMALLE1`, `DSB NSH`, `ISB`: the TLB entries of the EL1&0 regime
    /// of the executing CPU are invalidated before the instructions after
    /// it.
    LocalTlb,
}

/// Executes `barrier`.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
fn synchronize(barrier: Barrier) {
    match barrier {
        Barrier::Fence => {
            // SAFETY: the barrier orders the memory accesses of the CPU and
            // changes no memory, the stack or the flags; the asm is not
            // `nomem`, so the compiler keeps the stores before it on their
            // side.
            unsafe { asm!("dmb ishst", options(nostack, preserves_flags)) }
        }
        Barrier::Sync => {
            // SAFETY: the barriers wait for the memory accesses before them
            // and synchronize the context; they change no memory, the stack
            // or the flags, and the asm is not `nomem`.
            unsafe { asm!("dsb ish", "isb", options(nostack, preserves_flags)) }
        }
        Barrier::LocalTlb => {
            // SAFETY: the invalidation removes only cached copies of
            // translation table entries of the executing CPU, which it may
            // drop at any time, so a later access translates through the
            // tables that the TTBRs hold, and the code that wrote them
            // carries their obligations; `enable` executes it before the MMU
            // is on. A TLB invalidation raises no abort, and none of the
            // instructions changes memory, the stack or the flags.
            unsafe {
                asm!(
                    "tlbi vmalle1",
                    "dsb nsh",
                    "isb",
                    options(nostack, preserves_flags)
                )
            }
        }
    }
}

/// Turns the MMU on for the executing CPU with the kernel tables: `lower`,
/// the address of the root of the lower kernel set, and `direct`, that of
/// the root of the direct map, for the physical address size `bits`, with
/// the caches on when `caches`. It invalidates the TLB entries of the EL1&0
/// regime of the executing CPU (`TLBI VMALLE1`, `DSB NSH`, `ISB`); writes
/// `MAIR_EL1` with Device-nGnRnE at index 0 and Normal memory at index 1,
/// Write-Back with `caches` and Non-cacheable otherwise; writes `TCR_EL1`
/// with `T0SZ` and `T1SZ` 25, 4 KiB granules, inner-shareable walks of the
/// cacheability of that Normal memory, `IPS` the encoding of `bits`, the
/// 8-bit ASID of `TTBR0_EL1`, no top-byte ignore and no hardware update of
/// the access or dirty flags; writes `lower` into `TTBR0_EL1`, with ASID 0,
/// and `direct` into `TTBR1_EL1`; executes `ISB`; and sets `SCTLR_EL1.M` and
/// `WXN`, with `C` and `I` when `caches`, keeping its other bits, followed
/// by `ISB`.
///
/// It reports nothing, as the contract has its callers vouch for its
/// arguments: a `bits` other than 32, 36, 40, 42, 44 and 48, which the
/// obligation of the caller excludes, has no encoding in `IPS`, so the
/// function writes no register and the MMU stays off.
///
/// # Safety
///
/// The executing CPU runs at EL1 with the MMU off and every exception
/// masked. `lower` and `direct` are the roots of the lower kernel set and of
/// the direct map, whose plans have been executed to their `Sync` and which
/// change afterwards only by the plans that the contract allows on them. The
/// lower set maps the code, the data, the stack, the vectors and the console
/// that the CPU uses after the call at their physical addresses, with kinds
/// that allow those accesses. `bits` is the physical address size that
/// `physical_width` reports for the CPU. With `caches`, the caller has done
/// the cache maintenance that turning the caches on requires.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub unsafe fn enable(lower: u64, direct: u64, bits: u8, caches: bool) {
    let Some(control) = translation_control(bits, caches) else {
        return;
    };
    synchronize(Barrier::LocalTlb);
    let attributes = memory_attributes(caches);
    // SAFETY: the MMU is off, so the writes change no translation of the
    // running code; `MAIR_EL1` and `TCR_EL1` take the values of the
    // contract, and the TTBRs the roots of the two kernel sets, which the
    // caller vouches for, complete and published by the `Sync` of their
    // plans. `ISB` makes the writes take effect before `SCTLR_EL1` is
    // written. The asm is not `nomem`, so the compiler keeps the memory
    // accesses before it, the stores of the plans among them, on their side;
    // it touches no stack or flags.
    unsafe {
        asm!(
            "msr mair_el1, {attributes}",
            "msr tcr_el1, {control}",
            "msr ttbr0_el1, {lower}",
            "msr ttbr1_el1, {direct}",
            "isb",
            attributes = in(reg) attributes,
            control = in(reg) control,
            lower = in(reg) lower,
            direct = in(reg) direct,
            options(nostack, preserves_flags)
        )
    };
    let system = cpu::system_control() | system_control_bits(caches);
    // SAFETY: setting `M` turns translation on through the tables written
    // above, under which the code, the data, the stack, the vectors and the
    // console that the CPU uses keep their addresses, as the caller vouches,
    // so the next instruction is fetched at the same address; `WXN` makes
    // every writable page execute-never, which no kind of the contract
    // contradicts. `C` and `I` are set only with `caches`, after the cache
    // maintenance that the caller vouches for. `ISB` makes the CPU fetch
    // the instructions after it under the new translation. The asm is not
    // `nomem` and touches no stack or flags.
    unsafe { asm!("msr sctlr_el1, {}", "isb", in(reg) system, options(nostack, preserves_flags)) };
}

/// Writes 0 into each byte of `range` once, through its address in the
/// direct map, `page_tables::direct_address(range)`, with volatile stores:
/// bytes up to the first multiple of 8, words of 8 bytes, then the bytes
/// after the last word.
///
/// It reports nothing, as the contract has its callers vouch for its
/// arguments: a range that leaves the window of the direct map, which the
/// obligation of the caller excludes, has no address there, so the function
/// writes nothing.
///
/// # Safety
///
/// The MMU is on with the direct map in `TTBR1_EL1`, which maps every page of
/// `range` `ReadWrite`. The caller holds the pages of `range` in the page
/// ownership table or, at boot, they are pages that nothing else uses, so
/// that no Rust reference and no other access reaches their bytes while they
/// are zeroed.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub unsafe fn zero_frames(range: PhysRange) {
    let Some(start) = direct_address(range) else {
        return;
    };
    let size = range.size();
    let head = ((8 - start % 8) % 8).min(size);
    let words = (size - head) / 8;
    for offset in 0..head {
        // SAFETY: the byte lies in `range`, which the direct map maps
        // `ReadWrite` at this address and which no other access reaches, as
        // the caller vouches; held pages belong to no allocation of the Rust
        // program, so the pointer needs the provenance of none. The address
        // does not wrap, as the offset is below the size of the range, and a
        // byte store needs no alignment.
        unsafe {
            ptr::with_exposed_provenance_mut::<u8>((start + offset) as usize).write_volatile(0)
        };
    }
    for word in 0..words {
        // SAFETY: the 8 bytes lie in `range` after its first `head` bytes, at
        // an address that is a multiple of 8, mapped and held as for the
        // bytes above.
        unsafe {
            ptr::with_exposed_provenance_mut::<u64>((start + head + 8 * word) as usize)
                .write_volatile(0)
        };
    }
    for offset in head + 8 * words..size {
        // SAFETY: the byte lies in `range` after its last word, mapped and
        // held as for the bytes above.
        unsafe {
            ptr::with_exposed_provenance_mut::<u8>((start + offset) as usize).write_volatile(0)
        };
    }
}

/// The physical address size of the executing CPU, from
/// `ID_AA64MMFR0_EL1`: 32, 36, 40, 42, 44 or 48 bits by its `PARange`, or
/// none when it reports another size or no 4 KiB granule in `TGran4`.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub fn physical_width() -> Option<u8> {
    let value: u64;
    // SAFETY: EL1 reads `ID_AA64MMFR0_EL1` unless EL2 traps the read with
    // `HCR_EL2.TID3`, which no entry of krepi sets. The read has no side
    // effect and touches no memory, the stack or the condition flags.
    unsafe {
        asm!("mrs {}, id_aa64mmfr0_el1", out(reg) value, options(nomem, nostack, preserves_flags))
    };
    width_of(value)
}

/// The value of `TCR_EL1` for the physical address size `bits` and the
/// cacheability of Normal memory that `caches` gives, or none for a size
/// other than 32, 36, 40, 42, 44 and 48 bits: `T0SZ` and `T1SZ` 25, so that
/// each region spans 2^39 bytes; `IRGN0`, `ORGN0`, `IRGN1` and `ORGN1`
/// Write-Back with read and write allocation, `0b01`, with `caches`, and
/// Non-cacheable, `0b00`, otherwise; `SH0` and `SH1` inner shareable,
/// `0b11`; `TG0` 4 KiB, `0b00`, and `TG1` 4 KiB, `0b10`; `IPS` the encoding
/// of `bits`, 0 to 5; and `EPD0`, `EPD1`, `A1`, `AS`, `TBI0`, `TBI1`, `HA`,
/// `HD` and every other field 0.
#[cfg(any(test, all(target_arch = "aarch64", target_os = "none")))]
fn translation_control(bits: u8, caches: bool) -> Option<u64> {
    let size: u64 = match bits {
        32 => 0,
        36 => 1,
        40 => 2,
        42 => 3,
        44 => 4,
        48 => 5,
        _ => return None,
    };
    let regions = 25 | (25 << 16);
    let walks = (0b11 << 12) | (0b11 << 28) | (0b10 << 30);
    let cacheability = if caches {
        (0b01 << 8) | (0b01 << 10) | (0b01 << 24) | (0b01 << 26)
    } else {
        0
    };
    Some(regions | walks | cacheability | (size << 32))
}

/// The value of `MAIR_EL1`: Device-nGnRnE, `0x00`, at index 0, and Normal
/// memory at index 1, inner and outer Write-Back with read and write
/// allocation, `0xff`, with `caches`, and inner and outer Non-cacheable,
/// `0x44`, otherwise.
#[cfg(any(test, all(target_arch = "aarch64", target_os = "none")))]
fn memory_attributes(caches: bool) -> u64 {
    let normal: u64 = if caches { 0xff } else { 0x44 };
    normal << 8
}

/// The bits of `SCTLR_EL1` that `enable` sets: `M`, bit 0, and `WXN`, bit
/// 19, and with `caches` also `C`, bit 2, and `I`, bit 12.
#[cfg(any(test, all(target_arch = "aarch64", target_os = "none")))]
fn system_control_bits(caches: bool) -> u64 {
    let translation = 1 | (1 << 19);
    if caches {
        translation | (1 << 2) | (1 << 12)
    } else {
        translation
    }
}

/// The physical address size of a value of `ID_AA64MMFR0_EL1`: none unless
/// its `TGran4`, bits 28 to 31, is `0b0000` or `0b0001`, a 4 KiB granule;
/// else 32, 36, 40, 42, 44 or 48 bits for its `PARange`, bits 0 to 3, of 0
/// to 5, and none for another `PARange`.
#[cfg(any(test, all(target_arch = "aarch64", target_os = "none")))]
fn width_of(features: u64) -> Option<u8> {
    let granule = (features >> 28) & 0xf;
    if granule != 0b0000 && granule != 0b0001 {
        return None;
    }
    match features & 0xf {
        0 => Some(32),
        1 => Some(36),
        2 => Some(40),
        3 => Some(42),
        4 => Some(44),
        5 => Some(48),
        _ => None,
    }
}
