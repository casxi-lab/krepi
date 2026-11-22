//! The page tables: the descriptors and kinds of the stage 1 translation
//! tables of the EL1&0 regime, the physical ranges, the table sets with
//! their pools and the entries that look up, map, unmap, reset and copy
//! them, the kernel's mappings of its image and its devices, the kernel
//! direct map, and the page ownership table of the physical RAM.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The rules are those of the component's contract,
//! `docs/domains/memory/page-tables/contract.md`. The module writes no
//! table: an entry that changes a set checks every rule first and returns
//! its write as a plan of steps, which the architecture crate carries out;
//! a failed entry returns one error and changes nothing, and no entry
//! panics.
//!
//! The module follows the provable Rust subset
//! (`docs/conventions/provable-subset.md`) in the code shapes of the
//! component's proof path (`docs/domains/memory/page-tables/proof.md`).
//! Every type and function that a root of its proof target names is
//! defined in this file, and the submodules hold the behaviour. The types
//! whose values keep an invariant have private fields. A descriptor is put
//! together with shifts and masks, a kind gives its bits by a `match`, an
//! end that may pass 64 bits is checked, a function holds at most one
//! loop, every loop walks arrays of plain data and scalars, and the plan
//! iterators implement `next` alone.

// The code shapes of the proof path write a `match` where Clippy suggests a
// combinator, the `?` of an `Option` or `matches!`, `%` where it suggests
// `is_multiple_of`, a comparison where it suggests `saturating_sub` and
// three moves where it suggests `swap`: each of those would reach a library
// function without a model; and a nested `if` where it suggests a let
// chain.
#![allow(
    clippy::collapsible_if,
    clippy::implicit_saturating_sub,
    clippy::manual_is_multiple_of,
    clippy::manual_map,
    clippy::manual_range_contains,
    clippy::manual_swap,
    clippy::match_like_matches_macro,
    clippy::question_mark,
    clippy::redundant_pattern_matching
)]

mod boot;
mod copy;
mod encoding;
mod ownership;
mod range;
mod walk;
mod write;

use crate::fdt::{AvailableRanges, MemoryPlan, Span};
use boot::{MapCursor, direct, layout};
use walk::check_pool;

#[cfg(test)]
mod tests;

/// The descriptors of a table.
pub const ENTRIES: usize = 512;

/// The start of the upper region and of the window of the direct map,
/// `2^64 - 2^39`.
pub const DIRECT_BASE: u64 = 0xffff_ff80_0000_0000;

/// The most steps of the plan of `map_page`, `map_block` or `unmap_page`.
pub const MAX_PLAN_STEPS: usize = 7;

/// The tables of the pool of the direct map's set, sized for 16 GiB of RAM.
pub const DIRECT_MAP_TABLES: usize = 80;

/// The tables of the pool of the lower kernel set, and of the lower tables
/// of each address space, which the copy of the kernel tables fills.
pub const KERNEL_TABLES: usize = 32;

/// The most ranges of a layout.
pub const MAX_LAYOUT_RANGES: usize = 16;

/// The extents of the page ownership table of the kernel root, free and
/// held together.
pub const EXTENTS: usize = 160;

/// The exclusion records of the page ownership table of the kernel root:
/// the 4 spans of boot storage and the 128 firmware reservations that the
/// boot memory map admits at most.
pub const EXCLUSION_RECORDS: usize = 132;

/// A page, 4 KiB.
const PAGE_SIZE: u64 = 0x1000;

/// A block, the span of a level 2 entry, 2 MiB.
const BLOCK_SIZE: u64 = 0x20_0000;

/// The end of the lower region and the size of the window of the direct
/// map, `2^39`.
const VA_LIMIT: u64 = 1 << 39;

/// The nine attribute sets of a leaf, the rows of the kind table of the
/// contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Text of the image: EL1 read-only and executable.
    ReadExecute,
    /// Read-only data of the image and the device tree.
    ReadOnly,
    /// Data, BSS and stacks of the image, and the direct map.
    ReadWrite,
    /// Kernel pages private to one address space, tagged with its ASID.
    KernelPrivateReadWrite,
    /// Registers of the kernel's devices, Device-nGnRnE.
    Device,
    /// Code of a process: EL0 read-only and executable.
    UserReadExecute,
    /// Read-only data of a process.
    UserReadOnly,
    /// Data and stacks of a process.
    UserReadWrite,
    /// Device registers mapped into a process.
    UserDevice,
}

/// An error of a table set: the rule that the input breaks, as the error
/// table of the contract names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableError {
    /// An address or `base` off its 4 KiB or 2 MiB boundary.
    Alignment,
    /// An address outside the region of the set or at or above `2^bits`,
    /// or `bits` outside 32 to 48.
    AddressWidth,
    /// A pool of no table or beyond `2^bits`, or a table descriptor outside
    /// the tables in use.
    TableBacking,
    /// The plan needs more tables than the pool has free.
    OutOfTables,
    /// A slot that the write needs is not free.
    AlreadyMapped,
    /// No page leaf, or no block, where the entry needs one.
    NotMapped,
    /// A descriptor of the source of a copy that the copy refuses.
    InvalidDescriptor,
}

/// An error of a physical range or of the page ownership table, as the
/// error table of the contract names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnershipError {
    /// No bank, overlapping banks, or a range of length 0.
    InvalidRange,
    /// A size or an end that does not fit in 64 bits.
    AddressOverflow,
    /// A bank off page boundaries, or an alignment that is not a power of
    /// two.
    InvalidAlignment,
    /// A request of 0 pages.
    InvalidSize,
    /// The arena 0.
    InvalidArena,
    /// More extents or exclusions than their capacity.
    MetadataExhausted,
    /// No free range of the request in the window.
    OutOfMemory,
    /// The generation counter after `2^64 - 1`.
    GenerationExhausted,
    /// A failed zeroing, or the cancel of an attempted reservation.
    ZeroFailed,
    /// A receipt, packet or reservation of another arena.
    WrongArena,
    /// A receipt, packet or reservation of another owner identity.
    WrongOwner,
    /// A receipt, packet or reservation that names no held range of its
    /// generation and state.
    InvalidAllocation,
}

/// A step of a write plan, which the architecture crate executes in order,
/// each completing before the next. A table is named by its index in the
/// pool and an entry by its index in the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    /// Writes 0 into the 512 entries of a table.
    Zero(usize),
    /// Writes a descriptor into an entry of a table.
    Store(usize, usize, u64),
    /// `DMB ISHST`.
    Fence,
    /// `DSB ISH`, then `ISB`.
    Sync,
    /// `DSB ISH`, `TLBI VAAE1IS` of the address, `DSB ISH`, `ISB`.
    Invalidate(u64),
}

/// The write plan of `map_page`, `map_block`, `unmap_page` or `reset`:
/// `Zero(0)` to `Zero(zero_tables - 1)`, then the first `len` of `steps`;
/// the steps after them are not part of the plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WritePlan {
    /// The tables of the lowest indices that the plan zeroes first.
    pub zero_tables: usize,
    /// The steps after the zeroed tables.
    pub steps: [Step; MAX_PLAN_STEPS],
    /// The number of those steps.
    pub len: usize,
}

/// The tables of one region, the lower when `UPPER` is false, in a pool of
/// `N` tables with the root at index 0, and the record of the tables in
/// use: those of the indices below it.
pub struct Tables<const N: usize, const UPPER: bool> {
    /// The storage of the tables.
    pool: [[u64; ENTRIES]; N],
    /// The number of tables in use.
    used: usize,
}

/// The plan of [`Tables::clone_kernel_from`], given one step at a time by
/// `next`: a `Zero` of every table in use of the target, in the order of
/// their indices; then a `Store` of every valid entry of every table in use
/// of the source into the target's table of the same index, the tables and
/// the entries of each in the order of their indices, its table
/// descriptors pointing into the target's pool; and `Sync` last. The plan
/// borrows the source and the target for its lifetime, so neither changes
/// until its last step.
pub struct ClonePlan<'a, const N: usize, const UPPER: bool> {
    /// The source of the copy.
    source: &'a Tables<N, UPPER>,
    /// The `base` of the pool of the source.
    source_base: u64,
    /// The `base` of the pool of the target.
    base: u64,
    /// The level of each table in use of the source, 1 to 3.
    levels: [u8; N],
    /// The tables of the target to zero.
    zero_tables: usize,
    /// The tables of the target zeroed so far.
    zeroed: usize,
    /// The table of the source from which the next store is looked for.
    table: usize,
    /// The entry of that table from which the next store is looked for.
    entry: usize,
    /// Whether the plan has given its `Sync`.
    done: bool,
}

/// The kind of a range of a layout: one of the four kinds that a layout
/// names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LayoutKind {
    /// `Kind::ReadExecute`: the text of the image.
    ReadExecute,
    /// `Kind::ReadOnly`: the read-only data of the image, the device tree.
    ReadOnly,
    /// `Kind::ReadWrite`: data, BSS, stacks and the pools of the kernel
    /// tables.
    ReadWrite,
    /// `Kind::Device`: the registers of the kernel's devices.
    Device,
}

/// A range of a layout, mapped at its physical address with its kind.
#[derive(Clone, Copy, Debug)]
pub struct LayoutRange {
    /// The physical range.
    pub range: PhysRange,
    /// Its kind.
    pub kind: LayoutKind,
}

/// The layout that the board gives [`kernel_map`]: the first `count` of
/// `ranges`, a count above 16 reading as 16, and the guard pages, each named
/// by an address in it. The board writes the ranges of whole pages, no two
/// sharing a page and none holding a guard page, which `kernel_map` checks.
#[derive(Clone, Copy, Debug)]
pub struct Layout<'a> {
    /// The ranges, in any order.
    pub ranges: [LayoutRange; MAX_LAYOUT_RANGES],
    /// The number of ranges.
    pub count: usize,
    /// An address in each guard page.
    pub guards: &'a [u64],
}

/// The plan of [`kernel_map`], given one step at a time by `next`, in the
/// order of the map plans of the contract: the leaves in address order, one
/// 1 GiB slot after the other. Under a new level 2 table, each new level 3
/// table with its pages comes first, then the level 2 table with its
/// entries, `Fence` and the store of its table descriptor into the root.
/// Under a level 2 table of the set, each 2 MiB slot is the store of its
/// block, the stores of its pages into a level 3 table of the set, or a new
/// level 3 table with its pages, `Fence` and the store of its table
/// descriptor. `Sync` ends the plan.
///
/// The plan borrows the set for its lifetime and reads only entries that
/// none of its earlier steps writes: the root entry of a 1 GiB slot at the
/// first step of the slot, before the store into it, and the level 2 and
/// level 3 entries of a 2 MiB slot at the first step of the slot. So the
/// caller may execute each step before it asks for the next.
pub struct KernelMapPlan<'a, const N: usize> {
    /// The lower kernel set, after the write phase.
    set: &'a Tables<N, false>,
    /// The `base` of its pool.
    base: u64,
    /// The position of the plan.
    cursor: MapCursor,
    /// The ranges of the layout, sorted by their start.
    ranges: [LayoutRange; MAX_LAYOUT_RANGES],
    /// The number of ranges.
    count: usize,
}

/// The plan of [`direct_map`], given one step at a time by `next`, in the
/// order and with the reads of [`KernelMapPlan`]. The plan borrows the set
/// and the boot memory map for its lifetime.
pub struct DirectMapPlan<'a, const N: usize> {
    /// The direct map's set, after the write phase.
    set: &'a Tables<N, true>,
    /// The `base` of its pool.
    base: u64,
    /// The position of the plan.
    cursor: MapCursor,
    /// The usable ranges after `range`.
    ranges: AvailableRanges<'a>,
    /// The usable range from which the plan looks for the leaves of its
    /// 1 GiB slot: the range of the first of them.
    range: Span,
}

/// A nonempty range of physical addresses `[start, start + len)` whose end
/// fits in 64 bits; only [`PhysRange::new`] builds one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhysRange {
    /// The first address.
    start: u64,
    /// The length, not 0.
    len: u64,
}

/// The owner of an exclusion and of the pages that it excludes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Excluder {
    /// A firmware reservation, `no-map`, `reusable` or neither.
    Firmware,
    /// The boot storage of the kernel image, with its BSS, its stacks and
    /// the pools of the kernel tables.
    Image,
    /// Another span of boot storage, such as the device tree.
    BootStorage,
}

/// A range that the page ownership table excludes, as the boot wiring
/// gives it from the boot memory map: a physical range, which need not lie
/// on page boundaries, with its owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Exclusion {
    /// The range.
    pub range: PhysRange,
    /// Its owner.
    pub owner: Excluder,
}

/// The state of a holder.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HoldState {
    /// The pages are held at once, not yet zeroed or not yet published.
    Reserved,
    /// The pages are zeroed and published.
    Published,
}

/// The owner of a managed page.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Owner {
    /// No one holds the page.
    Free,
    /// An exclusion holds the page.
    Excluded(Excluder),
    /// A holder: its owner identity, its generation and its state.
    Held(u64, u64, HoldState),
}

/// What an extent records: its pages free, or held by one holder, with its
/// owner identity, its generation and its state.
#[derive(Clone, Copy)]
enum Holding {
    Free,
    Held(u64, u64, HoldState),
}

/// A range of whole pages of the bank of index `bank`, in the address order
/// of the banks, with one holding.
#[derive(Clone, Copy)]
struct Extent {
    range: PhysRange,
    bank: usize,
    holding: Holding,
}

/// The generation of the next allocation or reservation, or exhausted once
/// the generation `2^64 - 1` has been given.
#[derive(Clone, Copy)]
enum Counter {
    Next(u64),
    Exhausted,
}

/// The page ownership table: one owner for every page of its managed
/// banks, free, the owner of an exclusion or a holder. A page in an extent
/// has the owner of the extent, and a page of a bank in no extent the first
/// owner, in the order firmware, image, boot storage, of the exclusion
/// records that touch it. The table records at most `E` extents, free and
/// held together, and `X` exclusion records; the kernel root's has
/// `EXTENTS` and `EXCLUSION_RECORDS`. Its fields are private, so only its
/// entries change it.
pub struct Ownership<const E: usize, const X: usize> {
    /// The arena, not 0.
    arena: u64,
    /// The managed banks, in address order.
    banks: [PhysRange; E],
    /// The number of banks.
    bank_count: usize,
    /// The extents, in address order.
    extents: [Extent; E],
    /// The number of extents.
    extent_count: usize,
    /// The exclusion records, in the order given.
    exclusions: [Exclusion; X],
    /// The number of exclusion records.
    exclusion_count: usize,
    /// The generation counter.
    counter: Counter,
}

/// A receipt: the arena, the owner identity, the generation and the range
/// of an allocation. It is bookkeeping, not authority: each entry that
/// takes one checks it against the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Allocation {
    /// The arena of the table.
    pub arena: u64,
    /// The owner identity.
    pub owner: u64,
    /// The generation.
    pub generation: u64,
    /// The pages.
    pub range: PhysRange,
}

/// The direction of a placement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// From the lowest free extent, at the lowest aligned start.
    Low,
    /// From the highest free extent, at the highest aligned start.
    High,
}

/// Where a request is placed, the caller's choice: a direction and an
/// optional window, a physical range outside which no page is taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Placement {
    /// The direction of the scan.
    pub direction: Direction,
    /// The window, if any.
    pub window: Option<PhysRange>,
}

/// The pages that [`Ownership::choose`] gives an owner identity, which
/// [`Ownership::assign`] takes once the caller has zeroed them. Only
/// `choose` builds one.
#[derive(Debug)]
pub struct Choice {
    /// The owner identity of the request.
    owner: u64,
    /// The pages.
    range: PhysRange,
}

/// Pages that [`Ownership::reserve`] holds at once, reserved, whose bytes
/// the caller has not zeroed yet: their allocation, whether a zeroing was
/// attempted, and the count of failed zeroings. A reservation that its
/// holder drops keeps its pages held.
#[derive(Debug)]
pub(crate) struct Reservation {
    /// The allocation of the pages.
    allocation: Allocation,
    /// Whether a zeroing was attempted.
    attempted: bool,
    /// The failed zeroings, a count that stays at `2^64 - 1` once there.
    failures: u64,
}

/// Reserved pages whose zeroing has completed and that are not published
/// yet, with the count of the failed zeroings before it.
#[derive(Debug)]
pub(crate) struct Initialized {
    /// The allocation of the pages.
    allocation: Allocation,
    /// The failed zeroings before the one that completed.
    failures: u64,
}

/// The statistics of a page ownership table. The excluded pages take no
/// extent and count as no managed bytes; reserved pages count as allocated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Stats {
    /// The bytes of the free and held pages.
    pub managed: u64,
    /// The bytes of the free pages.
    pub free: u64,
    /// The bytes of the held pages.
    pub allocated: u64,
    /// The number of holders.
    pub allocations: usize,
    /// The number of free extents.
    pub free_extents: usize,
    /// The bytes of the largest free extent.
    pub largest_free: u64,
    /// The extents in use.
    pub extents: usize,
    /// The capacity of the extents.
    pub capacity: usize,
}

/// The trait of the assertions of rule 6: `CHECK` is ambiguous for a type
/// that implements `Clone`, so such an assertion does not compile.
trait AmbiguousIfClone<A> {
    const CHECK: () = ();
}

impl<T: ?Sized> AmbiguousIfClone<()> for T {}

impl<T: Clone> AmbiguousIfClone<u8> for T {}

// A set is neither `Clone` nor `Copy`: a copy would keep a record of tables
// in use that its pool no longer has.
const _: () = <Tables<1, false> as AmbiguousIfClone<_>>::CHECK;

// A page ownership table is neither `Clone` nor `Copy`: a copy would give
// the same pages twice.
const _: () = <Ownership<1, 1> as AmbiguousIfClone<_>>::CHECK;

// A reservation is neither `Clone` nor `Copy`: a copy kept across a failed
// zeroing could be cancelled as if no zeroing had been attempted.
const _: () = <Reservation as AmbiguousIfClone<_>>::CHECK;

// A packet is neither `Clone` nor `Copy`: it is published once.
const _: () = <Initialized as AmbiguousIfClone<_>>::CHECK;

/// The page descriptor of `kind` at the output address `address`, of
/// which it takes bits 12 to 47.
// Called by the page-table entries of this module and by the modules vm
// and creation of the core, which are planned.
#[allow(dead_code)]
pub(crate) fn descriptor(kind: Kind, address: u64) -> u64 {
    (address & encoding::ADDRESS_MASK) | kind.bits() | encoding::TABLE_OR_PAGE
}

/// The address of `range` in the direct map, `DIRECT_BASE | start`, or
/// none when the range ends above `2^39` and so leaves the window.
pub fn direct_address(range: PhysRange) -> Option<u64> {
    if range.end() <= VA_LIMIT {
        Some(DIRECT_BASE | range.start)
    } else {
        None
    }
}

/// Maps every page of every range of `layout` into the lower kernel set
/// `set`, whose pool is at `base`, at its physical address with the kind of
/// its range, and writes no entry of a guard page. It checks, in this order:
/// the pool; the ranges in the order of their starts, those of one start in
/// the order given, each with its ends off a page (`Alignment`), its end
/// above `2^39` or `2^bits` (`AddressWidth`) and its pages in address order,
/// first the walk (`TableBacking`, `AlreadyMapped`) and then a page that an
/// earlier range or a guard holds (`AlreadyMapped`); and last the tables of
/// the whole plan (`OutOfTables`). The boot wiring calls it once, before the
/// MMU is on.
pub fn kernel_map<'a, const N: usize>(
    set: &'a mut Tables<N, false>,
    layout: Layout<'a>,
    base: u64,
    bits: u8,
) -> Result<KernelMapPlan<'a, N>, TableError> {
    check_pool(N, base, bits)?;
    let count = if layout.count < MAX_LAYOUT_RANGES {
        layout.count
    } else {
        MAX_LAYOUT_RANGES
    };
    let mut ranges = layout.ranges;
    layout::sort_ranges(&mut ranges, count);
    let check = layout::check_layout(set, &ranges, count, layout.guards, base, bits)?;
    let cursor = boot::write_phase(set, check)?;
    Ok(KernelMapPlan {
        set,
        base,
        cursor,
        ranges,
        count,
    })
}

/// Maps every page of every usable range of the boot memory map `memory`
/// into the direct map's set `set`, whose pool is at `base`, at
/// `DIRECT_BASE | pa` as `ReadWrite`: a block at each multiple of 2 MiB with
/// at least 2 MiB of its range left, and a page elsewhere. It checks, in
/// this order: the pool; the usable ranges in address order, each with its
/// ends off a page (`Alignment`), its end above `2^39` or `2^bits`
/// (`AddressWidth`) and its leaves in address order, first the walk
/// (`TableBacking`, `AlreadyMapped`) and then a leaf that an earlier range
/// holds (`AlreadyMapped`); and last the tables of the whole plan
/// (`OutOfTables`). The boot wiring calls it once, before the MMU is on.
pub fn direct_map<'a, const N: usize>(
    set: &'a mut Tables<N, true>,
    memory: &'a MemoryPlan,
    base: u64,
    bits: u8,
) -> Result<DirectMapPlan<'a, N>, TableError> {
    check_pool(N, base, bits)?;
    let check = direct::check_usable(set, memory.available_ranges(), base, bits)?;
    let cursor = boot::write_phase(set, check)?;
    Ok(DirectMapPlan {
        set,
        base,
        cursor,
        ranges: memory.available_ranges(),
        range: Span { start: 0, size: 0 },
    })
}
