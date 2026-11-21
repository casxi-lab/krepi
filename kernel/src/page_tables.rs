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
// `is_multiple_of` and a comparison where it suggests `saturating_sub`: each
// of those would reach a library function without a model; and a nested
// `if` where it suggests a let chain.
#![allow(
    clippy::collapsible_if,
    clippy::implicit_saturating_sub,
    clippy::manual_is_multiple_of,
    clippy::manual_map,
    clippy::manual_range_contains,
    clippy::match_like_matches_macro,
    clippy::question_mark,
    clippy::redundant_pattern_matching
)]

mod encoding;
mod range;
mod walk;
mod write;

#[cfg(test)]
mod tests;

/// The descriptors of a table.
pub const ENTRIES: usize = 512;

/// The start of the upper region and of the window of the direct map,
/// `2^64 - 2^39`.
pub const DIRECT_BASE: u64 = 0xffff_ff80_0000_0000;

/// The most steps of the plan of `map_page`, `map_block` or `unmap_page`.
pub const MAX_PLAN_STEPS: usize = 7;

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

/// A nonempty range of physical addresses `[start, start + len)` whose end
/// fits in 64 bits; only [`PhysRange::new`] builds one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhysRange {
    /// The first address.
    start: u64,
    /// The length, not 0.
    len: u64,
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
