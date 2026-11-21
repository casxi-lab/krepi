//! The page ownership table: its initialization from the managed banks and
//! the exclusions of the boot memory map, the owner of a page and the
//! statistics.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The cut of an exclusion in a bank is the pages of the bank that it
//! touches: its start rounded down and its end rounded up to a page, within
//! the bank. The free extents of a bank are the maximal runs of its pages
//! that no cut holds, found by a cursor that moves forward through the
//! bank: where cuts hold the cursor, it moves to the furthest end of those;
//! elsewhere the run from it to the nearest start of a cut above it, or to
//! the end of the bank, is an extent.

mod placement;
mod receipts;

use super::{
    Counter, Excluder, Exclusion, Extent, Holding, Owner, Ownership, OwnershipError, PAGE_SIZE,
    PhysRange, Stats,
};

/// The filler of the unused slots of the banks.
const NO_RANGE: PhysRange = PhysRange { start: 0, len: 0 };

/// The filler of the unused slots of the extents.
const NO_EXTENT: Extent = Extent {
    range: NO_RANGE,
    bank: 0,
    holding: Holding::Free,
};

/// The filler of the unused slots of the exclusion records.
const NO_EXCLUSION: Exclusion = Exclusion {
    range: NO_RANGE,
    owner: Excluder::Firmware,
};

impl<const E: usize, const X: usize> Ownership<E, X> {
    /// The table of the managed banks `banks` and the exclusions
    /// `exclusions` of the boot memory map in the arena `arena`. It checks,
    /// in this order: a bank off page boundaries, `InvalidAlignment`; the
    /// arena 0, `InvalidArena`; no bank, `InvalidRange`; more banks than `E`,
    /// `MetadataExhausted`; two banks that overlap, `InvalidRange`; more
    /// exclusions than `X`, then more extents than `E`, `MetadataExhausted`.
    /// The table keeps the banks in address order, a free extent for each
    /// maximal run of the pages of a bank that no exclusion touches, each
    /// exclusion in a record of its own, and the generation counter at 1.
    /// The boot wiring calls it once, for the kernel root.
    pub fn new(
        arena: u64,
        banks: &[PhysRange],
        exclusions: &[Exclusion],
    ) -> Result<Ownership<E, X>, OwnershipError> {
        if !on_pages(banks) {
            return Err(OwnershipError::InvalidAlignment);
        }
        if arena == 0 {
            return Err(OwnershipError::InvalidArena);
        }
        if banks.is_empty() {
            return Err(OwnershipError::InvalidRange);
        }
        if banks.len() > E {
            return Err(OwnershipError::MetadataExhausted);
        }
        if any_overlap(banks) {
            return Err(OwnershipError::InvalidRange);
        }
        if exclusions.len() > X {
            return Err(OwnershipError::MetadataExhausted);
        }
        let mut sorted = [NO_RANGE; E];
        sort_banks(&mut sorted, banks);
        let mut records = [NO_EXCLUSION; X];
        copy_exclusions(&mut records, exclusions);
        let mut extents = [NO_EXTENT; E];
        let extent_count = initial_extents(&mut extents, &sorted, banks.len(), exclusions)?;
        Ok(Ownership {
            arena,
            banks: sorted,
            bank_count: banks.len(),
            extents,
            extent_count,
            exclusions: records,
            exclusion_count: exclusions.len(),
            counter: Counter::Next(1),
        })
    }

    /// The owner of the page that holds `address`: the holding of the extent
    /// that holds the page; for a page of a bank in no extent, the first
    /// owner, in the order firmware, image, boot storage, of the exclusion
    /// records that touch it; none for a page of no bank. It writes nothing.
    // Called by the modules of the core that take pages, which are planned.
    #[allow(dead_code)]
    pub(crate) fn owner(&self, address: u64) -> Option<Owner> {
        let page = address & !(PAGE_SIZE - 1);
        if let Some(index) = holding_extent(&self.extents, self.extent_count, page) {
            return Some(self.extents[index].holding.owner());
        }
        if !in_banks(&self.banks, self.bank_count, page) {
            return None;
        }
        match first_excluder(&self.exclusions, self.exclusion_count, page) {
            Some(excluder) => Some(Owner::Excluded(excluder)),
            None => None,
        }
    }

    /// The statistics of the table. It writes nothing.
    // Called by the modules of the core that take pages, which are planned.
    #[allow(dead_code)]
    pub(crate) fn stats(&self) -> Stats {
        extent_stats(&self.extents, self.extent_count)
    }

    /// The extents that the capacity has free beyond those in use.
    fn room(&self) -> usize {
        if self.extent_count < E {
            E - self.extent_count
        } else {
            0
        }
    }
}

impl Holding {
    /// The owner of the pages of an extent of the holding.
    // A value, not the place in the extents: Aeneas refuses a `match` that
    // binds the fields of an enumeration in an element of a borrowed array.
    fn owner(self) -> Owner {
        match self {
            Holding::Free => Owner::Free,
            Holding::Held(owner, generation, state) => Owner::Held(owner, generation, state),
        }
    }
}

/// Whether the pages of a holding are free.
fn is_free(holding: Holding) -> bool {
    match holding {
        Holding::Free => true,
        Holding::Held(..) => false,
    }
}

/// Whether every bank starts and ends on a page boundary.
fn on_pages(banks: &[PhysRange]) -> bool {
    let mut index = 0;
    while index < banks.len() {
        if banks[index].start % PAGE_SIZE != 0 || banks[index].end() % PAGE_SIZE != 0 {
            return false;
        }
        index += 1;
    }
    true
}

/// Whether a bank after the one at `index` overlaps it.
fn overlaps_later(banks: &[PhysRange], index: usize) -> bool {
    let mut later = index + 1;
    while later < banks.len() {
        if banks[index].overlaps(banks[later]) {
            return true;
        }
        later += 1;
    }
    false
}

/// Whether two of the banks overlap.
fn any_overlap(banks: &[PhysRange]) -> bool {
    let mut index = 0;
    while index < banks.len() {
        if overlaps_later(banks, index) {
            return true;
        }
        index += 1;
    }
    false
}

/// Puts `bank` among the first `count` of `sorted`, which are in address
/// order, after those that start below it.
fn insert_bank<const E: usize>(sorted: &mut [PhysRange; E], count: usize, bank: PhysRange) {
    let mut at = count;
    while at > 0 && sorted[at - 1].start > bank.start {
        sorted[at] = sorted[at - 1];
        at -= 1;
    }
    sorted[at] = bank;
}

/// Writes the banks into `sorted` in address order, by insertion.
fn sort_banks<const E: usize>(sorted: &mut [PhysRange; E], banks: &[PhysRange]) {
    let mut index = 0;
    while index < banks.len() && index < E {
        insert_bank(sorted, index, banks[index]);
        index += 1;
    }
}

/// Writes the exclusions into the records in the order given.
fn copy_exclusions<const X: usize>(records: &mut [Exclusion; X], exclusions: &[Exclusion]) {
    let mut index = 0;
    while index < exclusions.len() && index < X {
        records[index] = exclusions[index];
        index += 1;
    }
}

/// The cut of `exclusion` in `bank`, a bank on page boundaries: the pages
/// `[start, stop)` of the bank that it touches, or none when it does not
/// overlap the bank.
fn cut(exclusion: PhysRange, bank: PhysRange) -> Option<(u64, u64)> {
    if !exclusion.overlaps(bank) {
        return None;
    }
    let down = exclusion.start & !(PAGE_SIZE - 1);
    let start = if down > bank.start { down } else { bank.start };
    // An end below that of the bank rounds up to at most the end of the
    // bank, so the rounding does not pass 64 bits.
    let stop = if exclusion.end() < bank.end() {
        (exclusion.end() + (PAGE_SIZE - 1)) & !(PAGE_SIZE - 1)
    } else {
        bank.end()
    };
    Some((start, stop))
}

/// The cuts in `bank` around `at`: the furthest stop of those that hold
/// `at`, or `at` when none holds it, and the nearest start of those above
/// `at`, or the end of the bank when none starts between them.
fn cuts_at(exclusions: &[Exclusion], bank: PhysRange, at: u64) -> (u64, u64) {
    let mut reach = at;
    let mut nearest = bank.end();
    let mut index = 0;
    while index < exclusions.len() {
        if let Some((start, stop)) = cut(exclusions[index].range, bank) {
            if start <= at && stop > reach {
                reach = stop;
            }
            if at < start && start < nearest {
                nearest = start;
            }
        }
        index += 1;
    }
    (reach, nearest)
}

/// Writes the free extents of `bank`, the bank of index `index`, after the
/// first `used` extents, and gives the extents in use after them;
/// `MetadataExhausted` when one does not fit.
fn bank_extents<const E: usize>(
    extents: &mut [Extent; E],
    mut used: usize,
    index: usize,
    bank: PhysRange,
    exclusions: &[Exclusion],
) -> Result<usize, OwnershipError> {
    let mut at = bank.start;
    while at < bank.end() {
        let (reach, stop) = cuts_at(exclusions, bank, at);
        if reach > at {
            at = reach;
        } else {
            if used >= E {
                return Err(OwnershipError::MetadataExhausted);
            }
            extents[used] = Extent {
                range: PhysRange {
                    start: at,
                    len: stop - at,
                },
                bank: index,
                holding: Holding::Free,
            };
            used += 1;
            at = stop;
        }
    }
    Ok(used)
}

/// Writes the free extents of the first `count` of `banks`, in address
/// order, from the first slot, and gives their number; `MetadataExhausted`
/// when they need more than `E`.
fn initial_extents<const E: usize>(
    extents: &mut [Extent; E],
    banks: &[PhysRange; E],
    count: usize,
    exclusions: &[Exclusion],
) -> Result<usize, OwnershipError> {
    let mut used = 0;
    let mut bank = 0;
    while bank < count && bank < E {
        used = bank_extents(extents, used, bank, banks[bank], exclusions)?;
        bank += 1;
    }
    Ok(used)
}

/// Whether `range` holds the whole page at `page`, a multiple of 4 KiB.
fn holds_page(range: PhysRange, page: u64) -> bool {
    range.start <= page && page < range.end() && range.end() - page >= PAGE_SIZE
}

/// Whether `range` shares an address with the page at `page`, a multiple of
/// 4 KiB.
fn touches_page(range: PhysRange, page: u64) -> bool {
    range.start <= page + (PAGE_SIZE - 1) && page < range.end()
}

/// The first of the first `count` extents that holds the page at `page`.
fn holding_extent<const E: usize>(extents: &[Extent; E], count: usize, page: u64) -> Option<usize> {
    let mut index = 0;
    while index < count && index < E {
        if holds_page(extents[index].range, page) {
            return Some(index);
        }
        index += 1;
    }
    None
}

/// Whether one of the first `count` banks holds the page at `page`.
fn in_banks<const E: usize>(banks: &[PhysRange; E], count: usize, page: u64) -> bool {
    let mut index = 0;
    while index < count && index < E {
        if holds_page(banks[index], page) {
            return true;
        }
        index += 1;
    }
    false
}

/// The place of an owner in the order firmware, image, boot storage.
fn rank(excluder: Excluder) -> u8 {
    match excluder {
        Excluder::Firmware => 0,
        Excluder::Image => 1,
        Excluder::BootStorage => 2,
    }
}

/// Whether `excluder` comes before `first`, none coming last.
fn precedes(excluder: Excluder, first: Option<Excluder>) -> bool {
    match first {
        Some(other) => rank(excluder) < rank(other),
        None => true,
    }
}

/// The first owner, in the order firmware, image, boot storage, of the
/// first `count` records that touch the page at `page`, or none when none
/// touches it.
fn first_excluder<const X: usize>(
    records: &[Exclusion; X],
    count: usize,
    page: u64,
) -> Option<Excluder> {
    let mut first = None;
    let mut index = 0;
    while index < count && index < X {
        let record = records[index];
        if touches_page(record.range, page) && precedes(record.owner, first) {
            first = Some(record.owner);
        }
        index += 1;
    }
    first
}

/// The statistics of the first `count` extents and the capacity `E`.
fn extent_stats<const E: usize>(extents: &[Extent; E], count: usize) -> Stats {
    let mut stats = Stats {
        managed: 0,
        free: 0,
        allocated: 0,
        allocations: 0,
        free_extents: 0,
        largest_free: 0,
        extents: count,
        capacity: E,
    };
    let mut index = 0;
    while index < count && index < E {
        let len = extents[index].range.len;
        stats.managed += len;
        if is_free(extents[index].holding) {
            stats.free += len;
            stats.free_extents += 1;
            if len > stats.largest_free {
                stats.largest_free = len;
            }
        } else {
            stats.allocated += len;
            stats.allocations += 1;
        }
        index += 1;
    }
    stats
}
