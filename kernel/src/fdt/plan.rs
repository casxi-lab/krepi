//! The boot memory map: the RAM banks of a discovery with the boot storage
//! and the firmware reservations excluded by whole pages, and its queries.
//!
//! Feature: krepi.platform.device-tree
//!
//! The map describes memory: it allocates nothing and maps nothing. The
//! kernel direct map and the page ownership table of the page-tables
//! component take its usable ranges and its reservations as values. The
//! entries check their rules in the error order of the boot memory map and
//! fill a local map while they check, which they return only when every
//! rule holds.

mod available;

use super::span::{EMPTY, in_one_range, part, prefix, touches_any, valid};
use super::{
    AvailableRanges, BANKS, BOOT_SPANS, BootMemory, Cursor, FIRMWARE, MemoryPlan, PlanError,
    ReservedRegion, Span,
};

#[cfg(test)]
mod tests;

/// The page of the boot memory map, 4 KiB.
const PAGE_SIZE: u64 = 0x1000;

/// The most bytes of a managed window of [`MemoryPlan::new`], 128 MiB.
const MAX_WINDOW_BYTES: u64 = 0x800_0000;

/// The most bytes of the RAM banks together, 16 GiB.
const MAX_RAM_BYTES: u64 = 0x4_0000_0000;

/// The boot memory map before an entry adds anything.
const NO_PLAN: MemoryPlan = MemoryPlan {
    ram: [EMPTY; BANKS],
    ram_count: 0,
    managed: [EMPTY; BANKS],
    managed_count: 0,
    reserved: [EMPTY; BOOT_SPANS + FIRMWARE],
    boot_count: 0,
    reserved_count: 0,
};

/// A span that the boot memory map takes: of size 0, `InvalidRange`; whose
/// end leaves 64 bits, `Overflow`.
fn check_span(span: Span) -> Result<(), PlanError> {
    if span.size == 0 {
        return Err(PlanError::InvalidRange);
    }
    if !valid(span) {
        return Err(PlanError::Overflow);
    }
    Ok(())
}

/// The pages of a span, from its start rounded down to its end rounded up
/// to whole pages: the span itself ([`check_span`]); then its end rounded
/// up, `Overflow` when it leaves 64 bits.
fn pages_of(span: Span) -> Result<Span, PlanError> {
    check_span(span)?;
    let start = span.start & !(PAGE_SIZE - 1);
    let stop = match (span.start + span.size).checked_add(PAGE_SIZE - 1) {
        Some(end) => end & !(PAGE_SIZE - 1),
        None => return Err(PlanError::Overflow),
    };
    Ok(Span {
        start,
        size: stop - start,
    })
}

/// The RAM banks in input order: each span ([`check_span`]), then sharing
/// an address with an earlier bank, `Overlap`.
fn add_banks(plan: &mut MemoryPlan, ram: &[Span]) -> Result<(), PlanError> {
    let mut index = 0;
    while index < ram.len() {
        let bank = ram[index];
        check_span(bank)?;
        if touches_any(prefix(&plan.ram, plan.ram_count), bank) {
            return Err(PlanError::Overlap);
        }
        plan.ram[plan.ram_count] = bank;
        plan.ram_count += 1;
        index += 1;
    }
    Ok(())
}

/// The bank at `index` moved down among the banks before it, which are
/// sorted by their start, to its place.
fn insert_bank(banks: &mut [Span; BANKS], index: usize) {
    let mut at = index;
    while at > 0 && banks[at - 1].start > banks[at].start {
        let moved = banks[at];
        banks[at] = banks[at - 1];
        banks[at - 1] = moved;
        at -= 1;
    }
}

/// The first `count` banks sorted by their start, by insertion. Disjoint
/// nonempty banks have distinct starts, so the order is unique.
fn sort_banks(banks: &mut [Span; BANKS], count: usize) {
    let mut index = 1;
    while index < count {
        insert_bank(banks, index);
        index += 1;
    }
}

/// The RAM banks in address order, one at a time: the sum of the banks so
/// far, `Overflow`, then above 16 GiB, `ArenaTooLarge`; then the start of
/// the bank rounded up to a page, `Overflow`. The complete pages of a bank
/// are its managed bank; a bank without one contributes none.
fn admit_banks(plan: &mut MemoryPlan) -> Result<(), PlanError> {
    let mut sum: u64 = 0;
    let mut index = 0;
    while index < plan.ram_count {
        let bank = plan.ram[index];
        sum = match sum.checked_add(bank.size) {
            Some(sum) => sum,
            None => return Err(PlanError::Overflow),
        };
        if sum > MAX_RAM_BYTES {
            return Err(PlanError::ArenaTooLarge);
        }
        let start = match bank.start.checked_add(PAGE_SIZE - 1) {
            Some(start) => start & !(PAGE_SIZE - 1),
            None => return Err(PlanError::Overflow),
        };
        let stop = (bank.start + bank.size) & !(PAGE_SIZE - 1);
        if start < stop {
            plan.managed[plan.managed_count] = Span {
                start,
                size: stop - start,
            };
            plan.managed_count += 1;
        }
        index += 1;
    }
    Ok(())
}

/// The first `count` spans of boot storage in input order: its pages
/// ([`pages_of`]); not inside one bank, `OutsideRam`; sharing a page with
/// earlier boot storage, `Overlap`.
fn add_boot(plan: &mut MemoryPlan, boot: &[Span], count: usize) -> Result<(), PlanError> {
    let mut index = 0;
    while index < count {
        let pages = pages_of(boot[index])?;
        if !in_one_range(prefix(&plan.ram, plan.ram_count), pages) {
            return Err(PlanError::OutsideRam);
        }
        if touches_any(prefix(&plan.reserved, plan.boot_count), pages) {
            return Err(PlanError::Overlap);
        }
        plan.reserved[plan.boot_count] = pages;
        plan.boot_count += 1;
        index += 1;
    }
    plan.reserved_count = plan.boot_count;
    Ok(())
}

/// The firmware reservations in input order: its pages ([`pages_of`]);
/// sharing a page with the boot storage, `Overlap`. Their flags do not
/// matter: every page of every reservation is excluded.
fn add_firmware(plan: &mut MemoryPlan, firmware: &[ReservedRegion]) -> Result<(), PlanError> {
    let mut index = 0;
    while index < firmware.len() {
        let pages = pages_of(firmware[index].span)?;
        if touches_any(prefix(&plan.reserved, plan.boot_count), pages) {
            return Err(PlanError::Overlap);
        }
        plan.reserved[plan.reserved_count] = pages;
        plan.reserved_count += 1;
        index += 1;
    }
    Ok(())
}

/// The boot memory map that manages every complete page of every bank,
/// with the first `count` spans of `boot` as boot storage, where `count`
/// is the number of spans that the caller gives: steps 2 to 7 of the error
/// order of the boot memory map.
fn build(
    ram: &[Span],
    boot: &[Span],
    count: usize,
    firmware: &[ReservedRegion],
) -> Result<MemoryPlan, PlanError> {
    if ram.is_empty()
        || ram.len() > BANKS
        || count == 0
        || count > BOOT_SPANS
        || firmware.len() > FIRMWARE
    {
        return Err(PlanError::Capacity);
    }
    let mut plan = NO_PLAN;
    add_banks(&mut plan, ram)?;
    sort_banks(&mut plan.ram, plan.ram_count);
    admit_banks(&mut plan)?;
    if plan.managed_count == 0 {
        return Err(PlanError::Alignment);
    }
    add_boot(&mut plan, boot, count)?;
    add_firmware(&mut plan, firmware)?;
    Ok(plan)
}

/// Step 1 of the error order of the boot memory map: the managed window
/// ([`check_span`]); its ends not on pages, `Alignment`; above 128 MiB,
/// `ArenaTooLarge`.
fn check_window(window: Span) -> Result<(), PlanError> {
    check_span(window)?;
    if window.start % PAGE_SIZE != 0 || (window.start + window.size) % PAGE_SIZE != 0 {
        return Err(PlanError::Alignment);
    }
    if window.size > MAX_WINDOW_BYTES {
        return Err(PlanError::ArenaTooLarge);
    }
    Ok(())
}

/// Step 8 of the error order of the boot memory map: the map `plan` that
/// manages only `window`, or `OutsideRam` when the window lies outside
/// every single bank.
fn manage_window(plan: MemoryPlan, window: Span) -> Result<MemoryPlan, PlanError> {
    if !plan.contains_ram(window) {
        return Err(PlanError::OutsideRam);
    }
    let mut plan = plan;
    plan.managed[0] = window;
    plan.managed_count = 1;
    Ok(plan)
}

/// The sum of the sizes of `spans`, which a boot memory map that an entry
/// built bounds by 16 GiB.
fn sum_sizes(spans: &[Span]) -> u64 {
    let mut sum = 0;
    let mut index = 0;
    while index < spans.len() {
        sum += spans[index].size;
        index += 1;
    }
    sum
}

impl MemoryPlan {
    /// The boot memory map that manages every complete page of every bank,
    /// from the RAM ranges `ram` of a discovery, the boot storage table
    /// `boot` of the board and the reserved regions `firmware` of the
    /// discovery as firmware reservations: no bank or more than 32, no boot
    /// storage or more than 4 spans, more than 128 firmware reservations,
    /// `Capacity`; each bank in input order, `InvalidRange`, `Overflow` or
    /// `Overlap`; the banks in address order, `Overflow` or `ArenaTooLarge`;
    /// no complete page in any bank, `Alignment`; each span of boot storage
    /// in input order, `InvalidRange`, `Overflow`, `OutsideRam` or
    /// `Overlap`; each firmware reservation in input order, `InvalidRange`,
    /// `Overflow` or `Overlap`.
    pub fn all_ram(
        ram: &[Span],
        boot: &[Span],
        firmware: &[ReservedRegion],
    ) -> Result<MemoryPlan, PlanError> {
        build(ram, boot, boot.len(), firmware)
    }

    /// The boot memory map of [`MemoryPlan::all_ram`] that manages only
    /// `window`, a span of whole pages of at most 128 MiB inside one bank:
    /// the window, `InvalidRange`, `Overflow`, `Alignment` or
    /// `ArenaTooLarge`; then the errors of [`MemoryPlan::all_ram`]; then the
    /// window outside every single bank, `OutsideRam`.
    pub fn new(
        window: Span,
        ram: &[Span],
        boot: &[Span],
        firmware: &[ReservedRegion],
    ) -> Result<MemoryPlan, PlanError> {
        check_window(window)?;
        let plan = build(ram, boot, boot.len(), firmware)?;
        manage_window(plan, window)
    }

    /// [`MemoryPlan::new`] with the RAM ranges of the boot memory `memory`,
    /// the boot storage of its image, its tree and then the further spans
    /// `more` of the board, such as the boot bundle, in this order, and its
    /// reserved regions as firmware reservations; more than two further
    /// spans make more than 4 spans of boot storage, `Capacity`.
    pub fn from_boot_memory(
        memory: &BootMemory,
        window: Span,
        more: &[Span],
    ) -> Result<MemoryPlan, PlanError> {
        check_window(window)?;
        let mut boot = [memory.image, memory.dtb, EMPTY, EMPTY];
        if more.len() <= 2 {
            let mut index = 0;
            while index < more.len() {
                boot[2 + index] = more[index];
                index += 1;
            }
        }
        let plan = build(memory.ram(), &boot, 2 + more.len(), memory.reserved())?;
        manage_window(plan, window)
    }

    /// The managed banks, in address order: the complete pages of each
    /// bank, or the window of [`MemoryPlan::new`].
    pub fn managed_banks(&self) -> &[Span] {
        prefix(&self.managed, self.managed_count)
    }

    /// The RAM banks, sorted by their start.
    pub fn ram(&self) -> &[Span] {
        prefix(&self.ram, self.ram_count)
    }

    /// The reservations: the pages of the boot storage, in input order, and
    /// then those of the firmware reservations, in input order.
    pub fn reservations(&self) -> &[Span] {
        prefix(&self.reserved, self.reserved_count)
    }

    /// The pages of the boot storage, in input order.
    pub fn boot_ranges(&self) -> &[Span] {
        prefix(&self.reserved, self.boot_count)
    }

    /// The pages of the firmware reservations, in input order.
    pub fn firmware_ranges(&self) -> &[Span] {
        part(&self.reserved, self.boot_count, self.reserved_count)
    }

    /// The sum of the sizes of the banks.
    pub fn described_bytes(&self) -> u64 {
        sum_sizes(self.ram())
    }

    /// The sum of the sizes of the managed banks.
    pub fn managed_bytes(&self) -> u64 {
        sum_sizes(self.managed_banks())
    }

    /// Whether one bank holds `range`; false for a span of size 0 or one
    /// whose end leaves 64 bits, which lies in no bank.
    pub fn contains_ram(&self, range: Span) -> bool {
        range.size != 0 && valid(range) && in_one_range(self.ram(), range)
    }

    /// Whether one bank holds `range` and no reservation touches it.
    pub fn is_available(&self, range: Span) -> bool {
        self.contains_ram(range) && !touches_any(self.reservations(), range)
    }

    /// Whether a managed bank holds `range` and it is available.
    pub fn permits_backing(&self, range: Span) -> bool {
        in_one_range(self.managed_banks(), range) && self.is_available(range)
    }

    /// The usable ranges, in address order: the managed banks without the
    /// union of the reservations, each a maximal range of whole pages inside
    /// one managed bank.
    pub fn available_ranges(&self) -> AvailableRanges<'_> {
        AvailableRanges {
            managed: self.managed_banks(),
            reservations: self.reservations(),
            cursor: Cursor { bank: 0, at: 0 },
        }
    }
}
