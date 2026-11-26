//! The host tests of the boot memory map: Pi 5 shaped banks, the rounded
//! exclusions, the boot storage of QEMU virt, invalid windows and banks,
//! adjacent banks and holes, boot storage and firmware reservations on
//! shared pages, the capacities, every bank of a full map and the usable
//! ranges against a model of pages.
//!
//! Feature: krepi.platform.device-tree

extern crate std;

use super::*;
use std::vec::Vec;

// The copy of the boot memory before its profile became a value keeps the
// lines of its source; the suffix of its names makes some of them longer
// than the formatter allows.
#[rustfmt::skip]
pub(in crate::fdt) mod before;

// The copy of the entry on a boot memory before it checked the number of
// further spans right after the window.
mod old;

const RAM: Span = Span {
    start: 0,
    size: 0x0800_0000,
};
const IMAGE: Span = Span {
    start: 0x80000,
    size: 0x38000,
};
const DTB: Span = Span {
    start: 0x200000,
    size: 80596,
};
const ATF: ReservedRegion = reserved(0, 0x80000);

const fn reserved(start: u64, size: u64) -> ReservedRegion {
    ReservedRegion {
        span: Span { start, size },
        no_map: true,
        reusable: false,
    }
}

fn span(start: u64, size: u64) -> Span {
    Span { start, size }
}

/// The usable ranges of a boot memory map, in order.
fn available(plan: &MemoryPlan) -> Vec<Span> {
    let mut ranges = plan.available_ranges();
    let mut spans = Vec::new();
    while let Some(range) = ranges.next() {
        spans.push(range);
    }
    spans
}

#[test]
fn pi5_shaped_banks_keep_holes_high_ram_and_page_exclusions() {
    let banks = [
        span(0, 0x3fc00000),
        span(0x40000000, 0xc0000000),
        span(0x1_0000_0000, 0x1_0000_0000),
    ];
    let memory =
        MemoryPlan::new(RAM, &banks, &[IMAGE, DTB], &[ATF, reserved(0x3fd231e0, 62)]).unwrap();
    assert_eq!(
        memory.boot_ranges(),
        &[span(0x80000, 0x38000), span(0x200000, 0x14000)]
    );
    assert_eq!(
        memory.firmware_ranges(),
        &[span(0, 0x80000), span(0x3fd23000, 0x1000)]
    );
    for blocked in [
        span(0x213000, 4096),
        span(0x3fc00000, 4096),
        span(0x80000, 4096),
    ] {
        assert!(!memory.is_available(blocked));
        assert!(!memory.permits_backing(blocked));
    }
    assert!(memory.is_available(span(0x1_0000_0000, PAGE_SIZE)));
    assert!(!memory.permits_backing(span(0x1_0000_0000, PAGE_SIZE)));
    assert!(memory.permits_backing(span(0x214000, PAGE_SIZE)));
}

/// The allocations of the prototype's page allocator in this test go
/// through the page ownership table of the page-tables component, whose
/// tests cover them; this test keeps the managed bank, the reservations and
/// the backing of the two ranges that those allocations take.
#[test]
fn allocator_consumes_the_same_rounded_boot_and_firmware_exclusions() {
    let memory = MemoryPlan::new(
        span(0x100000, 5 * PAGE_SIZE),
        &[RAM],
        &[IMAGE],
        &[reserved(0x101fff, 2)],
    )
    .unwrap();
    assert_eq!(memory.managed_banks(), &[span(0x100000, 0x5000)]);
    assert_eq!(
        memory.reservations(),
        &[span(0x80000, 0x38000), span(0x101000, 0x2000)]
    );
    assert!(memory.permits_backing(span(0x100000, PAGE_SIZE)));
    assert!(memory.permits_backing(span(0x103000, 2 * PAGE_SIZE)));
}

#[test]
fn qemu_prefix_is_reserved_without_truncating_installed_ram() {
    let arena = span(0x40000000, RAM.size);
    let memory = MemoryPlan::new(
        arena,
        &[span(arena.start, 4097 * 1024 * 1024)],
        &[span(arena.start, 0x300000)],
        &[],
    )
    .unwrap();
    assert!(!memory.permits_backing(span(arena.start, PAGE_SIZE)));
    assert!(memory.permits_backing(span(0x40300000, PAGE_SIZE)));
    assert!(memory.is_available(span(0x1_0000_0000, PAGE_SIZE)));
    assert!(!memory.permits_backing(span(0x48000000, PAGE_SIZE)));
}

#[test]
fn rejects_empty_overflowing_unaligned_and_oversized_mapping_windows() {
    for (arena, error) in [
        (span(0, 0), PlanError::InvalidRange),
        (span(u64::MAX, 1), PlanError::Overflow),
        (span(1, 4096), PlanError::Alignment),
        (span(0, 4097), PlanError::Alignment),
        (span(0, RAM.size + PAGE_SIZE), PlanError::ArenaTooLarge),
    ] {
        assert_eq!(
            MemoryPlan::new(arena, &[RAM], &[IMAGE], &[]).unwrap_err(),
            error
        );
    }
}

#[test]
fn rejects_invalid_overlapping_or_missing_ram_banks() {
    for (banks, error) in [
        ([RAM, span(0, 0)], PlanError::InvalidRange),
        ([RAM, span(u64::MAX, 1)], PlanError::Overflow),
        ([RAM, span(4096, 4096)], PlanError::Overlap),
        ([span(0, 4096), span(8192, 4096)], PlanError::OutsideRam),
    ] {
        assert_eq!(
            MemoryPlan::new(RAM, &banks, &[IMAGE], &[]).unwrap_err(),
            error
        );
    }
}

#[test]
fn neither_adjacent_banks_nor_holes_can_supply_one_allocation() {
    let banks = [
        span(0, 0x200000),
        span(0x200000, 0x200000),
        span(0x800000, 0x100000),
    ];
    let memory = MemoryPlan::new(banks[0], &banks, &[IMAGE], &[]).unwrap();
    assert!(!memory.contains_ram(span(0x1ff000, 8192)));
    assert!(!memory.is_available(span(0x3ff000, 0x402000)));
    assert_eq!(
        MemoryPlan::new(span(0, 0x400000), &banks, &[IMAGE], &[]).unwrap_err(),
        PlanError::OutsideRam
    );
}

#[test]
fn boot_storage_must_occupy_disjoint_pages_inside_one_ram_bank() {
    for (boot, error) in [
        ([IMAGE, IMAGE], PlanError::Overlap),
        ([IMAGE, span(0xb7fff, 2)], PlanError::Overlap),
        ([IMAGE, span(RAM.size, 1)], PlanError::OutsideRam),
        ([IMAGE, span(0x100000, 0)], PlanError::InvalidRange),
        ([IMAGE, span(u64::MAX - 1, 1)], PlanError::Overflow),
    ] {
        assert_eq!(MemoryPlan::new(RAM, &[RAM], &boot, &[]).unwrap_err(), error);
    }
    assert_eq!(
        MemoryPlan::new(span(4096, 4096), &[span(1, 8192)], &[span(1, 1)], &[]).unwrap_err(),
        PlanError::OutsideRam
    );
}

#[test]
fn rejects_firmware_on_boot_pages_even_without_byte_overlap() {
    let boot = [span(0x80001, 1)];
    assert_eq!(
        MemoryPlan::new(RAM, &[RAM], &boot, &[reserved(0x80fff, 1)]).unwrap_err(),
        PlanError::Overlap
    );
    for (region, error) in [
        (reserved(0, 0), PlanError::InvalidRange),
        (reserved(u64::MAX, 1), PlanError::Overflow),
        (reserved(u64::MAX - 1, 1), PlanError::Overflow),
    ] {
        assert_eq!(
            MemoryPlan::new(RAM, &[RAM], &[IMAGE], &[region]).unwrap_err(),
            error
        );
    }
}

#[test]
fn overlapping_and_reusable_firmware_reservations_stay_excluded() {
    let mut reusable = reserved(0x400001, 1);
    reusable.no_map = false;
    reusable.reusable = true;
    let memory = MemoryPlan::new(
        RAM,
        &[RAM],
        &[IMAGE, DTB],
        &[reusable, reserved(0x400fff, 2)],
    )
    .unwrap();
    assert!(!memory.is_available(span(0x400000, 8192)));
    assert!(memory.permits_backing(span(0x402000, 4096)));
}

/// Boot storage of three copies of the image now fails with `Overlap`,
/// where the prototype, which allowed 2 spans, gave `Capacity`: 4 spans fit
/// and the second shares the pages of the first.
#[test]
fn exact_capacity_is_supported_and_excess_input_is_rejected() {
    let mut banks = [RAM; 32];
    for (index, bank) in banks.iter_mut().enumerate().skip(1) {
        *bank = span(index as u64 * 0x10000000, PAGE_SIZE);
    }
    let regions = [reserved(0x400000, 1); 128];
    let memory = MemoryPlan::new(RAM, &banks, &[IMAGE, DTB], &regions).unwrap();
    assert_eq!(memory.ram().len(), 32);
    assert_eq!(memory.reservations().len(), 130);
    assert!(!memory.permits_backing(span(0x400000, PAGE_SIZE)));
    for (ram, boot, firmware) in [
        (&[][..], &[IMAGE][..], &[][..]),
        (&[RAM][..], &[][..], &[][..]),
        (&[RAM; 33][..], &[IMAGE][..], &[][..]),
        (&[RAM][..], &[IMAGE][..], &[ATF; 129][..]),
    ] {
        assert_eq!(
            MemoryPlan::new(RAM, ram, boot, firmware).unwrap_err(),
            PlanError::Capacity
        );
    }
    assert_eq!(
        MemoryPlan::new(RAM, &[RAM], &[IMAGE; 3], &[]).unwrap_err(),
        PlanError::Overlap
    );
}

/// The prototype also compared the bytes of the usable ranges with the
/// free bytes of a page allocator, which belongs to the page ownership
/// table of the page-tables component; this test compares them with the
/// managed bytes less the four sizes of the exclusions.
#[test]
fn full_ram_registers_all_bank_pages_and_reservation_union() {
    let banks = [
        span(0x100000000, 0x100000000),
        span(0, 0x3fc00000),
        span(0x40000000, 0xc0000000),
    ];
    let memory = MemoryPlan::all_ram(
        &banks,
        &[IMAGE, DTB],
        &[ATF, reserved(0x40002001, 4096), reserved(0x40003000, 1)],
    )
    .unwrap();
    assert_eq!(memory.managed_bytes(), (8 << 30) - (4 << 20));
    assert_eq!(memory.managed_banks().len(), 3);
    assert!(memory.permits_backing(span(0x1fffff000, PAGE_SIZE)));
    assert!(!memory.permits_backing(span(0xfffff000, 2 * PAGE_SIZE)));
    let bytes: u64 = available(&memory).iter().map(|range| range.size).sum();
    assert_eq!(
        bytes,
        memory.managed_bytes() - 0x80000 - 0x38000 - 0x14000 - 8192
    );
}

#[test]
fn partial_bank_pages_are_not_managed_and_total_ram_is_bounded() {
    let memory = MemoryPlan::all_ram(
        &[span(1, 5 * PAGE_SIZE), span(0x10001, 8)],
        &[span(PAGE_SIZE, PAGE_SIZE)],
        &[],
    )
    .unwrap();
    assert_eq!(memory.managed_banks(), &[span(PAGE_SIZE, 4 * PAGE_SIZE)]);
    assert_eq!(available(&memory), [span(2 * PAGE_SIZE, 3 * PAGE_SIZE)]);
    assert_eq!(
        MemoryPlan::all_ram(&[span(0, (16 << 30) + 1)], &[IMAGE], &[]).unwrap_err(),
        PlanError::ArenaTooLarge
    );
}

#[test]
fn available_iterator_matches_page_oracle_across_unsorted_overlapping_exclusions() {
    let banks = [
        span(0, 24 * PAGE_SIZE),
        span(32 * PAGE_SIZE, 24 * PAGE_SIZE),
    ];
    let regions = [
        reserved(9 * PAGE_SIZE, 5 * PAGE_SIZE),
        reserved(5 * PAGE_SIZE, 7 * PAGE_SIZE),
        reserved(22 * PAGE_SIZE, 12 * PAGE_SIZE),
        reserved(40 * PAGE_SIZE + 1, 1),
    ];
    let memory = MemoryPlan::all_ram(&banks, &[span(0, PAGE_SIZE)], &regions).unwrap();
    let spans = available(&memory);
    for page in 0..60 {
        let range = span(page * PAGE_SIZE, PAGE_SIZE);
        let end = range.start + range.size;
        let expected = banks
            .iter()
            .any(|b| b.start <= range.start && end <= b.start + b.size)
            && page != 0
            && !regions
                .iter()
                .any(|r| r.span.start < end && range.start < r.span.start + r.span.size);
        assert_eq!(
            spans
                .iter()
                .filter(|s| s.start <= range.start && end <= s.start + s.size)
                .count(),
            usize::from(expected)
        );
    }
}
