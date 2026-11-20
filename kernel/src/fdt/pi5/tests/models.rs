//! The RAM models of the Pi 5: hand-over trees of the 1, 2, 4 and 16 GB
//! models with the RAM ranges that the contract infers from the 8 GB
//! measurement, and the 8 GB hand-over tree with the region of 62 bytes in
//! its hole, through the discovery and the boot memory map.
//!
//! Feature: krepi.platform.device-tree
//!
//! Every model has RAM from address 0 up to its installed size, with ranges
//! divided at 1 GiB and at 4 GiB and a hole of 4 MiB below 1 GiB. The
//! expected ranges, sums and usable ranges below are written from the
//! table of the contract.

use super::*;
use crate::fdt::{MemoryPlan, ReservedRegion};

const GIB: u64 = 0x4000_0000;

/// The hole of 4 MiB below 1 GiB.
const HOLE: Span = Span {
    start: 0x3fc0_0000,
    size: 0x40_0000,
};

/// The `atf@0` region.
const ATF: ReservedRegion = ReservedRegion {
    span: Span {
        start: 0,
        size: 0x8_0000,
    },
    no_map: true,
    reusable: false,
};

/// The region of 62 bytes in the hole of the 8 GB hand-over tree.
const HOLE_REGION: Span = Span {
    start: 0x3fd2_31e0,
    size: 0x3e,
};

/// The cells of a `reg` of 2 and 2 cells with the spans `ranges`.
fn reg_cells(ranges: &[Span]) -> Vec<u32> {
    let mut values = Vec::new();
    for span in ranges {
        values.extend([
            (span.start >> 32) as u32,
            span.start as u32,
            (span.size >> 32) as u32,
            span.size as u32,
        ]);
    }
    values
}

/// A Pi 5 hand-over tree with the RAM ranges `ranges`, `atf@0` below
/// `/reserved-memory`, and the region of the hole as an entry of the
/// reservation map or as a child of `/reserved-memory` when asked.
fn hand_over(ranges: &[Span], hole_region: Option<bool>) -> Vec<u8> {
    let mut b = root();
    if hole_region == Some(true) {
        b.reservations.push(HOLE_REGION);
    }
    ram(&mut b, &reg_cells(ranges));
    reservations(&mut b);
    b.begin("atf@0");
    b.cells("reg", &reg_cells(&[ATF.span]));
    b.property("no-map", &[]);
    b.end();
    if hole_region == Some(false) {
        b.begin("nvram@3fd231e0");
        b.cells("reg", &reg_cells(&[HOLE_REGION]));
        b.property("no-map", &[]);
        b.end();
    }
    b.end();
    finish(b)
}

/// The usable ranges of every complete page of `ranges` without `atf@0`,
/// the image and the tree, whose pages end at `dtb_end`: the first range
/// from the end of the image to the tree and from the end of the tree to
/// the hole, then every other range whole.
fn usable(ranges: &[Span], dtb_end: u64) -> Vec<Span> {
    let image_end = IMAGE.start + IMAGE.size;
    let mut spans = vec![
        Span::new(image_end, DTB - image_end).unwrap(),
        Span::new(dtb_end, HOLE.start - dtb_end).unwrap(),
    ];
    spans.extend_from_slice(&ranges[1..]);
    spans
}

/// The usable ranges of a boot memory map, in order.
fn available(plan: &MemoryPlan) -> Vec<Span> {
    let mut ranges = plan.available_ranges();
    let mut spans = Vec::new();
    while let Some(span) = ranges.next() {
        spans.push(span);
    }
    spans
}

/// Checks the hand-over tree of a model with the RAM ranges `ranges` and
/// `installed` bytes of RAM: its RAM ranges, its sum of the installed size
/// less 4 MiB, and the boot memory map of `MemoryPlan::all_ram` with the
/// image and the tree as boot storage and the reserved regions as firmware
/// reservations, whose usable ranges leave out the hole.
fn check_model(ranges: &[Span], installed: u64) {
    let bytes = hand_over(ranges, None);
    let memory = report(&bytes).unwrap();
    assert_eq!(memory.ram(), ranges);
    assert_eq!(memory.ram_bytes(), installed - 0x40_0000);
    assert_eq!(memory.reserved(), &[ATF]);
    let dtb = Span::new(DTB, bytes.len() as u64).unwrap();
    let plan = MemoryPlan::all_ram(memory.ram(), &[IMAGE, dtb], memory.reserved()).unwrap();
    let dtb_end = (DTB + bytes.len() as u64).next_multiple_of(0x1000);
    assert_eq!(plan.ram(), ranges);
    assert_eq!(plan.managed_banks(), ranges);
    assert_eq!(available(&plan), usable(ranges, dtb_end));
    assert!(!plan.is_available(Span::new(HOLE.start, 0x1000).unwrap()));
    assert!(!plan.contains_ram(HOLE));
}

/// The first range of every model, from 0 to the hole.
const LOW: Span = Span {
    start: 0,
    size: 0x3fc0_0000,
};

#[test]
fn pi5_1gb_hand_over_shape_builds_its_boot_memory_map() {
    check_model(&[LOW], GIB);
}

#[test]
fn pi5_2gb_hand_over_shape_builds_its_boot_memory_map() {
    check_model(&[LOW, Span::new(GIB, GIB).unwrap()], 2 * GIB);
}

#[test]
fn pi5_4gb_hand_over_shape_builds_its_boot_memory_map() {
    check_model(&[LOW, Span::new(GIB, 3 * GIB).unwrap()], 4 * GIB);
}

#[test]
fn pi5_16gb_hand_over_shape_builds_its_boot_memory_map() {
    check_model(
        &[
            LOW,
            Span::new(GIB, 3 * GIB).unwrap(),
            Span::new(4 * GIB, 12 * GIB).unwrap(),
        ],
        16 * GIB,
    );
}

/// The 8 GB hand-over tree: three RAM ranges and the two reserved regions,
/// `atf@0` and the 62 bytes in the hole, once as an entry of the
/// reservation map and once as a child of `/reserved-memory`. The tree is
/// accepted, and the region in the hole is kept and excluded by whole
/// pages.
#[test]
fn pi5_8gb_hand_over_tree_keeps_the_region_in_the_hole() {
    let ranges = [
        LOW,
        Span::new(GIB, 3 * GIB).unwrap(),
        Span::new(4 * GIB, 4 * GIB).unwrap(),
    ];
    let hole_region = ReservedRegion {
        span: HOLE_REGION,
        no_map: true,
        reusable: false,
    };
    for (in_map, regions) in [(true, [hole_region, ATF]), (false, [ATF, hole_region])] {
        let bytes = hand_over(&ranges, Some(in_map));
        let memory = report(&bytes).unwrap();
        assert_eq!(memory.ram(), &ranges);
        assert_eq!(memory.ram_bytes(), 8 * GIB - 0x40_0000);
        assert_eq!(memory.reserved(), &regions);
        assert!(!memory.is_available(HOLE_REGION).unwrap());
        let dtb = Span::new(DTB, bytes.len() as u64).unwrap();
        let plan = MemoryPlan::all_ram(memory.ram(), &[IMAGE, dtb], memory.reserved()).unwrap();
        let page = Span::new(0x3fd2_3000, 0x1000).unwrap();
        assert!(plan.firmware_ranges().contains(&page));
        assert!(!plan.is_available(page));
        let dtb_end = (DTB + bytes.len() as u64).next_multiple_of(0x1000);
        assert_eq!(available(&plan), usable(&ranges, dtb_end));
    }
}
