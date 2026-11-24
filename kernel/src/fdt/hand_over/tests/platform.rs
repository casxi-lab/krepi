//! The boot memory map of a Pi 5 boot memory: the banks of the discovery
//! with the pages of the image, of the tree and of the firmware
//! reservations excluded.
//!
//! Feature: krepi.platform.device-tree

use super::*;
use crate::fdt::{MemoryPlan, PlanError};

const MANAGED: Span = Span {
    start: 0,
    size: 0x08000000,
};

fn page(start: u64) -> Span {
    Span::new(start, 4096).unwrap()
}

/// The 8 GB model: three RAM ranges and `atf@0` as a reservation entry.
#[test]
fn kernel_projection_preserves_discovered_banks_and_excludes_boot_pages() {
    let mut b = root();
    ram(
        &mut b,
        &[
            0, 0, 0, 0x3fc00000, 0, 0x40000000, 0, 0xc0000000, 1, 0, 1, 0,
        ],
    );
    b.reservations.push(Span::new(0, 0x80000).unwrap());
    let bytes = finish(b);
    let map = report(&bytes).unwrap();
    let plan = MemoryPlan::from_boot_memory(&map, MANAGED, &[]).unwrap();
    assert_eq!(plan.ram().len(), 3);
    assert_eq!(plan.boot_ranges()[0], IMAGE);
    assert!(!plan.permits_backing(page(0)));
    assert!(!plan.permits_backing(page(IMAGE.start)));
    assert!(!plan.permits_backing(page(DTB)));
    assert!(plan.permits_backing(page(0x400000)));
    assert!(!plan.is_available(page(0x3fc00000)));
    assert!(plan.is_available(page(0x1_0000_0000)));
    assert!(!plan.permits_backing(page(0x1_0000_0000)));
}

#[test]
fn kernel_projection_rejects_boot_pages_claimed_by_firmware() {
    let mut b = root();
    ram(&mut b, &[0, 0, 2, 0]);
    b.reservations.push(Span::new(DTB, 0x20000).unwrap());
    let bytes = finish(b);
    let map = report(&bytes).unwrap();
    // The discovery describes overlapping exclusions; the boot memory map
    // cannot both keep a page as boot storage and leave it to the firmware.
    assert_eq!(
        MemoryPlan::from_boot_memory(&map, MANAGED, &[]).unwrap_err(),
        PlanError::Overlap
    );
}
