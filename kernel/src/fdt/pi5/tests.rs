//! The host tests of the Pi 5 boot memory: trees of a Pi 5 root with their
//! RAM, reservations and boot storage, and the test modules of its
//! boundaries, its selection, the boot memory map built from it, the RAM
//! models and the firmware trees.
//!
//! Feature: krepi.platform.device-tree

extern crate std;

use super::*;
use crate::fdt::{MAX_MEMORY_REGIONS, MAX_RESERVED_REGIONS};
use std::{vec, vec::Vec};

mod boundaries;
mod builder;
mod selection;
use builder::Builder;

const IMAGE: Span = Span {
    start: 0x80000,
    size: 0x20000,
};
const DTB: u64 = 0x200000;

fn root() -> Builder {
    let mut builder = Builder::default();
    builder.begin("");
    builder.cells("#address-cells", &[2]);
    builder.cells("#size-cells", &[2]);
    builder.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    builder
}

fn ram(builder: &mut Builder, values: &[u32]) {
    builder.begin("memory@0");
    builder.property("device_type", b"memory\0");
    builder.cells("reg", values);
    builder.end();
}

fn reservations(builder: &mut Builder) {
    builder.begin("reserved-memory");
    builder.cells("#address-cells", &[2]);
    builder.cells("#size-cells", &[2]);
    builder.property("ranges", &[]);
}

fn finish(mut builder: Builder) -> Vec<u8> {
    builder.end();
    builder.finish()
}

fn report(bytes: &[u8]) -> Result<Pi5BootMemory, Error> {
    Fdt::parse(bytes)?.discover_pi5_boot_memory(DTB, IMAGE)
}

#[test]
fn retains_high_ram_and_excludes_all_boot_and_firmware_storage() {
    let mut b = root();
    b.reservations.push(Span::new(DTB, 0x20000).unwrap());
    // The middle bank is above 4 GiB and the final bank is separated by a hole.
    ram(&mut b, &[0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0, 0x100000]);
    reservations(&mut b);
    b.begin("atf@0");
    b.cells("reg", &[0, 0, 0, 0x80000]);
    b.property("no-map", &[]);
    b.end();
    b.begin("pool@100000000");
    b.cells("reg", &[1, 0, 0, 0x10000]);
    b.property("reusable", &[]);
    b.end();
    b.end();
    // PCI tagged addresses belong to another binding, not root RAM decoding.
    b.begin("pcie@1000120000");
    b.cells("#address-cells", &[3]);
    b.cells("#size-cells", &[2]);
    b.cells("ranges", &[0x02000000, 0, 0, 0x1b, 0, 0, 0x100000]);
    b.begin("ethernet@0");
    b.cells("reg", &[0, 0, 0, 0, 0x1000]);
    b.end();
    b.end();
    let bytes = finish(b);
    let map = report(&bytes).unwrap();
    assert_eq!(map.ram().len(), 3);
    assert_eq!(
        map.ram()[1],
        Span::new(0x1_0000_0000, 0x1_0000_0000).unwrap()
    );
    assert_eq!(map.ram_bytes(), 0x2_0010_0000);
    assert_eq!(map.dtb(), Span::new(DTB, bytes.len() as u64).unwrap());
    assert_eq!(map.image(), IMAGE);
    assert!(map.reserved()[0].no_map);
    assert!(map.reserved()[1].no_map);
    assert!(map.reserved()[2].reusable);
    for span in [
        Span::new(0, 0x1000).unwrap(),
        IMAGE,
        Span::new(DTB, 8).unwrap(),
        Span::new(0x1_0000_0000, 0x1000).unwrap(),
        Span::new(0x2_0000_0000, 0x1000).unwrap(),
    ] {
        assert!(!map.is_available(span).unwrap(), "{span:?}");
    }
    assert!(
        map.is_available(Span::new(0x1_0001_0000, 0x1000).unwrap())
            .unwrap()
    );
    assert!(
        !map.is_available(Span::new(0xffff_f000, 0x2000).unwrap())
            .unwrap()
    );
    assert!(
        !map.is_available(Span::new(0x1_ffff_f000, 0x1_0000_2000).unwrap())
            .unwrap()
    );
}

#[test]
fn ignores_disabled_ram_and_disabled_dynamic_reservations() {
    let mut b = root();
    ram(&mut b, &[0, 0, 2, 0]);
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.property("status", b"disabled\0");
    b.cells("reg", &[0, 0, 2, 0]);
    b.end();
    reservations(&mut b);
    b.begin("linux,cma");
    b.cells("size", &[0x4000000]);
    b.property("reusable", &[]);
    b.property("status", b"disabled\0");
    b.end();
    b.end();
    let bytes = finish(b);
    let map = report(&bytes).unwrap();
    assert_eq!(map.ram_bytes(), 0x2_0000_0000);
    assert_eq!(map.ram().len(), 1);
    assert!(map.reserved().is_empty());
    assert_eq!(map.dynamic(), 0);
}

#[test]
fn compatibility_allows_model_revision_and_extra_compatible_entries() {
    let mut b = Builder::default();
    b.begin("");
    b.cells("#address-cells", &[2]);
    b.cells("#size-cells", &[2]);
    b.property("model", b"Raspberry Pi 5 Model B Rev 1.1\0");
    b.property(
        "compatible",
        b"vendor,new-revision\0raspberrypi,5-model-b\0brcm,bcm2712\0",
    );
    ram(&mut b, &[0, 0, 2, 0]);
    assert_eq!(report(&finish(b)).unwrap().ram_bytes(), 0x2_0000_0000);
}

/// The prototype rejected the dynamic `pool` with an error of its own; the
/// contract accepts it and counts one dynamic reservation, which is no
/// reserved region.
#[test]
fn rejects_active_dynamic_reservations_and_conflicting_flags() {
    for dynamic in [true, false] {
        let mut b = root();
        ram(&mut b, &[0, 0, 2, 0]);
        reservations(&mut b);
        b.begin("pool");
        b.property("reusable", &[]);
        if dynamic {
            b.cells("size", &[0x4000000]);
        } else {
            b.cells("reg", &[0, 0x400000, 0, 0x1000]);
            b.property("no-map", &[]);
        }
        b.end();
        b.end();
        let result = report(&finish(b));
        if dynamic {
            let map = result.unwrap();
            assert_eq!(map.ram_bytes(), 0x2_0000_0000);
            assert!(map.reserved().is_empty());
            assert_eq!(map.dynamic(), 1);
        } else {
            assert_eq!(result.unwrap_err(), Error::BadProperty);
        }
    }
}
