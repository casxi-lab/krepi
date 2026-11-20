//! The memory discovery on the minimal tree: high RAM with both sources of
//! reserved regions, disabled RAM and cell counts that are not inherited,
//! disabled secure memory, `/reserved-memory` with a dynamic child, empty
//! and overlapping RAM, and the capacity and flags of reserved regions.
//!
//! Feature: krepi.platform.device-tree

use super::*;

#[test]
fn discovers_high_ram_and_both_reservation_sources() {
    let mut b = Builder::default();
    b.reservations.push(Span {
        start: 0x1_0000_0000,
        size: 0x1000,
    });
    b.root();
    b.memory();
    b.begin("reserved-memory");
    b.cells("#address-cells", &[2]);
    b.cells("#size-cells", &[2]);
    b.property("ranges", &[]);
    b.begin("firmware@100001000");
    b.cells("reg", &[1, 0x1000, 0, 0x2000]);
    b.property("no-map", &[]);
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    let map = tree.discover_memory().unwrap();
    assert_eq!(tree.total_size(), bytes.len() as u64);
    assert_eq!(
        map.ram(),
        &[Span {
            start: 0x1_0000_0000,
            size: 0x200000
        }]
    );
    assert_eq!(map.reserved().len(), 2);
    assert!(map.reserved().iter().all(|r| r.no_map));
    assert_eq!(
        map.reserved()[1].span,
        Span {
            start: 0x1_0000_1000,
            size: 0x2000
        }
    );
}

#[test]
fn disabled_ram_is_not_allocatable_and_defaults_are_not_inherited() {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.begin("memory@200000000");
    b.property("device_type", b"memory\0");
    b.property("status", b"disabled\0");
    b.cells("reg", &[2, 0, 0, 0x1000]);
    b.end();
    b.begin("bus");
    b.property("ranges", &[]);
    b.begin("dev@0");
    b.cells("reg", &[0, 0, 0x1000]);
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    assert_eq!(tree.discover_memory().unwrap().ram().len(), 1);
    let reg = tree
        .find_node("/bus/dev@0")
        .unwrap()
        .unwrap()
        .reg()
        .unwrap()
        .next()
        .unwrap();
    assert_eq!(reg.size, 0x1000);
}

#[test]
fn disabled_secure_memory_is_excluded_before_binding_validation() {
    for (status, rejected) in [
        (b"disabled\0".as_slice(), false),
        (b"okay\0", true),
        (b"okay\0junk", true),
    ] {
        let mut b = Builder::default();
        b.root();
        b.memory();
        b.begin("secram@e000000");
        b.property("device_type", b"memory\0");
        b.property("status", status);
        b.property("secure-status", b"okay\0");
        b.cells("reg", &[0, 0xe000000, 0, 0x1000000]);
        b.end();
        b.end();
        let bytes = b.finish();
        let result = Fdt::parse(&bytes).unwrap().discover_memory();
        if rejected {
            assert_eq!(result.unwrap_err(), Error::BadProperty);
        } else {
            let map = result.unwrap();
            assert_eq!(map.ram().len(), 1);
            assert_eq!(map.ram()[0].start, 0x1_0000_0000);
        }
    }
}

/// The prototype rejected the dynamic child with an error of its own; the
/// contract accepts it and counts one dynamic reservation, which is no
/// reserved region.
#[test]
fn reserved_memory_requires_explicit_identity_and_static_regions() {
    for dynamic in [false, true] {
        let mut b = Builder::default();
        b.root();
        b.memory();
        b.begin("reserved-memory");
        b.cells("#address-cells", &[2]);
        b.cells("#size-cells", &[2]);
        if dynamic {
            b.property("ranges", &[]);
        }
        b.begin("pool");
        b.cells("size", &[0, 0x1000]);
        b.end();
        b.end();
        b.end();
        let bytes = b.finish();
        let result = Fdt::parse(&bytes).unwrap().discover_memory();
        if dynamic {
            let map = result.unwrap();
            assert_eq!(
                map.ram(),
                &[Span {
                    start: 0x1_0000_0000,
                    size: 0x200000
                }]
            );
            assert!(map.reserved().is_empty());
            assert_eq!(map.dynamic(), 1);
        } else {
            assert_eq!(result.unwrap_err(), Error::BadProperty);
        }
    }
}

#[test]
fn empty_or_overlapping_ram_is_rejected() {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.memory();
    b.end();
    let bytes = b.finish();
    assert_eq!(
        Fdt::parse(&bytes).unwrap().discover_memory().unwrap_err(),
        Error::Overlap
    );
    let mut b = Builder::default();
    b.root();
    b.end();
    let bytes = b.finish();
    assert_eq!(
        Fdt::parse(&bytes).unwrap().discover_memory().unwrap_err(),
        Error::NoMemory
    );
}

#[test]
fn discovery_capacity_and_reserved_flags_fail_closed() {
    let mut b = Builder::default();
    b.root();
    for index in 0..=MAX_MEMORY_REGIONS {
        b.begin(&std::format!("memory@{:x}", index * 0x1000));
        b.property("device_type", b"memory\0");
        b.cells("reg", &[0, index as u32 * 0x1000, 0, 0x1000]);
        b.end();
    }
    b.end();
    let bytes = b.finish();
    assert_eq!(
        Fdt::parse(&bytes).unwrap().discover_memory().unwrap_err(),
        Error::LimitExceeded
    );
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.begin("reserved-memory");
    b.cells("#address-cells", &[2]);
    b.cells("#size-cells", &[2]);
    b.property("ranges", &[]);
    b.begin("pool");
    b.cells("reg", &[1, 0, 0, 0x1000]);
    b.property("no-map", &[]);
    b.property("reusable", &[]);
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    assert_eq!(
        Fdt::parse(&bytes).unwrap().discover_memory().unwrap_err(),
        Error::BadProperty
    );
}
