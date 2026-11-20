//! The boundaries of the Pi 5 boot memory: the root `compatible`, the root
//! cells and the size of the hand-over tree, the alignment and the spans of
//! the tree and of the image, overlapping and out-of-range RAM, and the
//! capacities of the discovery.
//!
//! Feature: krepi.platform.device-tree

use super::*;

#[test]
fn rejects_missing_wrong_and_malformed_compatible_values() {
    for compatible in [
        None,
        Some(&b"raspberrypi,4-model-b\0brcm,bcm2711\0"[..]),
        Some(&b"raspberrypi,5-model-b\0brcm,bcm2712"[..]),
        Some(&b"raspberrypi,5-model-b\0\0brcm,bcm2712\0"[..]),
        Some(&b"raspberrypi,5-model-b\0brcm,bcm2712\0\xff\0"[..]),
    ] {
        let mut b = Builder::default();
        b.begin("");
        b.cells("#address-cells", &[2]);
        b.cells("#size-cells", &[2]);
        if let Some(value) = compatible {
            b.property("compatible", value);
        }
        ram(&mut b, &[0, 0, 2, 0]);
        assert!(report(&finish(b)).is_err());
    }
}

#[test]
fn rejects_wrong_root_cells_and_oversized_handoff() {
    let mut b = Builder::default();
    b.begin("");
    b.cells("#address-cells", &[1]);
    b.cells("#size-cells", &[1]);
    b.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    assert_eq!(report(&finish(b)).unwrap_err(), Error::UnsupportedCells);
    let mut b = root();
    b.property("padding", &vec![0; PI5_MAX_BLOB_SIZE as usize]);
    ram(&mut b, &[0, 0, 2, 0]);
    assert_eq!(report(&finish(b)).unwrap_err(), Error::LimitExceeded);
}

#[test]
fn validates_storage_alignment_overflow_overlap_and_ram_containment() {
    let mut b = root();
    ram(&mut b, &[0, 0, 0, 0x400000]);
    let bytes = finish(b);
    let tree = Fdt::parse(&bytes).unwrap();
    for (dtb, image, expected) in [
        (DTB + 1, IMAGE, Error::BadAlignment),
        (u64::MAX - 7, IMAGE, Error::Overflow),
        (
            DTB,
            Span {
                start: DTB,
                size: 0x1000,
            },
            Error::Overlap,
        ),
        (DTB, Span { start: 0, size: 0 }, Error::EmptyRegion),
        (
            DTB,
            Span {
                start: u64::MAX,
                size: 1,
            },
            Error::Overflow,
        ),
        (0x400000, IMAGE, Error::Unmapped),
        (0x3ffff8, IMAGE, Error::Unmapped),
        (
            DTB,
            Span {
                start: 0x3ff000,
                size: 0x2000,
            },
            Error::Unmapped,
        ),
    ] {
        assert_eq!(
            tree.discover_pi5_boot_memory(dtb, image).unwrap_err(),
            expected
        );
    }
    let map = tree.discover_pi5_boot_memory(DTB, IMAGE).unwrap();
    assert_eq!(
        map.is_available(Span { start: 0, size: 0 }),
        Err(Error::EmptyRegion)
    );
    assert_eq!(
        map.is_available(Span {
            start: u64::MAX,
            size: 1
        }),
        Err(Error::Overflow)
    );
}

#[test]
fn rejects_overlapping_ram_aliases_and_out_of_range_regs() {
    for (values, expected) in [
        (&[0, 0, 2, 0, 1, 0, 1, 0][..], Error::Overlap),
        (&[u32::MAX, u32::MAX, 0, 1][..], Error::Overflow),
        (&[0, 0, 0, 0][..], Error::EmptyRegion),
    ] {
        let mut b = root();
        ram(&mut b, values);
        assert_eq!(report(&finish(b)).unwrap_err(), expected);
    }
}

#[test]
fn capacity_exhaustion_never_returns_a_partial_memory_map() {
    let mut b = root();
    let values: Vec<_> = (0..=MAX_MEMORY_REGIONS)
        .flat_map(|index| [index as u32, 0, 1, 0])
        .collect();
    ram(&mut b, &values);
    assert_eq!(report(&finish(b)).unwrap_err(), Error::LimitExceeded);

    let mut b = root();
    ram(&mut b, &[0, 0, 2, 0]);
    reservations(&mut b);
    b.begin("many-regions");
    let values: Vec<_> = (0..=MAX_RESERVED_REGIONS)
        .flat_map(|index| [0, index as u32 * 0x1000, 0, 0x1000])
        .collect();
    b.cells("reg", &values);
    b.end();
    b.end();
    assert_eq!(report(&finish(b)).unwrap_err(), Error::LimitExceeded);
}
