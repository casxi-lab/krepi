//! Dynamic reservations: an enabled child of `/reserved-memory` with `size`
//! and without `reg` is counted and is no reserved region, whatever its
//! cells and whether it has `alloc-ranges`; a child with `reg` and `size` is
//! a static region; and the shipped Pi 5 tree with its placeholder RAM,
//! `atf@0` and the dynamic `linux,cma` is accepted.
//!
//! Feature: krepi.platform.device-tree

use super::*;

/// The minimal tree with a `/reserved-memory` of 2 and 2 cells whose child
/// `linux,cma` has the properties `properties`.
fn with_pool(properties: &[(&str, Vec<u8>)]) -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.begin("reserved-memory");
    b.cells("#address-cells", &[2]);
    b.cells("#size-cells", &[2]);
    b.property("ranges", &[]);
    b.begin("linux,cma");
    b.property("compatible", b"shared-dma-pool\0");
    for (name, value) in properties {
        b.property(name, value);
    }
    b.end();
    b.end();
    b.end();
    b.finish()
}

#[test]
fn dynamic_reservations_are_counted_whatever_their_size_cells() {
    for size in [cells(&[0x400_0000]), cells(&[0, 0x400_0000])] {
        for alloc_ranges in [false, true] {
            let mut properties = vec![("size", size.clone()), ("reusable", Vec::new())];
            if alloc_ranges {
                properties.push(("alloc-ranges", cells(&[0, 0, 0, 0x4000_0000])));
            }
            let bytes = with_pool(&properties);
            let memory = Fdt::parse(&bytes).unwrap().discover_memory().unwrap();
            assert_eq!(memory.dynamic(), 1, "{size:?} {alloc_ranges}");
            assert!(memory.reserved().is_empty(), "{size:?} {alloc_ranges}");
        }
    }
}

#[test]
fn a_child_with_reg_and_size_is_a_static_region() {
    let bytes = with_pool(&[
        ("reg", cells(&[1, 0x1000, 0, 0x2000])),
        ("size", cells(&[0, 0x2000])),
        ("reusable", Vec::new()),
    ]);
    let memory = Fdt::parse(&bytes).unwrap().discover_memory().unwrap();
    assert_eq!(memory.dynamic(), 0);
    assert_eq!(
        memory.reserved(),
        &[ReservedRegion {
            span: Span::new(0x1_0000_1000, 0x2000).unwrap(),
            no_map: false,
            reusable: true,
        }]
    );
}

/// The shape of the tree that the firmware ships: the placeholder RAM node
/// of 640 MiB, `atf@0` and a dynamic `linux,cma` with a `size` of one cell
/// below 2 size cells, with the image of the firmware vectors.
#[test]
fn shipped_placeholder_shape_is_accepted_with_its_dynamic_reservation() {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0, 0, 0x2800_0000]);
    b.end();
    b.begin("reserved-memory");
    b.cells("#address-cells", &[2]);
    b.cells("#size-cells", &[2]);
    b.property("ranges", &[]);
    b.begin("atf@0");
    b.cells("reg", &[0, 0, 0, 0x8_0000]);
    b.property("no-map", &[]);
    b.end();
    b.begin("linux,cma");
    b.property("compatible", b"shared-dma-pool\0");
    b.cells("size", &[0x400_0000]);
    b.property("reusable", &[]);
    b.property("linux,cma-default", &[]);
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    let image = Span::new(0x8_0000, 0x8_0000).unwrap();
    let memory = Fdt::parse(&bytes)
        .unwrap()
        .discover_pi5_boot_memory(0x20_0000, image)
        .unwrap();
    assert_eq!(memory.ram(), &[Span::new(0, 0x2800_0000).unwrap()]);
    assert_eq!(
        memory.reserved(),
        &[ReservedRegion {
            span: Span::new(0, 0x8_0000).unwrap(),
            no_map: true,
            reusable: false,
        }]
    );
    assert_eq!(memory.dynamic(), 1);
    assert_eq!(memory.ram_bytes(), 640 * 1024 * 1024);
}
