//! The translation: recursive `ranges` and separate `dma-ranges`, absent
//! and identity maps, windows that refuse crossing, unmapped and ambiguous
//! requests, cells that cannot truncate and one-cell regions within 4 GiB.
//!
//! Feature: krepi.platform.device-tree

use super::*;

#[test]
fn translation_is_recursive_and_dma_is_separate() {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.begin("bus");
    b.cells("#address-cells", &[1]);
    b.cells("#size-cells", &[1]);
    b.cells("ranges", &[0, 2, 0, 0x10000]);
    b.cells("dma-ranges", &[0, 3, 0, 0x10000]);
    b.begin("bridge");
    b.cells("#address-cells", &[1]);
    b.cells("#size-cells", &[1]);
    b.cells("ranges", &[0, 0x1000, 0x1000]);
    b.begin("serial@20");
    b.cells("reg", &[0x20, 0x10]);
    b.end();
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    let node = tree.find_node("/bus/bridge/serial@20").unwrap().unwrap();
    let reg = node.reg().unwrap().next().unwrap();
    assert_eq!(
        node.translate_reg(reg).unwrap(),
        Span {
            start: 0x2_0000_1020,
            size: 0x10
        }
    );
    let bus = tree.find_node("/bus").unwrap().unwrap();
    let dma = bus.dma_ranges().unwrap();
    let device = Span {
        start: 0x1020,
        size: 0x10,
    };
    let physical = Span {
        start: 0x3_0000_1020,
        size: 0x10,
    };
    assert_eq!(dma.to_parent(device), Ok(physical));
    assert_eq!(dma.to_child(physical), Ok(device));
}

#[test]
fn identity_and_absent_are_distinct_and_width_checked() {
    let absent = AddressMap::new(None, 2, 2, 2).unwrap();
    let identity = AddressMap::new(Some(&[]), 2, 2, 2).unwrap();
    let span = Span::new(0x1_0000_0000, 4096).unwrap();
    assert_eq!(absent.kind(), MappingKind::Absent);
    assert_eq!(identity.kind(), MappingKind::Identity);
    assert_eq!(absent.to_parent(span), Err(Error::Unmapped));
    assert_eq!(identity.to_parent(span), Ok(span));
    assert_eq!(
        AddressMap::new(Some(&[]), 2, 1, 1).unwrap().to_parent(span),
        Err(Error::Overflow)
    );
}

#[test]
fn windows_refuse_crossing_unmapped_and_ambiguous_requests() {
    let bytes = cells(&[0, 1, 0, 0x1000, 0x1000, 2, 0, 0x1000]);
    let map = AddressMap::new(Some(&bytes), 1, 2, 1).unwrap();
    assert_eq!(
        map.to_parent(Span::new(0xff0, 0x20).unwrap()),
        Err(Error::Unmapped)
    );
    assert_eq!(
        map.to_parent(Span::new(0x4000, 1).unwrap()),
        Err(Error::Unmapped)
    );
    let duplicate = cells(&[0, 1, 0, 0x1000, 0, 2, 0, 0x1000]);
    assert_eq!(
        AddressMap::new(Some(&duplicate), 1, 2, 1)
            .unwrap()
            .to_parent(Span::new(4, 4).unwrap()),
        Err(Error::AmbiguousMapping)
    );
}

#[test]
fn numeric_cells_and_pci_tags_cannot_truncate() {
    assert_eq!(
        cells_u64(&cells(&[0x12, 0x34567890]), 2),
        Ok(0x12_3456_7890)
    );
    assert_eq!(
        cells_u64(&cells(&[0, 0, 1]), 3),
        Err(Error::UnsupportedCells)
    );
    assert!(matches!(
        AddressMap::new(Some(&[]), 3, 2, 2),
        Err(Error::UnsupportedCells)
    ));
    assert!(matches!(
        Reg::new(&cells(&[0, 0, 1, 0x1000]), 3, 1),
        Err(Error::UnsupportedCells)
    ));
    assert!(matches!(
        Reg::new(&cells(&[u32::MAX, u32::MAX, 0, 1]), 2, 2),
        Err(Error::Overflow)
    ));
    assert!(matches!(
        AddressMap::new(Some(&cells(&[0, u32::MAX, u32::MAX, 2])), 1, 2, 1),
        Err(Error::Overflow)
    ));
    assert!(matches!(Reg::new(&[0; 7], 1, 1), Err(Error::BadProperty)));
    assert!(matches!(
        AddressMap::new(Some(&[0; 7]), 1, 1, 1),
        Err(Error::BadProperty)
    ));
}

#[test]
fn one_cell_regions_cannot_cross_their_address_space() {
    assert!(matches!(
        Reg::new(&cells(&[u32::MAX, 2]), 1, 1),
        Err(Error::Overflow)
    ));
    let bytes = cells(&[u32::MAX, 1]);
    assert_eq!(
        Reg::new(&bytes, 1, 1).unwrap().next().unwrap().end(),
        Ok(1u64 << 32)
    );
}
