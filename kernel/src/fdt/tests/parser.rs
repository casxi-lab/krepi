//! The parse: truncations, the header, the reservation map, the tokens,
//! names and padding, the depth, single-byte corruptions, the property
//! padding of QEMU, unaligned host bytes and the bounded vendor names and
//! symbol tables.
//!
//! Feature: krepi.platform.device-tree

use super::*;

#[test]
fn all_truncations_are_rejected_without_panics() {
    let bytes = minimal();
    for end in 0..bytes.len() {
        assert!(Fdt::parse(&bytes[..end]).is_err(), "accepted length {end}");
    }
}

#[test]
fn rejects_bad_header_layout_version_and_reservation_map() {
    for (offset, value, error) in [
        (0, 0, Error::BadMagic),
        (4, 12, Error::BadLayout),
        (4, MAX_BLOB_SIZE as u32 + 1, Error::LimitExceeded),
        (8, 57, Error::BadAlignment),
        (16, 41, Error::BadAlignment),
        (20, 16, Error::UnsupportedVersion),
        (24, 18, Error::UnsupportedVersion),
        (24, 0, Error::UnsupportedVersion),
        (12, 4, Error::BadLayout),
        (16, 56, Error::BadLayout),
    ] {
        let mut bytes = minimal();
        set_word(&mut bytes, offset, value);
        assert_eq!(Fdt::parse(&bytes).unwrap_err(), error, "field {offset}");
    }
    let mut bytes = minimal();
    let start = u32_at(&bytes, 8).unwrap();
    set_word(&mut bytes, 12, start);
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::BadLayout);
    let mut bytes = minimal();
    bytes[40..48].copy_from_slice(&1u64.to_be_bytes());
    bytes[48..56].copy_from_slice(&1u64.to_be_bytes());
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::BadLayout);
}

#[test]
fn reservation_overflow_and_overlap_fail_closed() {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.end();
    b.reservations.push(Span {
        start: u64::MAX,
        size: 1,
    });
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::Overflow);
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.end();
    b.reservations.extend([
        Span {
            start: 0x1000,
            size: 0x2000,
        },
        Span {
            start: 0x2000,
            size: 0x2000,
        },
    ]);
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::Overlap);
}

#[test]
fn rejects_bad_tokens_names_padding_and_property_order() {
    let mut b = Builder::default();
    b.root();
    b.begin("child");
    b.end();
    b.property("late", &[]);
    b.end();
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::BadTree);
    let mut b = Builder::default();
    b.root();
    b.cells("#address-cells", &[2]);
    b.end();
    assert_eq!(
        Fdt::parse(&b.finish()).unwrap_err(),
        Error::DuplicateProperty
    );
    let mut bytes = minimal();
    let start = u32_at(&bytes, 8).unwrap() as usize;
    set_word(&mut bytes, start, 0xff);
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::BadToken);
    let mut bytes = minimal();
    bytes[start + 5] = 1;
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::BadPadding);
    let mut bytes = minimal();
    set_word(&mut bytes, start + 16, u32::MAX);
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::BadString);
    let mut bytes = minimal();
    let strings = u32_at(&bytes, 12).unwrap() as usize;
    bytes[strings..].fill(b'a');
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::BadString);
}

#[test]
fn rejects_unbalanced_tree_trailing_tokens_and_excess_depth() {
    let mut b = Builder::default();
    b.root();
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::BadTree);
    let mut b = Builder::default();
    b.root();
    b.end();
    b.end();
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::BadTree);
    let mut b = Builder::default();
    b.root();
    b.end();
    b.word(9);
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::BadTree);
    let mut b = Builder::default();
    b.root();
    for _ in 0..MAX_DEPTH {
        b.begin("child");
    }
    for _ in 0..=MAX_DEPTH {
        b.end();
    }
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::LimitExceeded);
}

#[test]
fn header_and_structure_single_byte_corruptions_do_not_panic() {
    let original = minimal();
    for at in 0..original.len() {
        let mut mutated = original.clone();
        mutated[at] ^= 0xff;
        if let Ok(tree) = Fdt::parse(&mutated) {
            let _ = tree.discover_memory();
            for node in all_nodes(tree) {
                let _ = node.reg();
                let _ = node.ranges();
                let _ = node.dma_ranges();
            }
        }
    }
}

#[test]
fn qemu_property_padding_residue_is_not_payload_or_a_token() {
    // Minimized from the QEMU 11.1.2 tree of the machine `virt`: its root
    // `model` has a length of 17 followed by `00 00 02`, and the
    // `device_type` of its memory node a length of 7 followed by `73`.
    // DTSpec asks for zero padding, which this producer does not write; the
    // parse accepts other bytes in the padding of a property value and
    // still requires the padding to lie within the block.
    let mut b = Builder::default();
    b.root();
    b.property("model", b"linux,dummy-virt\0");
    let end = b.structure.len();
    b.structure[end - 3..end].copy_from_slice(&[0, 0, 2]);
    b.begin("memory@40000000");
    b.property("device_type", b"memory\0");
    *b.structure.last_mut().unwrap() = 0x73;
    b.cells("reg", &[0, 0x40000000, 0, 0x08000000]);
    b.end();
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    assert_eq!(
        tree.find_node("/")
            .unwrap()
            .unwrap()
            .string_property("model"),
        Ok(Some(&b"linux,dummy-virt"[..]))
    );
    assert_eq!(
        tree.discover_memory().unwrap().ram(),
        &[Span {
            start: 0x40000000,
            size: 0x08000000
        }]
    );
    assert_eq!(padded_end(&[0; 5], 5, false), Err(Error::Truncated));
    assert_eq!(padded_end(&[0; 8], 5, false), Ok(8));
}

#[test]
fn accepts_unaligned_host_bytes_and_compatible_future_version() {
    let mut bytes = minimal();
    set_word(&mut bytes, 20, 18);
    set_word(&mut bytes, 24, 17);
    let mut unaligned = vec![0];
    unaligned.extend(&bytes);
    assert!(
        Fdt::parse(&unaligned[1..])
            .unwrap()
            .discover_memory()
            .is_ok()
    );
}

/// Covers 334, 512 and 513 properties of `/__symbols__`, and the vendor
/// property name of 32 bytes with names of 64 and 65 bytes.
#[test]
fn vendor_property_names_and_symbol_tables_remain_bounded() {
    for (count, accepted) in [
        (334, true),
        (MAX_PROPERTIES, true),
        (MAX_PROPERTIES + 1, false),
    ] {
        let mut b = Builder::default();
        b.root();
        b.begin("__symbols__");
        for index in 0..count {
            b.property(&std::format!("symbol_{index}"), b"/device\0");
        }
        b.end();
        b.end();
        let bytes = b.finish();
        let parsed = Fdt::parse(&bytes);
        if accepted {
            assert!(parsed.is_ok());
        } else {
            assert_eq!(parsed.unwrap_err(), Error::LimitExceeded);
        }
    }
    let longest = MAX_PROPERTY_NAME as usize;
    for (name, accepted) in [
        (
            std::string::String::from("snps,parkmode-disable-fsls-quirk"),
            true,
        ),
        ("x".repeat(longest), true),
        ("x".repeat(longest + 1), false),
    ] {
        let mut b = Builder::default();
        b.root();
        b.property(&name, &[]);
        b.end();
        let bytes = b.finish();
        let parsed = Fdt::parse(&bytes);
        if accepted {
            assert!(parsed.is_ok());
        } else {
            assert_eq!(parsed.unwrap_err(), Error::BadString);
        }
    }
}
