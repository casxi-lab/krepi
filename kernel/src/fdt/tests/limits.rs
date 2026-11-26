//! The limits of the format at the limit and 1 above, where no vector holds
//! that case, with a path one component below the deepest node; the lookup
//! of a path at its last component; the errors that no vector gives; the
//! boot storage of 4 and 5 spans, also as the further spans of a boot
//! memory; and `Span::contains` on spans that end beyond 64 bits.
//!
//! Feature: krepi.platform.device-tree

use super::*;

/// The image and the tree of the Pi 5 tests.
const IMAGE: Span = Span {
    start: 0x80000,
    size: 0x20000,
};
const DTB: u64 = 0x200000;

/// A tree of exactly `total` bytes: `bytes` with zeros after its blocks and
/// `totalsize` set to `total`.
fn padded(mut bytes: Vec<u8>, total: u64) -> Vec<u8> {
    bytes.resize(total as usize, 0);
    set_word(&mut bytes, 4, total as u32);
    bytes
}

/// A Pi 5 hand-over tree of one RAM range of 8 GiB.
fn pi5() -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0, 2, 0]);
    b.end();
    b.end();
    b.finish()
}

#[test]
fn a_tree_of_exactly_max_blob_size_is_accepted() {
    let bytes = padded(minimal(), MAX_BLOB_SIZE);
    let tree = Fdt::parse(&bytes).unwrap();
    assert_eq!(tree.total_size(), MAX_BLOB_SIZE);
    assert!(tree.discover_memory().is_ok());
}

#[test]
fn a_pi5_tree_of_exactly_128_kib_is_accepted() {
    let bytes = padded(pi5(), PI5_HAND_OVER.max_blob_size);
    let memory = Fdt::parse(&bytes)
        .unwrap()
        .discover_boot_memory(PI5_HAND_OVER, DTB, IMAGE)
        .unwrap();
    assert_eq!(
        memory.dtb(),
        Span::new(DTB, PI5_HAND_OVER.max_blob_size).unwrap()
    );
}

#[test]
fn a_pi5_tree_one_byte_over_128_kib_fails() {
    let bytes = padded(pi5(), PI5_HAND_OVER.max_blob_size + 1);
    assert_eq!(
        Fdt::parse(&bytes)
            .unwrap()
            .discover_boot_memory(PI5_HAND_OVER, DTB, IMAGE)
            .unwrap_err(),
        Error::LimitExceeded
    );
}

/// 32 nodes on a path, the root included: a node at depth 31.
#[test]
fn a_node_at_depth_31_is_accepted() {
    let mut b = Builder::default();
    b.root();
    for _ in 1..MAX_DEPTH {
        b.begin("child");
    }
    for _ in 0..MAX_DEPTH {
        b.end();
    }
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    let path = "/child".repeat(MAX_DEPTH as usize - 1);
    let deepest = tree.find_node(&path).unwrap().unwrap();
    let mut depth = 0;
    let mut node = deepest;
    while let Some(parent) = node.parent() {
        depth += 1;
        node = parent;
    }
    assert_eq!(depth, MAX_DEPTH - 1);
}

/// A path of 32 components below the root, one more than a tree holds:
/// none, after its first 31 components each matched a node.
#[test]
fn a_path_below_the_deepest_node_gives_none() {
    let mut b = Builder::default();
    b.root();
    for _ in 1..MAX_DEPTH {
        b.begin("child");
    }
    for _ in 0..MAX_DEPTH {
        b.end();
    }
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    let path = "/child".repeat(MAX_DEPTH as usize);
    assert!(tree.find_node(&path).unwrap().is_none());
}

/// The last component of a path: the node of that name below the node of
/// the components before it; none when no child of that node has the name
/// as it is written, unit address included; `AmbiguousMapping` when two
/// have it; and none when an earlier component matches nothing.
#[test]
fn a_path_is_looked_up_at_its_last_component() {
    let mut b = Builder::default();
    b.root();
    b.begin("soc");
    for name in ["serial@1000", "timer", "timer"] {
        b.begin(name);
        b.end();
    }
    b.end();
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    let serial = tree.find_node("/soc/serial@1000").unwrap().unwrap();
    assert_eq!(serial.name(), b"serial@1000");
    assert_eq!(serial.parent().unwrap().name(), b"soc");
    for path in [
        "/soc/serial",
        "/soc/serial@100",
        "/soc/serial@1000/x",
        "/bus/timer",
    ] {
        assert!(tree.find_node(path).unwrap().is_none(), "{path}");
    }
    assert_eq!(
        tree.find_node("/soc/timer").unwrap_err(),
        Error::AmbiguousMapping
    );
}

/// A root, `nops` no-operation tokens, the end node of the root and the end
/// token.
fn tokens(nops: u64) -> Vec<u8> {
    let mut b = Builder::default();
    b.begin("");
    for _ in 0..nops {
        b.word(4);
    }
    b.end();
    b.finish()
}

#[test]
fn exactly_max_tokens_are_accepted() {
    assert!(Fdt::parse(&tokens(MAX_TOKENS - 3)).is_ok());
}

#[test]
fn one_token_over_max_tokens_fails() {
    assert_eq!(
        Fdt::parse(&tokens(MAX_TOKENS - 2)).unwrap_err(),
        Error::LimitExceeded
    );
}

/// The minimal tree with `count` disjoint reservation entries of one page.
fn reserved(count: u64) -> Vec<u8> {
    let mut b = Builder::default();
    for index in 0..count {
        b.reservations
            .push(Span::new(index * 0x1000, 0x1000).unwrap());
    }
    b.root();
    b.memory();
    b.end();
    b.finish()
}

#[test]
fn max_reservation_entries_are_accepted() {
    let bytes = reserved(MAX_RESERVATIONS);
    let tree = Fdt::parse(&bytes).unwrap();
    let mut entries = tree.reservations();
    let mut count = 0;
    while let Some(entry) = entries.next() {
        assert_eq!(entry, Span::new(count * 0x1000, 0x1000).unwrap());
        count += 1;
    }
    assert_eq!(count, MAX_RESERVATIONS);
}

#[test]
fn one_reservation_entry_over_the_limit_fails() {
    assert_eq!(
        Fdt::parse(&reserved(MAX_RESERVATIONS + 1)).unwrap_err(),
        Error::LimitExceeded
    );
}

#[test]
fn max_memory_regions_are_accepted() {
    let mut b = Builder::default();
    b.root();
    for index in 0..MAX_MEMORY_REGIONS {
        b.begin(&std::format!("memory@{:x}", index * 0x1000));
        b.property("device_type", b"memory\0");
        b.cells("reg", &[0, index as u32 * 0x1000, 0, 0x1000]);
        b.end();
    }
    b.end();
    let bytes = b.finish();
    let memory = Fdt::parse(&bytes).unwrap().discover_memory().unwrap();
    assert_eq!(memory.ram().len() as u64, MAX_MEMORY_REGIONS);
}

/// The RAM of the boot memory map tests, 128 MiB from 0.
const RAM: Span = Span {
    start: 0,
    size: 0x800_0000,
};

/// Four spans of boot storage on pages of their own.
const BOOT: [Span; 5] = [
    Span {
        start: 0x1000,
        size: 0x10,
    },
    Span {
        start: 0x3000,
        size: 0x10,
    },
    Span {
        start: 0x5000,
        size: 0x10,
    },
    Span {
        start: 0x7000,
        size: 0x10,
    },
    Span {
        start: 0x9000,
        size: 0x10,
    },
];

#[test]
fn boot_storage_of_four_spans_is_accepted() {
    let plan = MemoryPlan::all_ram(&[RAM], &BOOT[..4], &[]).unwrap();
    assert_eq!(
        plan.boot_ranges(),
        &[
            Span::new(0x1000, 0x1000).unwrap(),
            Span::new(0x3000, 0x1000).unwrap(),
            Span::new(0x5000, 0x1000).unwrap(),
            Span::new(0x7000, 0x1000).unwrap(),
        ]
    );
}

#[test]
fn boot_storage_of_five_spans_fails_with_capacity() {
    assert_eq!(
        MemoryPlan::all_ram(&[RAM], &BOOT, &[]).unwrap_err(),
        PlanError::Capacity
    );
}

/// Two further spans of a boot memory make 4 spans of boot storage, the
/// image, the tree and the two in this order, each by whole pages; three
/// and four fail with `Capacity`.
#[test]
fn a_boot_memory_takes_two_further_spans_and_fails_with_three() {
    let bytes = pi5();
    let memory = Fdt::parse(&bytes)
        .unwrap()
        .discover_boot_memory(PI5_HAND_OVER, DTB, IMAGE)
        .unwrap();
    let window = Span::new(0x40_0000, 0x10_0000).unwrap();
    let more = [
        Span::new(0x30_0000, 0x1000).unwrap(),
        Span::new(0x31_0000, 1).unwrap(),
        Span::new(0x32_0000, 0x1000).unwrap(),
        Span::new(0x33_0000, 0x1000).unwrap(),
    ];
    let plan = MemoryPlan::from_boot_memory(&memory, window, &more[..2]).unwrap();
    assert_eq!(
        plan.boot_ranges(),
        &[
            IMAGE,
            Span::new(DTB, 0x1000).unwrap(),
            Span::new(0x30_0000, 0x1000).unwrap(),
            Span::new(0x31_0000, 0x1000).unwrap(),
        ]
    );
    assert_eq!(plan.managed_banks(), &[window]);
    for count in [3, 4] {
        assert_eq!(
            MemoryPlan::from_boot_memory(&memory, window, &more[..count]).unwrap_err(),
            PlanError::Capacity
        );
    }
}

#[test]
fn parse_of_fewer_than_40_bytes_is_truncated() {
    let bytes = minimal();
    assert_eq!(Fdt::parse(&bytes[..39]).unwrap_err(), Error::Truncated);
}

#[test]
fn discover_cpus_without_cpus_is_missing_property() {
    let bytes = minimal();
    assert_eq!(
        Fdt::parse(&bytes)
            .unwrap()
            .discover_cpus(QEMU_HVC_CPUS)
            .unwrap_err(),
        Error::MissingProperty
    );
}

#[test]
fn find_node_with_a_double_slash_is_bad_path() {
    let bytes = minimal();
    let tree = Fdt::parse(&bytes).unwrap();
    assert_eq!(
        tree.find_node("//memory@100000000").unwrap_err(),
        Error::BadPath
    );
    assert_eq!(
        tree.find_node("memory@100000000").unwrap_err(),
        Error::BadPath
    );
    assert_eq!(
        tree.find_node("/memory@100000000/").unwrap_err(),
        Error::BadPath
    );
}

/// The span and its argument end beyond 64 bits: `Overflow`, where the
/// prototype compared the starts first and gave false.
#[test]
fn span_contains_checks_both_ends_before_comparing() {
    let span = Span::new(0x1000, 0x1000).unwrap();
    let beyond = Span {
        start: 0x800,
        size: u64::MAX,
    };
    assert_eq!(span.contains(beyond), Err(Error::Overflow));
    let wide = Span {
        start: 0x1000,
        size: u64::MAX,
    };
    assert_eq!(wide.contains(span), Err(Error::Overflow));
    assert_eq!(span.contains(Span::new(0x1800, 0x800).unwrap()), Ok(true));
    assert_eq!(span.contains(Span::new(0x1800, 0x801).unwrap()), Ok(false));
}
