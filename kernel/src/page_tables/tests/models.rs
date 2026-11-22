//! The direct maps of the five Raspberry Pi 5 models: the banks of the fdt
//! contract, inferred for 1, 2, 4 and 16 GB and measured for 8 GB, and the
//! exclusions of the contract's table pool (`atf@0`, the image and the
//! device tree), in a set of the capacity of the direct map's pool, checked
//! against a page model and the tables, blocks and pages of the contract's
//! table. The vector `dm-04` maps the 8 GB banks with other exclusions.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

/// The firmware's reservation `atf@0`.
const ATF: Span = Span {
    start: 0,
    size: 0x8_0000,
};

/// The image.
const IMAGE: Span = Span {
    start: 0x8_0000,
    size: 0x12_7000,
};

/// The device tree.
const TREE: Span = Span {
    start: 0x20_0000,
    size: 0x1_3ad4,
};

/// The bank below the hole of 4 MiB under 1 GiB, the first of every model.
const LOW: Span = Span {
    start: 0,
    size: 0x3fc0_0000,
};

/// Checks every 2 MiB block below `end` of the executed direct map `t`
/// against a page model of the banks and the exclusions: a page is mapped
/// when it lies in a bank and no exclusion touches it, and a block is one
/// leaf when it lies in one bank and no exclusion touches it. A leaf maps
/// its own physical address as `ReadWrite`, by the descriptors of the kind
/// table. Gives the bytes, blocks and pages of the model.
pub(super) fn check_direct_map<const N: usize>(
    t: &Tables<N, true>,
    base: u64,
    banks: &[Span],
    exclusions: &[Span],
    end: u64,
) -> (u64, u64, u64) {
    let mapped = |start: u64, size: u64| {
        let inside = banks
            .iter()
            .any(|b| b.start <= start && start + size <= b.start + b.size);
        let touched = exclusions
            .iter()
            .any(|x| x.start < start + size && start < x.start + x.size);
        inside && !touched
    };
    let (mut blocks, mut pages) = (0, 0);
    for block in (0..end).step_by(BLOCK_SIZE as usize) {
        let leaf = t.lookup_block(DIRECT_BASE | block, base, BITS);
        if mapped(block, BLOCK_SIZE) {
            assert_eq!(leaf, Ok(0x60_0000_0000_0705 | block), "{block:#x}");
            blocks += 1;
            continue;
        }
        assert_eq!(leaf, Err(TableError::NotMapped), "{block:#x}");
        for pa in (block..block + BLOCK_SIZE).step_by(PAGE_SIZE as usize) {
            let page = t.lookup_page(DIRECT_BASE | pa, base, BITS);
            if mapped(pa, PAGE_SIZE) {
                assert_eq!(page, Ok(0x60_0000_0000_0707 | pa), "{pa:#x}");
                pages += 1;
            } else {
                assert_eq!(page, Err(TableError::NotMapped), "{pa:#x}");
            }
        }
    }
    (blocks * BLOCK_SIZE + pages * PAGE_SIZE, blocks, pages)
}

/// The direct map of a model of the banks `banks`, against the page model,
/// with the tables in use, the blocks and the pages of the contract.
fn model(banks: &[Span], expected: (usize, u64, u64)) {
    let firmware = ReservedRegion {
        span: ATF,
        no_map: true,
        reusable: false,
    };
    let memory = MemoryPlan::all_ram(banks, &[IMAGE, TREE], &[firmware]).unwrap();
    let mut t = set::<DIRECT_MAP_TABLES, true>();
    let steps = direct(&mut t, &memory, BASE, BITS).unwrap();
    let last = banks[banks.len() - 1];
    let end = last.start + last.size;
    let model = check_direct_map(&t, BASE, banks, &[ATF, IMAGE, TREE], end);
    assert_eq!(counts(&steps), model);
    assert_eq!((t.used(), model.1, model.2), expected);
}

#[test]
fn pi5_1gb_direct_map_matches_the_page_model() {
    model(&[LOW], (4, 508, 581));
}

#[test]
fn pi5_2gb_direct_map_matches_the_page_model() {
    model(&[LOW, span(0x4000_0000, 0x4000_0000)], (5, 1020, 581));
}

#[test]
fn pi5_4gb_direct_map_matches_the_page_model() {
    model(&[LOW, span(0x4000_0000, 0xc000_0000)], (7, 2044, 581));
}

#[test]
fn pi5_8gb_direct_map_matches_the_page_model() {
    let banks = [
        LOW,
        span(0x4000_0000, 0xc000_0000),
        span(0x1_0000_0000, 0x1_0000_0000),
    ];
    model(&banks, (11, 4092, 581));
}

#[test]
fn pi5_16gb_direct_map_matches_the_page_model() {
    let banks = [
        LOW,
        span(0x4000_0000, 0xc000_0000),
        span(0x1_0000_0000, 0x3_0000_0000),
    ];
    model(&banks, (19, 8188, 581));
}
