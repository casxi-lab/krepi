//! The vectors of `src/platform/mapping.rs` of the contract: the direct
//! map. Each is built in an upper set at `base` `0x80000` with width 40.
//!
//! Feature: krepi.kernel.kernel-memory

use super::models::check_direct_map;
use super::*;

/// The `base` of the direct maps of the vectors.
const DIRECT: u64 = 0x8_0000;

/// `dm-01`.
#[test]
fn reservations_and_boot_pages_break_blocks_without_writable_aliases() {
    let ram = span(0, 0x100_0000);
    let firmware = ReservedRegion {
        span: span(0x60_0fff, 2),
        no_map: false,
        reusable: true,
    };
    let memory = MemoryPlan::new(ram, &[ram], &[span(DIRECT, 0x1000)], &[firmware]).unwrap();
    let mut t = set::<8, true>();
    let steps = direct(&mut t, &memory, DIRECT, BITS).unwrap();
    assert_eq!(counts(&steps), (0xff_d000, 6, 1021));
    for pa in [0x8_0000, 0x60_0000, 0x60_1000] {
        let page = t.lookup_page(DIRECT_BASE | pa, DIRECT, BITS);
        assert_eq!(page, Err(TableError::NotMapped));
    }
    let block = t.lookup_block(DIRECT_BASE | 0x20_0000, DIRECT, BITS);
    assert_eq!(block, Ok(0x60_0000_0020_0705));
    let page = t.lookup_page(DIRECT_BASE | 0x8_1000, DIRECT, BITS);
    assert_eq!(page, Ok(0x60_0000_0008_1707));
    let page = t.lookup_page(DIRECT_BASE | 0x60_2000, DIRECT, BITS);
    assert_eq!(page, Ok(0x60_0000_0060_2707));
    assert_eq!(t.used(), 4);
}

/// `dm-02`.
#[test]
fn mapping_above_four_gib_keeps_pa_bits_and_omits_ram_outside_the_window() {
    let low = span(0, 0x20_0000);
    let high = span(0x1_0000_0000, 0x40_0000);
    let memory = MemoryPlan::new(high, &[low, high], &[span(DIRECT, 0x1000)], &[]).unwrap();
    let mut t = set::<3, true>();
    let steps = direct(&mut t, &memory, DIRECT, BITS).unwrap();
    assert_eq!(counts(&steps), (0x40_0000, 2, 0));
    let block = t.lookup_block(DIRECT_BASE | 0x1_0000_0000, DIRECT, BITS);
    assert_eq!(block, Ok(0x60_0001_0000_0705));
    let page = t.lookup_page(DIRECT_BASE, DIRECT, BITS);
    assert_eq!(page, Err(TableError::NotMapped));
    let block = t.lookup_block(DIRECT_BASE | 0x1_0040_0000, DIRECT, BITS);
    assert_eq!(block, Err(TableError::NotMapped));
}

/// `dm-03`.
#[test]
fn exhausted_storage_never_reports_a_complete_map() {
    let ram = span(0, 0x40_0000);
    let memory = MemoryPlan::new(ram, &[ram], &[span(DIRECT, 0x1000)], &[]).unwrap();
    let mut t = set::<2, true>();
    let map = direct(&mut t, &memory, DIRECT, BITS);
    assert_eq!(map, Err(TableError::OutOfTables));
    assert_eq!(t.used(), 1);
}

/// `dm-04`: the page oracle of the vector is the page model of
/// `check_direct_map`, and the lines of the vector are 4,092 blocks, the two
/// blocks of the hole without a page, and the blocks of `0x80000` and
/// `0x1fffff000` in pages without them.
#[test]
fn every_descriptor_in_sparse_eight_gib_matches_a_separate_page_oracle() {
    let banks = [
        span(0, 0x3fc0_0000),
        span(0x4000_0000, 0xc000_0000),
        span(0x1_0000_0000, 0x1_0000_0000),
    ];
    let boot = span(DIRECT, 0x1000);
    let firmware = ReservedRegion {
        span: span(0x1_ffff_f001, 1),
        no_map: true,
        reusable: false,
    };
    let memory = MemoryPlan::all_ram(&banks, &[boot], &[firmware]).unwrap();
    let mut t = set::<16, true>();
    let steps = direct(&mut t, &memory, DIRECT, BITS).unwrap();
    let model = check_direct_map(&t, DIRECT, &banks, &[boot, firmware.span], 0x2_0000_0000);
    assert_eq!(model, (0x1_ffbf_e000, 4092, 2 * 511));
    assert_eq!(counts(&steps), model);
}
