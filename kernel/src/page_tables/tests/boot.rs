//! The maps of the boot wiring on the host: the refusal of a layout that
//! would map a page writable and executable, the bits of each kind of a
//! layout, the guard pages, and the execute-never leaves of the direct map.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

/// The text of an image.
const TEXT: (u64, u64, LayoutKind) = (0x4008_0000, 0x2000, LayoutKind::ReadExecute);

/// Its read-only data.
const RODATA: (u64, u64, LayoutKind) = (0x4008_2000, 0x1000, LayoutKind::ReadOnly);

/// Its data.
const DATA: (u64, u64, LayoutKind) = (0x4008_3000, 0x3000, LayoutKind::ReadWrite);

/// Its stack, above the guard page `0x4008_6000`.
const STACK: (u64, u64, LayoutKind) = (0x4008_7000, 0x4000, LayoutKind::ReadWrite);

/// An address in the guard page of the stack.
const GUARD: u64 = 0x4008_6ff8;

/// The registers of the console.
const CONSOLE: (u64, u64, LayoutKind) = (0x900_0000, 0x1000, LayoutKind::Device);

/// Whether the set holds no valid entry.
fn empty<const N: usize, const UPPER: bool>(t: &Tables<N, UPPER>) -> bool {
    t.pool.iter().all(|table| table.iter().all(|&d| d == 0))
}

/// Text and data on page boundaries that share a page, in either order: no
/// page is mapped writable and executable.
#[test]
fn kernel_map_refuses_text_and_data_on_one_page() {
    let mut t = set::<KERNEL_TABLES, false>();
    let data = (0x4008_1000, 0x2000, LayoutKind::ReadWrite);
    for ranges in [[TEXT, data], [data, TEXT]] {
        let map = kernel(&mut t, layout(&ranges, &[]), BASE, BITS);
        assert_eq!(map, Err(TableError::AlreadyMapped));
        assert_eq!(t.used(), 1);
    }
    assert!(empty(&t));
}

#[test]
fn kernel_map_gives_each_layout_kind_its_bits() {
    let mut t = set::<KERNEL_TABLES, false>();
    let ranges = [DATA, CONSOLE, TEXT, RODATA];
    let steps = kernel(&mut t, layout(&ranges, &[]), BASE, BITS).unwrap();
    // AP[2], PXN, UXN and AttrIndx of a page of each range.
    for (pa, bits) in [
        (0x4008_0000, [1, 0, 1, 1]),
        (0x4008_1000, [1, 0, 1, 1]),
        (0x4008_2000, [1, 1, 1, 1]),
        (0x4008_3000, [0, 1, 1, 1]),
        (0x4008_5000, [0, 1, 1, 1]),
        (0x900_0000, [0, 1, 1, 0]),
    ] {
        let d = t.lookup_page(pa, BASE, BITS).unwrap();
        assert_eq!(d & 0x0000_ffff_ffff_f000, pa);
        let columns = [(d >> 7) & 1, (d >> 53) & 1, (d >> 54) & 1, (d >> 2) & 7];
        assert_eq!(columns, bits, "{pa:#x}");
    }
    // The root, and a level 2 and a level 3 table in each of two 1 GiB
    // slots.
    assert_eq!(t.used(), 5);
    assert_eq!(counts(&steps), (0x7000, 0, 7));
}

#[test]
fn kernel_map_leaves_guard_pages_invalid() {
    let mut t = set::<KERNEL_TABLES, false>();
    let ranges = [TEXT, RODATA, DATA, STACK];
    let steps = kernel(&mut t, layout(&ranges, &[GUARD]), BASE, BITS).unwrap();
    let guard = t.lookup_page(0x4008_6000, BASE, BITS);
    assert_eq!(guard, Err(TableError::NotMapped));
    for pa in [0x4008_5000, 0x4008_7000] {
        assert!(t.lookup_page(pa, BASE, BITS).is_ok());
    }
    // No step writes the entry of the guard page.
    let (table, _) = t.page_leaf(0x4008_7000, BASE).unwrap();
    let entry = (0x4008_6000 >> 12) & 511;
    for step in &steps {
        if let Step::Store(t3, index, _) = *step {
            assert!(t3 != table || index != entry);
        }
    }
}

#[test]
fn kernel_map_refuses_a_range_over_a_guard() {
    let mut t = set::<KERNEL_TABLES, false>();
    // The stack grown down over its guard page, and a guard address at the
    // last byte of a page of the data.
    let stack = (0x4008_6000, 0x5000, LayoutKind::ReadWrite);
    for (ranges, guard) in [([TEXT, stack], GUARD), ([TEXT, DATA], 0x4008_5fff)] {
        let map = kernel(&mut t, layout(&ranges, &[guard]), BASE, BITS);
        assert_eq!(map, Err(TableError::AlreadyMapped));
        assert_eq!(t.used(), 1);
    }
    assert!(empty(&t));
}

#[test]
fn direct_map_leaves_are_execute_never() {
    let memory = MemoryPlan::all_ram(&[span(0, 0x100_0000)], &[span(0x8_0000, 0x1000)], &[]);
    let mut t = set::<8, true>();
    let steps = direct(&mut t, &memory.unwrap(), BASE, BITS).unwrap();
    // Every leaf, a store with the access flag, has the bits of
    // `ReadWrite`, PXN and UXN among them, as a block or a page.
    let mut leaves = 0;
    for step in &steps {
        if let Step::Store(_, _, d) = *step {
            if d & (1 << 10) != 0 {
                let bits = d & !0x0000_ffff_ffff_f000;
                assert!(bits == 0x60_0000_0000_0705 || bits == 0x60_0000_0000_0707);
                leaves += 1;
            }
        }
    }
    assert_eq!(leaves, 7 + 511);
}
