//! The maps of the boot wiring on the host: the refusal of a layout that
//! would map a page writable and executable, the bits of each kind of a
//! layout, the guard pages, the execute-never leaves of the direct map, and
//! the page ownership table of each board shape against its direct map.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;
use crate::fdt::Fdt;
use crate::fdt::tests::{Builder, PI5_HAND_OVER, set_word};
use std::vec;

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

/// A run of pages `[start, end)` with one owner, or none.
type Run = (u64, u64, Option<Owner>);

/// The owner of a free page.
const FREE: Option<Owner> = Some(Owner::Free);

/// The image of every board shape, of the size of the Pi 5 image of the
/// contract's table pool, `[0x80000, 0x1a7000)`.
const IMAGE: u64 = 0x12_7000;

/// A device tree with 2 and 2 cells: the root `compatible`, if any; the RAM
/// node with `ram`; `/reserved-memory` with `atf@0`, `[0, 0x80000)` and
/// `no-map`, when asked; the reservation map `map`; padded to `total` bytes.
fn tree(compatible: Option<&[u8]>, ram: &[Span], atf: bool, map: &[Span], total: usize) -> Vec<u8> {
    let reg = |spans: &[Span]| -> Vec<u8> {
        let words = spans.iter().flat_map(|s| [s.start, s.size]);
        words.flat_map(u64::to_be_bytes).collect()
    };
    let mut b = Builder::default();
    b.reservations.extend(map);
    b.root();
    if let Some(value) = compatible {
        b.property("compatible", value);
    }
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.property("reg", &reg(ram));
    b.end();
    if atf {
        b.begin("reserved-memory");
        b.cells("#address-cells", &[2]);
        b.cells("#size-cells", &[2]);
        b.property("ranges", &[]);
        b.begin("atf@0");
        b.property("reg", &reg(&[span(0, 0x8_0000)]));
        b.property("no-map", &[]);
        b.end();
        b.end();
    }
    b.end();
    let mut bytes = b.finish();
    if total > bytes.len() {
        bytes.resize(total, 0);
        set_word(&mut bytes, 4, total as u32);
    }
    bytes
}

/// The six board shapes, each with its boot memory map, built from its
/// device tree by the discovery, and the free bytes that the contracts give
/// it. QEMU virt: the RAM of `-m 128M` less the page of the tree at its
/// start and the image at `0x4020_0000`. The Pi 5 models: the RAM ranges of
/// the fdt contract, `atf@0` and, on the 8 GB model, the region of 62 bytes
/// in the hole; the image `[0x80000, 0x1a7000)` and the tree `[0x200000,
/// 0x213ad4)`; the blocks and pages of the table of the table pool.
fn shapes() -> Vec<(MemoryPlan, u64)> {
    let ram = span(0x4000_0000, 0x800_0000);
    let bytes = tree(None, &[ram], false, &[], 0);
    let memory = Fdt::parse(&bytes).unwrap().discover_memory().unwrap();
    let dtb = span(ram.start, bytes.len() as u64);
    let boot = [span(0x4020_0000, IMAGE), dtb];
    let qemu = MemoryPlan::new(ram, memory.ram(), &boot, memory.reserved());
    let mut shapes = vec![(qemu.unwrap(), ram.size - 0x1000 - IMAGE)];
    let low = span(0, 0x3fc0_0000);
    let (two, four) = (span(1 << 30, 1 << 30), span(1 << 30, 3 << 30));
    let hole = [span(0x3fd2_31e0, 0x3e)];
    let models: [(&[Span], u64, &[Span]); 5] = [
        (&[low], 508, &[]),
        (&[low, two], 1020, &[]),
        (&[low, four], 2044, &[]),
        (&[low, four, span(4 << 30, 4 << 30)], 4092, &hole),
        (&[low, four, span(4 << 30, 12 << 30)], 8188, &[]),
    ];
    for (banks, blocks, map) in models {
        let compatible = b"raspberrypi,5-model-b\0brcm,bcm2712\0";
        let bytes = tree(Some(compatible), banks, true, map, 0x1_3ad4);
        let tree = Fdt::parse(&bytes).unwrap();
        let memory = tree.discover_boot_memory(PI5_HAND_OVER, 0x20_0000, span(0x8_0000, IMAGE));
        let memory = memory.unwrap();
        assert_eq!(memory.dtb(), span(0x20_0000, 0x1_3ad4));
        let boot = [memory.image(), memory.dtb()];
        let plan = MemoryPlan::all_ram(memory.ram(), &boot, memory.reserved()).unwrap();
        shapes.push((plan, blocks * BLOCK_SIZE + 581 * PAGE_SIZE));
    }
    shapes
}

/// The exclusions `(start, end, owner)` of `exclusions`, rounded out to
/// whole pages.
fn pages(exclusions: &[Exclusion]) -> Vec<(u64, u64, Excluder)> {
    let mut pages = Vec::new();
    for x in exclusions {
        let end = x.range.end().next_multiple_of(PAGE_SIZE);
        pages.push((x.range.start & !(PAGE_SIZE - 1), end, x.owner));
    }
    pages
}

/// Pushes the pieces of `[start, end)` cut at the ends of the exclusions
/// `cuts`, each with the first owner, in the order firmware, image, boot
/// storage, which is the order of `Excluder`, of the exclusions that touch
/// it, or `none`.
fn pieces(start: u64, end: u64, cuts: &[(u64, u64, Excluder)], none: Option<Owner>) -> Vec<Run> {
    let mut points: Vec<u64> = cuts.iter().flat_map(|c| [c.0, c.1]).collect();
    points.retain(|&p| start < p && p < end);
    points.extend([start, end]);
    points.sort();
    points.dedup();
    let piece = |p: &[u64]| {
        let first = cuts
            .iter()
            .filter(|c| c.0 <= p[0] && p[0] < c.1)
            .min_by_key(|c| c.2 as u8);
        (p[0], p[1], first.map(|c| Owner::Excluded(c.2)).or(none))
    };
    points.windows(2).map(piece).collect()
}

/// Runs sorted, checked to be disjoint and joined where they meet with one
/// owner: the maximal runs of one owner.
fn maximal(mut runs: Vec<Run>) -> Vec<Run> {
    runs.sort_by_key(|run| run.0);
    let mut joined: Vec<Run> = Vec::new();
    for run in runs {
        match joined.last_mut() {
            Some(last) if last.1 == run.0 && last.2 == run.2 => last.1 = run.1,
            Some(last) => {
                assert!(last.1 <= run.0, "{last:x?} and {run:x?} overlap");
                joined.push(run);
            }
            None => joined.push(run),
        }
    }
    joined
}

/// The owners of the pages of a page ownership table, read from its
/// representation: its extents with their holders, and the pages of its
/// banks in no extent with the first owner of the exclusion records that
/// touch them.
fn owners<const E: usize, const X: usize>(t: &Ownership<E, X>) -> Vec<Run> {
    let records = pages(&t.exclusions[..t.exclusion_count]);
    let extents = &t.extents[..t.extent_count];
    let mut runs = Vec::new();
    for e in extents {
        let owner = match e.holding {
            Holding::Free => Owner::Free,
            Holding::Held(owner, generation, state) => Owner::Held(owner, generation, state),
        };
        runs.push((e.range.start, e.range.end(), Some(owner)));
    }
    for bank in &t.banks[..t.bank_count] {
        let mut at = bank.start;
        for e in extents.iter().filter(|e| bank.overlaps(e.range)) {
            runs.extend(pieces(at, e.range.start, &records, None));
            at = e.range.end();
        }
        runs.extend(pieces(at, bank.end(), &records, None));
    }
    maximal(runs)
}

/// The pages that an executed direct map maps, walked from the root of its
/// pool at `BASE`, each leaf checked to map its own physical address as
/// `ReadWrite`.
fn mapped<const N: usize>(t: &Tables<N, true>) -> Vec<Run> {
    let table = |d: u64| ((d & 0x0000_ffff_ffff_f000) - BASE) as usize / 0x1000;
    let mut runs = Vec::new();
    for (i, &d1) in t.pool[0].iter().enumerate().filter(|e| *e.1 != 0) {
        for (j, &d2) in t.pool[table(d1)].iter().enumerate().filter(|e| *e.1 != 0) {
            let block = (i as u64) << 30 | (j as u64) << 21;
            if d2 & 3 == 1 {
                assert_eq!(d2, 0x60_0000_0000_0705 | block);
                runs.push((block, block + BLOCK_SIZE, FREE));
                continue;
            }
            for (k, &d3) in t.pool[table(d2)].iter().enumerate().filter(|e| *e.1 != 0) {
                let pa = block | (k as u64) << 12;
                assert_eq!(d3, 0x60_0000_0000_0707 | pa);
                runs.push((pa, pa + PAGE_SIZE, FREE));
            }
        }
    }
    maximal(runs)
}

/// One board shape: its page ownership table from the managed banks, the
/// boot storage (the image first) and the firmware reservations of its boot
/// memory map, and its direct map, executed; each against a model of the
/// pages: a page of a managed bank is excluded, with the first owner of the
/// exclusions that touch it, or free. The runs give each page one owner, so
/// equal lists of runs are an equal owner of every page.
fn check_shape(memory: &MemoryPlan, free: u64) {
    let phys = |s: &Span| range(s.start, s.size);
    let banks: Vec<PhysRange> = memory.managed_banks().iter().map(phys).collect();
    let boot = memory.boot_ranges().len();
    let mut exclusions = Vec::new();
    for (i, s) in memory.reservations().iter().enumerate() {
        let owner = match i {
            0 => Excluder::Image,
            i if i < boot => Excluder::BootStorage,
            _ => Excluder::Firmware,
        };
        let range = phys(s);
        exclusions.push(Exclusion { range, owner });
    }
    let table = Ownership::<EXTENTS, EXCLUSION_RECORDS>::new(1, &banks, &exclusions).unwrap();
    let mut t = set::<DIRECT_MAP_TABLES, true>();
    direct(&mut t, memory, BASE, BITS).unwrap();
    let cuts = pages(&exclusions);
    let bank_pieces = |b: &PhysRange| pieces(b.start, b.end(), &cuts, FREE);
    let model = maximal(banks.iter().flat_map(bank_pieces).collect());
    let free_runs: Vec<Run> = model.iter().filter(|r| r.2 == FREE).copied().collect();
    assert_eq!(owners(&table), model);
    assert_eq!(mapped(&t), free_runs);
    assert_eq!(free_runs.iter().map(|r| r.1 - r.0).sum::<u64>(), free);
    assert_eq!(table.stats().free, free);
    for &(start, end, owner) in &model {
        for pa in [start, end - PAGE_SIZE] {
            assert_eq!(table.owner(pa), owner, "{pa:#x}");
            let page = t.lookup_page(DIRECT_BASE | pa, BASE, BITS);
            let slot = pa & !(BLOCK_SIZE - 1);
            let block = t.lookup_block(DIRECT_BASE | slot, BASE, BITS);
            let maps = page == Ok(0x60_0000_0000_0707 | pa);
            let maps = maps || block == Ok(0x60_0000_0000_0705 | slot);
            assert_eq!(maps, owner == FREE, "{pa:#x}");
        }
    }
}

/// The page ownership table of QEMU virt and of the five Pi 5 models gives
/// every managed page exactly one owner, that of the model, and its free
/// pages are exactly the pages of the direct map.
#[test]
fn boot_owners_match_the_direct_map_on_every_board_shape() {
    let shapes = shapes();
    assert_eq!(shapes.len(), 6);
    for (memory, free) in &shapes {
        check_shape(memory, *free);
    }
}
