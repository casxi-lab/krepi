//! The tests of the boot wiring of QEMU virt: the boot memory map of the
//! machine with its exclusions and banks, the layout of the lower kernel
//! set, and the counts of the plans of the two kernel table sets, written
//! from the table pool and the kernel direct map of the page-tables
//! contract for a map of the shape of QEMU virt.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;
use krepi_kernel::page_tables::{
    DIRECT_MAP_TABLES, ENTRIES, KERNEL_TABLES, Tables, direct_map, kernel_map,
};

/// A block, 2 MiB.
const BLOCK_SIZE: u64 = 0x20_0000;

/// The RAM of the runner, 128 MiB at the start of RAM.
const RAM: Span = Span {
    start: 0x4000_0000,
    size: 0x800_0000,
};

/// A tree of 1 MiB at the start of RAM, as QEMU 11.1.2 builds it.
const TREE: Span = Span {
    start: TREE_BASE,
    size: 0x10_0000,
};

/// An image of 576 KiB at 2 MiB above the start of RAM, the start of its
/// link script.
const IMAGE: ImageSpans = ImageSpans {
    text_start: 0x4020_0000,
    text_end: 0x4021_0000,
    rodata_start: 0x4021_0000,
    rodata_end: 0x4021_4000,
    stack_guard: 0x4027_f000,
    stack_bottom: 0x4028_0000,
    image_end: 0x4029_0000,
};

/// The `base` of the pools of the tests, a page of the data of the image.
const BASE: u64 = 0x4021_4000;

/// The physical address size of the Cortex-A76 of QEMU virt.
const BITS: u8 = 40;

/// The boot memory map of the runner's RAM with the image and the tree.
fn map() -> MemoryPlan {
    memory_plan(&[RAM], &[], IMAGE.span(), TREE).unwrap()
}

/// The pages of `[start, end)`.
fn pages(start: u64, end: u64) -> usize {
    ((end - start) / PAGE_SIZE) as usize
}

/// The counts of `plan`, driven to its end.
fn counts<const N: usize>(plan: impl Plan<N>) -> Counts {
    let mut counts = Counts::new();
    let mut counted = Counted {
        plan,
        counts: &mut counts,
    };
    while counted.next_step().is_some() {}
    counts
}

#[test]
fn the_boot_storage_is_the_image_and_then_the_tree() {
    let map = map();
    assert_eq!(map.ram(), &[RAM]);
    assert_eq!(map.boot_ranges(), &[IMAGE.span(), TREE]);
    assert_eq!(map.firmware_ranges(), &[]);
    assert_eq!(map.managed_banks(), &[RAM]);
    let mut ranges = map.available_ranges();
    let usable: Vec<Span> = std::iter::from_fn(|| ranges.next()).collect();
    let below = Span {
        start: 0x4010_0000,
        size: 0x10_0000,
    };
    let above = Span {
        start: IMAGE.image_end,
        size: RAM.start + RAM.size - IMAGE.image_end,
    };
    assert_eq!(usable, [below, above]);
}

#[test]
fn the_exclusions_name_the_image_the_tree_and_the_firmware() {
    let firmware = ReservedRegion {
        span: Span {
            start: 0x4700_0800,
            size: 0x100,
        },
        no_map: true,
        reusable: false,
    };
    let map = memory_plan(&[RAM], &[firmware], IMAGE.span(), TREE).unwrap();
    let unused = Exclusion {
        range: PhysRange::new(0, PAGE_SIZE).unwrap(),
        owner: Excluder::Firmware,
    };
    let mut out = [unused; EXCLUSION_RECORDS];
    assert_eq!(exclusions(&map, &mut out), Ok(3));
    let expected = [
        (IMAGE.text_start, 0x9_0000, Excluder::Image),
        (TREE.start, TREE.size, Excluder::BootStorage),
        (0x4700_0000, PAGE_SIZE, Excluder::Firmware),
    ];
    for (record, (start, len, owner)) in out.iter().zip(expected) {
        assert_eq!(record.range, PhysRange::new(start, len).unwrap());
        assert_eq!(record.owner, owner);
    }
    let mut banks_out = [PhysRange::new(0, PAGE_SIZE).unwrap(); BANKS];
    assert_eq!(banks(&map, &mut banks_out), Ok(1));
    assert_eq!(banks_out[0], PhysRange::new(RAM.start, RAM.size).unwrap());
    assert!(ownership(&map).is_ok());
}

#[test]
fn the_layout_maps_the_image_the_tree_and_the_devices() {
    let guards = [IMAGE.stack_guard];
    let layout = layout(&IMAGE, TREE, &guards).unwrap();
    assert_eq!(layout.count, 7);
    assert_eq!(layout.guards, &[IMAGE.stack_guard]);
    let expected = [
        (0x4020_0000, 0x1_0000, LayoutKind::ReadExecute),
        (0x4021_0000, 0x4000, LayoutKind::ReadOnly),
        (0x4021_4000, 0x6_b000, LayoutKind::ReadWrite),
        (0x4028_0000, 0x1_0000, LayoutKind::ReadWrite),
        (0x4000_0000, 0x10_0000, LayoutKind::ReadOnly),
        (0x0900_0000, 0x1000, LayoutKind::Device),
        (0x0800_0000, 0x2_0000, LayoutKind::Device),
    ];
    for (range, (start, len, kind)) in layout.ranges.iter().zip(expected) {
        assert_eq!(range.range, PhysRange::new(start, len).unwrap());
        assert_eq!(range.kind, kind);
    }
}

#[test]
fn an_empty_part_of_the_image_is_refused() {
    let image = ImageSpans {
        stack_guard: IMAGE.rodata_end,
        ..IMAGE
    };
    let guards = [image.stack_guard];
    assert_eq!(
        layout(&image, TREE, &guards).err(),
        Some(OwnershipError::InvalidRange)
    );
}

#[test]
fn the_lower_kernel_set_has_the_tables_and_pages_of_the_contract() {
    let mut set = Tables::<KERNEL_TABLES, false>::new([[0; ENTRIES]; KERNEL_TABLES]);
    let guards = [IMAGE.stack_guard];
    let layout = layout(&IMAGE, TREE, &guards).unwrap();
    let counts = counts(kernel_map(&mut set, layout, BASE, BITS).unwrap());
    // 6 + the 2 MiB blocks that the image touches, 1 on QEMU virt: the
    // root, the level 2 tables of the 1 GiB slots of the RAM and of the
    // devices, and the level 3 tables of the image, the tree, the PL011
    // and the GICv2.
    let image_blocks = (IMAGE.image_end - IMAGE.text_start).div_ceil(BLOCK_SIZE) as usize;
    assert_eq!(counts.tables, 6 + image_blocks);
    assert_eq!(counts.blocks, 0);
    let image =
        pages(IMAGE.text_start, IMAGE.stack_guard) + pages(IMAGE.stack_bottom, IMAGE.image_end);
    let tree = pages(TREE.start, TREE.start + TREE.size);
    let devices = 1 + pages(0x0800_0000, 0x0802_0000);
    assert_eq!(counts.pages, image + tree + devices);
}

#[test]
fn the_direct_map_has_the_tables_blocks_and_pages_of_the_contract() {
    let mut set = Tables::<DIRECT_MAP_TABLES, true>::new([[0; ENTRIES]; DIRECT_MAP_TABLES]);
    let map = map();
    let counts = counts(direct_map(&mut set, &map, BASE, BITS).unwrap());
    // The root, one level 2 table and one level 3 table for each of the
    // two blocks that the usable ranges cover in part: below the image,
    // after the tree, and above it.
    let block = IMAGE.image_end.div_ceil(BLOCK_SIZE) * BLOCK_SIZE;
    assert_eq!(counts.tables, 4);
    assert_eq!(
        counts.blocks,
        ((RAM.start + RAM.size - block) / BLOCK_SIZE) as usize
    );
    assert_eq!(counts.blocks, 62);
    let below = pages(TREE.start + TREE.size, IMAGE.text_start);
    let above = pages(IMAGE.image_end, block);
    assert_eq!(counts.pages, below + above);
    assert_eq!(counts.pages, 256 + 368);
}

#[test]
fn a_counted_plan_passes_its_steps_on_unchanged() {
    let mut first = Tables::<KERNEL_TABLES, false>::new([[0; ENTRIES]; KERNEL_TABLES]);
    let mut second = Tables::<KERNEL_TABLES, false>::new([[0; ENTRIES]; KERNEL_TABLES]);
    let guards = [IMAGE.stack_guard];
    let layout = layout(&IMAGE, TREE, &guards).unwrap();
    let mut plain = kernel_map(&mut first, layout, BASE, BITS).unwrap();
    let mut counts = Counts::new();
    let mut counted = Counted {
        plan: kernel_map(&mut second, layout, BASE, BITS).unwrap(),
        counts: &mut counts,
    };
    let plain: Vec<Step> = std::iter::from_fn(|| plain.next_step()).collect();
    let counted: Vec<Step> = std::iter::from_fn(|| counted.next_step()).collect();
    assert_eq!(plain, counted);
    assert_eq!(counted.last(), Some(&Step::Sync));
}

#[test]
fn counts_classify_the_steps() {
    let mut counts = Counts::new();
    for step in [
        Step::Zero(1),
        Step::Store(1, 0, 0x4000_0000 | ACCESS_FLAG | BLOCK),
        Step::Store(1, 1, 0x4000_0000 | ACCESS_FLAG | TABLE_OR_PAGE),
        Step::Store(0, 1, 0x4000_1000 | TABLE_OR_PAGE),
        Step::Fence,
        Step::Sync,
        Step::Invalidate(0),
    ] {
        counts.count(step);
    }
    let expected = Counts {
        tables: 2,
        blocks: 1,
        pages: 1,
    };
    assert_eq!(counts, expected);
    assert_eq!(Counts::default(), Counts::new());
}
