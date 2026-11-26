//! The differential tests of the entries that take the profile of a board:
//! each input goes through the entry with the profile of the Pi 5 or of
//! QEMU virt and through the copy of the code before the profiles became
//! values, which names the board, and the two must give the same error or
//! the same value in every field and query. The inputs are the cases of the
//! vector file for those entries; the trees of the other host tests that
//! reach them; trees and values built for the branches of the two codes
//! that these profiles reach, with each loop run 0 times, once and up to
//! its bound; and values from a fixed seed.
//!
//! Feature: krepi.platform.device-tree
//!
//! The comparison shows that the two codes agree on these inputs, not that
//! either is right: the expected values are those of the vectors and of the
//! other host tests. The branches that only other profiles reach have no
//! copy to agree with, and the tests of other profiles cover them.

use super::*;
use crate::fdt::cpus::tests::before::CpuProfile_before;
use crate::fdt::plan::tests::before::Pi5BootMemory_before;

mod lengths;

/// The CPU profiles of the boards and the variants of the copy that name
/// them.
const CPU_PROFILES: [(CpuProfile, CpuProfile_before); 3] = [
    (QEMU_HVC_CPUS, CpuProfile_before::QemuHvc),
    (QEMU_SMC_CPUS, CpuProfile_before::QemuSmc),
    (PI5_CPUS, CpuProfile_before::Pi5),
];

/// The tree and the image of the hand-over tests, the root `compatible` of
/// the Pi 5, `atf@0` and the region of 62 bytes in the hole of the 8 GB
/// model.
const DTB: u64 = 0x20_0000;
const IMAGE: Span = at(0x8_0000, 0x2_0000);
const PI5: &[u8] = b"raspberrypi,5-model-b\0brcm,bcm2712\0";
const ATF: Span = at(0, 0x8_0000);
const HOLE_REGION: Span = at(0x3fd2_31e0, 0x3e);

/// The arguments of `find_available`: size, alignment, minimum and limit.
type Request = (u64, u64, u64, u64);

const fn at(start: u64, size: u64) -> Span {
    Span { start, size }
}

/// The bytes of big-endian cells.
fn be(cells: &[u32]) -> Vec<u8> {
    cells.iter().flat_map(|cell| cell.to_be_bytes()).collect()
}

/// The spans that the queries are asked about: an empty span, one that
/// leaves 64 bits, and for each span of `edges`, a byte and a page at its
/// start, at its last byte, at its end and a page before it, and the span.
fn probes(edges: &[Span]) -> Vec<Span> {
    let mut spans = vec![at(0, 0), at(u64::MAX, 2)];
    for edge in edges {
        let end = edge.start.wrapping_add(edge.size);
        let starts = [
            edge.start,
            end.wrapping_sub(1),
            end,
            edge.start.wrapping_sub(0x1000),
        ];
        for start in starts {
            spans.extend([at(start, 1), at(start, 0x1000)]);
        }
        spans.push(*edge);
    }
    spans
}

/// The requests of `find_available`: those that fail, and from the start
/// of each span of `edges`, of a page, of its size and of its size and 1.
fn requests(edges: &[Span]) -> Vec<Request> {
    let mut requests = vec![
        (0, 0x1000, 0, u64::MAX),
        (1, 0, 0, u64::MAX),
        (1, 3, 0, u64::MAX),
        (1, 1, 5, 5),
        (1, 1, 0, u64::MAX),
        (0x10_0000, 0x20_0000, 0, u64::MAX),
        (0x1000, 1 << 63, 0, u64::MAX),
        (u64::MAX, 0x1000, 0x1000, u64::MAX),
        (0x1000, 0x1000, u64::MAX - 0x800, u64::MAX),
    ];
    for edge in edges {
        let end = edge.start.wrapping_add(edge.size);
        requests.push((0x1000, 0x1000, edge.start, u64::MAX));
        requests.push((edge.size, 1, edge.start, end));
        requests.push((edge.size.wrapping_add(1), 1, 0, u64::MAX));
    }
    requests
}

/// The managed windows of `from_boot_memory`: those that fail, and one of
/// at most 128 MiB at the start of each RAM range.
fn windows(ram: &[Span]) -> Vec<Span> {
    let mut windows = vec![at(0, 0), at(0x1000, 0x800), at(0, 0x800_1000)];
    windows.extend([at(u64::MAX - 0xfff, 0x1000), at(0x3fc0_0000, 0x1000)]);
    for range in ram {
        let size = range.size.min(0x800_0000) & !0xfff;
        windows.push(at(range.start, size.max(0x1000)));
    }
    windows
}

/// The further spans of boot storage of `from_boot_memory`: none, one, two
/// and three, one on the page of the tree and one in the hole.
const MORE: [&[Span]; 6] = [
    &[],
    &[at(0x30_0000, 0x1000)],
    &[at(0x30_0000, 0x1000), at(0x40_0000, 0x2000)],
    &[
        at(0x30_0000, 0x1000),
        at(0x40_0000, 0x2000),
        at(0x50_0000, 1),
    ],
    &[at(DTB, 1)],
    &[at(0x3fc0_0000, 0x1000)],
];

/// What a boot memory map gives: its lists and its usable ranges, its sums,
/// and `contains_ram`, `is_available` and `permits_backing` on `spans`.
type PlanView = (Vec<Vec<Span>>, [u64; 2], Vec<[bool; 3]>);

fn plan_view(plan: &MemoryPlan, spans: &[Span]) -> PlanView {
    let mut lists = vec![plan.ram().to_vec(), plan.managed_banks().to_vec()];
    lists.extend([plan.reservations().to_vec(), plan.boot_ranges().to_vec()]);
    lists.push(plan.firmware_ranges().to_vec());
    let mut ranges = plan.available_ranges();
    let mut usable = Vec::new();
    while let Some(span) = ranges.next() {
        usable.push(span);
    }
    lists.push(usable);
    let sums = [plan.described_bytes(), plan.managed_bytes()];
    let queries = spans.iter().map(|&span| {
        [
            plan.contains_ram(span),
            plan.is_available(span),
            plan.permits_backing(span),
        ]
    });
    (lists, sums, queries.collect())
}

/// What a boot memory gives: its RAM ranges and reserved regions, the
/// number of dynamic reservations and the sum of the RAM, the spans of the
/// tree and of the image, and its answers to `is_available` on `spans` and
/// to `find_available` on `requests`.
type MemoryView = (
    Vec<Span>,
    Vec<ReservedRegion>,
    [u64; 2],
    [Span; 2],
    Vec<Result<bool, Error>>,
    Vec<Result<Option<Span>, Error>>,
);

fn memory_view(memory: &BootMemory, spans: &[Span], requests: &[Request]) -> MemoryView {
    let found = requests.iter().map(|&(size, alignment, minimum, limit)| {
        memory.find_available(size, alignment, minimum, limit)
    });
    (
        memory.ram().to_vec(),
        memory.reserved().to_vec(),
        [memory.dynamic(), memory.ram_bytes()],
        [memory.dtb(), memory.image()],
        spans
            .iter()
            .map(|&span| memory.is_available(span))
            .collect(),
        found.collect(),
    )
}

fn memory_view_before(
    memory: &Pi5BootMemory_before,
    spans: &[Span],
    requests: &[Request],
) -> MemoryView {
    let found = requests.iter().map(|&(size, alignment, minimum, limit)| {
        memory.find_available_before(size, alignment, minimum, limit)
    });
    (
        memory.ram_before().to_vec(),
        memory.reserved_before().to_vec(),
        [memory.dynamic_before(), memory.ram_bytes_before()],
        [memory.dtb_before(), memory.image_before()],
        spans
            .iter()
            .map(|&span| memory.is_available_before(span))
            .collect(),
        found.collect(),
    )
}

/// Checks the boot memory of the tree `bytes` at `dtb_address` with `image`
/// against the copy: the error, or every field and query, with the further
/// requests `extra`, and the boot memory maps of `from_boot_memory` on each
/// window and further spans.
fn check_boot(bytes: &[u8], dtb_address: u64, image: Span, extra: &[Request]) {
    let tree = Fdt::parse(bytes);
    let new = tree.and_then(|tree| tree.discover_boot_memory(PI5_HAND_OVER, dtb_address, image));
    let old = tree.and_then(|tree| tree.discover_pi5_boot_memory_before(dtb_address, image));
    let mut edges = Vec::new();
    if let Ok(memory) = &new {
        edges.extend(memory.ram().iter().chain(&[memory.dtb(), memory.image()]));
        edges.extend(memory.reserved().iter().map(|region| region.span));
    }
    let (spans, mut requests) = (probes(&edges), requests(&edges));
    requests.extend(extra);
    let view = new
        .as_ref()
        .map(|memory| memory_view(memory, &spans, &requests));
    let before = old
        .as_ref()
        .map(|memory| memory_view_before(memory, &spans, &requests));
    assert_eq!(view, before, "{dtb_address:#x} {image:?}");
    let (Ok(new), Ok(old)) = (new, old) else {
        return;
    };
    let view = |plan: MemoryPlan| plan_view(&plan, &spans);
    for window in windows(new.ram()) {
        for more in MORE {
            let plan = MemoryPlan::from_boot_memory(&new, window, more).map(view);
            let before = MemoryPlan::from_pi5_before(&old, window, more).map(view);
            assert_eq!(plan, before, "{window:?} {more:?}");
        }
    }
}

/// The `interrupts` that `validate_timers` is given for a topology of
/// `count` CPUs: the records of the first 0 to 5 private interrupts of
/// QEMU virt with the flags of 1, 2, 4 and `count` CPUs, each also with one
/// cell changed, a byte short and with a record more.
fn timer_inputs(count: u64) -> Vec<Vec<u8>> {
    let mut inputs = Vec::new();
    for cpus in [1, 2, 4, count] {
        let flags = (((1u32 << cpus) - 1) << 8) | 4;
        for records in 0..=5 {
            let ppis = &[13, 14, 11, 10, 12][..records];
            let cells: Vec<u32> = ppis.iter().flat_map(|&ppi| [1, ppi, flags]).collect();
            for changed in 0..=cells.len() {
                let mut cells = cells.clone();
                if let Some(cell) = cells.get_mut(changed) {
                    *cell ^= 1;
                }
                inputs.push(be(&cells));
            }
            let valid = be(&cells);
            inputs.push(valid[..valid.len().saturating_sub(1)].to_vec());
            inputs.push([valid, be(&[1, 13, flags])].concat());
        }
    }
    inputs
}

/// Checks the CPU topology of the tree `bytes` for each profile against
/// the copy: the error, or its count, its profile, the affinities of the
/// indices 0 to 4 and its answers to `validate_timers`, also on the further
/// `interrupts` `extra`.
fn check_cpus(bytes: &[u8], extra: &[Vec<u8>]) {
    let Ok(tree) = Fdt::parse(bytes) else {
        return;
    };
    for (profile, variant) in CPU_PROFILES {
        let view = tree.discover_cpus(profile).map(|topology| {
            let records = timer_inputs(topology.count())
                .into_iter()
                .chain(extra.to_vec());
            let timers = records.map(|records| topology.validate_timers(&records));
            let affinities: Vec<_> = (0..=4).map(|index| topology.affinity(index)).collect();
            let named = topology.profile() == profile;
            (
                topology.count(),
                named,
                affinities,
                timers.collect::<Vec<_>>(),
            )
        });
        let before = tree.discover_cpus_before(variant).map(|topology| {
            let records = timer_inputs(topology.count_before())
                .into_iter()
                .chain(extra.to_vec());
            let timers = records.map(|records| topology.validate_qemu_timers_before(&records));
            let affinities: Vec<_> = (0..=4)
                .map(|index| topology.affinity_before(index))
                .collect();
            let named = topology.profile_before() == variant;
            (
                topology.count_before(),
                named,
                affinities,
                timers.collect::<Vec<_>>(),
            )
        });
        assert_eq!(view, before, "{variant:?}");
    }
}

/// Checks `logical_id` of `mpidr` and the other functions of each profile
/// against the copy.
fn check_logical_id(mpidr: u64) {
    for (profile, variant) in CPU_PROFILES {
        let id = (
            profile.logical_id(mpidr),
            profile.affinity_shift(),
            profile.conduit(),
        );
        let before = (
            variant.logical_id_before(mpidr),
            variant.affinity_shift_before(),
            variant.conduit_before(),
        );
        assert_eq!(id, before, "{mpidr:#x}");
    }
}

/// The entries on a tree that take the profile of a board, by the names of
/// the vectors.
const TREE_ENTRIES: [&str; 5] = [
    "discover_pi5_boot_memory",
    "find_available",
    "from_pi5",
    "discover_cpus",
    "validate_qemu_timers",
];

#[test]
fn the_vector_inputs_agree_with_the_code_before_the_profiles() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let text = std::fs::read_to_string(root.join(VECTORS)).expect("the vector file");
    let mut compared = 0;
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let fields = fields(line.split('\t').nth(1).expect("an input"));
        let value = |key: &str| field(&fields, key).expect(key);
        let number = |key: &str| number64(value(key)).unwrap();
        let entry = value("entry");
        if entry == "logical_id" {
            check_logical_id(number("mpidr"));
            compared += 1;
            continue;
        }
        if !TREE_ENTRIES.contains(&entry) {
            continue;
        }
        compared += 1;
        let bytes = hex_bytes(value("dtb")).unwrap();
        if entry == "discover_cpus" || entry == "validate_qemu_timers" {
            let interrupts = field(&fields, "interrupts").map(|text| hex_bytes(text).unwrap());
            check_cpus(&bytes, interrupts.as_slice());
            continue;
        }
        let (address, image) = (number("dtb_address"), span(value("image")).unwrap());
        let mut requested = Vec::new();
        if entry == "find_available" {
            let request = (
                number("size"),
                number("alignment"),
                number("minimum"),
                number("limit"),
            );
            requested.push(request);
        }
        check_boot(&bytes, address, image, &requested);
        if entry == "from_pi5" {
            let (window, more) = (
                span(value("window")).unwrap(),
                spans(value("more")).unwrap(),
            );
            let tree = Fdt::parse(&bytes).unwrap();
            let new = tree
                .discover_boot_memory(PI5_HAND_OVER, address, image)
                .unwrap();
            let old = tree
                .discover_pi5_boot_memory_before(address, image)
                .unwrap();
            let view = |plan: MemoryPlan| plan_view(&plan, &[window]);
            let plan = MemoryPlan::from_boot_memory(&new, window, &more).map(view);
            assert_eq!(
                plan,
                MemoryPlan::from_pi5_before(&old, window, &more).map(view)
            );
        }
    }
    assert_eq!(compared, 243);
}

/// A hand-over tree as the other host tests build it: the root with 2 and
/// 2 cells and `compatible` when given, the reservation map `map`,
/// `memory@0` with the RAM ranges `ram` when there are any, and
/// `/reserved-memory` with the `no-map` children `children` and, when
/// asked, a dynamic `linux,cma`; padded to `total` bytes when that is more.
fn hand_over_tree(
    compatible: Option<&[u8]>,
    ram: &[Span],
    map: &[Span],
    children: &[(&str, Span)],
    dynamic: bool,
    total: usize,
) -> Vec<u8> {
    let reg = |spans: &[Span]| -> Vec<u8> {
        let words = spans.iter().flat_map(|span| [span.start, span.size]);
        words.flat_map(u64::to_be_bytes).collect()
    };
    let mut b = Builder::default();
    b.reservations.extend(map);
    b.root();
    if let Some(value) = compatible {
        b.property("compatible", value);
    }
    if !ram.is_empty() {
        b.begin("memory@0");
        b.property("device_type", b"memory\0");
        b.property("reg", &reg(ram));
        b.end();
    }
    if !children.is_empty() || dynamic {
        b.begin("reserved-memory");
        b.cells("#address-cells", &[2]);
        b.cells("#size-cells", &[2]);
        b.property("ranges", &[]);
        for (name, span) in children {
            b.begin(name);
            b.property("reg", &reg(&[*span]));
            b.property("no-map", &[]);
            b.end();
        }
        if dynamic {
            b.begin("linux,cma");
            b.property("compatible", b"shared-dma-pool\0");
            b.cells("size", &[0x400_0000]);
            b.property("reusable", &[]);
            b.property("linux,cma-default", &[]);
            b.end();
        }
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

/// The RAM ranges of the five RAM models of the Pi 5.
fn models() -> [Vec<Span>; 5] {
    let (low, gib) = (at(0, 0x3fc0_0000), 0x4000_0000);
    let four = vec![low, at(gib, 3 * gib)];
    let higher = |size| [four.clone(), vec![at(4 * gib, size)]].concat();
    let two = vec![low, at(gib, gib)];
    [
        vec![low],
        two,
        four.clone(),
        higher(4 * gib),
        higher(12 * gib),
    ]
}

#[test]
fn the_trees_of_the_other_tests_agree_with_the_code_before_the_profiles() {
    let mut compared = 0;
    let mut check = |bytes: Vec<u8>, address: u64, image: Span, extra: &[Request]| {
        check_boot(&bytes, address, image, extra);
        compared += 1;
    };
    let atf = [("atf@0", ATF)];
    let tree =
        |ram: &[Span], map: &[Span], total| hand_over_tree(Some(PI5), ram, map, &atf, false, total);
    // The RAM models, also padded with the image of the page-tables tests;
    // the 8 GB model with the region of the hole in the reservation map,
    // padded, or below `/reserved-memory`.
    let padded_image = at(0x8_0000, 0x12_7000);
    for ram in models() {
        check(tree(&ram, &[], 0), DTB, IMAGE, &[]);
        check(tree(&ram, &[], 0x1_3ad4), DTB, padded_image, &[]);
    }
    let eight = &models()[3];
    check(tree(eight, &[HOLE_REGION], 0), DTB, IMAGE, &[]);
    check(
        tree(eight, &[HOLE_REGION], 0x1_3ad4),
        DTB,
        padded_image,
        &[],
    );
    let hole = [atf[0], ("nvram@3fd231e0", HOLE_REGION)];
    check(
        hand_over_tree(Some(PI5), eight, &[], &hole, false, 0),
        DTB,
        IMAGE,
        &[],
    );
    // A tree of one range of 8 GiB at the limit of 128 KiB and 1 byte
    // above it.
    for total in [0x2_0000, 0x2_0001] {
        let ram = [at(0, 0x2_0000_0000)];
        check(
            hand_over_tree(Some(PI5), &ram, &[], &[], false, total),
            DTB,
            IMAGE,
            &[],
        );
    }
    // The error orders: a tree without RAM with an image and with an empty
    // one; a selection of size 0 and one of alignment 3.
    let bare = || hand_over_tree(Some(PI5), &[], &[], &[], false, 0);
    check(bare(), 0x10_0000, at(0x20_0000, 0x1000), &[]);
    check(bare(), 0x10_0000, at(0x20_0000, 0), &[]);
    let one = hand_over_tree(Some(PI5), &[at(0, 0x4000_0000)], &[], &[], false, 0);
    let selections = [(0, 3, 0, 0x1000), (1, 3, 0, 0x1000)];
    check(one, 0x10_0000, at(0x20_0000, 0x1000), &selections);
    // The shape of the shipped tree, with its placeholder RAM and dynamic
    // `linux,cma`, and the 8 GB model of the feature document.
    let shipped = hand_over_tree(Some(PI5), &[at(0, 0x2800_0000)], &[], &atf, true, 0);
    check(shipped, DTB, at(0x8_0000, 0x8_0000), &[]);
    check(tree(eight, &[], 0), DTB, IMAGE, &[]);
    assert_eq!(compared, 20);
}

#[test]
fn built_hand_over_inputs_agree_with_the_code_before_the_profiles() {
    let mut compared = 0;
    let mut check = |bytes: &[u8], address: u64, image: Span, extra: &[Request]| {
        check_boot(bytes, address, image, extra);
        compared += 1;
    };
    let eight = &models()[3];
    let tree = |compatible| hand_over_tree(compatible, eight, &[], &[("atf@0", ATF)], false, 0);
    // The root `compatible`: empty, without its last NUL, with an empty
    // entry, with an entry that is not UTF-8 before and after the two, the
    // two in either order, each alone, neither, longer and shorter names,
    // repeated entries, 3 entries, 2 and 200; and absent.
    let many = [b"a\0".repeat(198), PI5.to_vec()].concat();
    let compatibles: [&[u8]; 16] = [
        b"",
        b"raspberrypi,5-model-b\0brcm,bcm2712",
        b"\0",
        b"raspberrypi,5-model-b\0\0brcm,bcm2712\0",
        b"\xff\0raspberrypi,5-model-b\0brcm,bcm2712\0",
        b"raspberrypi,5-model-b\0brcm,bcm2712\0\xc3\0",
        b"brcm,bcm2712\0raspberrypi,5-model-b\0",
        b"raspberrypi,5-model-b\0",
        b"brcm,bcm2712\0",
        b"vendor,board\0",
        b"raspberrypi,5-model-b-x\0brcm,bcm27120\0",
        b"raspberrypi,5-model\0brcm,bcm271\0",
        b"brcm,bcm2712\0brcm,bcm2712\0raspberrypi,5-model-b\0raspberrypi,5-model-b\0",
        b"vendor,new-revision\0raspberrypi,5-model-b\0brcm,bcm2712\0",
        PI5,
        &many,
    ];
    for compatible in compatibles.iter().map(|&value| Some(value)).chain([None]) {
        check(&tree(compatible), DTB, IMAGE, &[]);
    }
    // The cells of the root: 2 and 2, 1 of either, 3, absent, and values
    // that are not 4 bytes.
    let cells: [(&[u8], &[u8]); 7] = [
        (&[0, 0, 0, 2], &[0, 0, 0, 2]),
        (&[0, 0, 0, 1], &[0, 0, 0, 2]),
        (&[0, 0, 0, 2], &[0, 0, 0, 1]),
        (&[0, 0, 0, 3], &[0, 0, 0, 3]),
        (&[], &[]),
        (&[0, 0, 2], &[0, 0, 0, 2]),
        (&[0, 0, 0, 2], &[0, 0, 0, 0, 0, 0, 0, 2]),
    ];
    for (address, size) in cells {
        let mut b = Builder::default();
        b.begin("");
        for (name, value) in [("#address-cells", address), ("#size-cells", size)] {
            if !value.is_empty() {
                b.property(name, value);
            }
        }
        b.property("compatible", PI5);
        b.begin("memory@0");
        b.property("device_type", b"memory\0");
        b.cells("reg", &[0, 0, 2, 0]);
        b.end();
        b.end();
        check(&b.finish(), DTB, IMAGE, &[]);
    }
    // The address of the tree: each remainder modulo 8, 0, a span that
    // leaves 64 bits, outside the RAM, across its end and across the hole.
    let pi5 = tree(Some(PI5));
    let addresses = [0, 0x1_ffff_fff8, 0x2_0000_0000, 0x3fbf_fff8, u64::MAX - 7];
    for address in (DTB..DTB + 8).chain(addresses) {
        check(&pi5, address, IMAGE, &[]);
    }
    // The image: empty, leaving 64 bits, on the tree, on its first page,
    // next to it on either side, on `atf@0`, outside the RAM and across the
    // hole.
    let after = DTB + pi5.len() as u64;
    let images = [at(0x8_0000, 0), at(u64::MAX - 0xf, 0x20), at(DTB, 0x1000)];
    let images = images
        .into_iter()
        .chain([at(DTB - 0x1000, 0x1001), at(DTB - 0x1000, 0x1000)]);
    let images = images.chain([at(after, 0x1000), at(0, 0x1000), at(0x2_0000_0000, 0x1000)]);
    for image in images.chain([at(0x3fbf_f000, 0x2000)]) {
        check(&pi5, DTB, image, &[]);
    }
    // The size of the tree below the limit, at it and above it; no RAM
    // range, one with 128 reservations of one page between gaps of one
    // page, which a selection of 6 KiB hops one by one, 32 ranges and 33.
    let ranges: Vec<Span> = (0..33).map(|k| at(k << 28, 0x800_0000)).collect();
    let pages: Vec<Span> = (0..128)
        .map(|k| at(0x40_0000 + k * 0x2000, 0x1000))
        .collect();
    let hops = [
        (0x1800, 0x1000, 0x40_0000, u64::MAX),
        (0x1800, 0x1000, 0, 0x50_0000),
    ];
    let shapes = [
        (eight.clone(), Vec::new(), 0x1_ffff),
        (eight.clone(), Vec::new(), 0x2_0000),
        (eight.clone(), Vec::new(), 0x2_0001),
        (Vec::new(), Vec::new(), 0),
        (ranges[..1].to_vec(), pages, 0),
        (ranges[..32].to_vec(), Vec::new(), 0),
        (ranges, Vec::new(), 0),
    ];
    for (ram, map, total) in shapes {
        let bytes = hand_over_tree(Some(PI5), &ram, &map, &[], false, total);
        check(&bytes, DTB, IMAGE, &hops);
    }
    assert_eq!(compared, 53);
}

/// The properties of a node, in their order.
type Properties = Vec<(&'static str, Vec<u8>)>;

/// A CPU node of the affinity `reg`, with the `enable-method` `psci` when
/// asked.
fn cpu(reg: &[u32], enable: bool) -> Properties {
    let mut node = vec![("device_type", b"cpu\0".to_vec())];
    node.extend([
        ("compatible", b"arm,cortex-a76\0".to_vec()),
        ("reg", be(reg)),
    ]);
    if enable {
        node.push(("enable-method", b"psci\0".to_vec()));
    }
    node
}

/// A tree with `/cpus` of the properties `cpus` and the CPU nodes `nodes`,
/// and `/psci` of the properties `psci`, each absent when none.
fn cpu_tree(cpus: Option<Properties>, nodes: &[Properties], psci: Option<Properties>) -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    let begin = |b: &mut Builder, name: &str, properties: &Properties| {
        b.begin(name);
        for (property, value) in properties {
            b.property(property, value);
        }
    };
    if let Some(cpus) = cpus {
        begin(&mut b, "cpus", &cpus);
        for (index, node) in nodes.iter().enumerate() {
            begin(&mut b, &format!("cpu@{index}"), node);
            b.end();
        }
        b.end();
    }
    if let Some(psci) = psci {
        begin(&mut b, "psci", &psci);
        b.end();
    }
    b.end();
    b.finish()
}

/// The properties of `/cpus` with `cells` address cells and `size` size
/// cells, and of `/psci` with the conduit `method` and the `compatible`
/// `list`.
fn cpus_node(cells: u32, size: u32) -> Properties {
    vec![
        ("#address-cells", be(&[cells])),
        ("#size-cells", be(&[size])),
    ]
}

fn psci_node(method: &[u8], list: &[u8]) -> Properties {
    vec![("compatible", list.to_vec()), ("method", method.to_vec())]
}

/// The longest `compatible` list of `/psci`.
const PSCI: &[u8] = b"arm,psci-1.0\0arm,psci-0.2\0arm,psci\0";

#[test]
fn built_cpu_inputs_agree_with_the_code_before_the_profiles() {
    let tree = |nodes: &[Properties], method: &[u8]| {
        cpu_tree(Some(cpus_node(1, 0)), nodes, Some(psci_node(method, PSCI)))
    };
    let (hvc, smc) = (&b"hvc\0"[..], &b"smc\0"[..]);
    // 0 to 4 CPUs at affinity level 0 and 1, with and without the
    // `enable-method` of CPU 0, for each conduit.
    let mut trees = Vec::new();
    for k in 0..8 {
        let (shift, cpu0, method) = ([0, 8][k & 1], k & 2 == 0, [hvc, smc][k >> 2]);
        for count in 0..=4u32 {
            let nodes: Vec<_> = (0..count)
                .map(|id| cpu(&[id << shift], id != 0 || cpu0))
                .collect();
            trees.push(tree(&nodes, method));
        }
    }
    // Repeated, missing, foreign and mixed IDs, and 5 nodes, for each
    // conduit.
    let ids: [&[u32]; 11] = [
        &[0, 1, 1],
        &[0, 2],
        &[1],
        &[0, 1, 2],
        &[0, 4],
        &[0, 0x400],
        &[0, 0x101],
        &[0x100],
        &[0, 0x100, 0x200, 0x300, 0x100],
        &[0, 1, 2, 3, 0],
        &[0, 0x100, 0x200, 0x300, 0x400],
    ];
    for (ids, method) in ids.iter().flat_map(|ids| [(ids, hvc), (ids, smc)]) {
        let nodes: Vec<_> = ids.iter().map(|&id| cpu(&[id], true)).collect();
        trees.push(tree(&nodes, method));
    }
    // IDs of 2 cells, with a high cell of 0 and of 1.
    for high in [0, 1] {
        let nodes: Vec<_> = (0..4).map(|id| cpu(&[high, id << 8], true)).collect();
        trees.push(cpu_tree(
            Some(cpus_node(2, 0)),
            &nodes,
            Some(psci_node(smc, PSCI)),
        ));
    }
    // A second node that is no CPU, disabled, failed, of another model,
    // without `reg`, with `reg` of 2 cells, without `enable-method`, with
    // another one, or with a `device_type` without its NUL.
    let changes: [(&str, &[u8]); 9] = [
        ("device_type", b"l2-cache\0"),
        ("status", b"disabled\0"),
        ("status", b"fail\0"),
        ("compatible", b"arm,cortex-a72\0"),
        ("reg", b""),
        ("reg", &[0, 0, 0, 0, 0, 0, 0, 1]),
        ("enable-method", b""),
        ("enable-method", b"spin-table\0"),
        ("device_type", b"cpu"),
    ];
    for (name, value) in changes {
        let mut second = cpu(&[1], true);
        second.retain(|(property, _)| *property != name);
        if !value.is_empty() {
            second.push((name, value.to_vec()));
        }
        trees.push(tree(&[cpu(&[0], true), second], hvc));
    }
    // `/cpus` absent, disabled, with 1 size cell, with 3 address cells;
    // `/psci` absent, disabled, with another method, without one, with
    // each `compatible` list, another list, one without its last NUL, an
    // empty one and none.
    let two = [cpu(&[0], true), cpu(&[1], true)];
    let mut disabled = cpus_node(1, 0);
    disabled.push(("status", b"disabled\0".to_vec()));
    for cpus in [
        None,
        Some(disabled),
        Some(cpus_node(1, 1)),
        Some(cpus_node(3, 0)),
    ] {
        trees.push(cpu_tree(cpus, &two, Some(psci_node(hvc, PSCI))));
    }
    let mut psci_disabled = psci_node(hvc, PSCI);
    psci_disabled.push(("status", b"disabled\0".to_vec()));
    let mut pscis = vec![None, Some(psci_disabled), Some(psci_node(b"none\0", PSCI))];
    pscis.push(Some(vec![("compatible", PSCI.to_vec())]));
    let lists: [&[u8]; 6] = [
        b"arm,psci-0.2\0",
        b"arm,psci-1.0\0arm,psci-0.2\0",
        b"arm,psci\0",
        b"arm,psci-1.0\0arm,psci-0.2\0arm,psci",
        b"",
        PSCI,
    ];
    pscis.extend(lists.iter().map(|list| Some(psci_node(hvc, list))));
    pscis.push(Some(vec![("method", hvc.to_vec())]));
    for psci in pscis {
        trees.push(cpu_tree(Some(cpus_node(1, 0)), &two, psci));
    }
    // The tree without `/cpus` of the limits, and the one of 3 address
    // cells and 1 size cell of the error orders.
    trees.push(minimal());
    trees.push(cpu_tree(Some(cpus_node(3, 1)), &[], None));
    for tree in &trees {
        check_cpus(tree, &[]);
    }
    assert_eq!(trees.len(), 90);
}

/// The next value of a xorshift generator.
fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

#[test]
fn seeded_values_agree_with_the_code_before_the_profiles() {
    let mut state = 0x9e37_79b9_7f4a_7c15;
    // 4096 values of `MPIDR_EL1` for each profile: random ones, their
    // affinity fields alone, and IDs 0 to 7 at each level with random flag
    // bits and with the U and MT bits.
    for k in 0..4096u64 {
        let (random, id) = (next(&mut state), (k / 4) % 8);
        let at_level = id << [0, 8, 16, 32][(k / 32 % 4) as usize];
        let flags = [random, 0, random & !0xff_00ff_ffff, random & 0xc100_0000];
        let affinity = [0, random & 0xff_00ff_ffff, at_level, at_level];
        check_logical_id(flags[(k % 4) as usize] | affinity[(k % 4) as usize]);
    }
    // 1024 spans and 1024 requests on each of three boot memories.
    let atf = [("atf@0", ATF)];
    let pages = [at(0x40_0000, 0x1000), at(0x40_2000, 0x1000)];
    let memories = [
        hand_over_tree(Some(PI5), &models()[3], &[HOLE_REGION], &atf, false, 0),
        hand_over_tree(Some(PI5), &models()[4], &[], &atf, true, 0),
        hand_over_tree(Some(PI5), &[at(0, 0x4000_0000)], &pages, &atf, false, 0),
    ];
    let mut compared = 0;
    for bytes in &memories {
        let tree = Fdt::parse(bytes).unwrap();
        let new = tree
            .discover_boot_memory(PI5_HAND_OVER, DTB, IMAGE)
            .unwrap();
        let old = tree.discover_pi5_boot_memory_before(DTB, IMAGE).unwrap();
        let (mut spans, mut requests) = (Vec::new(), Vec::new());
        for _ in 0..1024 {
            let [start, size, minimum, limit, power, other] = [0; 6].map(|_| next(&mut state));
            let start = (start % 0x4_0000_0000) & !(0xfff * (start & 1));
            spans.push(at(
                start,
                [1, 0x1000, size % 0x100_0000, size][(size >> 62) as usize],
            ));
            let alignment = [1 << (power % 40), other % 0x10_0000][(other & 1) as usize];
            let size = [0x1000, size % 0x10_0000][(size & 1) as usize];
            requests.push((size, alignment, minimum % (1 << 34), limit % (1 << 34)));
        }
        let view = memory_view(&new, &spans, &requests);
        assert_eq!(view, memory_view_before(&old, &spans, &requests));
        compared += spans.len() + requests.len();
    }
    assert_eq!(compared, 6144);
}

/// The trees that the firmware ships, outside this repository, from the
/// directory that the firmware tests read them from.
#[test]
#[ignore = "reads the device-tree files of the firmware from KREPI_PI5_SOURCE_DTB_DIR"]
fn the_shipped_trees_agree_with_the_code_before_the_profiles() {
    let directory = std::env::var_os("KREPI_PI5_SOURCE_DTB_DIR").expect("the directory");
    for name in ["bcm2712-rpi-5-b.dtb", "bcm2712d0-rpi-5-b.dtb"] {
        let bytes = std::fs::read(std::path::Path::new(&directory).join(name)).expect(name);
        check_boot(&bytes, DTB, at(0x8_0000, 0x8_0000), &[]);
        check_cpus(&bytes, &[]);
    }
}
