//! The differential tests of the two entries whose code no longer adds a
//! constant to the length of an argument: `MemoryPlan::from_boot_memory`,
//! which checks the number of further spans right after the window, and
//! `Fdt::find_node`, which returns at the last component of a path. Each
//! input goes through the entry and through the verbatim copy of its code
//! before, and the two must give the same error, or the same boot memory map
//! in every field, or the same node. The inputs are the boot memories and
//! the trees of the vector file, with the windows and further spans of
//! `from_boot_memory` and the paths of every node of each tree with their
//! variants; boot memories and trees built for the branches of the two
//! codes, with each loop run 0 times, once and up to its bound and beyond
//! it; and paths from a fixed seed.
//!
//! Feature: krepi.platform.device-tree
//!
//! The comparison shows that the two codes agree on these inputs, not that
//! either is right: the expected values are those of the vectors and of the
//! other host tests, among them the tests of the limits and of the error
//! orders.

use super::*;
use std::string::String;

/// Every field of a boot memory map.
type PlanFields = (
    [Span; BANKS],
    usize,
    [Span; BANKS],
    usize,
    [Span; BOOT_SPANS + FIRMWARE],
    usize,
    usize,
);

fn plan_fields(plan: MemoryPlan) -> PlanFields {
    (
        plan.ram,
        plan.ram_count,
        plan.managed,
        plan.managed_count,
        plan.reserved,
        plan.boot_count,
        plan.reserved_count,
    )
}

/// The further spans of `from_boot_memory`: those of the other differential
/// tests, none to three; one of size 0, one whose end leaves 64 bits and one
/// on the page of `atf@0`; three whose first has size 0; and four, five and
/// 33 spans.
fn further() -> Vec<Vec<Span>> {
    let mut further: Vec<Vec<Span>> = MORE.iter().map(|more| more.to_vec()).collect();
    further.extend([
        vec![at(0x40_0000, 0)],
        vec![at(u64::MAX, 1)],
        vec![at(0x1000, 0x1000)],
        vec![
            at(0x40_0000, 0),
            at(0x30_0000, 0x1000),
            at(0x50_0000, 0x1000),
        ],
    ]);
    for count in [4, 5, 33] {
        let spans = (0..count).map(|k| at(0x30_0000 + k * 0x2000, 0x1000));
        further.push(spans.collect());
    }
    further
}

/// Checks `from_boot_memory` on `memory` against the copy, on each window of
/// [`windows`] and the further windows `extra`, with each of the further
/// spans of [`further`] and `more`; gives the number of inputs.
fn check_plans(memory: &BootMemory, extra: &[Span], more: &[Vec<Span>]) -> usize {
    let mut compared = 0;
    let mut spans = further();
    spans.extend(more.iter().cloned());
    for window in windows(memory.ram())
        .into_iter()
        .chain(extra.iter().copied())
    {
        for more in &spans {
            let plan = MemoryPlan::from_boot_memory(memory, window, more).map(plan_fields);
            let old = MemoryPlan::from_boot_memory_old(memory, window, more).map(plan_fields);
            assert_eq!(plan, old, "{window:?} {more:?}");
            compared += 1;
        }
    }
    compared
}

/// The boot memory of the hand-over tree `bytes` with the tree at `DTB` and
/// the image `IMAGE`.
fn boot_memory(bytes: &[u8]) -> BootMemory {
    let tree = Fdt::parse(bytes).unwrap();
    tree.discover_boot_memory(PI5_HAND_OVER, DTB, IMAGE)
        .unwrap()
}

#[test]
fn the_vector_boot_memories_agree_with_the_code_before_the_further_spans_check() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let text = std::fs::read_to_string(root.join(VECTORS)).expect("the vector file");
    let (mut memories, mut compared) = (0, 0);
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let fields = fields(line.split('\t').nth(1).expect("an input"));
        let value = |key: &str| field(&fields, key).expect(key);
        let entry = value("entry");
        if !["discover_pi5_boot_memory", "find_available", "from_pi5"].contains(&entry) {
            continue;
        }
        let bytes = hex_bytes(value("dtb")).unwrap();
        let address = number64(value("dtb_address")).unwrap();
        let image = span(value("image")).unwrap();
        let Ok(tree) = Fdt::parse(&bytes) else {
            continue;
        };
        let Ok(memory) = tree.discover_boot_memory(PI5_HAND_OVER, address, image) else {
            continue;
        };
        let (mut window, mut more) = (Vec::new(), Vec::new());
        if entry == "from_pi5" {
            window.push(span(value("window")).unwrap());
            more.push(spans(value("more")).unwrap());
        }
        compared += check_plans(&memory, &window, &more);
        memories += 1;
    }
    assert_eq!((memories, compared), (20, 1719));
}

#[test]
fn built_boot_memories_agree_with_the_code_before_the_further_spans_check() {
    let atf = [("atf@0", ATF)];
    let tree =
        |ram: &[Span], map: &[Span], total| hand_over_tree(Some(PI5), ram, map, &atf, false, total);
    let mut trees = Vec::new();
    // The RAM models, also padded; the 8 GB model with the region of the
    // hole in the reservation map and below `/reserved-memory`; the shipped
    // shape with its dynamic `linux,cma`.
    for ram in models() {
        trees.push(tree(&ram, &[], 0));
        trees.push(tree(&ram, &[], 0x1_3ad4));
    }
    let eight = &models()[3];
    trees.push(tree(eight, &[HOLE_REGION], 0));
    let hole = [atf[0], ("nvram@3fd231e0", HOLE_REGION)];
    trees.push(hand_over_tree(Some(PI5), eight, &[], &hole, false, 0));
    trees.push(hand_over_tree(
        Some(PI5),
        &[at(0, 0x2800_0000)],
        &[],
        &atf,
        true,
        0,
    ));
    // 32 RAM ranges; one range with 127 reservations of one page beside
    // `atf@0`, so 128 reserved regions.
    let ranges: Vec<Span> = (0..32).map(|k| at(k << 28, 0x800_0000)).collect();
    trees.push(hand_over_tree(Some(PI5), &ranges, &[], &[], false, 0));
    let pages: Vec<Span> = (0..127)
        .map(|k| at(0x80_0000 + k * 0x2000, 0x1000))
        .collect();
    trees.push(tree(&[at(0, 0x4000_0000)], &pages, 0));
    // Windows beside the image, on the tree and at the end of a bank.
    let extra = [
        at(0x10_0000, 0x1000),
        at(DTB, 0x1000),
        at(0x3fbf_f000, 0x1000),
    ];
    let mut compared = 0;
    for bytes in &trees {
        compared += check_plans(&boot_memory(bytes), &extra, &[]);
    }
    assert_eq!((trees.len(), compared), (15, 2366));
}

/// What a lookup gives: its error, or where the node lies, none when no
/// node has the path.
type Found = Result<Option<(usize, usize, Option<usize>, usize, usize)>, Error>;

fn found(lookup: Result<Option<Node<'_>>, Error>) -> Found {
    lookup.map(|node| {
        node.map(|node| {
            let at = node.at;
            (
                at.offset,
                at.properties,
                at.parent,
                at.name_start,
                at.name_end,
            )
        })
    })
}

/// Checks `find_node` on `tree` against the copy on `path`.
fn check_path(tree: Fdt<'_>, path: &str) {
    let node = found(tree.find_node(path));
    assert_eq!(node, found(tree.find_node_old(path)), "{path:?}");
}

/// The absolute path of `node`, `/` for the root, with each name as UTF-8
/// where it is and replaced where it is not.
fn path_of(node: Node<'_>) -> String {
    let mut names = Vec::new();
    let mut node = node;
    while let Some(parent) = node.parent() {
        names.push(String::from_utf8_lossy(node.name()).into_owned());
        node = parent;
    }
    names.reverse();
    format!("/{}", names.join("/"))
}

/// The paths of the lookups on `tree`: the fixed ones, which `path_valid`
/// refuses or which match nothing, and for the path of each node, the path,
/// a missing child below it, a missing node above it, the path without its
/// last byte, with a `/` after it and with its last component twice.
fn tree_paths(tree: Fdt<'_>) -> Vec<String> {
    let fixed = ["", "x", "/", "//", "/x", "/x/y", "x/", "/x/"];
    let mut paths: Vec<String> = fixed.iter().map(|path| path.to_string()).collect();
    let mut nodes = tree.nodes();
    while let Some(node) = nodes.next() {
        let path = path_of(node);
        let last = path.rsplit('/').next().unwrap_or_default().to_string();
        paths.push(format!("{path}/x"));
        paths.push(format!("/x{path}"));
        paths.push(path[..path.len() - 1].to_string());
        paths.push(format!("{path}/"));
        paths.push(format!("{path}/{last}"));
        paths.push(path);
    }
    paths
}

#[test]
fn the_vector_trees_agree_with_the_code_before_the_last_component_return() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let text = std::fs::read_to_string(root.join(VECTORS)).expect("the vector file");
    let (mut trees, mut compared) = (0, 0);
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let fields = fields(line.split('\t').nth(1).expect("an input"));
        let Some(bytes) = field(&fields, "dtb").and_then(hex_bytes) else {
            continue;
        };
        let Ok(tree) = Fdt::parse(&bytes) else {
            continue;
        };
        let mut paths = tree_paths(tree);
        paths.extend(field(&fields, "node").map(str::to_string));
        for path in &paths {
            check_path(tree, path);
        }
        compared += paths.len();
        trees += 1;
    }
    assert_eq!((trees, compared), (263, 9777));
}

/// A tree for the branches of the lookup: below the root, `a` with `b` with
/// `c`; two siblings `d`, the first with `e`; `ab`, `a@1` and `x@0`; and a
/// chain of `child` nodes 31 deep, the deepest that a tree holds.
fn lookup_tree() -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    for name in ["a", "b", "c"] {
        b.begin(name);
    }
    for _ in 0..3 {
        b.end();
    }
    b.begin("d");
    b.begin("e");
    b.end();
    b.end();
    for name in ["d", "ab", "a@1", "x@0"] {
        b.begin(name);
        b.end();
    }
    for _ in 1..MAX_DEPTH {
        b.begin("child");
    }
    for _ in 1..MAX_DEPTH {
        b.end();
    }
    b.end();
    b.finish()
}

#[test]
fn built_paths_agree_with_the_code_before_the_last_component_return() {
    let bytes = lookup_tree();
    let tree = Fdt::parse(&bytes).unwrap();
    // The root; one component that matches, matches nothing, is a prefix or
    // an extension of a name, or matches two siblings; two and three
    // components, which end or fail at the last one or fail at an earlier
    // one; and the chain of 0 to 33 components, 31 being the deepest node.
    let mut paths: Vec<String> = [
        "/", "/a", "/x", "/a@1", "/a@", "/x@0", "/x@00", "/ab", "/abc", "/d", "/a/b", "/a/x",
        "/x/b", "/d/e", "/d/x", "/a/b/c", "/a/b/x", "/a/x/c", "/a/b/c/x", "/a//b", "/a/b/",
    ]
    .iter()
    .map(|path| path.to_string())
    .collect();
    for count in 0..=MAX_DEPTH as usize + 1 {
        paths.push("/child".repeat(count));
        paths.push(format!("{}/x", "/child".repeat(count)));
    }
    paths.extend(tree_paths(tree));
    for path in &paths {
        check_path(tree, path);
    }
    assert_eq!(paths.len(), 343);
}

#[test]
fn seeded_paths_agree_with_the_code_before_the_last_component_return() {
    let bytes = lookup_tree();
    let tree = Fdt::parse(&bytes).unwrap();
    // 4096 strings of up to 24 bytes over the bytes of the names of the
    // tree and `/`, most of them starting with `/`.
    let alphabet = b"/abcdex@01";
    let mut state = 0x2545_f491_4f6c_dd1d;
    for _ in 0..4096 {
        let length = (next(&mut state) % 25) as usize;
        let mut path: Vec<u8> = (0..length)
            .map(|_| alphabet[(next(&mut state) % alphabet.len() as u64) as usize])
            .collect();
        if next(&mut state) % 8 != 0 {
            path.insert(0, b'/');
        }
        check_path(tree, std::str::from_utf8(&path).unwrap());
    }
}
