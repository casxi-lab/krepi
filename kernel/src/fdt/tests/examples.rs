//! The examples of the device-tree feature document,
//! `docs/features/platform/device-tree.md`: one test for each, named after
//! the example, on trees that the tests build.
//!
//! Feature: krepi.platform.device-tree
//!
//! The expected values are those that the examples write, worked out from
//! the contract, never taken from a run of the code.

use super::*;

/// A tree of the shape that QEMU virt hands over: a root of 2 and 2 cells,
/// one memory node of 128 MiB at `0x4000_0000`, and `/chosen` with the
/// seeds `rng` and `kaslr`.
fn qemu_virt(rng: &[u8; 32], kaslr: &[u8; 8]) -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", b"linux,dummy-virt\0");
    b.begin("chosen");
    b.property("rng-seed", rng);
    b.property("kaslr-seed", kaslr);
    b.end();
    b.begin("memory@40000000");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0x4000_0000, 0, 0x800_0000]);
    b.end();
    b.end();
    b.finish()
}

/// The usable ranges of a boot memory map, in order.
fn usable(plan: &MemoryPlan) -> Vec<Span> {
    let mut ranges = plan.available_ranges();
    let mut spans = Vec::new();
    while let Some(span) = ranges.next() {
        spans.push(span);
    }
    spans
}

fn span(start: u64, size: u64) -> Span {
    Span { start, size }
}

#[test]
fn ex1_a_qemu_virt_tree_gives_its_ram() {
    let bytes = qemu_virt(&[0x5a; 32], &[0xa5; 8]);
    let tree = Fdt::parse(&bytes).unwrap();
    assert_eq!(tree.total_size(), bytes.len() as u64);
    let memory = tree.discover_memory().unwrap();
    assert_eq!(memory.ram(), &[span(0x4000_0000, 0x800_0000)]);
    assert!(memory.reserved().is_empty());
    assert_eq!(memory.dynamic(), 0);
}

#[test]
fn ex2_a_truncated_tree_is_rejected() {
    let bytes = minimal();
    let short = &bytes[..bytes.len() - 1];
    assert_eq!(Fdt::parse(short).unwrap_err(), Error::Truncated);
    assert_eq!(Fdt::parse(&bytes[..39]).unwrap_err(), Error::Truncated);
}

#[test]
fn ex3_a_dynamic_reservation_is_counted_and_not_reserved() {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.begin("reserved-memory");
    b.cells("#address-cells", &[2]);
    b.cells("#size-cells", &[2]);
    b.property("ranges", &[]);
    b.begin("linux,cma");
    b.property("compatible", b"shared-dma-pool\0");
    b.cells("size", &[0x400_0000]);
    b.property("reusable", &[]);
    b.property("linux,cma-default", &[]);
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    let memory = Fdt::parse(&bytes).unwrap().discover_memory().unwrap();
    assert_eq!(memory.ram(), &[span(0x1_0000_0000, 0x20_0000)]);
    assert!(memory.reserved().is_empty());
    assert_eq!(memory.dynamic(), 1);
}

#[test]
fn ex4_the_boot_memory_map_of_the_pi5_8gb_model() {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    // The three RAM ranges of the 8 GB model, each in 2 and 2 cells.
    let ranges = [
        [0, 0, 0, 0x3fc0_0000],
        [0, 0x4000_0000, 0, 0xc000_0000],
        [1, 0, 1, 0],
    ];
    b.cells("reg", &ranges.concat());
    b.end();
    b.begin("reserved-memory");
    b.cells("#address-cells", &[2]);
    b.cells("#size-cells", &[2]);
    b.property("ranges", &[]);
    b.begin("atf@0");
    b.cells("reg", &[0, 0, 0, 0x8_0000]);
    b.property("no-map", &[]);
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    // The tree fits one page, so its pages end at `0x20_1000`.
    assert!(bytes.len() < 0x1000);
    let image = span(0x8_0000, 0x2_0000);
    let tree = Fdt::parse(&bytes).unwrap();
    let memory = tree
        .discover_boot_memory(PI5_HAND_OVER, 0x20_0000, image)
        .unwrap();
    assert_eq!(memory.ram_bytes(), 0x1_ffc0_0000);
    assert_eq!(memory.dtb(), span(0x20_0000, bytes.len() as u64));
    let boot = [memory.image(), memory.dtb()];
    let plan = MemoryPlan::all_ram(memory.ram(), &boot, memory.reserved()).unwrap();
    assert_eq!(plan.managed_bytes(), 0x1_ffc0_0000);
    assert_eq!(
        usable(&plan),
        [
            span(0xa_0000, 0x16_0000),
            span(0x20_1000, 0x3f9f_f000),
            span(0x4000_0000, 0xc000_0000),
            span(0x1_0000_0000, 0x1_0000_0000),
        ]
    );
    let hole = span(0x3fc0_0000, 0x1000);
    assert!(!plan.contains_ram(hole));
    assert!(!plan.is_available(hole));
    assert!(!plan.is_available(image));
    assert!(!plan.is_available(span(0x20_0000, 0x1000)));
    assert!(!plan.is_available(span(0, 0x1000)));
    assert!(plan.is_available(span(0x1_0000_0000, 0x1000)));
}

#[test]
fn ex5_a_device_address_is_translated_through_a_bus() {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.begin("soc@107c000000");
    b.cells("#address-cells", &[1]);
    b.cells("#size-cells", &[1]);
    b.cells("ranges", &[0, 0x10, 0x7c00_0000, 0x400_0000]);
    b.begin("serial@1001000");
    b.cells("reg", &[0x100_1000, 0x200]);
    b.end();
    b.end();
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    let serial = tree
        .find_node("/soc@107c000000/serial@1001000")
        .unwrap()
        .unwrap();
    let local = serial.reg().unwrap().next().unwrap();
    assert_eq!(local, span(0x100_1000, 0x200));
    assert_eq!(serial.translate_reg(local), Ok(span(0x10_7d00_1000, 0x200)));
    // A request that the window holds only in part is not translated.
    assert_eq!(
        serial.translate_reg(span(0x3ff_ff00, 0x200)),
        Err(Error::Unmapped)
    );
}

#[test]
fn ex6_the_cpu_topology_of_the_pi5() {
    let mut b = Builder::default();
    b.root();
    b.begin("cpus");
    b.cells("#address-cells", &[1]);
    b.cells("#size-cells", &[0]);
    for (name, id) in [
        ("cpu@0", 0),
        ("cpu@100", 0x100),
        ("cpu@200", 0x200),
        ("cpu@300", 0x300),
    ] {
        b.begin(name);
        b.property("device_type", b"cpu\0");
        b.property("compatible", b"arm,cortex-a76\0");
        b.property("enable-method", b"psci\0");
        b.cells("reg", &[id]);
        b.end();
    }
    b.end();
    b.begin("psci");
    b.property("compatible", b"arm,psci-1.0\0arm,psci-0.2\0arm,psci\0");
    b.property("method", b"smc\0");
    b.end();
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    let cpus = tree.discover_cpus(PI5_CPUS).unwrap();
    assert_eq!(cpus.count(), 4);
    assert_eq!(cpus.profile(), PI5_CPUS);
    assert_eq!(cpus.affinity(2), Some(0x200));
    assert_eq!(cpus.affinity(4), None);
    assert_eq!(PI5_CPUS.affinity_shift(), 8);
    assert_eq!(PI5_CPUS.conduit(), PsciConduit::Smc);
    // The flag bits of `MPIDR_EL1`, bits 31 and 24, change no logical ID.
    assert_eq!(PI5_CPUS.logical_id(0x8100_0200), Some(2));
    // The IDs of level 1 are no IDs of the QEMU virt profile.
    assert_eq!(tree.discover_cpus(QEMU_HVC_CPUS), Err(Error::BadProperty));
}

#[test]
fn ex7_seeds_in_the_chosen_node_change_no_result() {
    let first = qemu_virt(&[0x11; 32], &[0x22; 8]);
    let second = qemu_virt(&[0xee; 32], &[0xdd; 8]);
    assert_ne!(first, second);
    assert_eq!(first.len(), second.len());
    // The tree fits one page at the start of RAM, and the image follows.
    assert!(first.len() < 0x1000);
    let image = span(0x4020_0000, 0x10_0000);
    let mut results = Vec::new();
    for bytes in [&first, &second] {
        let tree = Fdt::parse(bytes).unwrap();
        let memory = tree.discover_memory().unwrap();
        let boot = [span(0x4000_0000, tree.total_size()), image];
        let plan = MemoryPlan::all_ram(memory.ram(), &boot, memory.reserved()).unwrap();
        results.push((
            memory.ram().to_vec(),
            memory.reserved().to_vec(),
            memory.dynamic(),
            usable(&plan),
        ));
    }
    assert_eq!(results[0], results[1]);
    assert_eq!(
        results[0].3,
        [span(0x4000_1000, 0x1f_f000), span(0x4030_0000, 0x7d0_0000)]
    );
}
