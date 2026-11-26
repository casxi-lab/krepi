//! The error orders: for each step of the order of the parse and the
//! entries on a tree, 1 to 8, and of the order of the boot memory map, 1 to
//! 7, an input that breaks a rule of that step and a later rule gives the
//! error of the step. Step 8 of the boot memory map, the last check of
//! `MemoryPlan::new`, has no later rule.
//!
//! Feature: krepi.platform.device-tree

use super::*;

/// The boot storage and the firmware reservation of the boot memory map
/// tests.
const BOOT: [Span; 1] = [Span {
    start: 0x1000,
    size: 0x10,
}];
const FIRMWARE: [ReservedRegion; 1] = [ReservedRegion {
    span: Span {
        start: 0x8000,
        size: 0x10,
    },
    no_map: true,
    reusable: false,
}];

/// A version of 16, `UnsupportedVersion`, before the reservation entry of
/// size 0 of step 2, `EmptyRegion`.
#[test]
fn error_order_parse_step_1() {
    let mut b = Builder::default();
    b.reservations.push(Span {
        start: 0x1000,
        size: 0,
    });
    b.begin("");
    b.end();
    let mut bytes = b.finish();
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::EmptyRegion);
    set_word(&mut bytes, 20, 16);
    assert_eq!(Fdt::parse(&bytes).unwrap_err(), Error::UnsupportedVersion);
}

/// Two reservation entries that share `[0x1800, 0x2000)`, `Overlap`, before
/// the token 5 of step 3, `BadToken`.
#[test]
fn error_order_parse_step_2() {
    let mut b = Builder::default();
    b.reservations.push(Span::new(0x1000, 0x1000).unwrap());
    b.reservations.push(Span::new(0x1800, 0x1000).unwrap());
    b.begin("");
    b.word(5);
    b.end();
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::Overlap);
}

/// The encoding of a token before its place in the tree: a property named
/// `a b` after the child `a` of the root fails on its name, `BadString`,
/// before its place after a child, `BadTree`.
#[test]
fn error_order_parse_step_3() {
    let mut b = Builder::default();
    b.begin("");
    b.begin("a");
    b.end();
    b.property("a b", &[]);
    b.end();
    assert_eq!(Fdt::parse(&b.finish()).unwrap_err(), Error::BadString);
}

/// The whole `reg` of a memory node before its ranges: the second range of
/// `memory@1` leaves 64 bits, `Overflow`, before its first range, which
/// shares an address with that of `memory@0`, `Overlap`.
#[test]
fn error_order_parse_step_4() {
    let mut b = Builder::default();
    b.root();
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0, 0, 0x1000]);
    b.end();
    b.begin("memory@1");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0, 0, 0x1000, u32::MAX, u32::MAX, 0, 0x10]);
    b.end();
    b.end();
    let bytes = b.finish();
    assert_eq!(
        Fdt::parse(&bytes).unwrap().discover_memory().unwrap_err(),
        Error::Overflow
    );
}

/// An empty image, `EmptyRegion`, before the memory discovery of a tree
/// without RAM, `NoMemory`.
#[test]
fn error_order_parse_step_5() {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    b.end();
    let bytes = b.finish();
    let tree = Fdt::parse(&bytes).unwrap();
    assert_eq!(
        tree.discover_boot_memory(
            PI5_HAND_OVER,
            0x10_0000,
            Span::new(0x20_0000, 0x1000).unwrap()
        )
        .unwrap_err(),
        Error::NoMemory
    );
    assert_eq!(
        tree.discover_boot_memory(PI5_HAND_OVER, 0x10_0000, Span::new(0x20_0000, 0).unwrap())
            .unwrap_err(),
        Error::EmptyRegion
    );
}

/// The size cells of `/cpus`, 1, `BadProperty`, before its 3 address
/// cells, `UnsupportedCells`.
#[test]
fn error_order_parse_step_6() {
    let mut b = Builder::default();
    b.root();
    b.begin("cpus");
    b.cells("#address-cells", &[3]);
    b.cells("#size-cells", &[1]);
    b.end();
    b.end();
    let bytes = b.finish();
    assert_eq!(
        Fdt::parse(&bytes)
            .unwrap()
            .discover_cpus(QEMU_HVC_CPUS)
            .unwrap_err(),
        Error::BadProperty
    );
}

/// The windows of a translation in order: the first two hold the request,
/// `AmbiguousMapping` at the second, before the third, which holds part of
/// it, `Unmapped`.
#[test]
fn error_order_parse_step_7() {
    let bytes = cells(&[0, 0x2000, 0x100, 0, 0x3000, 0x100, 0x10, 0x1000, 0x10]);
    let map = AddressMap::new(Some(&bytes), 1, 1, 1).unwrap();
    assert_eq!(
        map.to_parent(Span::new(0x18, 0x10).unwrap()),
        Err(Error::AmbiguousMapping)
    );
}

/// A selection of size 0, `EmptyRegion`, before its alignment of 3,
/// `BadAlignment`.
#[test]
fn error_order_parse_step_8() {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0, 0, 0x4000_0000]);
    b.end();
    b.end();
    let bytes = b.finish();
    let memory = Fdt::parse(&bytes)
        .unwrap()
        .discover_boot_memory(
            PI5_HAND_OVER,
            0x10_0000,
            Span::new(0x20_0000, 0x1000).unwrap(),
        )
        .unwrap();
    assert_eq!(
        memory.find_available(0, 3, 0, 0x1000),
        Err(Error::EmptyRegion)
    );
    assert_eq!(
        memory.find_available(1, 3, 0, 0x1000),
        Err(Error::BadAlignment)
    );
}

/// A managed window of size 0, `InvalidRange`, before the missing RAM bank
/// of step 2, `Capacity`.
#[test]
fn error_order_plan_step_1() {
    assert_eq!(
        MemoryPlan::new(Span { start: 0, size: 0 }, &[], &BOOT, &FIRMWARE).unwrap_err(),
        PlanError::InvalidRange
    );
}

/// 33 RAM banks, `Capacity`, before the first of them, of size 0, in step
/// 3, `InvalidRange`.
#[test]
fn error_order_plan_step_2() {
    let mut banks = vec![Span { start: 0, size: 0 }];
    for index in 1..=32 {
        banks.push(Span::new(index * 0x10000, 0x1000).unwrap());
    }
    assert_eq!(
        MemoryPlan::all_ram(&banks, &BOOT, &FIRMWARE).unwrap_err(),
        PlanError::Capacity
    );
}

/// `MemoryPlan::from_boot_memory` with three further spans, 5 spans of boot
/// storage: after a managed window of size 0, `InvalidRange`; otherwise
/// `Capacity` of step 2, before the first further span, of size 0, in step
/// 6, `InvalidRange`, and before the managed window outside every bank of
/// step 8, `OutsideRam`.
#[test]
fn error_order_plan_step_2_further_spans() {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", b"raspberrypi,5-model-b\0brcm,bcm2712\0");
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0, 0, 0x4000_0000]);
    b.end();
    b.end();
    let bytes = b.finish();
    let memory = Fdt::parse(&bytes)
        .unwrap()
        .discover_boot_memory(
            PI5_HAND_OVER,
            0x20_0000,
            Span::new(0x10_0000, 0x1000).unwrap(),
        )
        .unwrap();
    let more = [
        Span::new(0x30_0000, 0).unwrap(),
        Span::new(0x40_0000, 0x1000).unwrap(),
        Span::new(0x50_0000, 0x1000).unwrap(),
    ];
    let empty = Span::new(0x60_0000, 0).unwrap();
    assert_eq!(
        MemoryPlan::from_boot_memory(&memory, empty, &more).unwrap_err(),
        PlanError::InvalidRange
    );
    for window in [0x60_0000, 0x8000_0000] {
        let window = Span::new(window, 0x1000).unwrap();
        assert_eq!(
            MemoryPlan::from_boot_memory(&memory, window, &more).unwrap_err(),
            PlanError::Capacity
        );
    }
}

/// A bank that shares `[0x1000, 0x2000)` with an earlier one, `Overlap`,
/// before the 16 GiB and 4 KiB of the banks in step 4, `ArenaTooLarge`.
#[test]
fn error_order_plan_step_3() {
    let banks = [
        Span::new(0, 0x4_0000_0000).unwrap(),
        Span::new(0x1000, 0x1000).unwrap(),
    ];
    assert_eq!(
        MemoryPlan::all_ram(&banks, &BOOT, &FIRMWARE).unwrap_err(),
        PlanError::Overlap
    );
}

/// A bank of 16 GiB and 4 KiB, `ArenaTooLarge`, before the boot storage
/// outside every bank of step 6, `OutsideRam`.
#[test]
fn error_order_plan_step_4() {
    assert_eq!(
        MemoryPlan::all_ram(
            &[Span::new(0, 0x4_0000_1000).unwrap()],
            &[Span::new(0x8_0000_0000, 0x10).unwrap()],
            &[]
        )
        .unwrap_err(),
        PlanError::ArenaTooLarge
    );
}

/// A bank without a complete page, `Alignment`, before the boot storage
/// outside every bank of step 6, `OutsideRam`.
#[test]
fn error_order_plan_step_5() {
    assert_eq!(
        MemoryPlan::all_ram(
            &[Span::new(1, 0x800).unwrap()],
            &[Span::new(0x10_0000, 0x10).unwrap()],
            &[]
        )
        .unwrap_err(),
        PlanError::Alignment
    );
}

/// Boot storage outside every bank, `OutsideRam`, before the firmware
/// reservation on its page in step 7, `Overlap`.
#[test]
fn error_order_plan_step_6() {
    let firmware = [ReservedRegion {
        span: Span::new(0x1000_0000, 1).unwrap(),
        no_map: true,
        reusable: false,
    }];
    assert_eq!(
        MemoryPlan::all_ram(
            &[Span::new(0, 0x800_0000).unwrap()],
            &[Span::new(0x1000_0000, 0x10).unwrap()],
            &firmware
        )
        .unwrap_err(),
        PlanError::OutsideRam
    );
}

/// A firmware reservation on a page of the boot storage, `Overlap`, before
/// the managed window outside every bank of step 8, `OutsideRam`.
#[test]
fn error_order_plan_step_7() {
    let firmware = [ReservedRegion {
        span: Span::new(0x8_0000, 1).unwrap(),
        no_map: true,
        reusable: false,
    }];
    assert_eq!(
        MemoryPlan::new(
            Span::new(0x1000_0000, 0x1000).unwrap(),
            &[Span::new(0, 0x800_0000).unwrap()],
            &[Span::new(0x8_0000, 0x3_8000).unwrap()],
            &firmware
        )
        .unwrap_err(),
        PlanError::Overlap
    );
}
