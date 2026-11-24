//! The device-tree files of the Raspberry Pi firmware, outside this
//! repository: the two trees that the firmware ships and three trees merged
//! from them with the overlays of a boot configuration. The tests are
//! ignored; each reads its files from the directory that an environment
//! variable names.
//!
//! Feature: krepi.platform.device-tree

use super::*;
use crate::fdt::{MemoryPlan, ReservedRegion};
use std::{env, fs::File, io::Read, path::PathBuf};

const FIXTURE_IMAGE: Span = Span {
    start: 0x80000,
    size: 0x80000,
};

/// The bytes of the file `name` of the directory that `variable` names, of
/// 40 bytes to `PI5_HAND_OVER.max_blob_size`.
fn fixture(variable: &str, name: &str) -> Vec<u8> {
    let directory = env::var_os(variable)
        .unwrap_or_else(|| panic!("{variable} must name the directory of the device-tree files"));
    let path = PathBuf::from(directory).join(name);
    let file = File::open(&path)
        .unwrap_or_else(|error| panic!("cannot open fixture {}: {error}", path.display()));
    let mut bytes = Vec::new();
    file.take(PI5_HAND_OVER.max_blob_size + 1)
        .read_to_end(&mut bytes)
        .unwrap_or_else(|error| panic!("cannot read fixture {}: {error}", path.display()));
    assert!(
        (40..=PI5_HAND_OVER.max_blob_size as usize).contains(&bytes.len()),
        "invalid fixture size for {}",
        path.display(),
    );
    bytes
}

/// The `atf@0` region of the trees that the firmware ships.
const ATF: ReservedRegion = ReservedRegion {
    span: Span {
        start: 0,
        size: 0x80000,
    },
    no_map: true,
    reusable: false,
};

/// The prototype rejected the shipped trees for their dynamic `linux,cma`;
/// the contract accepts each with one dynamic reservation. The RAM of a
/// shipped tree is the placeholder that the bootloader replaces, 640 MiB.
#[test]
#[ignore = "reads the device-tree files of the firmware from KREPI_PI5_SOURCE_DTB_DIR"]
fn source_firmware_rejects_dynamic_reservations() {
    for name in ["bcm2712-rpi-5-b.dtb", "bcm2712d0-rpi-5-b.dtb"] {
        let bytes = fixture("KREPI_PI5_SOURCE_DTB_DIR", name);
        let tree = Fdt::parse(&bytes).unwrap_or_else(|error| panic!("{name}: {error:?}"));
        let map = tree
            .discover_boot_memory(PI5_HAND_OVER, DTB, FIXTURE_IMAGE)
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        assert_eq!(map.dynamic(), 1, "{name}");
        assert_eq!(
            map.dtb(),
            Span::new(DTB, bytes.len() as u64).unwrap(),
            "{name}"
        );
        if name == "bcm2712-rpi-5-b.dtb" {
            assert_eq!(bytes.len(), 0x133b2, "{name}");
            assert_eq!(map.ram(), &[Span::new(0, 0x28000000).unwrap()], "{name}");
            assert_eq!(map.reserved(), &[ATF], "{name}");
            assert_eq!(map.ram_bytes(), 640 * 1024 * 1024, "{name}");
        }
    }
}

/// A merged tree keeps the placeholder RAM until the firmware updates it,
/// so these files establish nothing about the RAM installed on a board.
#[test]
#[ignore = "reads merged device-tree files from KREPI_PI5_VALIDATED_DTB_DIR"]
fn merged_firmware_preserves_placeholder_ram_and_boot_exclusions() {
    for name in ["c1.dtb", "d0.dtb", "d0-auto.dtb"] {
        let bytes = fixture("KREPI_PI5_VALIDATED_DTB_DIR", name);
        let tree = Fdt::parse(&bytes).unwrap_or_else(|error| panic!("{name}: {error:?}"));
        let map = tree
            .discover_boot_memory(PI5_HAND_OVER, DTB, FIXTURE_IMAGE)
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        assert_eq!(map.ram(), &[Span::new(0, 0x28000000).unwrap()], "{name}");
        assert_eq!(map.ram_bytes(), 640 * 1024 * 1024, "{name}");
        assert_eq!(map.reserved(), &[ATF], "{name}");
        assert_eq!(map.image(), FIXTURE_IMAGE, "{name}");
        let window = Span::new(0, 128 * 1024 * 1024).unwrap();
        let plan = MemoryPlan::from_boot_memory(&map, window, &[])
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        assert_eq!(plan.ram()[0].size, 640 * 1024 * 1024, "{name}");
        for excluded in [map.reserved()[0].span, map.image(), map.dtb()] {
            assert!(!plan.permits_backing(excluded), "{name}: {excluded:?}");
        }
        assert!(
            plan.permits_backing(Span::new(0x100000, 0x1000).unwrap()),
            "{name}"
        );
        assert_eq!(
            map.dtb(),
            Span::new(DTB, bytes.len() as u64).unwrap(),
            "{name}"
        );
        for excluded in [map.reserved()[0].span, map.image(), map.dtb()] {
            assert!(!map.is_available(excluded).unwrap(), "{name}: {excluded:?}");
        }
        assert!(
            map.is_available(Span::new(0x100000, 0x1000).unwrap())
                .unwrap(),
            "{name}"
        );
        assert!(
            !map.is_available(Span::new(0x28000000, 0x1000).unwrap())
                .unwrap(),
            "{name}"
        );
        assert!(tree.reservations().next().is_none(), "{name}");
        assert!(
            !tree
                .find_node("/reserved-memory/linux,cma")
                .unwrap()
                .unwrap()
                .enabled()
                .unwrap(),
            "{name}"
        );
    }
}
