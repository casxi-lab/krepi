//! Profiles that no board gives: the alignment exponents from 64 up, empty
//! and non-UTF-8 pieces among the required entries of a hand-over profile,
//! a set of CPU counts with 3 CPUs, the affinity levels 2 and 3, and the
//! timer counts 0 and above 5. The rules of the contract hold for every
//! profile; each expected value follows from them.
//!
//! Feature: krepi.platform.device-tree

use super::*;

/// The span of the image with its BSS and stacks.
const IMAGE: Span = Span {
    start: 0x8_0000,
    size: 0x2_0000,
};

/// A hand-over profile of a tree of at most 128 KiB at a multiple of
/// `2 ^ alignment_log2`, whose root `compatible` holds what `compatible`
/// requires.
fn hand_over(alignment_log2: u8, compatible: &[u8]) -> HandOverProfile<'_> {
    HandOverProfile {
        max_blob_size: 0x2_0000,
        alignment_log2,
        compatible,
    }
}

/// A hand-over tree: a root of 2 and 2 cells with the `compatible` value
/// `compatible` and one RAM range `[0, 4 MiB)`, which holds the image.
fn hand_over_tree(compatible: &[u8]) -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    b.property("compatible", compatible);
    b.begin("memory@0");
    b.property("device_type", b"memory\0");
    b.cells("reg", &[0, 0, 0, 0x40_0000]);
    b.end();
    b.end();
    b.finish()
}

fn boot_memory(bytes: &[u8], profile: HandOverProfile<'_>, dtb: u64) -> Result<BootMemory, Error> {
    Fdt::parse(bytes)?.discover_boot_memory(profile, dtb, IMAGE)
}

/// A tree of CPU nodes of the affinities `ids` in `cells` address cells,
/// each with the `enable-method` `psci`, and `/psci` with the method `hvc`.
fn cpu_tree(ids: &[u64], cells: u32) -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    b.begin("cpus");
    b.cells("#address-cells", &[cells]);
    b.cells("#size-cells", &[0]);
    for (index, id) in ids.iter().enumerate() {
        b.begin(&std::format!("cpu@{index}"));
        b.property("device_type", b"cpu\0");
        b.property("compatible", b"arm,cortex-a76\0");
        b.property("enable-method", b"psci\0");
        if cells == 2 {
            b.cells("reg", &[(id >> 32) as u32, *id as u32]);
        } else {
            b.cells("reg", &[*id as u32]);
        }
        b.end();
    }
    b.end();
    b.begin("psci");
    b.property("compatible", b"arm,psci-1.0\0arm,psci-0.2\0arm,psci\0");
    b.property("method", b"hvc\0");
    b.end();
    b.end();
    b.finish()
}

fn cpus(bytes: &[u8], profile: CpuProfile) -> Result<CpuTopology, Error> {
    Fdt::parse(bytes)?.discover_cpus(profile)
}

/// The CPU profile of QEMU virt over HVC with `cpu_counts` and the affinity
/// level `level`.
fn cpu_profile(cpu_counts: u8, level: AffinityLevel) -> CpuProfile {
    CpuProfile {
        cpu_counts,
        affinity_level: level,
        ..QEMU_HVC_CPUS
    }
}

/// The timer records of `numbers`, each with the flags of 2 CPUs.
fn timer_records(numbers: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for number in numbers {
        for cell in [1, *number, 0x304] {
            bytes.extend_from_slice(&cell.to_be_bytes());
        }
    }
    bytes
}

/// From an exponent of 64 up only the address 0 is a multiple of the
/// alignment, although every address is a multiple of `2 ^ 63` or less.
#[test]
fn alignment_exponent_64_admits_only_address_0() {
    let bytes = hand_over_tree(b"vendor,board\0");
    let memory = boot_memory(&bytes, hand_over(64, b"vendor,board\0"), 0).unwrap();
    assert_eq!(memory.dtb(), Span::new(0, bytes.len() as u64).unwrap());
    assert_eq!(memory.ram_bytes(), 0x40_0000);
    for (log2, dtb, expected) in [
        (64, 1 << 63, Error::BadAlignment),
        (64, 0x20_0000, Error::BadAlignment),
        // Aligned to 2 ^ 63, the tree lies outside the RAM.
        (63, 1 << 63, Error::Unmapped),
    ] {
        let profile = hand_over(log2, b"vendor,board\0");
        assert_eq!(boot_memory(&bytes, profile, dtb).unwrap_err(), expected);
    }
}

#[test]
fn alignment_exponent_255_admits_only_address_0() {
    let bytes = hand_over_tree(b"vendor,board\0");
    let profile = hand_over(255, b"vendor,board\0");
    let memory = boot_memory(&bytes, profile, 0).unwrap();
    assert_eq!(memory.dtb(), Span::new(0, bytes.len() as u64).unwrap());
    for dtb in [1, 0x20_0000, 1 << 63] {
        let error = boot_memory(&bytes, profile, dtb).unwrap_err();
        assert_eq!(error, Error::BadAlignment);
    }
}

/// An empty piece of the required entries, before the first NUL, between
/// two NULs or after the last, requires nothing.
#[test]
fn empty_required_pieces_require_nothing() {
    let bytes = hand_over_tree(b"vendor,board\0vendor,soc\0");
    for required in [&b""[..], b"\0\0", b"\0vendor,soc\0\0vendor,board"] {
        let profile = hand_over(3, required);
        assert!(
            boot_memory(&bytes, profile, 0x20_0000).is_ok(),
            "{required:?}"
        );
    }
    let profile = hand_over(3, b"vendor,soc\0\0vendor,other\0");
    let error = boot_memory(&bytes, profile, 0x20_0000).unwrap_err();
    assert_eq!(error, Error::BadProperty);
}

/// A required piece that is not UTF-8 matches no entry; an entry of the
/// same bytes fails as an entry that is not UTF-8 first.
#[test]
fn required_piece_that_is_not_utf8_matches_no_entry() {
    let bytes = hand_over_tree(b"vendor,board\0vendor,soc\0");
    for required in [&b"vendor,board\0\xff\0"[..], b"\xff", b"vendor,\xc3"] {
        let profile = hand_over(3, required);
        let error = boot_memory(&bytes, profile, 0x20_0000).unwrap_err();
        assert_eq!(error, Error::BadProperty, "{required:?}");
    }
    let bytes = hand_over_tree(b"vendor,board\0\xff\0");
    let error = boot_memory(&bytes, hand_over(3, b"\xff\0"), 0x20_0000).unwrap_err();
    assert_eq!(error, Error::BadString);
}

/// The bit 3 of `cpu_counts` allows 3 CPUs, whose IDs are 0 to 2.
#[test]
fn cpu_counts_with_bit_3_admit_three_cpus() {
    let three = cpu_tree(&[0, 1, 2], 1);
    for counts in [0x08, 0x0e] {
        let topology = cpus(&three, cpu_profile(counts, AffinityLevel::Aff0)).unwrap();
        assert_eq!(topology.count(), 3);
        assert_eq!(topology.affinity(2), Some(2));
        assert_eq!(topology.affinity(3), None);
    }
    let two = cpu_tree(&[0, 1], 1);
    let error = cpus(&two, cpu_profile(0x08, AffinityLevel::Aff0)).unwrap_err();
    assert_eq!(error, Error::BadProperty);
}

#[test]
fn cpu_counts_without_bit_3_reject_three_cpus() {
    let three = cpu_tree(&[0, 1, 2], 1);
    for counts in [0x16, 0xf7, 0x01] {
        let error = cpus(&three, cpu_profile(counts, AffinityLevel::Aff0)).unwrap_err();
        assert_eq!(error, Error::BadProperty, "{counts:#x}");
    }
}

/// Affinity level 2: the CPU IDs are bits 16 to 23 of `MPIDR_EL1`.
#[test]
fn affinity_level_2_shifts_ids_by_16() {
    let profile = cpu_profile(0x16, AffinityLevel::Aff2);
    assert_eq!(profile.affinity_shift(), 16);
    assert_eq!(profile.logical_id(0x2_0000), Some(2));
    assert_eq!(profile.logical_id(0x8102_0000), Some(2));
    for mpidr in [0x200, 0x4_0000, 0x2_0001, 2 << 32] {
        assert_eq!(profile.logical_id(mpidr), None, "{mpidr:#x}");
    }
    let bytes = cpu_tree(&[0, 0x1_0000], 1);
    let topology = cpus(&bytes, profile).unwrap();
    assert_eq!(topology.count(), 2);
    assert_eq!(topology.affinity(1), Some(0x1_0000));
    let error = cpus(&bytes, QEMU_HVC_CPUS).unwrap_err();
    assert_eq!(error, Error::BadProperty);
}

/// Affinity level 3: the CPU IDs are bits 32 to 39 of `MPIDR_EL1`, which
/// need 2 address cells.
#[test]
fn affinity_level_3_shifts_ids_by_32() {
    let profile = cpu_profile(0x16, AffinityLevel::Aff3);
    assert_eq!(profile.affinity_shift(), 32);
    assert_eq!(profile.logical_id(0x3_8100_0000), Some(3));
    for mpidr in [0x3_0000_00ff, 0x4_0000_0000, 3 << 16] {
        assert_eq!(profile.logical_id(mpidr), None, "{mpidr:#x}");
    }
    let bytes = cpu_tree(&[0, 1 << 32], 2);
    let topology = cpus(&bytes, profile).unwrap();
    assert_eq!(topology.count(), 2);
    assert_eq!(topology.affinity(1), Some(1 << 32));
    let level_2 = cpu_profile(0x16, AffinityLevel::Aff2);
    assert_eq!(cpus(&bytes, level_2).unwrap_err(), Error::BadProperty);
}

/// A timer count of 0 expects no record.
#[test]
fn timer_count_0_expects_no_record() {
    let profile = CpuProfile {
        timer_interrupts: Some(TimerInterrupts {
            numbers: [13, 14, 11, 10, 12],
            count: 0,
        }),
        ..QEMU_HVC_CPUS
    };
    let topology = cpus(&cpu_tree(&[0, 1], 1), profile).unwrap();
    assert_eq!(topology.validate_timers(&[]), Ok(()));
    let error = topology.validate_timers(&timer_records(&[13])).unwrap_err();
    assert_eq!(error, Error::BadProperty);
}

/// A timer count above 5 stands for all five numbers.
#[test]
fn timer_count_9_expects_all_five_records() {
    let profile = CpuProfile {
        timer_interrupts: Some(TimerInterrupts {
            numbers: [13, 14, 11, 10, 12],
            count: 9,
        }),
        ..QEMU_HVC_CPUS
    };
    let topology = cpus(&cpu_tree(&[0, 1], 1), profile).unwrap();
    let all = timer_records(&[13, 14, 11, 10, 12]);
    assert_eq!(topology.validate_timers(&all), Ok(()));
    for numbers in [&[13, 14, 11, 10][..], &[], &[13, 14, 11, 10, 12, 12]] {
        let error = topology
            .validate_timers(&timer_records(numbers))
            .unwrap_err();
        assert_eq!(error, Error::BadProperty, "{numbers:?}");
    }
}
