//! The CPU nodes: the affinities and conduits of the Pi 5 and QEMU virt
//! profiles, aliased, missing and foreign IDs, the status, model and enable
//! method of a CPU node, the width of its `reg`, the flag bits of
//! `MPIDR_EL1` and the timer records of QEMU virt.
//!
//! Feature: krepi.platform.device-tree

use super::*;

fn tree(
    ids: &[u64],
    method: &str,
    disabled: Option<usize>,
    enable: &str,
    model: &str,
    cells_count: u32,
) -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    b.begin("cpus");
    b.cells("#address-cells", &[cells_count]);
    b.cells("#size-cells", &[0]);
    for (index, id) in ids.iter().enumerate() {
        b.begin(&std::format!("cpu@{index}"));
        b.property("device_type", b"cpu\0");
        b.property("compatible", model.as_bytes());
        b.property("enable-method", enable.as_bytes());
        if disabled == Some(index) {
            b.property("status", b"disabled\0");
        }
        if cells_count == 2 {
            b.cells("reg", &[(id >> 32) as u32, *id as u32]);
        } else {
            b.cells("reg", &[*id as u32]);
        }
        b.end();
    }
    b.end();
    b.begin("psci");
    b.property("compatible", b"arm,psci-1.0\0arm,psci-0.2\0arm,psci\0");
    b.property("method", method.as_bytes());
    b.end();
    b.end();
    b.finish()
}

fn discover(ids: &[u64], method: &str, profile: CpuProfile) -> Result<CpuTopology, Error> {
    let bytes = tree(ids, method, None, "psci\0", "arm,cortex-a76\0", 2);
    Fdt::parse(&bytes)?.discover_cpus(profile)
}

#[test]
fn separate_pi5_and_virtual_affinities_and_conduits() {
    let pi = discover(&[0, 0x100, 0x200, 0x300], "smc\0", PI5_CPUS).unwrap();
    assert_eq!(pi.count(), 4);
    assert_eq!(pi.profile(), PI5_CPUS);
    for index in 0..4 {
        assert_eq!(pi.affinity(index), Some(index << 8));
    }
    assert_eq!(pi.affinity(4), None);
    for (profile, method) in [(QEMU_HVC_CPUS, "hvc\0"), (QEMU_SMC_CPUS, "smc\0")] {
        for count in [1, 2, 4] {
            let ids: Vec<_> = (0..count).collect();
            assert_eq!(discover(&ids, method, profile).unwrap().count(), count);
        }
    }
    assert!(discover(&[0, 1, 2, 3], "smc\0", PI5_CPUS).is_err());
    assert!(discover(&[0, 0x100, 0x200, 0x300], "hvc\0", PI5_CPUS).is_err());
    assert!(discover(&[0, 1], "smc\0", QEMU_HVC_CPUS).is_err());
    assert!(discover(&[0, 1], "hvc\0", QEMU_SMC_CPUS).is_err());
}

#[test]
fn reject_alias_holes_foreign_affinities_and_incomplete_board() {
    for ids in [
        &[0, 0, 2, 3][..],
        &[0, 1, 3],
        &[0, 1, 2],
        &[1, 2],
        &[0, 4],
        &[0, 0x100],
        &[0, 1 << 32],
        &[0, 1 << 31],
    ] {
        assert!(discover(ids, "hvc\0", QEMU_HVC_CPUS).is_err(), "{ids:?}");
    }
    for ids in [
        &[0, 0x100][..],
        &[0, 0x100, 0x200, 0x301],
        &[0, 0x100, 0x200, 0x400],
    ] {
        assert!(discover(ids, "smc\0", PI5_CPUS).is_err());
    }
}

#[test]
fn cpu_status_model_and_enable_method_are_required() {
    for (disabled, enable, model) in [
        (Some(2), "psci\0", "arm,cortex-a76\0"),
        (None, "spin-table\0", "arm,cortex-a76\0"),
        (None, "psci\0", "arm,cortex-a53\0"),
    ] {
        let bytes = tree(
            &[0, 0x100, 0x200, 0x300],
            "smc\0",
            disabled,
            enable,
            model,
            2,
        );
        assert!(Fdt::parse(&bytes).unwrap().discover_cpus(PI5_CPUS).is_err());
    }
}

/// CPU 0 needs the `enable-method` `psci` on the Pi 5, whose profile sets
/// `cpu0_enable_method`, and not on QEMU virt: CPU 0 without it or with
/// `spin-table` is `BadProperty` on the Pi 5 and accepted on QEMU virt.
#[test]
fn cpu0_needs_its_enable_method_on_the_pi5_alone() {
    for cpu0 in [None, Some(&b"spin-table\0"[..])] {
        for (profile, method, shift) in [(PI5_CPUS, "smc\0", 8), (QEMU_HVC_CPUS, "hvc\0", 0)] {
            let mut b = Builder::default();
            b.root();
            b.begin("cpus");
            b.cells("#address-cells", &[1]);
            b.cells("#size-cells", &[0]);
            for id in 0..4u32 {
                b.begin(&std::format!("cpu@{id}"));
                b.property("device_type", b"cpu\0");
                b.property("compatible", b"arm,cortex-a76\0");
                b.cells("reg", &[id << shift]);
                match (id, cpu0) {
                    (0, None) => {}
                    (0, Some(enable)) => b.property("enable-method", enable),
                    _ => b.property("enable-method", b"psci\0"),
                }
                b.end();
            }
            b.end();
            b.begin("psci");
            b.property("compatible", b"arm,psci-1.0\0arm,psci-0.2\0arm,psci\0");
            b.property("method", method.as_bytes());
            b.end();
            b.end();
            let bytes = b.finish();
            let topology = Fdt::parse(&bytes).unwrap().discover_cpus(profile);
            if profile == PI5_CPUS {
                assert_eq!(topology.unwrap_err(), Error::BadProperty);
            } else {
                assert_eq!(topology.unwrap().count(), 4);
            }
        }
    }
}

#[test]
fn cpu_reg_cell_width_is_checked_without_truncation() {
    for cells_count in [1, 2] {
        let bytes = tree(
            &[0, 0x100, 0x200, 0x300],
            "smc\0",
            None,
            "psci\0",
            "arm,cortex-a76\0",
            cells_count,
        );
        assert_eq!(
            Fdt::parse(&bytes)
                .unwrap()
                .discover_cpus(PI5_CPUS)
                .unwrap()
                .count(),
            4
        );
    }
    assert!(discover(&[0, 0x100, 0x200, 0x100000300], "smc\0", PI5_CPUS).is_err());
}

#[test]
fn register_flags_do_not_change_logical_identity() {
    for id in 0..4 {
        for flags in [0, 1 << 24, 1 << 30, 1 << 31, 0xc1000000] {
            assert_eq!(PI5_CPUS.logical_id(flags | (id << 8)), Some(id));
            assert_eq!(QEMU_HVC_CPUS.logical_id(flags | id), Some(id));
        }
    }
    for id in [1, 0x101, 0x400, 0x10000, 1 << 32] {
        assert_eq!(PI5_CPUS.logical_id(id), None);
    }
}

#[test]
fn qemu_timer_records_follow_profile_and_admitted_cpus() {
    for (profile, method) in [(QEMU_HVC_CPUS, "hvc\0"), (QEMU_SMC_CPUS, "smc\0")] {
        let ppis: &[u32] = if profile == QEMU_HVC_CPUS {
            &[13, 14, 11, 10]
        } else {
            &[13, 14, 11, 10, 12]
        };
        for count in [1, 2, 4] {
            let ids: Vec<_> = (0..count).collect();
            let topology = discover(&ids, method, profile).unwrap();
            let flags = (((1u32 << count) - 1) << 8) | 4;
            let mut valid = Vec::new();
            for ppi in ppis {
                for cell in [1, *ppi, flags] {
                    valid.extend_from_slice(&cell.to_be_bytes());
                }
            }
            assert_eq!(topology.validate_timers(&valid), Ok(()));
            for length in [0, 12, valid.len() - 1, valid.len() - 12] {
                assert!(topology.validate_timers(&valid[..length]).is_err());
            }
            let mut extra = valid.clone();
            extra.extend_from_slice(&valid[..12]);
            assert!(topology.validate_timers(&extra).is_err());
            for offset in (0..valid.len()).step_by(4) {
                let mut wrong = valid.clone();
                wrong[offset + 3] ^= 1;
                assert!(topology.validate_timers(&wrong).is_err());
            }
            let mut wrong_mask = valid.clone();
            wrong_mask[10] ^= 1;
            assert!(topology.validate_timers(&wrong_mask).is_err());
            let pi = discover(&[0, 0x100, 0x200, 0x300], "smc\0", PI5_CPUS).unwrap();
            assert!(pi.validate_timers(&valid).is_err());
        }
    }
}
