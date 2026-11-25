//! The profiles of two boards that the tests give the entries: the
//! hand-over profile of the Raspberry Pi 5 and the CPU profiles of the Pi 5
//! and of QEMU virt, with the values that the contract's `Legacy test
//! vectors` section gives the profile names of the vectors. They are test
//! data: the rules hold for every profile, and whether a board gives these
//! values is not part of them.
//!
//! Feature: krepi.platform.device-tree

use super::*;

/// The hand-over profile of the Pi 5, `discover_pi5_boot_memory` in the
/// vectors: a tree of at most 128 KiB, at a multiple of 8, whose root
/// `compatible` holds `raspberrypi,5-model-b` and `brcm,bcm2712`.
pub(crate) const PI5_HAND_OVER: HandOverProfile<'static> = HandOverProfile {
    max_blob_size: 0x2_0000,
    alignment_log2: 3,
    compatible: b"raspberrypi,5-model-b\0brcm,bcm2712\0",
};

/// The CPU profile of the Pi 5, `Pi5` in the vectors: PSCI over SMC, CPU
/// IDs at affinity level 1, exactly 4 CPUs, an `enable-method` also on
/// CPU 0, and no timer that the core checks.
pub(crate) const PI5_CPUS: CpuProfile = CpuProfile {
    conduit: PsciConduit::Smc,
    affinity_level: AffinityLevel::Aff1,
    cpu_counts: 0x10,
    cpu0_enable_method: true,
    timer_interrupts: None,
};

/// The private interrupts of the timer of QEMU virt: 13, 14, 11 and 10, and
/// with EL2 12 after them.
const QEMU_TIMER: [u32; 5] = [13, 14, 11, 10, 12];

/// The CPU profile of QEMU virt with PSCI over HVC, `QemuHvc` in the
/// vectors: CPU IDs at affinity level 0, 1, 2 or 4 CPUs, no `enable-method`
/// needed on CPU 0, and the timer interrupts 13, 14, 11 and 10.
pub(crate) const QEMU_HVC_CPUS: CpuProfile = CpuProfile {
    conduit: PsciConduit::Hvc,
    affinity_level: AffinityLevel::Aff0,
    cpu_counts: 0x16,
    cpu0_enable_method: false,
    timer_interrupts: Some(TimerInterrupts {
        numbers: QEMU_TIMER,
        count: 4,
    }),
};

/// The CPU profile of QEMU virt with EL2 and PSCI over SMC, `QemuSmc` in the
/// vectors: as [`QEMU_HVC_CPUS`], and the timer interrupt 12 as well.
pub(crate) const QEMU_SMC_CPUS: CpuProfile = CpuProfile {
    conduit: PsciConduit::Smc,
    affinity_level: AffinityLevel::Aff0,
    cpu_counts: 0x16,
    cpu0_enable_method: false,
    timer_interrupts: Some(TimerInterrupts {
        numbers: QEMU_TIMER,
        count: 5,
    }),
};
