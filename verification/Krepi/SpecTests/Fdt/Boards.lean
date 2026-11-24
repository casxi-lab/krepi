module

public import Krepi.Spec.Fdt.BootMemory
public import Krepi.Spec.Fdt.Cpus

/-!
# Device tree: the profiles of two boards in the tests

The hand-over profile of the Raspberry Pi 5 and the CPU profiles of the Pi 5
and of QEMU virt, the values that the contract's `Legacy test vectors` give
the entries for the profile names of the vectors: the specification tests,
the witnesses and the replay of the vectors take them as inputs. They are
test data. The specification holds for every profile, and whether a board
gives these values is not part of it.
-/

@[expose] public section

namespace Krepi.SpecTests.Fdt

open Krepi.Spec.Fdt

/-- The hand-over profile of the Pi 5: a tree of at most 128 KiB, at a
multiple of 8, whose root `compatible` holds `raspberrypi,5-model-b` and
`brcm,bcm2712`. -/
def pi5HandOver : HandOverProfile :=
  ⟨0x2_0000, 3, ⟨(["raspberrypi,5-model-b", "brcm,bcm2712"].flatMap fun s =>
    s.toByteArray.toList ++ [0]).toArray⟩⟩

/-- The CPU profile of the Pi 5, `Pi5` in the vectors: PSCI over SMC, CPU IDs
at affinity level 1, exactly 4 CPUs, an `enable-method` also on CPU 0, and no
timer that the core checks. -/
def pi5Cpus : CpuProfile := ⟨.smc, .aff1, 0x10, true, none⟩

/-- The private interrupts of the timer of QEMU virt: 13, 14, 11 and 10, and
with EL2 12 after them. -/
def qemuTimer (el2 : Bool) : TimerInterrupts := ⟨#v[13, 14, 11, 10, 12], if el2 then 5 else 4⟩

/-- The CPU profile of QEMU virt with PSCI over HVC, `QemuHvc` in the
vectors: CPU IDs at affinity level 0, 1, 2 or 4 CPUs, no `enable-method`
needed on CPU 0, and the timer interrupts 13, 14, 11 and 10. -/
def qemuHvcCpus : CpuProfile := ⟨.hvc, .aff0, 0x16, false, some (qemuTimer false)⟩

/-- The CPU profile of QEMU virt with EL2 and PSCI over SMC, `QemuSmc` in the
vectors: as `qemuHvcCpus`, and the timer interrupt 12 as well. -/
def qemuSmcCpus : CpuProfile := ⟨.smc, .aff0, 0x16, false, some (qemuTimer true)⟩

end Krepi.SpecTests.Fdt
