module

public import Krepi.SpecTests.Fdt.Stp
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.StpLemmas

/-!
# Device tree: the specification tests of the memory discovery

The specification tests of FDT-R03, FDT-R04 and FDT-R10, which
`Krepi.Proofs.Fdt.Stp` restates. Each parse is the walk of the structure
block (`parse_fast0`), and the rest is a kernel decision. For the seeds of
FDT-R10, the two boots are decided one by one, and the two trees of the parse
are compared by `sameB`, which gives `Fdt.SameExceptValues` (`sameB_sound`).
-/

public section

namespace Krepi.Proofs.Fdt.StpMemory

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt Krepi.SpecTests.Fdt

attribute [local instance] decEqExcept

/-- FDT-R03, accepted. -/
theorem discoveryAcceptsMaxRamRanges : DiscoveryAcceptsMaxRamRanges := by
  unfold DiscoveryAcceptsMaxRamRanges ramRangesTree; rw [parse_fast0]; decide +kernel

/-- FDT-R03, rejected. -/
theorem discoveryRejectsExcessRamRanges : DiscoveryRejectsExcessRamRanges := by
  unfold DiscoveryRejectsExcessRamRanges ramRangesTree; rw [parse_fast0]; decide +kernel

/-- FDT-R04, accepted. -/
theorem discoveryRecordsDynamicReservations : DiscoveryRecordsDynamicReservations := by
  unfold DiscoveryRecordsDynamicReservations reservedTree; rw [parse_fast0]; decide +kernel

/-- FDT-R04, rejected. -/
theorem discoveryRejectsEmptyStaticReservation : DiscoveryRejectsEmptyStaticReservation := by
  unfold DiscoveryRejectsEmptyStaticReservation reservedTree; rw [parse_fast0]; decide +kernel

/-- FDT-R10, accepted. -/
theorem seedsDoNotReachResults : SeedsDoNotReachResults := by
  refine ⟨?_, ?_⟩
  · intro chosen hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> (unfold qemuBoot qemuTree; rw [parse_fast0]; decide +kernel)
  · have h : okAnd (Fdt.parse (qemuTree seedsA)) (fun t => okAnd (Fdt.parse (qemuTree seedsB))
        (fun t' => sameB (unreadByDiscoveries t) t t')) = true := by
      unfold qemuTree; rw [parse_fast0, parse_fast0]; decide +kernel
    obtain ⟨t, ht, h'⟩ := okAnd_spec h
    obtain ⟨t', ht', h''⟩ := okAnd_spec h'
    exact ⟨t, t', ht, ht', sameB_sound h''⟩

/-- FDT-R10, rejected. -/
theorem chosenDeviceTypeIsRead : ChosenDeviceTypeIsRead := by
  unfold ChosenDeviceTypeIsRead qemuTree; rw [parse_fast0]; decide +kernel

end Krepi.Proofs.Fdt.StpMemory
