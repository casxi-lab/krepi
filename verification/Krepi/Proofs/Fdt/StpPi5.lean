module

public import Krepi.SpecTests.Fdt.Stp
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.StpLemmas

/-!
# Device tree: the specification tests of the Pi 5 trees

The specification tests of FDT-R05 and FDT-R06 on the Pi 5 trees. Each parse is the walk of the structure block (`parse_fast` for the
trees of FDT-R05, finished to a size, and `parse_fast0` for those of FDT-R06),
so the trees of 128 KiB are never evaluated byte by byte: their zero bytes
after the strings block only set `totalsize`. The rest is a kernel decision,
for each of the five RAM models of FDT-R06 in a declaration of its own, so
that no declaration holds more than one decision.
-/

public section

namespace Krepi.Proofs.Fdt.StpPi5

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt Krepi.SpecTests.Fdt

attribute [local instance] decEqExcept

/-- FDT-R05, accepted. -/
theorem pi5AcceptsTreeAtLimit : Pi5AcceptsTreeAtLimit := by
  unfold Pi5AcceptsTreeAtLimit pi5BootOfSize; rw [parse_fast]; decide +kernel

/-- FDT-R05, rejected. -/
theorem pi5RejectsTreeAboveLimit : Pi5RejectsTreeAboveLimit := by
  unfold Pi5RejectsTreeAboveLimit pi5BootOfSize; rw [parse_fast]; decide +kernel

/-- FDT-R06, accepted, for one model: its boot memory map. -/
private abbrev ModelBuilds (model : RamModel) : Prop :=
  (pi5Plan model.ranges).map (fun r => (r.1.ram, r.1.ramBytes, r.2.map (·.availableRanges))) =
    .ok (model.ranges.map spanOf, model.ramBytes, .ok model.usable)

private theorem model0 : ModelBuilds (ramModels[0]'(by decide)) := by
  unfold ModelBuilds pi5Plan; rw [parse_fast0]; decide +kernel

private theorem model1 : ModelBuilds (ramModels[1]'(by decide)) := by
  unfold ModelBuilds pi5Plan; rw [parse_fast0]; decide +kernel

private theorem model2 : ModelBuilds (ramModels[2]'(by decide)) := by
  unfold ModelBuilds pi5Plan; rw [parse_fast0]; decide +kernel

private theorem model3 : ModelBuilds (ramModels[3]'(by decide)) := by
  unfold ModelBuilds pi5Plan; rw [parse_fast0]; decide +kernel

private theorem model4 : ModelBuilds (ramModels[4]'(by decide)) := by
  unfold ModelBuilds pi5Plan; rw [parse_fast0]; decide +kernel

/-- FDT-R06, accepted: one kernel decision for each model, each in its own
declaration (`model0` to `model4`). -/
theorem pi5ModelsBuildBootMemoryMaps : Pi5ModelsBuildBootMemoryMaps := by
  intro model hm
  simp only [ramModels, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact model0
  · exact model1
  · exact model2
  · exact model3
  · exact model4

/-- FDT-R06, rejected. -/
theorem bootMemoryMapRejectsRamAboveCapacity : BootMemoryMapRejectsRamAboveCapacity := by
  unfold BootMemoryMapRejectsRamAboveCapacity pi5Plan; rw [parse_fast0]; decide +kernel

end Krepi.Proofs.Fdt.StpPi5
