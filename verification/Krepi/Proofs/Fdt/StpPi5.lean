module

public import Krepi.SpecTests.Fdt.Stp
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.StpLemmas

/-!
# Device tree: the specification tests of the Pi 5 trees

The specification tests of FDT-R05 and FDT-R06, which `Krepi.Proofs.Fdt.Stp`
restates. Each parse is the walk of the structure block (`parse_fast`), so the
trees of 128 KiB are never evaluated byte by byte: their zero bytes after the
strings block only set `totalsize`. The rest is a kernel decision, for each
of the five RAM models of FDT-R06 in turn.
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

/-- FDT-R06, accepted. -/
theorem pi5ModelsBuildBootMemoryMaps : Pi5ModelsBuildBootMemoryMaps := by
  intro model hm
  simp only [ramModels, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (unfold pi5Plan; rw [parse_fast0]; decide +kernel)

/-- FDT-R06, rejected. -/
theorem bootMemoryMapRejectsRamAboveCapacity : BootMemoryMapRejectsRamAboveCapacity := by
  unfold BootMemoryMapRejectsRamAboveCapacity pi5Plan; rw [parse_fast0]; decide +kernel

end Krepi.Proofs.Fdt.StpPi5
