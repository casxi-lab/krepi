module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about the boot memory map

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the boot memory map, whose type is exactly that statement: that the
entries of the boot memory map give well-formed maps, and that their usable
ranges are well-formed and exact.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Plan

open Krepi.SpecProperties.Fdt

public theorem allRamWellFormed : AllRamWellFormed := by
  sorry

public theorem memoryPlanNewWellFormed : MemoryPlanNewWellFormed := by
  sorry

public theorem fromPi5WellFormed : FromPi5WellFormed := by
  sorry

public theorem availableRangesWellFormed : AvailableRangesWellFormed := by
  sorry

public theorem usableRangesExact : UsableRangesExact := by
  sorry

end Krepi.Proofs.Fdt.Plan
