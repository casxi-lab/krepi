module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.PlanLemmas
import Krepi.Proofs.Fdt.BootMemoryLemmas

/-!
# Device tree: proofs about the selection of the boot memory

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the selection of the boot memory, whose type is exactly that
statement: that `BootMemory::find_available` gives a well-formed span,
available and of the lowest aligned start in the first RAM range that has
one.

Both theorems are planned: each proof is `sorry` until a proof pull request
proves it. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.BootMemory

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

public theorem findAvailableWellFormed : FindAvailableWellFormed := by
  sorry

public theorem findAvailableLowest : FindAvailableLowest := by
  sorry

end Krepi.Proofs.Fdt.BootMemory
