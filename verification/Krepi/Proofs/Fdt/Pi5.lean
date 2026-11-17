module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about the selection of the Pi 5 boot memory

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the selection of the Pi 5 boot memory, whose type is exactly that
statement: that `Pi5BootMemory::find_available` gives a well-formed span,
available and of the lowest aligned start in the first RAM range that has
one.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Pi5

open Krepi.SpecProperties.Fdt

public theorem findAvailableWellFormed : FindAvailableWellFormed := by
  sorry

public theorem findAvailableLowest : FindAvailableLowest := by
  sorry

end Krepi.Proofs.Fdt.Pi5
