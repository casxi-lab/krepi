module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about duplicates and ambiguities

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about duplicates and ambiguities, whose type is exactly that statement: that
where an entry looks for one item and finds two, it rejects the input and
never picks one.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Duplicates

open Krepi.SpecProperties.Fdt

public theorem noChoiceAmongDuplicates : NoChoiceAmongDuplicates := by
  sorry

end Krepi.Proofs.Fdt.Duplicates
