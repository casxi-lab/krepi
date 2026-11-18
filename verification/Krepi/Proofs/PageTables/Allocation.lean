module

public import Krepi.SpecProperties.PageTables.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about placement and the owners at boot

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about placement and the owners at boot,
whose type is exactly that statement: that `choose` takes the first fit of
its placement, and that the table of the kernel root matches the direct map.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Allocation

open Krepi.SpecProperties.PageTables

public theorem placementFirstFit : PlacementFirstFit := by
  sorry

public theorem bootOwnersMatchDirectMap : BootOwnersMatchDirectMap := by
  sorry

end Krepi.Proofs.PageTables.Allocation
