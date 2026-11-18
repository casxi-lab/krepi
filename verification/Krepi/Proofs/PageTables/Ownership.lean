module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about the establishment and the well-formedness of the page ownership table

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the establishment and the well-
formedness of the page ownership table, whose type is exactly that
statement: that `Ownership::new` establishes the invariants of the table,
and that each write entry of the table keeps it well-formed.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Ownership

open Krepi.SpecProperties.PageTables

public theorem newOwnershipWellFormed : NewOwnershipWellFormed := by
  sorry

public theorem newOneOwner : NewOneOwner := by
  sorry

public theorem newHolderRanges : NewHolderRanges := by
  sorry

public theorem newGenerationsBelowCounter : NewGenerationsBelowCounter := by
  sorry

public theorem newFreeExtentsMaximal : NewFreeExtentsMaximal := by
  sorry

public theorem newFreeOrHeldUsable : NewFreeOrHeldUsable := by
  sorry

public theorem assignWellFormed : AssignWellFormed := by
  sorry

public theorem reserveWellFormed : ReserveWellFormed := by
  sorry

public theorem publishWellFormed : PublishWellFormed := by
  sorry

public theorem cancelWellFormed : CancelWellFormed := by
  sorry

public theorem releaseWellFormed : ReleaseWellFormed := by
  sorry

end Krepi.Proofs.PageTables.Ownership
