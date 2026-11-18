module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about the checks of the invariants

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the checks of the invariants, whose
type is exactly that statement: that each computable check agrees with its
invariant, on every value or on every value that keeps the invariants that
the check reads.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Checks

open Krepi.SpecProperties.PageTables

public theorem checkTablesWellFormed : CheckTablesWellFormed := by
  sorry

public theorem checkOwnershipWellFormed : CheckOwnershipWellFormed := by
  sorry

public theorem checkSharedWellFormed : CheckSharedWellFormed := by
  sorry

public theorem checkOneOwner : CheckOneOwner := by
  sorry

public theorem checkHolderRanges : CheckHolderRanges := by
  sorry

public theorem checkGenerationsBelowCounter : CheckGenerationsBelowCounter := by
  sorry

public theorem checkFreeExtentsMaximal : CheckFreeExtentsMaximal := by
  sorry

public theorem checkFreeOrHeldUsable : CheckFreeOrHeldUsable := by
  sorry

public theorem checkDirectMapOffset : CheckDirectMapOffset := by
  sorry

end Krepi.Proofs.PageTables.Checks
