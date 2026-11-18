module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about the preservation of the invariants of the page ownership table

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the preservation of the invariants
of the page ownership table, whose type is exactly that statement: that each
write entry of the page ownership table preserves each of its functional
invariants.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Preservation

open Krepi.SpecProperties.PageTables

public theorem assignOneOwner : AssignOneOwner := by
  sorry

public theorem reserveOneOwner : ReserveOneOwner := by
  sorry

public theorem publishOneOwner : PublishOneOwner := by
  sorry

public theorem cancelOneOwner : CancelOneOwner := by
  sorry

public theorem releaseOneOwner : ReleaseOneOwner := by
  sorry

public theorem assignHolderRanges : AssignHolderRanges := by
  sorry

public theorem reserveHolderRanges : ReserveHolderRanges := by
  sorry

public theorem publishHolderRanges : PublishHolderRanges := by
  sorry

public theorem cancelHolderRanges : CancelHolderRanges := by
  sorry

public theorem releaseHolderRanges : ReleaseHolderRanges := by
  sorry

public theorem assignGenerationsBelowCounter : AssignGenerationsBelowCounter := by
  sorry

public theorem reserveGenerationsBelowCounter : ReserveGenerationsBelowCounter := by
  sorry

public theorem publishGenerationsBelowCounter : PublishGenerationsBelowCounter := by
  sorry

public theorem cancelGenerationsBelowCounter : CancelGenerationsBelowCounter := by
  sorry

public theorem releaseGenerationsBelowCounter : ReleaseGenerationsBelowCounter := by
  sorry

public theorem assignFreeExtentsMaximal : AssignFreeExtentsMaximal := by
  sorry

public theorem reserveFreeExtentsMaximal : ReserveFreeExtentsMaximal := by
  sorry

public theorem publishFreeExtentsMaximal : PublishFreeExtentsMaximal := by
  sorry

public theorem cancelFreeExtentsMaximal : CancelFreeExtentsMaximal := by
  sorry

public theorem releaseFreeExtentsMaximal : ReleaseFreeExtentsMaximal := by
  sorry

public theorem assignFreeOrHeldUsable : AssignFreeOrHeldUsable := by
  sorry

public theorem reserveFreeOrHeldUsable : ReserveFreeOrHeldUsable := by
  sorry

public theorem publishFreeOrHeldUsable : PublishFreeOrHeldUsable := by
  sorry

public theorem cancelFreeOrHeldUsable : CancelFreeOrHeldUsable := by
  sorry

public theorem releaseFreeOrHeldUsable : ReleaseFreeOrHeldUsable := by
  sorry

end Krepi.Proofs.PageTables.Preservation
