module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about the shared state

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the shared state, whose type is
exactly that statement: that the shared state of the boot is well-formed and
keeps the offset of the direct map, that `direct_map` keeps that offset, and
that each transaction keeps the shared state well-formed.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Tokens

open Krepi.SpecProperties.PageTables

public theorem bootWellFormed : BootWellFormed := by
  sorry

public theorem bootDirectMapOffset : BootDirectMapOffset := by
  sorry

public theorem buildDirectMapOffset : BuildDirectMapOffset := by
  sorry

public theorem buildKernelMapWellFormed : BuildKernelMapWellFormed := by
  sorry

public theorem buildDirectMapWellFormed : BuildDirectMapWellFormed := by
  sorry

public theorem enableWellFormed : EnableWellFormed := by
  sorry

public theorem fillKernelWellFormed : FillKernelWellFormed := by
  sorry

public theorem newOwnershipSharedWellFormed : NewOwnershipSharedWellFormed := by
  sorry

public theorem withOwnershipWellFormed : WithOwnershipWellFormed := by
  sorry

public theorem allocateWellFormed : AllocateWellFormed := by
  sorry

end Krepi.Proofs.PageTables.Tokens
