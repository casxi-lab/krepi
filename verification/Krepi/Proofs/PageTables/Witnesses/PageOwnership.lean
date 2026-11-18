module

public import Krepi.Spec.PageTables.Witnesses.PageOwnership
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs of the unreachable error branches of the page ownership table

One theorem for each proposition of
`Krepi.Spec.PageTables.Witnesses.PageOwnership` that the module does not
prove itself, whose type is exactly that proposition: for each error branch
that no input of its entry reaches, that the entry never takes it.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Witnesses.PageOwnership

open Krepi.Spec.PageTables.Witnesses.PageOwnership

/-! ## Unreachable error branches -/

public theorem takeAcceptsChoice : TakeAcceptsChoice := by
  sorry

public theorem highPlacementNoOverflow : HighPlacementNoOverflow := by
  sorry

end Krepi.Proofs.PageTables.Witnesses.PageOwnership
