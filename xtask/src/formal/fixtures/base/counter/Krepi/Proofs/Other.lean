module

public import Krepi.Statements.Counter

namespace Krepi.Proofs.Other

open Krepi.Statements.Counter

/-- A statement defined in a proof module. -/
@[expose] public def P : Prop := True

public theorem u : S := by
  sorry

public theorem v : P := trivial

end Krepi.Proofs.Other
