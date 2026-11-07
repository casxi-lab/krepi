module

public import Krepi.Spec.Counter

namespace Krepi.Statements.Counter

open Krepi.Spec.Counter

/-- A step increases the counter. -/
@[expose] public def S : Prop := ∀ n, n < step n

/-- A step does not decrease the counter. -/
@[expose] public def W : Prop := ∀ n, n ≤ step n

end Krepi.Statements.Counter
