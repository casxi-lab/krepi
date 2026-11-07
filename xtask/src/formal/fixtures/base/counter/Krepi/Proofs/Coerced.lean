module

public import Krepi.Proofs.Counter

namespace Krepi.Proofs.Coerced

open Krepi.Statements.Counter

/-- A proposition of the proofs. -/
@[expose] public def T : Prop := True

/-- A coercion of the proofs from `T` to the statement `W`. -/
public instance : Coe T W := ⟨fun _ => Krepi.Proofs.Counter.t⟩

/-- A theorem of `T`, which `example : W := c` accepts through the coercion. -/
public theorem c : T := trivial

end Krepi.Proofs.Coerced
