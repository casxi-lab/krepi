module

public import Krepi.Statements.Counter

namespace Krepi.Proofs.Counter

open Krepi.Statements.Counter Krepi.Spec.Counter

/-- The weaker proposition. -/
public theorem t : W := by
  intro n
  unfold step
  omega

theorem helper : S := by
  intro n
  unfold step
  omega

public theorem s : S := helper

end Krepi.Proofs.Counter
