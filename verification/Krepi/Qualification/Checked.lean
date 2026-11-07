module

public import KrepiGen.Qual.Checked.Funs

/-!
# Checked budget arithmetic

`checked_add` followed by a comparison, the shape of a work charge.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Qual.Checked

namespace Krepi.Qualification.Checked

/-- The sum is returned exactly when it neither overflows nor exceeds `max`. -/
public theorem add_within_spec (work amount max : Std.U64) :
    checked.add_within work amount max ⦃ o =>
      match o with
      | some total => total.val = work.val + amount.val ∧ total.val ≤ max.val
      | none => max.val < work.val + amount.val ⦄ := by
  unfold checked.add_within
  step*

end Krepi.Qualification.Checked
