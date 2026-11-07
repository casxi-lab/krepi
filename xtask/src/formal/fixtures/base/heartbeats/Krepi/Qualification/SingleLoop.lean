module

public import KrepiGen.Qual.SingleLoop.Funs

/-!
# A charge inside a loop

`?` on a fallible charge inside a single loop, the most common resource
accounting shape. The loop is translated with the `loop` combinator and its
specification is proved with a measure and an invariant.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Qual.SingleLoop

namespace Krepi.Qualification.SingleLoop

#count_heartbeats in
/-- Charging `count` single units succeeds exactly when the budget suffices;
otherwise the budget is exhausted and an error is returned. -/
public theorem charge_each_spec (b : budget.Budget) (count : Std.U32) :
    single_loop.charge_each b count ⦃ r b' =>
      (count.val ≤ b.left.val → r = .Ok count ∧ b'.left.val = b.left.val - count.val) ∧
      (b.left.val < count.val → r = .Err () ∧ b'.left.val = 0) ⦄ := by
  unfold single_loop.charge_each single_loop.charge_each_loop
  apply loop.spec_decr_nat
    (measure := fun (_, done) => count.val - done.val)
    (inv := fun (b1, done) =>
      done.val ≤ count.val ∧ done.val ≤ b.left.val ∧ b1.left.val = b.left.val - done.val)
  · rintro ⟨b1, done⟩ ⟨hle, hleft, hb1⟩
    unfold single_loop.charge_each_loop.body budget.Budget.take
    step*
    · rename_i hlt
      have : done.val < count.val := hlt
      by_cases hz : b1.left.val = 0
      · have hgt : 1#u64 > b1.left := by simp [UScalar.lt_equiv, hz]
        simp [hgt, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hz]
        omega
      · have hgt : ¬ 1#u64 > b1.left := by simp [UScalar.lt_equiv]; omega
        simp only [hgt, ite_false]
        step as ⟨ left1, hleft1 ⟩
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step as ⟨ done2, hdone2 ⟩
        omega
    · rename_i hge
      have hd : done.val = count.val := by
        have : ¬ done.val < count.val := hge
        omega
      have heq : done = count := UScalar.eq_of_val_eq hd
      refine ⟨fun _ => ⟨by rw [heq], by rw [hb1, hd]⟩, fun h => absurd h (by omega)⟩
  · simp

end Krepi.Qualification.SingleLoop
