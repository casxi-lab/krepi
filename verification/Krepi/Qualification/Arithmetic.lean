module

public import KrepiGen.Qual.Arithmetic.Funs

/-!
# Machine-word modular arithmetic

`u32` operands widened to `u64` before multiplying and reducing, as in
prime-field arithmetic. The proof discharges the overflow side condition of
the 64-bit product.
-/

open Aeneas Aeneas.Std Result
open KrepiGen.Qual.Arithmetic

namespace Krepi.Qualification.Arithmetic

public theorem mul_mod_spec (a b p : Std.U32) (hp : 0 < p.val) :
    arithmetic.mul_mod a b p ⦃ r => r.val = a.val * b.val % p.val ⦄ := by
  unfold arithmetic.mul_mod
  simp only [lift]
  step as ⟨ i2, hi2 ⟩
  step as ⟨ i4, hi4 ⟩
  simp only [core.convert.num.FromU64U32.from_val_eq] at hi2 hi4
  have hbound : i4.val < 2 ^ 32 := by
    have := Nat.mod_lt (a.val * b.val) hp
    have := p.hBounds
    simp_all
    omega
  rw [UScalar.cast_val_eq]
  simp only [UScalarTy.numBits]
  rw [Nat.mod_eq_of_lt hbound, hi4, hi2]

end Krepi.Qualification.Arithmetic
