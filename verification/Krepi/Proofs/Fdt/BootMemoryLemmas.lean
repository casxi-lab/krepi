module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.PlanLemmas

/-!
# Device tree: lemmas about the selection of the boot memory

Lemmas about `BootMemory::find_available` of the specification of the
`fdt` component, for the proofs of the statements about it:

- `alignUp_ok`: the least aligned address at or above an address;
- `cand_toNat` and `cand_size_ne`: the candidate at a start.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- A success of `alignUp` is the least multiple of the alignment at or above
the address, below `2 ^ 64`. -/
theorem alignUp_ok {a al c : Nat} (hal : 0 < al) (h : alignUp a al = .ok c) :
    a ≤ c ∧ c % al = 0 ∧ c < 2 ^ 64 ∧ ∀ t, a ≤ t → t % al = 0 → c ≤ t := by
  unfold alignUp at h
  dsimp only at h
  split at h
  · rename_i hlt
    injection h with h
    subst h
    refine ⟨?_, Nat.mul_mod_left _ _, hlt, ?_⟩
    · have := @Nat.lt_div_mul_add (a + al - 1) al hal
      omega
    · intro t hat ht
      have h2 : t / al * al = t := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ht)
      have hq : (a + al - 1) / al < t / al + 1 := by
        rw [Nat.div_lt_iff_lt_mul hal, Nat.add_mul, Nat.one_mul]
        omega
      have := Nat.mul_le_mul_right al (Nat.le_of_lt_succ hq)
      omega
  · cases h

/-- The start, size and end of a candidate within 64 bits. -/
theorem cand_toNat {t size : Nat} (h : t + size < 2 ^ 64) :
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).start.toNat = t ∧
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).size.toNat = size ∧
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).endNat = t + size := by
  have hu : UInt64.size = 2 ^ 64 := rfl
  have h1 : (UInt64.ofNat t).toNat = t := UInt64.toNat_ofNat_of_lt' (by omega)
  have h2 : (UInt64.ofNat size).toNat = size := UInt64.toNat_ofNat_of_lt' (by omega)
  exact ⟨h1, h2, by unfold Span.endNat; rw [h1, h2]⟩

/-- A candidate of a nonzero size within 64 bits is not empty. -/
theorem cand_size_ne {t size : Nat} (h : t + size < 2 ^ 64) (hs : 0 < size) :
    (⟨UInt64.ofNat t, UInt64.ofNat size⟩ : Span).size ≠ 0 := by
  intro h0
  have := (cand_toNat h).2.1
  rw [h0] at this
  simp at this
  omega

end Krepi.Proofs.Fdt
