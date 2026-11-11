module

public import Krepi.Calibration.Statements

/-!
# Proofs about the calibration target

A theorem for each statement of `Krepi.Calibration`, whose type is the
statement itself. The proofs of the functions that call others use the
statements of the callees, through the private lemmas below each, so that a
mutant of a callee fails the proof of the callee alone.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Calibration Krepi.Calibration

namespace Krepi.Proofs.Calibration

public theorem encode_spec : Encode := by
  intro index generation
  unfold handle.encode
  simp only [handle.INDEX_MASK, handle.GENERATION_MAX, handle.INDEX_BITS, generationMax]
  step*
  refine ⟨by scalar_tac, by scalar_tac, ?_⟩
  have hlow : index.val < 2 ^ 8 := by scalar_tac
  have hhigh : generation.val <<< 8 < U32.size := by rw [Nat.shiftLeft_eq]; scalar_tac
  rw [i1_post, UScalar.val_or, i_post, Nat.mod_eq_of_lt hhigh,
    ← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq]

@[step] private theorem encode_step (index generation : Std.U32) :
    handle.encode index generation ⦃ r =>
      match r with
      | some h =>
        index.val ≤ 255 ∧ generation.val ≤ generationMax ∧
          h.val = generation.val * 256 + index.val
      | none => 255 < index.val ∨ generationMax < generation.val ⦄ :=
  encode_spec index generation

public theorem index_spec : Index := by
  intro h
  unfold handle.index
  simp only [handle.INDEX_MASK, spec_ok, UScalar.val_and]
  have : (255#u32 : Std.U32).val = 2 ^ 8 - 1 := by simp
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

@[step] private theorem index_step (h : Std.U32) :
    handle.index h ⦃ r => r.val = h.val % 256 ⦄ :=
  index_spec h

public theorem generation_spec : Generation := by
  intro h
  unfold handle.generation
  simp only [handle.INDEX_BITS]
  step as ⟨ g, hg ⟩
  rw [hg, Nat.shiftRight_eq_div_pow]

@[step] private theorem generation_step (h : Std.U32) :
    handle.generation h ⦃ r => r.val = h.val / 256 ⦄ :=
  generation_spec h

public theorem next_spec : Next := by
  intro h
  unfold handle.next
  step as ⟨ g, hg ⟩
  step as ⟨ o, ho ⟩
  cases o with
  | none =>
    simp only at ho
    scalar_tac
  | some later =>
    simp only at ho ⊢
    obtain ⟨_, hlater, _⟩ := ho
    step as ⟨ i, hi ⟩
    step as ⟨ r, hr ⟩
    cases r with
    | none =>
      simp only at hr ⊢
      simp only [generationMax] at *
      scalar_tac
    | some h' =>
      simp only at hr ⊢
      obtain ⟨_, _, hh'⟩ := hr
      scalar_tac

public theorem charge_spec : Charge := by
  intro left cost
  unfold arith.charge
  have := U32.checked_sub_bv_spec left cost
  simp only [spec_ok]
  split <;> simp_all

public theorem split_spec : Split := by
  intro total parts
  unfold arith.split
  split
  · simp_all
  · step*

public theorem fits_spec : Fits := by
  intro base length limit
  unfold arith.fits
  step*

public theorem new_spec : New := by
  intro capacity
  unfold table.Table.new
  simp only [table.SLOTS]
  split
  · simp_all
  · split
    · simp only [spec_ok]
      scalar_tac
    · simp only [spec_ok]
      scalar_tac

public theorem alloc_spec : Alloc := by
  intro t hused
  unfold table.Table.alloc
  split
  · step*
  · simp only [spec_ok, uncurry']
    scalar_tac

/-- The slot that the generated code reads at a `Usize` index is the one
that the statements name at its value. -/
private theorem slot_eq (t : table.Table) (i : Usize) (j : Nat) (hj : i.val = j)
    (h : i.val < t.generations.val.length) :
    t.generations.val[i.val] = t.generations.val[j]! := by
  subst hj
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

public theorem retire_spec : Retire := by
  intro t index hcap
  unfold table.Table.retire
  split
  · simp_all [uncurry']
  · step as ⟨ i, hi ⟩
    step as ⟨ g, hg ⟩
    step as ⟨ o, ho ⟩
    cases o with
    | none =>
      simp only at ho ⊢
      simp only [spec_ok, uncurry', Bool.false_eq_true, ite_false, true_and]
      right
      have hgi : g = t.generations.val[index.val]! := by
        rw [hg]; apply slot_eq; scalar_tac
      rw [← hgi]
      scalar_tac
    | some later =>
      try simp only at ho ⊢
      step as ⟨ i2, hi2 ⟩
      step as ⟨ a, ha ⟩
      simp only [ite_true]
      have hgi : g = t.generations.val[index.val]! := by
        rw [hg]; apply slot_eq; scalar_tac
      have hidx : i2.val = index.val := by scalar_tac
      refine ⟨by scalar_tac, ?_, fun j hj => ?_⟩
      · rw [← Array.getElem!_Nat_eq, ha, Array.getElem!_Nat_set_eq _ _ _ _ ⟨hidx, by scalar_tac⟩,
          ← hgi, ho.2.1]
      · rw [← Array.getElem!_Nat_eq, ← Array.getElem!_Nat_eq, ha,
          Array.getElem!_Nat_set_ne _ _ _ _ (by omega)]

public theorem is_current_spec : IsCurrent := by
  intro t h hcap
  unfold table.Table.is_current
  step as ⟨ i, hi ⟩
  split
  · step as ⟨ u, hu ⟩
    step as ⟨ g, hg ⟩
    step as ⟨ gen, hgen ⟩
    have hgu : g = t.generations.val[h.val % 256]! := by
      rw [hg]; apply slot_eq; scalar_tac
    rw [decide_eq_true_iff]
    constructor
    · intro hgg
      subst hgg
      exact ⟨by scalar_tac, by rw [← hgu, hgen]⟩
    · rintro ⟨_, hval⟩
      rw [← hgu] at hval
      exact UScalar.eq_of_val_eq (by rw [hval, hgen])
  · simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro hlt
    exfalso
    scalar_tac

public theorem retired_spec : Retired := by
  intro t hcap
  unfold table.Table.retired table.Table.retired_loop
  apply loop.spec_decr_nat
    (measure := fun (slot, _) => t.capacity.val - slot.val)
    (inv := fun (slot, count) => slot.val ≤ t.capacity.val ∧ count.val ≤ slot.val ∧
      ((∀ j < t.capacity.val, (t.generations.val[j]!).val ≠ 0) → count.val = slot.val))
  · rintro ⟨slot, count⟩ ⟨hle, hcount, hall⟩
    unfold table.Table.retired_loop.body
    step*
    split
    · step as ⟨ count1, hcount1 ⟩
      step as ⟨ slot1, hslot1 ⟩
      refine ⟨by scalar_tac, by scalar_tac, fun hz => by have := hall hz; scalar_tac, by scalar_tac⟩
    · step as ⟨ slot1, hslot1 ⟩
      refine ⟨by scalar_tac, by scalar_tac, fun hz => ?_, by scalar_tac⟩
      exfalso
      have hnz := hz slot.val (by scalar_tac)
      have hgi : i1 = t.generations.val[slot.val]! := by
        rw [i1_post]; apply slot_eq; scalar_tac
      rw [← hgi] at hnz
      simp_all
  · simp

end Krepi.Proofs.Calibration
