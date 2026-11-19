module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Mathlib.Data.List.Nodup

/-!
# Page tables: lemmas about lists

Lemmas about the lists of the specification of the `page-tables` component:

- `sortByKey`, an insertion sort (private steps for one insertion):
  `sortByKey_perm` (it permutes its list), `sortByKey_pairwise` (its result
  is in the order of the key) and `sortByKey_of_pairwise` (it leaves a list
  in the order of the key as it is);
- `eq_of_perm_of_pairwise_le`: two permutations of one list of numbers, both
  in ascending order, are equal;
- `filterMap_nodup_inj`: a `filterMap` of a list without duplicates that
  has no duplicates takes each value at one element only.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

private theorem insert_perm {α : Type} (key : α → Nat) (x : α) :
    ∀ l, (sortByKey.insert key x l).Perm (x :: l)
  | [] => by simp [sortByKey.insert]
  | y :: ys => by
    unfold sortByKey.insert
    split
    · exact List.Perm.refl _
    · exact ((insert_perm key x ys).cons y).trans (List.Perm.swap x y ys)

private theorem insert_pairwise {α : Type} (key : α → Nat) (x : α) :
    ∀ l, l.Pairwise (fun a b => key a ≤ key b) →
      (sortByKey.insert key x l).Pairwise (fun a b => key a ≤ key b)
  | [] => fun _ => by simp [sortByKey.insert]
  | y :: ys => fun h => by
    unfold sortByKey.insert
    rw [List.pairwise_cons] at h
    split
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 h⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact Nat.le_trans hxy (h.1 z hz)
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨?_, insert_pairwise key x ys h.2⟩
      intro z hz
      rcases List.mem_cons.1 ((insert_perm key x ys).mem_iff.1 hz) with rfl | hz
      · omega
      · exact h.1 z hz

theorem sortByKey_perm {α : Type} (key : α → Nat) : ∀ l : List α, (sortByKey key l).Perm l
  | [] => by simp [sortByKey]
  | x :: rest => by
    simp only [sortByKey]
    exact (insert_perm key x _).trans ((sortByKey_perm key rest).cons x)

theorem sortByKey_pairwise {α : Type} (key : α → Nat) :
    ∀ l : List α, (sortByKey key l).Pairwise (fun a b => key a ≤ key b)
  | [] => by simp [sortByKey]
  | x :: rest => by
    simp only [sortByKey]
    exact insert_pairwise key x _ (sortByKey_pairwise key rest)

theorem eq_of_perm_of_pairwise_le :
    ∀ {l₁ l₂ : List Nat}, l₁.Perm l₂ → l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) → l₁ = l₂
  | [], l₂, hp, _, _ => List.Perm.nil_eq hp
  | a :: t₁, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: t₁, b :: t₂, hp, h₁, h₂ => by
    rw [List.pairwise_cons] at h₁ h₂
    have ha : a ∈ b :: t₂ := hp.mem_iff.1 List.mem_cons_self
    have hb : b ∈ a :: t₁ := hp.mem_iff.2 List.mem_cons_self
    have hab : a = b := by
      rcases List.mem_cons.1 ha with h | h
      · exact h
      · rcases List.mem_cons.1 hb with h' | h'
        · exact h'.symm
        · have := h₂.1 a h; have := h₁.1 b h'; omega
    subst hab
    rw [eq_of_perm_of_pairwise_le hp.cons_inv h₁.2 h₂.2]

theorem filterMap_nodup_inj {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup → (l.filterMap f).Nodup →
      ∀ {i j : α} {c : β}, i ∈ l → j ∈ l → f i = some c → f j = some c → i = j
  | [], _, _, _, _, _, hi, _, _, _ => absurd hi (by simp)
  | a :: rest, hl, hf, i, j, c, hi, hj, hfi, hfj => by
    rw [List.nodup_cons] at hl
    have key : ∀ {k}, k ∈ rest → f k = some c → f a = some c → False := by
      intro k hk hfk hfa
      rw [List.filterMap_cons, hfa] at hf
      exact (List.nodup_cons.1 hf).1 (List.mem_filterMap.2 ⟨k, hk, hfk⟩)
    have hrest : (rest.filterMap f).Nodup := by
      rw [List.filterMap_cons] at hf
      split at hf
      · exact hf
      · exact (List.nodup_cons.1 hf).2
    rcases List.mem_cons.1 hi with rfl | hi' <;> rcases List.mem_cons.1 hj with rfl | hj'
    · rfl
    · exact (key hj' hfj hfi).elim
    · exact (key hi' hfi hfj).elim
    · exact filterMap_nodup_inj hl.2 hrest hi' hj' hfi hfj

theorem sortByKey_of_pairwise {α : Type} (key : α → Nat) :
    ∀ l : List α, l.Pairwise (fun a b => key a ≤ key b) → sortByKey key l = l
  | [], _ => rfl
  | x :: rest, h => by
    rw [List.pairwise_cons] at h
    simp only [sortByKey, sortByKey_of_pairwise key rest h.2]
    cases rest with
    | nil => rfl
    | cons y ys => simp [sortByKey.insert, h.1 y (by simp)]

end Krepi.Proofs.PageTables
