module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Mathlib.Data.List.Nodup
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.ListLemmas

/-!
# Page tables: lemmas about the lists of tables of a set

The lists of tables that `Tables.checkWellFormed` reads, against the
propositions of `Tables.WellFormed`:

- `pointsAt?_eq_some` (`Tables.pointsAt?` is `Tables.PointsAt`),
  `mem_level2Tables`, `mem_level3Tables` and `mem_tablesOf` (the level 2
  and level 3 tables together are the tables that a parent points at), from
  the private `mem_childrenOf`;
- `tablesOf_nodup_iff`: with no pointer at the root, the level 2 and level 3
  tables are listed once each exactly when every table has at most one
  pointer from a parent (by the private `childrenOf_nodup_iff`: the table
  descriptors of one table point at different tables);
- `sort_eq_range_iff`: the sorted list of the tables is the list from 1 below
  the record exactly when it holds each of them once.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat} (s : Tables r N) (base : UInt64)

theorem pointsAt?_eq_some {t i c : Nat} (hi : i < ENTRIES) :
    s.pointsAt? base t i = some c ↔ s.PointsAt base t i c := by
  unfold Tables.pointsAt? Tables.PointsAt
  split <;> simp_all

private theorem mem_childrenOf {t c : Nat} : c ∈ s.childrenOf base t ↔ ∃ i, s.PointsAt base t i c := by
  simp only [Tables.childrenOf, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, (pointsAt?_eq_some s base hi).1 h⟩
  · rintro ⟨i, h⟩; exact ⟨i, h.1, (pointsAt?_eq_some s base h.1).2 h⟩

theorem mem_level2Tables {t : Nat} : t ∈ s.level2Tables base ↔ s.IsLevel2 base t :=
  mem_childrenOf s base

theorem mem_level3Tables {t : Nat} : t ∈ s.level3Tables base ↔ s.IsLevel3 base t := by
  simp only [Tables.level3Tables, List.mem_flatMap, mem_level2Tables, mem_childrenOf,
    Tables.IsLevel3]
  constructor
  · rintro ⟨t2, h2, i, h⟩; exact ⟨t2, i, h2, h⟩
  · rintro ⟨t2, i, h2, h⟩; exact ⟨t2, h2, i, h⟩

theorem mem_tablesOf {c : Nat} : c ∈ s.level2Tables base ++ s.level3Tables base ↔
    ∃ t i, s.IsParent base t ∧ s.PointsAt base t i c := by
  rw [List.mem_append, mem_level2Tables, mem_level3Tables]
  constructor
  · rintro (⟨i, h⟩ | ⟨t2, i, h2, h⟩)
    · exact ⟨0, i, Or.inl rfl, h⟩
    · exact ⟨t2, i, Or.inr h2, h⟩
  · rintro ⟨t, i, rfl | h2, h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨t, i, h2, h⟩

private theorem childrenOf_nodup_iff {t : Nat} : (s.childrenOf base t).Nodup ↔
    ∀ i j c, s.PointsAt base t i c → s.PointsAt base t j c → i = j := by
  constructor
  · intro h i j c hi hj
    exact filterMap_nodup_inj List.nodup_range h (List.mem_range.2 hi.1) (List.mem_range.2 hj.1)
      ((pointsAt?_eq_some s base hi.1).2 hi) ((pointsAt?_eq_some s base hj.1).2 hj)
  · intro h
    apply List.Nodup.filterMap _ List.nodup_range
    intro i j c hi hj
    have hi' := Option.mem_def.1 hi
    have hj' := Option.mem_def.1 hj
    unfold Tables.pointsAt? at hi' hj'
    split at hi'
    · split at hj'
      · rename_i hpi hpj
        by_cases hil : i < ENTRIES
        · by_cases hjl : j < ENTRIES
          · exact h i j c ⟨hil, hpi, hi'⟩ ⟨hjl, hpj, hj'⟩
          · rw [entry_eq_get, get_of_ge_entries _ _ (by omega)] at hpj
            exact absurd hpj (by decide)
        · rw [entry_eq_get, get_of_ge_entries _ _ (by omega)] at hpi
          exact absurd hpi (by decide)
      · cases hj'
    · cases hi'

theorem tablesOf_nodup_iff (h0 : 0 ∉ s.level2Tables base ++ s.level3Tables base) :
    (s.level2Tables base ++ s.level3Tables base).Nodup ↔
      ∀ t i t' i' c, s.IsParent base t → s.IsParent base t' →
        s.PointsAt base t i c → s.PointsAt base t' i' c → t = t' ∧ i = i' := by
  have hne : ∀ t, s.IsLevel2 base t → t ≠ 0 := by
    rintro t h rfl
    exact h0 (List.mem_append.2 (Or.inl ((mem_level2Tables s base).2 h)))
  rw [List.nodup_append, Tables.level3Tables, List.nodup_flatMap]
  constructor
  · rintro ⟨hA, ⟨hB1, hB2⟩, hAB⟩ t i t' i' c hp hp' ha hb
    rcases hp with rfl | h2 <;> rcases hp' with rfl | h2'
    · exact ⟨rfl, (childrenOf_nodup_iff s base).1 hA i i' c ha hb⟩
    · exact absurd rfl (hAB c ((mem_childrenOf s base).2 ⟨i, ha⟩) c
        (List.mem_flatMap.2 ⟨t', (mem_level2Tables s base).2 h2', (mem_childrenOf s base).2 ⟨i', hb⟩⟩))
    · exact absurd rfl (hAB c ((mem_childrenOf s base).2 ⟨i', hb⟩) c
        (List.mem_flatMap.2 ⟨t, (mem_level2Tables s base).2 h2, (mem_childrenOf s base).2 ⟨i, ha⟩⟩))
    · by_cases htt : t = t'
      · subst htt
        exact ⟨rfl, (childrenOf_nodup_iff s base).1 (hB1 t ((mem_level2Tables s base).2 h2))
          i i' c ha hb⟩
      · exfalso
        have hm := (mem_level2Tables s base).2 h2
        have hm' := (mem_level2Tables s base).2 h2'
        obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hm
        obtain ⟨n', hn', rfl⟩ := List.getElem_of_mem hm'
        have hnn : n ≠ n' := fun h => htt (by subst h; rfl)
        have hc := (mem_childrenOf s base).2 ⟨i, ha⟩
        have hc' := (mem_childrenOf s base).2 ⟨i', hb⟩
        rcases Nat.lt_or_gt_of_ne hnn with hlt | hlt
        · exact List.pairwise_iff_getElem.1 hB2 n n' hn hn' hlt hc hc'
        · exact List.pairwise_iff_getElem.1 hB2 n' n hn' hn hlt hc' hc
  · intro hu
    have hA : (s.childrenOf base 0).Nodup :=
      (childrenOf_nodup_iff s base).2 fun i j c hi hj => (hu 0 i 0 j c (Or.inl rfl) (Or.inl rfl) hi hj).2
    refine ⟨hA, ⟨?_, ?_⟩, ?_⟩
    · intro t ht
      exact (childrenOf_nodup_iff s base).2 fun i j c hi hj =>
        (hu t i t j c (Or.inr ((mem_level2Tables s base).1 ht))
          (Or.inr ((mem_level2Tables s base).1 ht)) hi hj).2
    · apply List.Nodup.pairwise_of_forall_ne hA
      intro a ha b hb hab c hca hcb
      obtain ⟨i, hi⟩ := (mem_childrenOf s base).1 hca
      obtain ⟨j, hj⟩ := (mem_childrenOf s base).1 hcb
      exact hab (hu a i b j c (Or.inr ((mem_level2Tables s base).1 ha))
        (Or.inr ((mem_level2Tables s base).1 hb)) hi hj).1
    · intro a ha b hb hab
      subst hab
      obtain ⟨i, hi⟩ := (mem_childrenOf s base).1 ha
      obtain ⟨t, ht, hb'⟩ := List.mem_flatMap.1 hb
      obtain ⟨j, hj⟩ := (mem_childrenOf s base).1 hb'
      have h2 := (mem_level2Tables s base).1 ht
      exact hne t h2 (hu 0 i t j a (Or.inl rfl) (Or.inr h2) hi hj).1.symm

theorem sort_eq_range_iff (L : List Nat) (u : Nat) :
    sortByKey id L = List.range' 1 (u - 1) ↔ L.Nodup ∧ ∀ c, c ∈ L ↔ 1 ≤ c ∧ c < u := by
  have hmem : ∀ c, c ∈ List.range' 1 (u - 1) ↔ 1 ≤ c ∧ c < u := by
    intro c; simp only [List.mem_range'_1]; omega
  constructor
  · intro h
    have hp : L.Perm (List.range' 1 (u - 1)) := (sortByKey_perm id L).symm.trans (h ▸ List.Perm.refl _)
    exact ⟨hp.nodup_iff.2 List.nodup_range', fun c => (hp.mem_iff).trans (hmem c)⟩
  · rintro ⟨hn, hm⟩
    have hp : L.Perm (List.range' 1 (u - 1)) :=
      (List.perm_ext_iff_of_nodup hn List.nodup_range').2 fun c => (hm c).trans (hmem c).symm
    exact eq_of_perm_of_pairwise_le ((sortByKey_perm id L).trans hp) (sortByKey_pairwise id L)
      (List.pairwise_le_range' 1)

end Krepi.Proofs.PageTables
