module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas

/-!
# Page tables: lemmas about the walk

What the walk of a virtual address gives, and what it finds on a well-formed
set:

- the indices: `index1_lt`, `index2_lt`, `index3_lt`;
- the steps of the walk: `walk2_ok`, `walk_ok_level3`, `walk_ok_block`,
  `pageLeaf_ok`;
- on a well-formed set: an invalid root entry is 0 (`wf_walk2_none`), a valid
  one points at a level 2 table (`wf_walk2_some`); an invalid entry of a
  level 2 table is 0 (`wf_level2_invalid`) and a valid one other than a block
  points at a level 3 table (`wf_level2_table`); an invalid entry of a level
  3 table is 0 (`wf_level3_invalid`) and no entry of it is a table descriptor
  (`wf_level3_not_plain`); the page leaf of an address is an entry of a
  level 3 table (`wf_pageLeaf`).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

theorem index1_lt (v : UInt64) : index1 v < ENTRIES := Nat.mod_lt _ (by decide)
theorem index2_lt (v : UInt64) : index2 v < ENTRIES := Nat.mod_lt _ (by decide)
theorem index3_lt (v : UInt64) : index3 v < ENTRIES := Nat.mod_lt _ (by decide)

theorem walk2_ok {s : Tables r N} {base v : UInt64} {w : Option (Nat × UInt64)} :
    s.walk2 base v = .ok w ↔
      (isValid (s.entry 0 (index1 v)) = false ∧ w = none) ∨
      (∃ t2, isValid (s.entry 0 (index1 v)) = true ∧
        s.child? base (s.entry 0 (index1 v)) = some t2 ∧ w = some (t2, s.entry t2 (index2 v))) := by
  unfold Tables.walk2
  cases hv : isValid (s.entry 0 (index1 v)) <;> cases hc : s.child? base (s.entry 0 (index1 v)) <;>
    simp [hv, hc, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, eq_comm]

theorem walk_ok_level3 {s : Tables r N} {base v : UInt64} {t2 t3 : Nat} {d : UInt64} :
    s.walk base v = .ok (.level3 t2 t3 d) ↔
      ∃ e2, s.walk2 base v = .ok (some (t2, e2)) ∧ isValid e2 = true ∧
        (typeBits e2 == BLOCK) = false ∧ s.child? base e2 = some t3 ∧
        d = s.entry t3 (index3 v) := by
  constructor
  · intro h
    unfold Tables.walk at h
    cases hw : s.walk2 base v with
    | error e => rw [hw] at h; cases h
    | ok w =>
      rw [hw] at h
      rcases w with _ | ⟨t2', e2⟩
      · cases h
      · cases hv : isValid e2 <;> cases hb : (typeBits e2 == BLOCK) <;>
          cases hc : s.child? base e2 <;>
          simp only [hv, hb, hc, bind, Except.bind, pure, Except.pure, throw, throwThe,
            MonadExceptOf.throw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false,
            ite_true, reduceCtorEq, Except.ok.injEq, Reach.level3.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨e2, rfl, hv, hb, hc, rfl⟩
  · rintro ⟨e2, hw, hv, hb, hc, rfl⟩
    unfold Tables.walk
    rw [hw]
    simp only [hv, hb, hc, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true,
      ite_false]

theorem walk_ok_block {s : Tables r N} {base v : UInt64} {t2 : Nat} {d : UInt64} :
    s.walk base v = .ok (.block t2 d) ↔
      s.walk2 base v = .ok (some (t2, d)) ∧ isValid d = true ∧ (typeBits d == BLOCK) = true := by
  constructor
  · intro h
    unfold Tables.walk at h
    cases hw : s.walk2 base v with
    | error e => rw [hw] at h; cases h
    | ok w =>
      rw [hw] at h
      rcases w with _ | ⟨t2', e2⟩
      · cases h
      · cases hv : isValid e2 <;> cases hb : (typeBits e2 == BLOCK) <;>
          cases hc : s.child? base e2 <;>
          simp only [hv, hb, hc, bind, Except.bind, pure, Except.pure, throw, throwThe,
            MonadExceptOf.throw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false,
            ite_true, reduceCtorEq, Except.ok.injEq, Reach.block.injEq] at h
        all_goals obtain ⟨rfl, rfl⟩ := h
        all_goals exact ⟨rfl, hv, hb⟩
  · rintro ⟨hw, hv, hb⟩
    unfold Tables.walk
    rw [hw]
    simp only [hv, hb, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true]

theorem pageLeaf_ok {s : Tables r N} {base v : UInt64} {t3 : Nat} {d : UInt64} :
    s.pageLeaf base v = .ok (t3, d) ↔
      ∃ t2, s.walk base v = .ok (.level3 t2 t3 d) ∧ typeBits d = TABLE_OR_PAGE := by
  constructor
  · intro h
    unfold Tables.pageLeaf at h
    cases hw : s.walk base v with
    | error e => rw [hw] at h; cases h
    | ok w =>
      rw [hw] at h
      cases w with
      | level3 t2' t3' d' =>
        by_cases hd : typeBits d' = TABLE_OR_PAGE
        · simp only [bind, Except.bind, hd, beq_self_eq_true, ite_true, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨t2', rfl, hd⟩
        · simp only [bind, Except.bind, beq_iff_eq, hd, ite_false, throw, throwThe,
            MonadExceptOf.throw, reduceCtorEq] at h
      | _ => simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  · rintro ⟨t2, hw, hd⟩
    unfold Tables.pageLeaf
    rw [hw]
    simp only [bind, Except.bind, hd, beq_self_eq_true, ite_true, pure, Except.pure]

section WellFormed

variable {s : Tables r N} {base : UInt64} {bits : UInt8}

theorem wf_walk2_none (hs : s.WellFormed base bits) {v : UInt64}
    (h : s.walk2 base v = .ok none) : s.entry 0 (index1 v) = 0 := by
  rcases walk2_ok.1 h with ⟨hv, -⟩ | ⟨_, -, -, h⟩
  · rcases hs.2.2.2.2.1 (index1 v) (index1_lt v) with h0 | ⟨c, hc⟩
    · exact h0
    · rw [isValid_of_isPlain hc.2.1] at hv; exact absurd hv (by decide)
  · exact absurd h (by simp)

theorem wf_walk2_some (hs : s.WellFormed base bits) {v : UInt64} {t2 : Nat} {e2 : UInt64}
    (h : s.walk2 base v = .ok (some (t2, e2))) :
    s.PointsAt base 0 (index1 v) t2 ∧ s.IsLevel2 base t2 ∧ e2 = s.entry t2 (index2 v) := by
  rcases walk2_ok.1 h with ⟨-, h⟩ | ⟨t2', hv, hc, h⟩
  · exact absurd h (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rcases hs.2.2.2.2.1 (index1 v) (index1_lt v) with h0 | ⟨c, hc'⟩
    · rw [h0] at hv; exact absurd hv (by decide)
    · have : c = t2 := Option.some.inj (hc'.2.2.symm.trans hc)
      subst this
      exact ⟨hc', ⟨_, hc'⟩, rfl⟩

theorem wf_level2_invalid (hs : s.WellFormed base bits) {t i : Nat} (ht : s.IsLevel2 base t)
    (hi : i < ENTRIES) (hv : isValid (s.entry t i) = false) : s.entry t i = 0 := by
  rcases hs.2.2.2.2.2.1 t ht i hi with h | ⟨c, hc⟩ | ⟨hb, -⟩
  · exact h
  · rw [isValid_of_isPlain hc.2.1] at hv; exact absurd hv (by decide)
  · have := typeBits_of_isReadWriteBlock hb
    simp only [isValid, this, BLOCK] at hv; exact absurd hv (by decide)

theorem wf_level2_table (hs : s.WellFormed base bits) {t i t3 : Nat} (ht : s.IsLevel2 base t)
    (hi : i < ENTRIES) (hv : isValid (s.entry t i) = true)
    (hb : (typeBits (s.entry t i) == BLOCK) = false) (hc : s.child? base (s.entry t i) = some t3) :
    s.PointsAt base t i t3 ∧ s.IsLevel3 base t3 := by
  rcases hs.2.2.2.2.2.1 t ht i hi with h | ⟨c, hc'⟩ | ⟨hb', -⟩
  · rw [h] at hv; exact absurd hv (by decide)
  · have : c = t3 := Option.some.inj (hc'.2.2.symm.trans hc)
    subst this
    exact ⟨hc', t, i, ht, hc'⟩
  · rw [typeBits_of_isReadWriteBlock hb'] at hb; exact absurd hb (by decide)

theorem wf_level3_invalid (hs : s.WellFormed base bits) {t i : Nat} (ht : s.IsLevel3 base t)
    (hi : i < ENTRIES) (hv : isValid (s.entry t i) = false) : s.entry t i = 0 := by
  rcases hs.2.2.2.2.2.2.1 t ht i hi with h | ⟨⟨k, hk⟩, -⟩
  · exact h
  · rw [hk, isValid_descriptor] at hv; exact absurd hv (by decide)

theorem wf_level3_not_plain (hs : s.WellFormed base bits) {t i : Nat} (ht : s.IsLevel3 base t)
    (hi : i < ENTRIES) : isPlainTableDescriptor (s.entry t i) = false := by
  rcases hs.2.2.2.2.2.2.1 t ht i hi with h | ⟨⟨k, hk⟩, -⟩
  · rw [h]; decide
  · rw [hk, isPlain_descriptor]

theorem wf_walk_level3 (hs : s.WellFormed base bits) {v : UInt64} {t2 t3 : Nat} {d : UInt64}
    (h : s.walk base v = .ok (.level3 t2 t3 d)) :
    s.IsLevel2 base t2 ∧ s.PointsAt base t2 (index2 v) t3 ∧ s.IsLevel3 base t3 ∧
      d = s.entry t3 (index3 v) := by
  obtain ⟨e2, hw, hv, hb, hc, hd⟩ := walk_ok_level3.1 h
  obtain ⟨-, h2, rfl⟩ := wf_walk2_some hs hw
  obtain ⟨hp, h3⟩ := wf_level2_table hs h2 (index2_lt v) hv hb hc
  exact ⟨h2, hp, h3, hd⟩

end WellFormed

end Krepi.Proofs.PageTables
