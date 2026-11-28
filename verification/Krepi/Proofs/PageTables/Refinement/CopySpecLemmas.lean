module

public import Krepi.Proofs.PageTables.Refinement.WalkSpecLemmas
public import Krepi.Proofs.PageTables.CloneLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.EntryLemmas

/-!
# Page tables: lemmas of the specification for the copy of the kernel tables

Lemmas about `Tables.cloneKernelFrom` and its walk, in the forms that the
triples of the generated functions of the copy need, for the proofs below
`Krepi.Proofs.PageTables.Refinement`. The module imports no generated
definitions, so it is built once and not again for every mutant of the code.

- The marks of the walk: `VisitRepr` (the code marks a table with a nonzero
  byte when the walk has reached it and with 3 when it is a level 3 table),
  with `visitRepr_root`, `visitRepr_set2`, `visitRepr_set3` (the marks of the
  root and of a newly reached table), `visitRepr_reached`,
  `visitRepr_leaves` and `visitRepr_all` (the check that every table in use
  was reached).
- One step of the walk: `reach_invalid`, `reach_none`, `reach_again`,
  `reach_new` (`Tables.reach`); `checkLeaves_cons`; `walkLevel2_invalid`,
  `walkLevel2_reach_error`, `walkLevel2_leaves_error`, `walkLevel2_next`;
  `walkRoot_invalid`, `walkRoot_reach_error`, `walkRoot_level2_error`,
  `walkRoot_next`; the entries of a table as a list from an index,
  `clone_table_drop`, `clone_table_drop_end`, and `clone_table_poolView`.
- What a walk that succeeds tells: `walkRoot_child` (a valid entry of a
  reached table that is not a level 3 table points at a table in use), with
  `clone_child?_le` (such a table lies at or above the pool).
- The stores of the plan from a position: `restStores` with
  `restStores_ge`, `restStores_end`, `restStores_invalid`,
  `restStores_valid`, `restStores_zero`, and `clone_zeros_succ` for the `Zero`
  steps.
- `NextValid`, the next valid entry from a position with the stores from it,
  and `clone_checkPool_bound`, what a pool that passes its first checks gives.
- The checks of the entry: `cloneKernelFrom_pool1`, `cloneKernelFrom_pool2`,
  `cloneKernelFrom_overlap`, `cloneKernelFrom_used`, `cloneKernelFrom_walk`,
  `cloneKernelFrom_unreached` and `cloneKernelFrom_ok`, its outcomes.
-/

@[expose] public section

open Aeneas Aeneas.Std
open Krepi.Statements Krepi.Spec.PageTables

namespace Krepi.Proofs.PageTables.Refinement

variable {r : Region} {N : Nat}

/-! ## The marks of the walk -/

/-- The marks of the walk of the code stand for a visit of the specification:
a table is reached exactly when its mark is not 0, and a level 3 table
exactly when its mark is 3. -/
def VisitRepr (levels : List U8) (st : Visit) : Prop :=
  (∀ t, t ∈ st.reached ↔ ∃ h : t < levels.length, (levels[t]'h).val ≠ 0) ∧
  (∀ t, t ∈ st.leaves ↔ ∃ h : t < levels.length, (levels[t]'h).val = 3)

/-- The marks at the start of the walk: the root marked 1, every other table
0. -/
theorem visitRepr_root {n : Nat} (hn : 0 < n) :
    VisitRepr ((List.replicate n (0#u8)).set 0 (1#u8)) ⟨[0], []⟩ := by
  constructor
  · intro t
    simp only [List.mem_singleton, List.length_set, List.length_replicate]
    constructor
    · rintro rfl
      exact ⟨hn, by simp⟩
    · rintro ⟨h, h'⟩
      by_contra hne
      rw [List.getElem_set_ne (Ne.symm hne), List.getElem_replicate] at h'
      exact h' rfl
  · intro t
    simp only [List.not_mem_nil, List.length_set, List.length_replicate, false_iff, not_exists]
    intro h h'
    by_cases ht : t = 0
    · subst ht; simp at h'
    · rw [List.getElem_set_ne (Ne.symm ht), List.getElem_replicate] at h'
      exact absurd h' (by decide)

/-- A table newly reached at level 2: marked 2. -/
theorem visitRepr_set2 {levels : List U8} {st : Visit} (hV : VisitRepr levels st) {t : Nat}
    (ht : t < levels.length) (h0 : (levels[t]'ht).val = 0) :
    VisitRepr (levels.set t (2#u8)) { st with reached := st.reached ++ [t] } := by
  obtain ⟨h1, h2⟩ := hV
  constructor
  · intro t'
    simp only [List.mem_append, List.mem_singleton, List.length_set]
    by_cases htt : t' = t
    · subst htt; simp [ht]
    · rw [h1 t']
      simp only [htt, or_false]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)]⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)] at h'⟩
  · intro t'
    simp only [List.length_set]
    by_cases htt : t' = t
    · subst htt
      rw [h2 t']
      simp only [List.getElem_set_self]
      constructor
      · rintro ⟨h, h'⟩; rw [h0] at h'; exact absurd h' (by decide)
      · rintro ⟨h, h'⟩; exact absurd h' (by decide)
    · rw [h2 t']
      constructor
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)]⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)] at h'⟩

/-- A table newly reached at level 3: marked 3. -/
theorem visitRepr_set3 {levels : List U8} {st : Visit} (hV : VisitRepr levels st) {t : Nat}
    (ht : t < levels.length) :
    VisitRepr (levels.set t (3#u8))
      { st with reached := st.reached ++ [t], leaves := st.leaves ++ [t] } := by
  obtain ⟨h1, h2⟩ := hV
  constructor
  · intro t'
    simp only [List.mem_append, List.mem_singleton, List.length_set]
    by_cases htt : t' = t
    · subst htt; simp [ht]
    · rw [h1 t']
      simp only [htt, or_false]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)]⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)] at h'⟩
  · intro t'
    simp only [List.mem_append, List.mem_singleton, List.length_set]
    by_cases htt : t' = t
    · subst htt; simp [ht]
    · rw [h2 t']
      simp only [htt, or_false]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)]⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by rwa [List.getElem_set_ne (Ne.symm htt)] at h'⟩

theorem visitRepr_reached {levels : List U8} {st : Visit} (hV : VisitRepr levels st) {t : Nat}
    (ht : t < levels.length) : st.reached.contains t = true ↔ (levels[t]'ht).val ≠ 0 := by
  rw [List.contains_iff_mem, hV.1 t]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨ht, h⟩⟩

theorem visitRepr_leaves {levels : List U8} {st : Visit} (hV : VisitRepr levels st) {t : Nat}
    (ht : t < levels.length) : st.leaves.contains t = true ↔ (levels[t]'ht).val = 3 := by
  rw [List.contains_iff_mem, hV.2 t]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨ht, h⟩⟩

/-- The check that every table in use was reached, on the marks. -/
theorem visitRepr_all {levels : List U8} {st : Visit} (hV : VisitRepr levels st) {u : Nat}
    (hu : u ≤ levels.length) :
    (List.range u).any (fun t => !st.reached.contains t) = false ↔
      ∀ t, t < u → ∃ h : t < levels.length, (levels[t]'h).val ≠ 0 := by
  rw [List.any_eq_false]
  constructor
  · intro h t ht
    have := h t (List.mem_range.2 ht)
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at this
    exact ⟨by omega, (visitRepr_reached hV (by omega)).1 (by simpa using this)⟩
  · intro h t ht
    obtain ⟨h1, h2⟩ := h t (List.mem_range.1 ht)
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false]
    simpa using (visitRepr_reached hV h1).2 h2

/-! ## One step of the walk -/

theorem reach_invalid (src : Tables r N) (sb : UInt64) {d : UInt64} (st : Visit)
    (h : isPlainTableDescriptor d = false) : src.reach sb d st = .error .invalidDescriptor := by
  simp only [Tables.reach, h, Bool.not_false, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
  rfl

theorem reach_none (src : Tables r N) (sb : UInt64) {d : UInt64} (st : Visit)
    (hp : isPlainTableDescriptor d = true) (hc : src.child? sb d = none) :
    src.reach sb d st = .error .tableBacking := by
  simp only [Tables.reach, hp, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, throw,
    throwThe, MonadExceptOf.throw]

theorem reach_again (src : Tables r N) (sb : UInt64) {d : UInt64} (st : Visit) {t : Nat}
    (hp : isPlainTableDescriptor d = true) (hc : src.child? sb d = some t)
    (hr : st.reached.contains t = true) : src.reach sb d st = .error .tableBacking := by
  simp only [Tables.reach, hp, hc, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, throw,
    throwThe, MonadExceptOf.throw]
  rfl

theorem reach_new (src : Tables r N) (sb : UInt64) {d : UInt64} (st : Visit) {t : Nat}
    (hp : isPlainTableDescriptor d = true) (hc : src.child? sb d = some t)
    (hr : st.reached.contains t = false) :
    src.reach sb d st = .ok (t, { st with reached := st.reached ++ [t] }) := by
  simp only [Tables.reach, hp, hc, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem checkLeaves_cons (bits : UInt8) (d : UInt64) (rest : List UInt64) :
    checkLeaves bits (d :: rest) =
      if (isValid d && !copyableLeaf bits d) = true then .error .invalidDescriptor
      else checkLeaves bits rest := rfl

theorem walkLevel2_invalid (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) (st : Visit) (hv : isValid d = false) :
    src.walkLevel2 sb bits (d :: rest) st = src.walkLevel2 sb bits rest st := by
  simp only [Tables.walkLevel2, hv, Bool.not_false, ↓reduceIte]

theorem walkLevel2_reach_error (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) {st : Visit} {e : TableError} (hv : isValid d = true)
    (h : src.reach sb d st = .error e) :
    src.walkLevel2 sb bits (d :: rest) st = .error e := by
  simp only [Tables.walkLevel2, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
  rfl

theorem walkLevel2_leaves_error (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) {st st' : Visit} {t : Nat} {e : TableError} (hv : isValid d = true)
    (h : src.reach sb d st = .ok (t, st')) (hc : checkLeaves bits (src.table t).toList = .error e) :
    src.walkLevel2 sb bits (d :: rest) st = .error e := by
  simp only [Tables.walkLevel2, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
  show (checkLeaves bits (src.table t).toList >>= _) = _
  rw [hc]; rfl

theorem walkLevel2_next (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) {st st' : Visit} {t : Nat} (hv : isValid d = true)
    (h : src.reach sb d st = .ok (t, st')) (hc : checkLeaves bits (src.table t).toList = .ok ()) :
    src.walkLevel2 sb bits (d :: rest) st =
      src.walkLevel2 sb bits rest { st' with leaves := st'.leaves ++ [t] } := by
  simp only [Tables.walkLevel2, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
  show (checkLeaves bits (src.table t).toList >>= _) = _
  rw [hc]; rfl

theorem walkRoot_invalid (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) (st : Visit) (hv : isValid d = false) :
    src.walkRoot sb bits (d :: rest) st = src.walkRoot sb bits rest st := by
  simp only [Tables.walkRoot, hv, Bool.not_false, ↓reduceIte]

theorem walkRoot_reach_error (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) {st : Visit} {e : TableError} (hv : isValid d = true)
    (h : src.reach sb d st = .error e) :
    src.walkRoot sb bits (d :: rest) st = .error e := by
  simp only [Tables.walkRoot, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
  rfl

theorem walkRoot_level2_error (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) {st st' : Visit} {t : Nat} {e : TableError} (hv : isValid d = true)
    (h : src.reach sb d st = .ok (t, st'))
    (hw : src.walkLevel2 sb bits (src.table t).toList st' = .error e) :
    src.walkRoot sb bits (d :: rest) st = .error e := by
  simp only [Tables.walkRoot, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
  show (src.walkLevel2 sb bits (src.table t).toList st' >>= _) = _
  rw [hw]; rfl

theorem walkRoot_next (src : Tables r N) (sb : UInt64) (bits : UInt8) {d : UInt64}
    (rest : List UInt64) {st st' st'' : Visit} {t : Nat} (hv : isValid d = true)
    (h : src.reach sb d st = .ok (t, st'))
    (hw : src.walkLevel2 sb bits (src.table t).toList st' = .ok st'') :
    src.walkRoot sb bits (d :: rest) st = src.walkRoot sb bits rest st'' := by
  simp only [Tables.walkRoot, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
  show (src.walkLevel2 sb bits (src.table t).toList st' >>= _) = _
  rw [hw]; rfl

/-- The entries of a table from index `i`: entry `i`, then those after it. -/
theorem clone_table_drop (s : Tables r N) (t : Nat) {i : Nat} (hi : i < ENTRIES) :
    (s.table t).toList.drop i = s.entry t i :: (s.table t).toList.drop (i + 1) := by
  rw [table_toList_eq, List.drop_eq_getElem_cons (by simpa using hi)]
  simp

theorem clone_table_drop_end (s : Tables r N) (t : Nat) {i : Nat} (hi : ENTRIES ≤ i) :
    (s.table t).toList.drop i = [] :=
  List.drop_eq_nil_of_le (by simpa using hi)

/-- A table of the pool of a set of the code, as a list: the words of the
descriptors of the code's table. -/
theorem clone_table_poolView {M : Usize}
    (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) M) (u : Nat) {t : Nat}
    (ht : t < pool.val.length) :
    ((⟨poolView pool, u⟩ : Tables r M.val).table t).toList = (pool.val[t]'ht).val.map word64 := by
  rw [table_poolView pool u ht]
  have hl : (pool.val[t]'ht).val.length = ENTRIES := (pool.val[t]'ht).property
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map]
    have h3 : i < (pool.val[t]'ht).val.length := by simpa using h2
    rw [List.getElem?_eq_getElem h3, Option.getD_some]

/-! ## What a walk that succeeds tells -/

/-- After a walk of the source that succeeds, a valid entry of a reached table
that is not a level 3 table points at a table in use. -/
theorem walkRoot_child {src : Tables r N} {sb : UInt64} {bits : UInt8} {st : Visit}
    (hw : src.walkRoot sb bits (src.table 0).toList ⟨[0], []⟩ = .ok st) {t : Nat}
    (ht : t ∈ st.reached) (hl : t ∉ st.leaves) {i : Nat} (hi : i < ENTRIES)
    (hv : isValid (src.entry t i) = true) : ∃ c, src.child? sb (src.entry t i) = some c := by
  obtain ⟨w1, w2, w3, -⟩ := walkRoot_ok src sb bits hw
  have hmem : ∀ t i, i < ENTRIES → src.entry t i ∈ (src.table t).toList := fun t i hi => by
    rw [table_toList_eq]; exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  rw [w2] at ht
  rw [w3] at hl
  simp only [List.singleton_append, List.nil_append, List.mem_cons, List.mem_flatMap] at ht hl
  rcases ht with rfl | ⟨c, hc, htc⟩
  · obtain ⟨-, c, hc, -⟩ := w1 _ (hmem 0 i hi) hv
    exact ⟨c, hc⟩
  · rcases htc with rfl | htc'
    · obtain ⟨d0, hd0, hk⟩ := List.mem_filterMap.1 hc
      have hv0 : isValid d0 = true := by
        by_contra h; simp [kidOf, h] at hk
      have hc0 : src.child? sb d0 = some t := by simpa [kidOf, hv0] using hk
      obtain ⟨-, c', hc', h2⟩ := w1 d0 hd0 hv0
      rw [hc0, Option.some.injEq] at hc'
      subst hc'
      obtain ⟨-, c'', hc'', -⟩ := h2 _ (hmem t i hi) hv
      exact ⟨c'', hc''⟩
    · exact absurd ⟨c, hc, htc'⟩ hl

/-- The table that a pointer reaches lies at or above the pool. -/
theorem clone_child?_le {s : Tables r N} {base d : UInt64} {c : Nat} (h : s.child? base d = some c) :
    base.toNat ≤ (outputAddress d).toNat := by
  simp only [Tables.child?] at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1
  · simp at h

/-! ## The stores of the plan from a position -/

/-- The stores of the plan of a copy from entry `i` of table `t` of the
source on: those of table `t` from entry `i`, then those of every later
table in use. -/
def restStores (src : Tables r N) (sb base : UInt64) (leaf : Nat → Bool) (t i : Nat) : Plan :=
  if t < src.used then
    copyStores sb base (leaf t) t ((src.table t).toList.drop i) i ++
      (List.range' (t + 1) (src.used - (t + 1))).flatMap
        (fun t' => copyStores sb base (leaf t') t' (src.table t').toList 0)
  else []

theorem restStores_ge (src : Tables r N) (sb base : UInt64) (leaf : Nat → Bool) {t : Nat}
    (i : Nat) (ht : src.used ≤ t) : restStores src sb base leaf t i = [] := by
  simp only [restStores, show ¬ t < src.used by omega, ↓reduceIte]

/-- The stores from the start of the source: those of every table in use. -/
theorem restStores_zero (src : Tables r N) (sb base : UInt64) (leaf : Nat → Bool) :
    restStores src sb base leaf 0 0 =
      (List.range src.used).flatMap fun t => copyStores sb base (leaf t) t (src.table t).toList 0 := by
  unfold restStores
  by_cases hu : 0 < src.used
  · rw [ite_of_pos hu, List.drop_zero, List.range_eq_range',
        show src.used = (src.used - 1) + 1 by omega,
      List.range'_succ, List.flatMap_cons]
    simp
  · rw [ite_of_neg hu, show src.used = 0 by omega]; rfl

theorem restStores_end (src : Tables r N) (sb base : UInt64) (leaf : Nat → Bool) {t i : Nat}
    (ht : t < src.used) (hi : ENTRIES ≤ i) :
    restStores src sb base leaf t i = restStores src sb base leaf (t + 1) 0 := by
  unfold restStores
  rw [ite_of_pos ht, clone_table_drop_end src t hi]
  simp only [copyStores, List.nil_append]
  by_cases ht1 : t + 1 < src.used
  · rw [ite_of_pos ht1, List.drop_zero,
        show src.used - (t + 1) = (src.used - (t + 1 + 1)) + 1 by omega,
      List.range'_succ, List.flatMap_cons]
  · rw [ite_of_neg ht1, show src.used - (t + 1) = 0 by omega]; rfl

theorem restStores_invalid (src : Tables r N) (sb base : UInt64) (leaf : Nat → Bool) {t i : Nat}
    (ht : t < src.used) (hi : i < ENTRIES) (hv : isValid (src.entry t i) = false) :
    restStores src sb base leaf t i = restStores src sb base leaf t (i + 1) := by
  unfold restStores
  rw [ite_of_pos ht, ite_of_pos ht, clone_table_drop src t hi]
  simp only [copyStores, hv, Bool.not_false, ↓reduceIte]

theorem restStores_valid (src : Tables r N) (sb base : UInt64) (leaf : Nat → Bool) {t i : Nat}
    (ht : t < src.used) (hi : i < ENTRIES) (hv : isValid (src.entry t i) = true) :
    restStores src sb base leaf t i =
      .store t i (copyValue sb base (leaf t) (src.entry t i)) ::
        restStores src sb base leaf t (i + 1) := by
  unfold restStores
  rw [ite_of_pos ht, ite_of_pos ht, clone_table_drop src t hi]
  simp only [copyStores, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.cons_append]
  rfl

/-- The `Zero` steps from table `z` on, the first one taken. -/
theorem clone_zeros_succ {z n : Nat} (h : z < n) :
    (List.range' z (n - z)).map Step.zero =
      Step.zero z :: (List.range' (z + 1) (n - (z + 1))).map Step.zero := by
  rw [show n - z = (n - (z + 1)) + 1 by omega, List.range'_succ, List.map_cons]

/-- The next valid entry of the source at or after entry `i` of table `t`,
in table-major order, is entry `i'` of table `t'`, and the stores of the
plan from `(t, i)` start with its store; or the source has none, `t'` is at
or past the record, and no store is left. -/
def NextValid (src : Tables r N) (t i t' i' : Nat) : Prop :=
  (t' < src.used ∧ i' < ENTRIES ∧ isValid (src.entry t' i') = true ∧
    ∀ sb base leaf, restStores src sb base leaf t i =
      .store t' i' (copyValue sb base (leaf t') (src.entry t' i')) ::
        restStores src sb base leaf t' (i' + 1)) ∨
  (src.used ≤ t' ∧ ∀ sb base leaf, restStores src sb base leaf t i = [])

/-- What a pool whose first checks pass gives: at least one table, an end at
or below $2^{48}$, and a width below 64. -/
theorem clone_checkPool_bound {base : UInt64} {bits : UInt8} (h : checkPool N base bits = .ok ()) :
    0 < N ∧ base.toNat + PAGE_SIZE * N ≤ 2 ^ 48 ∧ bits.toNat < 64 := by
  obtain ⟨-, hw, hf⟩ := checkPool_ok.1 h
  obtain ⟨hN, hle⟩ := (poolFits_iff N base bits).1 hf
  rw [widthOk_eq] at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  have h48 : 2 ^ bits.toNat ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hw.2
  exact ⟨Nat.pos_of_ne_zero hN, by omega, by omega⟩

/-! ## The outcomes of the entry -/

section Clone

variable {target source : Tables r N} {sb base : UInt64} {bits : UInt8}

theorem cloneKernelFrom_pool1 {e : TableError} (h : checkPool N sb bits = .error e) :
    target.cloneKernelFrom source sb base bits = .error e := by
  simp only [Tables.cloneKernelFrom, h]; rfl

theorem cloneKernelFrom_pool2 {e : TableError} (h1 : checkPool N sb bits = .ok ())
    (h : checkPool N base bits = .error e) :
    target.cloneKernelFrom source sb base bits = .error e := by
  simp only [Tables.cloneKernelFrom, h1, h]; rfl

theorem cloneKernelFrom_overlap (h1 : checkPool N sb bits = .ok ())
    (h2 : checkPool N base bits = .ok ()) (h3 : sb.toNat < base.toNat + PAGE_SIZE * N)
    (h4 : base.toNat < sb.toNat + PAGE_SIZE * N) :
    target.cloneKernelFrom source sb base bits = .error .tableBacking := by
  simp only [Tables.cloneKernelFrom, h1, h2, h3, h4, decide_true, Bool.and_self, ↓reduceIte]
  rfl

theorem cloneKernelFrom_used (h1 : checkPool N sb bits = .ok ())
    (h2 : checkPool N base bits = .ok ())
    (h3 : ¬ (sb.toNat < base.toNat + PAGE_SIZE * N ∧ base.toNat < sb.toNat + PAGE_SIZE * N))
    (h4 : source.used = 0 ∨ N < source.used) :
    target.cloneKernelFrom source sb base bits = .error .tableBacking := by
  have h3' : (decide (sb.toNat < base.toNat + PAGE_SIZE * N) &&
      decide (base.toNat < sb.toNat + PAGE_SIZE * N)) = false := by
    simpa using h3
  have h4' : (source.used == 0 || decide (N < source.used)) = true := by simpa using h4
  simp only [Tables.cloneKernelFrom, h1, h2, h3', h4', Bool.false_eq_true, ↓reduceIte]
  rfl

theorem cloneKernelFrom_walk {e : TableError} (h1 : checkPool N sb bits = .ok ())
    (h2 : checkPool N base bits = .ok ())
    (h3 : ¬ (sb.toNat < base.toNat + PAGE_SIZE * N ∧ base.toNat < sb.toNat + PAGE_SIZE * N))
    (h4 : ¬ (source.used = 0 ∨ N < source.used))
    (hw : source.walkRoot sb bits (source.table 0).toList ⟨[0], []⟩ = .error e) :
    target.cloneKernelFrom source sb base bits = .error e := by
  have h3' : (decide (sb.toNat < base.toNat + PAGE_SIZE * N) &&
      decide (base.toNat < sb.toNat + PAGE_SIZE * N)) = false := by
    simpa using h3
  have h4' : (source.used == 0 || decide (N < source.used)) = false := by simpa using h4
  simp only [Tables.cloneKernelFrom, h1, h2, h3', h4', hw, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem cloneKernelFrom_unreached {st : Visit} (h1 : checkPool N sb bits = .ok ())
    (h2 : checkPool N base bits = .ok ())
    (h3 : ¬ (sb.toNat < base.toNat + PAGE_SIZE * N ∧ base.toNat < sb.toNat + PAGE_SIZE * N))
    (h4 : ¬ (source.used = 0 ∨ N < source.used))
    (hw : source.walkRoot sb bits (source.table 0).toList ⟨[0], []⟩ = .ok st)
    (ha : (List.range source.used).any (fun t => !st.reached.contains t) = true) :
    target.cloneKernelFrom source sb base bits = .error .tableBacking := by
  have h3' : (decide (sb.toNat < base.toNat + PAGE_SIZE * N) &&
      decide (base.toNat < sb.toNat + PAGE_SIZE * N)) = false := by
    simpa using h3
  have h4' : (source.used == 0 || decide (N < source.used)) = false := by simpa using h4
  simp only [Tables.cloneKernelFrom, h1, h2, h3', h4', hw, Bool.false_eq_true, ↓reduceIte,
      Bind.bind,
    Except.bind]
  simp only [ha, ↓reduceIte]
  rfl

theorem cloneKernelFrom_ok {st : Visit} (h1 : checkPool N sb bits = .ok ())
    (h2 : checkPool N base bits = .ok ())
    (h3 : ¬ (sb.toNat < base.toNat + PAGE_SIZE * N ∧ base.toNat < sb.toNat + PAGE_SIZE * N))
    (h4 : ¬ (source.used = 0 ∨ N < source.used))
    (hw : source.walkRoot sb bits (source.table 0).toList ⟨[0], []⟩ = .ok st)
    (ha : (List.range source.used).any (fun t => !st.reached.contains t) = false) :
    target.cloneKernelFrom source sb base bits =
      .ok ({ target with used := source.used },
        (List.range (min target.used N)).map Step.zero ++
          (List.range source.used).flatMap (fun t =>
            copyStores sb base (st.leaves.contains t) t (source.table t).toList 0) ++
          [.sync]) := by
  have h3' : (decide (sb.toNat < base.toNat + PAGE_SIZE * N) &&
      decide (base.toNat < sb.toNat + PAGE_SIZE * N)) = false := by
    simpa using h3
  have h4' : (source.used == 0 || decide (N < source.used)) = false := by simpa using h4
  simp only [Tables.cloneKernelFrom, h1, h2, h3', h4', hw, Bool.false_eq_true, ↓reduceIte,
      Bind.bind,
    Except.bind]
  simp only [ha]
  rfl

end Clone

end Krepi.Proofs.PageTables.Refinement
