module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.EntryLemmas
public import Krepi.Proofs.PageTables.CloneLemmas

/-!
# Page tables: the abstract mapping of a copy of the kernel tables

What the target of `Tables.cloneKernelFrom` maps once its plan has run:

- `clone_facts`: the pools of the copy are ones that the contract admits, the
  record of the target is that of the source, the valid entries of the root
  and of the level 2 tables of the source are table descriptors with no
  attribute of tables in use, the leaf tables of the walk of the source are
  the tables that the level 2 tables point at, neither the root nor a table
  that the root points at is one of them, their valid entries are leaves that
  the copy takes (`copyableLeaf`), and each entry of the target
  is the copy of the entry of the source (`copyValue`) where that one is
  valid and in a table in use, and 0 elsewhere;
- `clone_M`: from a well-formed source, every leaf of the abstract mapping of
  the target is a leaf of the source at the same virtual address, with the
  same physical page, kind and form.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok)

variable {r : Region} {N : Nat}

theorem clone_facts {target source s : Tables r N} {sb base : UInt64} {bits : UInt8}
    {plan : Plan} (hz : ∀ t, target.used ≤ t → t < N → target.table t = Table.zero)
    (h : target.cloneKernelFrom source sb base bits = .ok (s, plan)) :
    ∃ leaves : List Nat, PoolOk N sb bits ∧ PoolOk N base bits ∧
      (s.apply plan).used = source.used ∧
      (∀ i, i < ENTRIES → isValid (source.entry 0 i) = true →
        isPlainTableDescriptor (source.entry 0 i) = true ∧ ∃ c,
          source.child? sb (source.entry 0 i) = some c ∧
          ∀ j, j < ENTRIES → isValid (source.entry c j) = true →
            isPlainTableDescriptor (source.entry c j) = true ∧
              ∃ c', source.child? sb (source.entry c j) = some c') ∧
      (∀ t, t ∈ leaves ↔ ∃ c, (∃ i, i < ENTRIES ∧ isValid (source.entry 0 i) = true ∧
          source.child? sb (source.entry 0 i) = some c) ∧
        ∃ j, j < ENTRIES ∧ isValid (source.entry c j) = true ∧
          source.child? sb (source.entry c j) = some t) ∧
      (∀ t, (t = 0 ∨ ∃ i, i < ENTRIES ∧ isValid (source.entry 0 i) = true ∧
          source.child? sb (source.entry 0 i) = some t) → t ∉ leaves) ∧
      (∀ t ∈ leaves, ∀ i, i < ENTRIES → isValid (source.entry t i) = true →
        copyableLeaf bits (source.entry t i) = true) ∧
      ∀ t i, (s.apply plan).entry t i =
        if t < source.used ∧ i < ENTRIES ∧ isValid (source.entry t i) = true then
          copyValue sb base (leaves.contains t) (source.entry t i) else 0 := by
  unfold Tables.cloneKernelFrom at h
  obtain ⟨u1, hc1, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hc2, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨hused, h⟩ := except_jp_ok h
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hused
  obtain ⟨st, hw, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨w1, w2, w3, w4⟩ := walkRoot_ok source sb bits hw
  have hnd := w4 (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
  simp only [table_toList_eq, List.singleton_append, List.nil_append] at w1 w2 w3 hnd
  rw [w2] at hnd
  have hmem : ∀ t i, i < ENTRIES → source.entry t i ∈ (List.range ENTRIES).map (source.entry t) :=
    fun t i hi => List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  refine ⟨st.leaves, checkPool_ok.1 hc1, checkPool_ok.1 hc2, rfl, fun i hi hv => ?_,
    fun t => ?_, fun t ht hl => ?_, fun t ht i hi hv => ?_, fun t i => ?_⟩
  · obtain ⟨hp, c, hc, h2⟩ := w1 _ (hmem 0 i hi) hv
    refine ⟨hp, c, hc, fun j hj hvj => ?_⟩
    obtain ⟨hp', c', hc', -⟩ := h2 _ (hmem c j hj) hvj
    exact ⟨hp', c', hc'⟩
  · rw [w3, List.mem_flatMap]
    constructor
    · rintro ⟨c, hc, ht⟩; exact ⟨c, mem_kids.1 hc, mem_kids.1 ht⟩
    · rintro ⟨c, hc, ht⟩; exact ⟨c, mem_kids.2 hc, mem_kids.2 ht⟩
  · rw [w3] at hl
    obtain ⟨c, hc, htc⟩ := List.mem_flatMap.1 hl
    rw [List.nodup_cons] at hnd
    obtain ⟨h0G, hGn⟩ := hnd
    rcases ht with rfl | ⟨i, hi, hv, hci⟩
    · exact h0G (List.mem_flatMap.2 ⟨c, hc, List.mem_cons_of_mem _ htc⟩)
    · rw [List.nodup_flatMap] at hGn
      obtain ⟨hgrp, hpw⟩ := hGn
      by_cases he : c = t
      · subst he; exact (List.nodup_cons.1 (hgrp c hc)).1 htc
      · exact disjoint_of_pairwise (g := fun c => c :: ((List.range ENTRIES).map
          (source.entry c)).filterMap (kidOf source sb)) hpw hc (mem_kids.2 ⟨i, hi, hv, hci⟩) he
          (List.mem_cons_of_mem _ htc) List.mem_cons_self
  · rw [w3] at ht
    obtain ⟨c, hc, htc⟩ := List.mem_flatMap.1 ht
    obtain ⟨i0, hi0, hv0, hc0⟩ := mem_kids.1 hc
    obtain ⟨-, c2, hc2, h2⟩ := w1 _ (hmem 0 i0 hi0) hv0
    obtain rfl : c = c2 := Option.some.inj (hc0.symm.trans hc2)
    obtain ⟨j, hj, hvj, hcj⟩ := mem_kids.1 htc
    obtain ⟨-, c3, hc3, h3⟩ := h2 _ (hmem c j hj) hvj
    obtain rfl : t = c3 := Option.some.inj (hcj.symm.trans hc3)
    exact h3 _ (hmem t i hi) hv
  · rw [entry_eq_get]
    show (Plan.exec _ target.pool).get t i = _
    by_cases ht : t < N
    · by_cases hi : i < ENTRIES
      · rw [get_exec _ _ ht hi, lastAt_append, lastAt_append, lastAt_zeros,
          lastAt_flatMap_range t i _ (fun t' ht' => by rw [lastAt_copyStores]; simp [ht'])]
        simp only [lastAt, stepAt, Option.none_or]
        have hzero : ¬ t < min target.used N → target.pool.get t i = 0 := fun hm => by
          rw [← entry_eq_get]; exact entry_of_table_zero (hz t (by omega) ht) i
        by_cases htu : t < source.used
        · rw [lastAt_copyStores, table_toList_eq]
          simp only [List.getElem?_map, List.getElem?_range hi, Nat.sub_zero, Option.map_some,
            Option.bind_some, Nat.zero_le, and_self, ite_true, htu, true_and, hi]
          by_cases hv : isValid (source.entry t i) = true
          · simp [hv]
          · simp only [hv, Bool.false_eq_true, ite_false, Option.none_or]
            by_cases hm : t < min target.used N
            · simp [List.mem_range, hm]
            · rw [ite_of_neg (by simpa [List.mem_range] using hm), Option.getD_none, hzero hm]
        · simp only [htu, ite_false, Option.none_or, false_and]
          by_cases hm : t < min target.used N
          · simp [List.mem_range, hm]
          · rw [ite_of_neg (by simpa [List.mem_range] using hm), Option.getD_none, hzero hm]
      · rw [get_of_ge_entries _ _ (by omega), ite_of_neg (fun h => hi h.2.1)]
    · rw [get_of_ge _ _ (by omega), ite_of_neg (fun h => ht (by omega))]

/-- In a well-formed source, no table that the root points at, nor the root,
is a leaf table of the walk of a copy. -/
private theorem not_leaf {source : Tables r N} {sb : UInt64} {bits : UInt8}
    (hsrc : source.WellFormed sb bits) {leaves : List Nat}
    (h1 : ∀ i, i < ENTRIES → isValid (source.entry 0 i) = true →
      isPlainTableDescriptor (source.entry 0 i) = true ∧ ∃ c,
        source.child? sb (source.entry 0 i) = some c ∧
        ∀ j, j < ENTRIES → isValid (source.entry c j) = true →
          isPlainTableDescriptor (source.entry c j) = true ∧
            ∃ c', source.child? sb (source.entry c j) = some c')
    (h3 : ∀ t, t ∈ leaves ↔ ∃ c, (∃ i, i < ENTRIES ∧ isValid (source.entry 0 i) = true ∧
        source.child? sb (source.entry 0 i) = some c) ∧
      ∃ j, j < ENTRIES ∧ isValid (source.entry c j) = true ∧
        source.child? sb (source.entry c j) = some t)
    {t : Nat} (ht : t = 0 ∨ ∃ i, source.PointsAt sb 0 i t) : t ∉ leaves := by
  intro hl
  obtain ⟨c, ⟨i, hi, hv, hc⟩, j, hj, hvj, hcj⟩ := (h3 t).1 hl
  obtain ⟨hp, c0, hc0, h2⟩ := h1 i hi hv
  rw [hc] at hc0; cases hc0
  have hpc : source.PointsAt sb 0 i c := ⟨hi, hp, hc⟩
  have hpt : source.PointsAt sb c j t := ⟨hj, (h2 j hj hvj).1, hcj⟩
  have hpar : source.IsParent sb c := Or.inr ⟨i, hpc⟩
  obtain ⟨-, -, -, -, -, -, -, hno0, -, huniq⟩ := hsrc
  rcases ht with rfl | ⟨i', hi'⟩
  · exact hno0 c j hpar hpt
  · obtain ⟨rfl, -⟩ := huniq 0 i' c j t (Or.inl rfl) hpar hi' hpt
    exact hno0 0 i (Or.inl rfl) hpc

/-- The abstract mapping of the target of a copy, once its plan has run, is
contained in that of a well-formed source: the same leaf at the same address.
-/
theorem clone_M {target source s : Tables r N} {sb base : UInt64} {bits : UInt8} {plan : Plan}
    (hsrc : source.WellFormed sb bits)
    (hz : ∀ t, target.used ≤ t → t < N → target.table t = Table.zero)
    (h : target.cloneKernelFrom source sb base bits = .ok (s, plan)) {v : UInt64} {l : Leaf}
    (hm : (s.apply plan).M base v l) : source.M sb v l := by
  obtain ⟨leaves, -, hpb, hused, h1, h3, -, -, hent⟩ := clone_facts hz h
  obtain ⟨hreg, hal, hcase⟩ := hm
  -- a valid entry of the target is the copy of a valid entry of the source
  have hval : ∀ t i, isValid ((s.apply plan).entry t i) = true →
      t < source.used ∧ i < ENTRIES ∧ isValid (source.entry t i) = true ∧
        (s.apply plan).entry t i = copyValue sb base (leaves.contains t) (source.entry t i) := by
    intro t i hv
    rw [hent] at hv ⊢
    by_cases hc : t < source.used ∧ i < ENTRIES ∧ isValid (source.entry t i) = true
    · rw [ite_of_pos hc]; exact ⟨hc.1, hc.2.1, hc.2.2, rfl⟩
    · rw [ite_of_neg hc] at hv; exact absurd hv (by decide)
  -- the copy of a table descriptor of a table that is not a leaf table
  have hcopy : ∀ t i c, t ∉ leaves → source.child? sb (source.entry t i) = some c →
      copyValue sb base (leaves.contains t) (source.entry t i) = tableAt base c ∧
        (s.apply plan).child? base (tableAt base c) = some c := by
    intro t i c htl hc
    have hcu := child?_some hc
    refine ⟨?_, child?_tableAt hpb (by rw [hused]; exact hcu.1) hcu.2⟩
    rw [copyValue, ite_of_neg (by simpa using htl), ← child?_index hc]; rfl
  -- the root and level 2 entries of the walk of the target
  have hwalk2 : ∀ {t2 : Nat} {e2 : UInt64}, (s.apply plan).walk2 base v = .ok (some (t2, e2)) →
      isValid (source.entry 0 (index1 v)) = true ∧
        source.child? sb (source.entry 0 (index1 v)) = some t2 ∧
        source.PointsAt sb 0 (index1 v) t2 ∧ e2 = (s.apply plan).entry t2 (index2 v) := by
    intro t2 e2 hw
    rcases walk2_ok.1 hw with ⟨-, hw⟩ | ⟨t2', hv, hc, hw⟩
    · cases hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨-, hi, hvs, he⟩ := hval 0 _ hv
      obtain ⟨hp, c, hcs, -⟩ := h1 _ hi hvs
      obtain ⟨hcv, hct⟩ := hcopy 0 _ c (not_leaf hsrc h1 h3 (Or.inl rfl)) hcs
      rw [he, hcv, hct, Option.some.injEq] at hc
      subst hc
      exact ⟨hvs, hcs, ⟨hi, hp, hcs⟩, rfl⟩
  -- a valid level 2 entry of the target under the slot of `v`
  have hlev2 : ∀ {t2 : Nat}, source.PointsAt sb 0 (index1 v) t2 →
      isValid ((s.apply plan).entry t2 (index2 v)) = true →
      isValid (source.entry t2 (index2 v)) = true ∧
        isPlainTableDescriptor (source.entry t2 (index2 v)) = true ∧ ∃ c,
          source.child? sb (source.entry t2 (index2 v)) = some c ∧
          (s.apply plan).entry t2 (index2 v) = tableAt base c ∧
          (s.apply plan).child? base (tableAt base c) = some c := by
    intro t2 hpt hv
    obtain ⟨-, hi, hvs, he⟩ := hval _ _ hv
    obtain ⟨hp0, c0, hc0, h2⟩ := h1 _ (index1_lt v) (isValid_of_isPlain hpt.2.1)
    rw [hpt.2.2, Option.some.injEq] at hc0
    subst hc0
    obtain ⟨hp, c, hc⟩ := h2 _ hi hvs
    obtain ⟨hcv, hct⟩ := hcopy _ _ c (not_leaf hsrc h1 h3 (Or.inr ⟨_, hpt⟩)) hc
    exact ⟨hvs, hp, c, hc, he.trans hcv, hct⟩
  rcases hcase with ⟨t2, t3, d, hw, htb, hk, hpa, hfm⟩ | ⟨t2, d, hw, hrw, -, -, -⟩
  · obtain ⟨e2, hw2, hv2, -, hc2, hd⟩ := walk_ok_level3.1 hw
    obtain ⟨hv1, hc1, hpt1, rfl⟩ := hwalk2 hw2
    obtain ⟨hvs2, hps2, c, hcs2, he2, hct⟩ := hlev2 hpt1 hv2
    rw [he2, hct, Option.some.injEq] at hc2
    subst c
    have hvd : isValid d = true := by
      simp only [isValid, htb, TABLE_OR_PAGE]; decide
    rw [hd] at hvd
    obtain ⟨-, -, hvs3, he3⟩ := hval _ _ hvd
    have hleaf : t3 ∈ leaves :=
      (h3 t3).2 ⟨t2, ⟨index1 v, index1_lt v, hv1, hc1⟩, index2 v, index2_lt v, hvs2, hcs2⟩
    rw [he3, copyValue, ite_of_pos (by simpa using hleaf)] at hd
    refine ⟨hreg, hal, Or.inl ⟨t2, t3, d, ?_, htb, hk, hpa, hfm⟩⟩
    refine walk_ok_level3.2 ⟨_, walk2_ok.2 (Or.inr ⟨t2, hv1, hc1, rfl⟩), hvs2, ?_, hcs2, hd⟩
    rw [typeBits_of_isPlain hps2]; decide
  · obtain ⟨hw2, hv2, hb⟩ := walk_ok_block.1 hw
    obtain ⟨-, -, hpt1, rfl⟩ := hwalk2 hw2
    obtain ⟨-, -, c, -, he2, -⟩ := hlev2 hpt1 hv2
    rw [he2, tableAt, typeBits_tableDescriptor] at hb
    exact absurd hb (by decide)

end Krepi.Proofs.PageTables
