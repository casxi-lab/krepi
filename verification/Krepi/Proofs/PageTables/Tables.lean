module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.CloneLemmas
import Krepi.Proofs.PageTables.MapCheckLemmas

/-!
# Page tables: proofs about the well-formedness of table sets

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the well-formedness of table sets,
whose type is exactly that statement: that `Tables::new` on zero storage and
the kernel tables that `kernel_map` and `direct_map` write into such sets
are well-formed, and that each write entry of a set keeps a set well-formed.

Every theorem here is proved. `map_page` and `map_block` are maps of their
one leaf (`mapPage_single`, `mapBlock_single`), and the leaves of
`kernel_map` and `direct_map` pass the checks of
`Krepi.Proofs.PageTables.MapCheckLemmas`, so the set after their plan is
well-formed (`Krepi.Proofs.PageTables.MapWriteLemmas`); `unmap_page` clears a
leaf, an elementary change of `Krepi.Proofs.PageTables.WellFormedLemmas`; the
copy is well-formed by what the walk of its source checked
(`Krepi.Proofs.PageTables.CloneLemmas`); and the kernel sets of the boot are
the maps on the set of `Tables::new`. Mathlib is imported so that the gate
counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Tables

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok)

public theorem newWellFormed : NewWellFormed := by
  intro r N base bits hp
  exact wf_zero hp (fun t i => by simp [Tables.new, Pool.zero, Pool.get, Table.zero]) rfl


public theorem resetWellFormed : ResetWellFormed := by
  intro r N s base bits hp hz
  apply wf_zero hp _ rfl
  intro t i
  by_cases ht : t < N
  · by_cases hi : i < ENTRIES
    · show (Plan.exec _ s.pool).get t i = 0
      rw [get_exec _ _ ht hi]
      simp only [Tables.reset]
      rw [lastAt_zeros]
      simp only [List.mem_range]
      by_cases htu : t < s.used
      · rw [ite_of_pos (by omega)]; rfl
      · rw [ite_of_neg (by omega), Option.getD_none, ← entry_eq_get]
        exact entry_of_table_zero (hz t (by omega) ht) i
    · exact get_of_ge_entries _ _ (by omega)
  · exact get_of_ge _ _ (by omega)

/-- The set that the copy leaves is well-formed, from what the walk of its
source tells: the target's entries are the copied entries of the tables in
use of the source and 0 elsewhere. -/
private theorem clone_wf {r : Region} {N : Nat} (src T : Tables r N) (sb base : UInt64)
    (bits : UInt8) (leaves : List Nat) (hp : PoolOk N base bits) (hu1 : 1 ≤ src.used)
    (huN : src.used ≤ N) (hTu : T.used = src.used)
    (hent : ∀ t i, T.entry t i = if t < src.used ∧ i < ENTRIES ∧ isValid (src.entry t i) = true
      then copyValue sb base (leaves.contains t) (src.entry t i) else 0)
    (R0 : List Nat) (K : Nat → List Nat)
    (hK : ∀ t c, c ∈ K t ↔ ∃ i, i < ENTRIES ∧ isValid (src.entry t i) = true ∧
      src.child? sb (src.entry t i) = some c)
    (hKn : ∀ t, (K t).Nodup → ∀ i j c, i < ENTRIES → j < ENTRIES →
      (isValid (src.entry t i) = true ∧ src.child? sb (src.entry t i) = some c) →
      (isValid (src.entry t j) = true ∧ src.child? sb (src.entry t j) = some c) → i = j)
    (hR0 : R0 = K 0) (hleaves : leaves = R0.flatMap K)
    (hnd : (0 :: R0.flatMap (fun c => c :: K c)).Nodup)
    (hall : ∀ t, t < src.used → t ∈ 0 :: R0.flatMap (fun c => c :: K c))
    (hplain : ∀ t, (t = 0 ∨ t ∈ R0) → ∀ i, i < ENTRIES → isValid (src.entry t i) = true →
      ∃ c, src.child? sb (src.entry t i) = some c)
    (hcopy : ∀ t, t ∈ leaves → ∀ i, i < ENTRIES → isValid (src.entry t i) = true →
      copyableLeaf bits (src.entry t i) = true) :
    T.WellFormed base bits := by
  rw [List.nodup_cons] at hnd
  obtain ⟨h0G, hGn⟩ := hnd
  rw [List.nodup_flatMap] at hGn
  obtain ⟨hgrp, hpw⟩ := hGn
  have hdisj : ∀ {a b}, a ∈ R0 → b ∈ R0 → a ≠ b → (a :: K a).Disjoint (b :: K b) :=
    fun ha hb hab => disjoint_of_pairwise (g := fun c => c :: K c) hpw ha hb hab
  have hnotleaf : ∀ c, c ∈ R0 → c ∉ leaves := by
    intro c hc hl
    rw [hleaves, List.mem_flatMap] at hl
    obtain ⟨c2, hc2, hcc⟩ := hl
    by_cases he : c2 = c
    · subst he; exact (List.nodup_cons.1 (hgrp c2 hc2)).1 hcc
    · exact hdisj hc2 hc he (List.mem_cons_of_mem _ hcc) List.mem_cons_self
  have h0R : 0 ∉ R0 := fun h => h0G (List.mem_flatMap.2 ⟨0, h, List.mem_cons_self⟩)
  have h0L : 0 ∉ leaves := fun h => by
    rw [hleaves, List.mem_flatMap] at h
    obtain ⟨c, hc, h⟩ := h
    exact h0G (List.mem_flatMap.2 ⟨c, hc, List.mem_cons_of_mem _ h⟩)
  have hR0u : ∀ c, c ∈ R0 → c < src.used := by
    intro c hc
    rw [hR0, hK] at hc
    obtain ⟨_, _, _, h⟩ := hc
    exact (child?_some h).1
  have hval : ∀ t i c, (t = 0 ∨ t ∈ R0) → i < ENTRIES → isValid (src.entry t i) = true →
      src.child? sb (src.entry t i) = some c → T.entry t i = tableAt base c := by
    intro t i c ht hi hv hc
    have htu : t < src.used := by
      rcases ht with rfl | h
      · omega
      · exact hR0u t h
    have htl : t ∉ leaves := by
      rcases ht with rfl | h
      · exact h0L
      · exact hnotleaf t h
    rw [hent, ite_of_pos ⟨htu, hi, hv⟩, copyValue, ite_of_neg (by simpa using htl),
      ← child?_index hc]
    rfl
  have hTc : ∀ c, c < src.used → c < N → T.child? base (tableAt base c) = some c :=
    fun c h1 h2 => child?_tableAt hp (hTu ▸ h1) h2
  have hpt : ∀ t i c, T.PointsAt base t i c ↔ (t = 0 ∨ t ∈ R0) ∧ i < ENTRIES ∧
      isValid (src.entry t i) = true ∧ src.child? sb (src.entry t i) = some c := by
    intro t i c
    constructor
    · rintro ⟨hi, hpl, hc⟩
      have hcond : t < src.used ∧ i < ENTRIES ∧ isValid (src.entry t i) = true := by
        by_contra hn
        rw [hent, ite_of_neg hn] at hpl
        exact absurd hpl (by decide)
      obtain ⟨htu, -, hv⟩ := hcond
      have htl : t ∉ leaves := by
        intro hl
        rw [hent, ite_of_pos ⟨htu, hi, hv⟩] at hpl
        simp only [copyValue, List.contains_iff_mem.2 hl, ite_true] at hpl
        rw [(copyable_facts (hcopy t hl i hi hv)).1] at hpl
        exact absurd hpl (by decide)
      have hpar : t = 0 ∨ t ∈ R0 := by
        rcases List.mem_cons.1 (hall t htu) with h | h
        · exact Or.inl h
        · obtain ⟨c2, hc2, h⟩ := List.mem_flatMap.1 h
          rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr hc2
          · exact absurd (hleaves ▸ List.mem_flatMap.2 ⟨c2, hc2, h⟩) htl
      obtain ⟨c0, hc0⟩ := hplain t hpar i hi hv
      have hc0u := child?_some hc0
      rw [hval t i c0 hpar hi hv hc0, hTc c0 hc0u.1 hc0u.2] at hc
      exact ⟨hpar, hi, hv, (Option.some.inj hc) ▸ hc0⟩
    · rintro ⟨hpar, hi, hv, hc⟩
      have hcu := child?_some hc
      refine ⟨hi, ?_, ?_⟩ <;> rw [hval t i c hpar hi hv hc]
      · exact isPlain_tableDescriptor _
      · exact hTc c hcu.1 hcu.2
  have hL2 : ∀ x, T.IsLevel2 base x ↔ x ∈ R0 := by
    intro x
    rw [hR0, hK]
    constructor
    · rintro ⟨i, h⟩
      obtain ⟨-, hi, hv, hc⟩ := (hpt 0 i x).1 h
      exact ⟨i, hi, hv, hc⟩
    · rintro ⟨i, hi, hv, hc⟩
      exact ⟨i, (hpt 0 i x).2 ⟨Or.inl rfl, hi, hv, hc⟩⟩
  have hL3 : ∀ x, T.IsLevel3 base x ↔ x ∈ leaves := by
    intro x
    rw [hleaves, List.mem_flatMap]
    constructor
    · rintro ⟨t2, i, h2, h⟩
      obtain ⟨-, hi, hv, hc⟩ := (hpt t2 i x).1 h
      exact ⟨t2, (hL2 t2).1 h2, (hK t2 x).2 ⟨i, hi, hv, hc⟩⟩
    · rintro ⟨t2, h2, hx⟩
      obtain ⟨i, hi, hv, hc⟩ := (hK t2 x).1 hx
      exact ⟨t2, i, (hL2 t2).2 h2, (hpt t2 i x).2 ⟨Or.inr h2, hi, hv, hc⟩⟩
  have hPar : ∀ x, T.IsParent base x ↔ x = 0 ∨ x ∈ R0 := fun x => by
    simp only [Tables.IsParent, hL2]
  have hzero : ∀ t i, ¬ (t < src.used ∧ i < ENTRIES ∧ isValid (src.entry t i) = true) →
      T.entry t i = 0 := fun t i h => by rw [hent, ite_of_neg h]
  refine ⟨hp, hTu ▸ hu1, hTu ▸ huN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht htN
    apply table_eq_zero; intro i _
    rw [← entry_eq_get]; exact hzero t i (fun h => by omega)
  · intro i hi
    by_cases hv : isValid (src.entry 0 i) = true
    · obtain ⟨c, hc⟩ := hplain 0 (Or.inl rfl) i hi hv
      exact Or.inr ⟨c, (hpt 0 i c).2 ⟨Or.inl rfl, hi, hv, hc⟩⟩
    · exact Or.inl (hzero 0 i fun h => hv h.2.2)
  · intro x hx i hi
    rw [hL2] at hx
    by_cases hv : isValid (src.entry x i) = true
    · obtain ⟨c, hc⟩ := hplain x (Or.inr hx) i hi hv
      exact Or.inr (Or.inl ⟨c, (hpt x i c).2 ⟨Or.inr hx, hi, hv, hc⟩⟩)
    · exact Or.inl (hzero x i fun h => hv h.2.2)
  · intro x hx i hi
    rw [hL3] at hx
    by_cases hcond : x < src.used ∧ i < ENTRIES ∧ isValid (src.entry x i) = true
    · right
      rw [hent, ite_of_pos hcond]
      simp only [copyValue, List.contains_iff_mem.2 hx, ite_true]
      exact (copyable_facts (hcopy x hx i hi hcond.2.2)).2
    · exact Or.inl (hzero x i hcond)
  · intro t i ht h
    obtain ⟨hpar, hi, hv, hc⟩ := (hpt t i 0).1 h
    have h0K : 0 ∈ K t := (hK t 0).2 ⟨i, hi, hv, hc⟩
    rcases hpar with rfl | h2
    · exact h0R (hR0 ▸ h0K)
    · exact h0G (List.mem_flatMap.2 ⟨t, h2, List.mem_cons_of_mem _ h0K⟩)
  · intro c hc1 hc2
    rcases List.mem_cons.1 (hall c (hTu ▸ hc2)) with h | h
    · omega
    · obtain ⟨c2, hc2', h⟩ := List.mem_flatMap.1 h
      rcases List.mem_cons.1 h with rfl | h
      · have : c ∈ K 0 := hR0 ▸ hc2'
        obtain ⟨i, hi, hv, hc⟩ := (hK 0 c).1 this
        exact ⟨0, i, Or.inl rfl, (hpt 0 i c).2 ⟨Or.inl rfl, hi, hv, hc⟩⟩
      · obtain ⟨j, hj, hv, hc⟩ := (hK c2 c).1 h
        exact ⟨c2, j, (hPar c2).2 (Or.inr hc2'), (hpt c2 j c).2 ⟨Or.inr hc2', hj, hv, hc⟩⟩
  · intro t i t' i' c _ _ ha hb
    obtain ⟨hpa, hi, hva, hca⟩ := (hpt t i c).1 ha
    obtain ⟨hpb, hi', hvb, hcb⟩ := (hpt t' i' c).1 hb
    have hKa : c ∈ K t := (hK t c).2 ⟨i, hi, hva, hca⟩
    have hKb : c ∈ K t' := (hK t' c).2 ⟨i', hi', hvb, hcb⟩
    have hR0n : R0.Nodup := by
      apply List.Pairwise.imp _ hpw
      intro a b hab he
      subst he
      exact hab List.mem_cons_self List.mem_cons_self
    have hsame : ∀ x, (x = 0 ∨ x ∈ R0) → (K x).Nodup := by
      rintro x (rfl | hx)
      · exact hR0 ▸ hR0n
      · exact (List.nodup_cons.1 (hgrp x hx)).2
    have hcross : ∀ x, x ∈ R0 → c ∈ R0 → c ∈ K x → False := by
      intro x hx hcR hcx
      by_cases he : c = x
      · subst he; exact (List.nodup_cons.1 (hgrp c hx)).1 hcx
      · exact hdisj hcR hx he List.mem_cons_self (List.mem_cons_of_mem _ hcx)
    rcases hpa with rfl | hta <;> rcases hpb with rfl | htb
    · exact ⟨rfl, hKn 0 (hsame 0 (Or.inl rfl)) i i' c hi hi' ⟨hva, hca⟩ ⟨hvb, hcb⟩⟩
    · exact (hcross t' htb (hR0 ▸ hKa) hKb).elim
    · exact (hcross t hta (hR0 ▸ hKb) hKa).elim
    · by_cases he : t = t'
      · subst he
        exact ⟨rfl, hKn t (hsame t (Or.inr hta)) i i' c hi hi' ⟨hva, hca⟩ ⟨hvb, hcb⟩⟩
      · exact (hdisj hta htb he (List.mem_cons_of_mem _ hKa) (List.mem_cons_of_mem _ hKb)).elim

public theorem cloneKernelFromWellFormed : CloneKernelFromWellFormed := by
  intro r N target source sourceBase base bits s plan hz h
  unfold Tables.cloneKernelFrom at h
  obtain ⟨u1, -, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hc2, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨hused, h⟩ := except_jp_ok h
  obtain ⟨st, hw, h⟩ := except_bind_ok.1 h
  obtain ⟨hreach, h⟩ := except_jp_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hp : PoolOk N base bits := checkPool_ok.1 hc2
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hused
  have hu1 : 1 ≤ source.used := by omega
  have huN : source.used ≤ N := by omega
  have hall0 : ∀ t, t < source.used → t ∈ st.reached := by
    intro t ht
    simp only [List.any_eq_true, List.mem_range, not_exists, not_and] at hreach
    have := hreach t ht
    simpa using this
  obtain ⟨w1, w2, w3, w4⟩ := walkRoot_ok source sourceBase bits hw
  have hnd := w4 (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
  simp only [table_toList_eq, List.singleton_append, List.nil_append] at w1 w2 w3 hnd
  rw [w2] at hnd hall0
  have hmem : ∀ t i, i < ENTRIES → source.entry t i ∈ (List.range ENTRIES).map (source.entry t) :=
    fun t i hi => List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  let K : Nat → List Nat := fun t =>
    ((List.range ENTRIES).map (source.entry t)).filterMap (kidOf source sourceBase)
  have hK : ∀ t c, c ∈ K t ↔ ∃ i, i < ENTRIES ∧ isValid (source.entry t i) = true ∧
      source.child? sourceBase (source.entry t i) = some c := fun t c => mem_kids
  have hlev2 : ∀ c, c ∈ K 0 → ∀ e ∈ (List.range ENTRIES).map (source.entry c), isValid e = true →
      isPlainTableDescriptor e = true ∧ ∃ c', source.child? sourceBase e = some c' ∧
        ∀ f ∈ (List.range ENTRIES).map (source.entry c'), isValid f = true →
          copyableLeaf bits f = true := by
    intro c hc
    obtain ⟨i, hi, hv, hci⟩ := (hK 0 c).1 hc
    obtain ⟨-, c'', hc'', h⟩ := w1 _ (hmem 0 i hi) hv
    rw [hci, Option.some.injEq] at hc''
    subst hc''
    exact h
  have hpool : ∀ t i, t < N → i < ENTRIES →
      (Plan.exec ((List.range (min target.used N)).map Step.zero ++
        (List.range source.used).flatMap (fun t => copyStores sourceBase base
          (st.leaves.contains t) t (source.table t).toList 0) ++ [Step.sync]) target.pool).get t i =
      if t < source.used ∧ isValid (source.entry t i) = true then
        copyValue sourceBase base (st.leaves.contains t) (source.entry t i) else 0 := by
    intro t i ht hi
    rw [get_exec _ _ ht hi, lastAt_append, lastAt_append, lastAt_zeros,
      lastAt_flatMap_range t i _ (fun t' ht' => by rw [lastAt_copyStores]; simp [ht'])]
    simp only [lastAt, stepAt, Option.none_or]
    by_cases htu : t < source.used
    · rw [lastAt_copyStores, table_toList_eq]
      simp only [List.getElem?_map, List.getElem?_range hi, Nat.sub_zero, Option.map_some,
        Option.bind_some, true_and, Nat.zero_le, and_self, ite_true, htu]
      by_cases hv : isValid (source.entry t i) = true
      · simp [hv]
      · simp only [hv, Bool.false_eq_true, ite_false, Option.none_or]
        by_cases hm : t < min target.used N
        · simp [List.mem_range, hm]
        · rw [ite_of_neg (by simpa [List.mem_range] using hm), Option.getD_none, ← entry_eq_get]
          exact entry_of_table_zero (hz t (by omega) ht) i
    · simp only [htu, ite_false, Option.none_or, false_and]
      by_cases hm : t < min target.used N
      · simp [List.mem_range, hm]
      · rw [ite_of_neg (by simpa [List.mem_range] using hm), Option.getD_none, ← entry_eq_get]
        exact entry_of_table_zero (hz t (by omega) ht) i
  refine clone_wf source _ sourceBase base bits st.leaves hp hu1 huN ?_ ?_ (K 0) K hK
    (fun t hn i j c hi hj hci hcj => kids_inj hn hi hj hci hcj) rfl w3 hnd hall0 ?_ ?_
  · rfl
  · intro t i
    rw [entry_eq_get]
    by_cases ht : t < N
    · by_cases hi : i < ENTRIES
      · rw [show ∀ q : Plan, (({ target with used := source.used } : Tables r N).apply q).pool =
          Plan.exec q target.pool from fun _ => rfl, hpool t i ht hi]
        by_cases hc : t < source.used ∧ isValid (source.entry t i) = true
        · rw [ite_of_pos hc, ite_of_pos ⟨hc.1, hi, hc.2⟩]
        · rw [ite_of_neg hc, ite_of_neg (fun h => hc ⟨h.1, h.2.2⟩)]
      · rw [get_of_ge_entries _ _ (by omega), ite_of_neg (fun h => hi h.2.1)]
    · rw [get_of_ge _ _ (by omega), ite_of_neg (fun h => ht (by omega))]
  · rintro t (rfl | ht) i hi hv
    · obtain ⟨-, c, hc, -⟩ := w1 _ (hmem 0 i hi) hv
      exact ⟨c, hc⟩
    · obtain ⟨-, c, hc, -⟩ := hlev2 t ht _ (hmem t i hi) hv
      exact ⟨c, hc⟩
  · intro t ht i hi hv
    rw [w3, List.mem_flatMap] at ht
    obtain ⟨c, hc, htc⟩ := ht
    obtain ⟨j, hj, hvj, hcj⟩ := (hK c t).1 htc
    obtain ⟨-, c', hc', h⟩ := hlev2 c hc _ (hmem c j hj) hvj
    rw [hcj, Option.some.injEq] at hc'
    subst hc'
    exact h _ (hmem t i hi) hv

public theorem mapPageWellFormed : MapPageWellFormed := by
  intro r N s v p k base bits s' plan hs h
  obtain ⟨pl, hl, happ, hN, -⟩ := mapPage_single hs h
  rw [happ]; exact final_wf hs hl hN

public theorem mapBlockWellFormed : MapBlockWellFormed := by
  intro r N s v p base bits s' plan hs h
  obtain ⟨pl, hl, happ, hN, -⟩ := mapBlock_single hs h
  rw [happ]; exact final_wf hs hl hN

public theorem unmapPageWellFormed : UnmapPageWellFormed := by
  intro r N s v base bits plan p hs h
  unfold Tables.unmapPage at h
  obtain ⟨u, -, h⟩ := except_bind_ok.1 h
  obtain ⟨⟨t3, d⟩, hl, h⟩ := except_bind_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨t2, hw, -⟩ := pageLeaf_ok.1 hl
  obtain ⟨-, -, h3, -⟩ := wf_walk_level3 hs hw
  exact wf_setLeaf hs (wf_level3_ne_zero hs h3) (wf_level3_lt h3).1 (index3_lt v)
    (wf_level3_not_plain hs h3 (index3_lt v)) (by decide)
    (fun h2 => absurd h3 fun h3 => wf_not_level2_level3 hs h2 h3) (fun _ => Or.inl rfl)

public theorem kernelMapWellFormed : KernelMapWellFormed := by
  intro N s layout base bits s' plan hs h
  obtain ⟨leaves, hl, happ, hN, -⟩ := kernelMap_facts hs h
  rw [happ]; exact final_wf hs hl hN

public theorem directMapWellFormed : DirectMapWellFormed := by
  intro N s memory base bits s' plan hs h
  obtain ⟨leaves, hl, happ, hN, -⟩ := directMap_facts hs h
  rw [happ]; exact final_wf hs hl hN

public theorem bootKernelMapWellFormed : BootKernelMapWellFormed := by
  intro N layout base bits s plan hp h
  exact kernelMapWellFormed N _ layout base bits s plan (newWellFormed .lower N base bits hp) h

public theorem bootDirectMapWellFormed : BootDirectMapWellFormed := by
  intro N memory base bits s plan hp h
  exact directMapWellFormed N _ memory base bits s plan (newWellFormed .upper N base bits hp) h

end Krepi.Proofs.PageTables.Tables
