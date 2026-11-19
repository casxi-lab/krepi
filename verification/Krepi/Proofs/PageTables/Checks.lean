module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.TreeLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.LeavesLemmas

/-!
# Page tables: proofs about the checks of the invariants

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the checks of the invariants, whose
type is exactly that statement: that each computable check agrees with its
invariant, on every value or on every value that keeps the invariants that
the check reads.

The checks of the structural invariants, `Tables.checkWellFormed`,
`Ownership.checkWellFormed` and `Shared.checkWellFormed`, and the check of
the offset of the direct map, `Shared.checkDirectMapOffset`, are proved. The
five checks of the functional invariants of the page ownership table are
still planned: their proof is `sorry`, and `verification/statements.json`
registers them as `planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Checks

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables

private theorem conj_tables {r : Region} {N : Nat} (s : Tables r N) (base : UInt64) :
    (sortByKey id (s.level2Tables base ++ s.level3Tables base) == List.range' 1 (s.used - 1)) = true ↔
      (∀ t i, s.IsParent base t → ¬ s.PointsAt base t i 0) ∧
      (∀ c, 1 ≤ c → c < s.used → ∃ t i, s.IsParent base t ∧ s.PointsAt base t i c) ∧
      (∀ t i t' i' c, s.IsParent base t → s.IsParent base t' →
        s.PointsAt base t i c → s.PointsAt base t' i' c → t = t' ∧ i = i') := by
  rw [beq_iff_eq, sort_eq_range_iff]
  constructor
  · rintro ⟨hn, hm⟩
    have h0 : 0 ∉ s.level2Tables base ++ s.level3Tables base := fun h => by
      have := (hm 0).1 h; omega
    refine ⟨fun t i hp h => h0 ((mem_tablesOf s base).2 ⟨t, i, hp, h⟩),
      fun c h1 h2 => (mem_tablesOf s base).1 ((hm c).2 ⟨h1, h2⟩),
      (tablesOf_nodup_iff s base h0).1 hn⟩
  · rintro ⟨h8, h9, h10⟩
    have h0 : 0 ∉ s.level2Tables base ++ s.level3Tables base := fun h => by
      obtain ⟨t, i, hp, h⟩ := (mem_tablesOf s base).1 h
      exact h8 t i hp h
    refine ⟨(tablesOf_nodup_iff s base h0).2 h10, fun c => ⟨fun h => ?_, fun ⟨h1, h2⟩ =>
      (mem_tablesOf s base).2 (h9 c h1 h2)⟩⟩
    obtain ⟨t, i, hp, h⟩ := (mem_tablesOf s base).1 h
    refine ⟨Nat.pos_of_ne_zero fun hc => ?_, (pointsAt_lt h).1⟩
    subst hc; exact h8 t i hp h

public theorem checkTablesWellFormed : CheckTablesWellFormed := by
  intro r N s base bits
  have h1 : poolOk N base bits = true ↔ PoolOk N base bits := by
    simp [poolOk, PoolOk, and_assoc]
  have h4 : ((List.range N).all fun t => decide (t < s.used) || s.table t == Table.zero) = true ↔
      ∀ t, s.used ≤ t → t < N → s.table t = Table.zero := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · intro h t ht1 ht2
      rcases h t ht2 with h | h
      · omega
      · exact h
    · intro h t ht
      by_cases h' : t < s.used
      · exact Or.inl h'
      · exact Or.inr (h t (by omega) ht)
  have h5 : ((List.range ENTRIES).all fun i =>
      s.entry 0 i == 0 || (s.pointsAt? base 0 i).isSome) = true ↔
      ∀ i, i < ENTRIES → s.entry 0 i = 0 ∨ ∃ c, s.PointsAt base 0 i c := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Option.isSome_iff_exists]
    exact forall_congr' fun i => imp_congr_right fun hi =>
      or_congr_right (exists_congr fun c => pointsAt?_eq_some s base hi)
  have h6 : ((s.level2Tables base).all fun t => (List.range ENTRIES).all fun i =>
      s.entry t i == 0 || (s.pointsAt? base t i).isSome ||
        (isReadWriteBlock (s.entry t i) && decide ((blockAddress (s.entry t i)).toNat <
          2 ^ bits.toNat))) = true ↔
      ∀ t, s.IsLevel2 base t → ∀ i, i < ENTRIES →
        s.entry t i = 0 ∨ (∃ c, s.PointsAt base t i c) ∨
          (isReadWriteBlock (s.entry t i) = true ∧
            (blockAddress (s.entry t i)).toNat < 2 ^ bits.toNat) := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Option.isSome_iff_exists, Bool.and_eq_true, decide_eq_true_eq, mem_level2Tables, or_assoc]
    exact forall_congr' fun t => imp_congr_right fun _ => forall_congr' fun i =>
      imp_congr_right fun hi => or_congr_right (or_congr_left
        (exists_congr fun c => pointsAt?_eq_some s base hi))
  have h7 : ((s.level3Tables base).all fun t => (List.range ENTRIES).all fun i =>
      s.entry t i == 0 || ((Kind.ofPage (s.entry t i)).isSome &&
        decide ((outputAddress (s.entry t i)).toNat < 2 ^ bits.toNat))) = true ↔
      ∀ t, s.IsLevel3 base t → ∀ i, i < ENTRIES →
        s.entry t i = 0 ∨
          ((∃ k, s.entry t i = descriptor k (outputAddress (s.entry t i))) ∧
            (outputAddress (s.entry t i)).toNat < 2 ^ bits.toNat) := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, mem_level3Tables, ofPage_isSome_iff]
    exact forall_congr' fun t => imp_congr_right fun _ => forall_congr' fun i =>
      imp_congr_right fun _ => or_congr_right (and_congr_left fun _ =>
        exists_congr fun k => eq_comm)
  unfold Tables.checkWellFormed Tables.WellFormed
  simp only [Bool.and_eq_true, decide_eq_true_eq, h1, h4, h5, h6, h7, conj_tables, and_assoc]

public theorem checkOwnershipWellFormed : CheckOwnershipWellFormed := by
  intro E X t
  unfold Ownership.checkWellFormed Ownership.WellFormed
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, Krepi.Proofs.Fdt.allPairs_iff, decide_eq_true_eq, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ =>
    forall_congr' fun x => imp_congr_right fun _ => and_congr_right fun _ => ?_
  unfold Extent.InBank
  cases t.banks[x.bank]? <;> simp

public theorem checkSharedWellFormed : CheckSharedWellFormed := by
  intro E X s cfg
  unfold Shared.checkWellFormed Shared.WellFormed
  rw [Bool.and_eq_true, Bool.and_eq_true, checkTablesWellFormed, checkTablesWellFormed, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  cases s.ownership with
  | none => simp
  | some t => simpa using checkOwnershipWellFormed E X t

public theorem checkOneOwner : CheckOneOwner := by
  sorry

public theorem checkHolderRanges : CheckHolderRanges := by
  sorry

public theorem checkGenerationsBelowCounter : CheckGenerationsBelowCounter := by
  sorry

public theorem checkFreeExtentsMaximal : CheckFreeExtentsMaximal := by
  sorry

public theorem checkFreeOrHeldUsable : CheckFreeOrHeldUsable := by
  sorry

public theorem checkDirectMapOffset : CheckDirectMapOffset := by
  intro E X sh cfg
  unfold Shared.checkDirectMapOffset Shared.DirectMapOffset
  rw [List.all_eq_true]
  have hD := direct_base_toNat
  constructor
  · intro hall v l hM
    obtain ⟨hreg, hpg, hcase⟩ := hM
    have hdec := upper_decomp hreg hpg
    have h1 := index1_lt v
    have h2 := index2_lt v
    have h3 := index3_lt v
    rcases hcase with ⟨t2, t3, d, hw, hd3, hk, hpa, -⟩ | ⟨t2, d, hw, hrw, hk, -, hpa⟩
    · obtain ⟨e2, hw2, hv2, hb2, hc2, hd⟩ := walk_ok_level3.1 hw
      rcases walk2_ok.1 hw2 with ⟨-, h⟩ | ⟨t2, hv1, hc1, h⟩
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem : (v.toNat, Form.page, d) ∈ sh.directMap.leaves cfg.directBase :=
          mem_leaves.2 ⟨index1 v, index2 v, t2, h1, h2, hv1, hc1, hv2, Or.inr ⟨hb2, t3, index3 v,
            hc2, h3, hd, hd3, by rw [hk]; rfl, rfl, by simp only [Region.first]; omega⟩⟩
        have hc := hall _ hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
          reduceCtorEq, false_or] at hc
        obtain ⟨⟨hlt, hva⟩, hkd⟩ := hc
        rw [hk, Option.some.injEq] at hkd
        rw [← hpa] at hlt hva
        refine ⟨UInt64.toNat_inj.1 ?_, hlt, hkd⟩
        rw [direct_or hlt, hva]
    · obtain ⟨hw2, hv2, hb2⟩ := walk_ok_block.1 hw
      rcases walk2_ok.1 hw2 with ⟨-, h⟩ | ⟨t2, hv1, hc1, h⟩
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, hd⟩ := h
        subst hd
        have hmem : (v.toNat - index3 v * PAGE_SIZE, Form.block,
            sh.directMap.entry t2 (index2 v)) ∈ sh.directMap.leaves cfg.directBase :=
          mem_leaves.2 ⟨index1 v, index2 v, t2, h1, h2, hv1, hc1, hv2,
            Or.inl ⟨hb2, hrw, rfl, rfl, by simp only [Region.first]; omega⟩⟩
        have hc := hall _ hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
          true_or, and_true] at hc
        obtain ⟨hlt, hva⟩ := hc
        have hm := blockAddress_mod (sh.directMap.entry t2 (index2 v))
        have hpl : l.pa.toNat < VA_LIMIT := by
          rw [hpa]; simp only [VA_LIMIT, BLOCK_SIZE, GIB_SIZE, PAGE_SIZE, ENTRIES] at hlt hm hdec h1 h2 h3 ⊢
          omega
        refine ⟨UInt64.toNat_inj.1 ?_, hpl, hk⟩
        rw [direct_or hpl, hpa]
        simp only [VA_LIMIT, BLOCK_SIZE, GIB_SIZE, PAGE_SIZE, ENTRIES] at hlt hm hdec hva h1 h2 h3 ⊢
        omega
  · rintro hoff ⟨va, form, d⟩ hmem
    obtain ⟨i, j, t2, hi, hj, hv1, hc1, hv2, hcase⟩ := mem_leaves.1 hmem
    rcases hcase with ⟨hb, hrw, rfl, rfl, rfl⟩ | ⟨hb, t3, k, hc2, hk, rfl, hd3, hp, rfl, rfl⟩
    · obtain ⟨v, hvn⟩ := exists_upper hi hj (k := 0) (by decide)
      obtain ⟨hreg, hpg, e1, e2, -⟩ := upper_of_toNat hi hj (by decide) hvn
      subst e1 e2
      have hw : sh.directMap.walk cfg.directBase v =
          .ok (.block t2 (sh.directMap.entry t2 (index2 v))) :=
        walk_ok_block.2 ⟨walk2_ok.2 (Or.inr ⟨t2, hv1, hc1, rfl⟩), hv2, hb⟩
      have hpa : (blockAddress (sh.directMap.entry t2 (index2 v))).toNat =
          (blockAddress (sh.directMap.entry t2 (index2 v))).toNat + v.toNat % BLOCK_SIZE := by
        simp only [GIB_SIZE, BLOCK_SIZE, PAGE_SIZE, hD] at hvn ⊢; omega
      obtain ⟨hv, hlt, -⟩ := hoff v ⟨blockAddress (sh.directMap.entry t2 (index2 v)), .readWrite,
        .block⟩ ⟨hreg, hpg, Or.inr ⟨t2, _, hw, hrw, rfl, rfl, hpa⟩⟩
      have hvt := congrArg UInt64.toNat hv
      rw [direct_or hlt] at hvt
      simp only [Region.first, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        true_or, and_true]
      rw [Nat.zero_mul, Nat.add_zero] at hvn
      generalize DIRECT_BASE.toNat = D at hvn hvt ⊢
      exact ⟨hlt, hvn.symm.trans hvt⟩
    · obtain ⟨kd, hkd⟩ := Option.isSome_iff_exists.1 hp
      obtain ⟨v, hvn⟩ := exists_upper hi hj hk
      obtain ⟨hreg, hpg, e1, e2, e3⟩ := upper_of_toNat hi hj hk hvn
      subst e1 e2 e3
      have hw : sh.directMap.walk cfg.directBase v =
          .ok (.level3 t2 t3 (sh.directMap.entry t3 (index3 v))) :=
        walk_ok_level3.2 ⟨_, walk2_ok.2 (Or.inr ⟨t2, hv1, hc1, rfl⟩), hv2, hb, hc2, rfl⟩
      obtain ⟨hv, hlt, hkind⟩ := hoff v ⟨outputAddress (sh.directMap.entry t3 (index3 v)), kd, .page⟩
        ⟨hreg, hpg, Or.inl ⟨t2, t3, _, hw, hd3, hkd, rfl, rfl⟩⟩
      have hvt := congrArg UInt64.toNat hv
      rw [direct_or hlt] at hvt
      subst hkind
      simp only [Region.first, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        hkd, reduceCtorEq, false_or, and_true]
      generalize DIRECT_BASE.toNat = D at hvn hvt ⊢
      exact ⟨hlt, hvn.symm.trans hvt⟩

end Krepi.Proofs.PageTables.Checks
