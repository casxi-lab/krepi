module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.EntryLemmas

/-!
# Page tables: proofs about the well-formedness of table sets

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the well-formedness of table sets,
whose type is exactly that statement: that `Tables::new` on zero storage and
the kernel tables that `kernel_map` and `direct_map` write into such sets
are well-formed, and that each write entry of a set keeps a set well-formed.

The theorems about `Tables::new`, `reset`, `map_page`, `map_block` and
`unmap_page` are proved: each write is put together from the elementary
changes of `Krepi.Proofs.PageTables.WellFormedLemmas`, a link of a new table
and a leaf in a free entry, and the pool after its plan is shown equal to
that of those changes. The other theorems are still planned: their proof is
`sorry`, and `verification/statements.json` registers them as `planned`.
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Tables

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok)

public theorem newWellFormed : NewWellFormed := by
  intro r N base bits hp
  exact wf_zero hp (fun t i => by simp [Tables.new, Pool.zero, Pool.get, Table.zero]) rfl

public theorem bootKernelMapWellFormed : BootKernelMapWellFormed := by
  sorry

public theorem bootDirectMapWellFormed : BootDirectMapWellFormed := by
  sorry

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

public theorem cloneKernelFromWellFormed : CloneKernelFromWellFormed := by
  sorry

public theorem mapPageWellFormed : MapPageWellFormed := by
  intro r N s v p k base bits s' plan hs h
  unfold Tables.mapPage at h
  obtain ⟨u1, hce, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hcp, h⟩ := except_bind_ok.1 h
  obtain ⟨w, hw, h⟩ := except_bind_ok.1 h
  have hp := hs.2.1
  have hpool := hs.1
  have hpb := (checkPhysical_ok.1 hcp).2
  have hgood : (∃ k', descriptor k p = descriptor k' (outputAddress (descriptor k p))) ∧
      (outputAddress (descriptor k p)).toNat < 2 ^ bits.toNat :=
    ⟨⟨k, by rw [outputAddress_descriptor, descriptor_outputAddress]⟩, by
      rw [outputAddress_descriptor]; exact Nat.lt_of_le_of_lt (outputAddress_le p) hpb⟩
  have hnew : isPlainTableDescriptor (descriptor k p) = false := isPlain_descriptor k p
  have hfresh : ∀ t i, s.used ≤ t → s.pool.get t i = 0 := fun t i ht => by
    rw [← entry_eq_get]; exact wf_entry_free hs ht i
  have i1 := index1_lt v
  have i2 := index2_lt v
  have i3 := index3_lt v
  rcases w with _ | ⟨t2, e2⟩
  · obtain ⟨hlt, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hu : s.used + 1 < N := by omega
    have hu0 : s.used ≠ 0 := by omega
    have hs1 := wf_link hs (Or.inl rfl) i1 (wf_walk2_none hs hw) (by omega)
    have hp1 := link_pointsAt (s := s) hpool (show 0 < N by omega) i1 (by omega)
    have h01 : (⟨s.pool.store 0 (index1 v) (tableAt base s.used), s.used + 1⟩ : Tables r N).entry
        s.used (index2 v) = 0 := by
      rw [entry_store (by omega) i1, ite_of_neg (by omega), wf_entry_free hs (Nat.le_refl _)]
    have hs2 := wf_link hs1 (Or.inr ⟨_, hp1⟩) i2 h01 hu
    have hp2 := link_pointsAt
      (s := (⟨s.pool.store 0 (index1 v) (tableAt base s.used), s.used + 1⟩ : Tables r N)) hpool (show s.used < N by omega) i2 hu
    have hl2 := pointsAt_store_of_ne (d := tableAt base (s.used + 1)) (show s.used < N by omega) i2
      (Nat.le_succ _) hp1 (by omega)
    have hold : isPlainTableDescriptor ((⟨(s.pool.store 0 (index1 v) (tableAt base s.used)).store
        s.used (index2 v) (tableAt base (s.used + 1)), s.used + 1 + 1⟩ : Tables r N).entry
        (s.used + 1) (index3 v)) = false := by
      rw [entry_eq_get, get_store, get_store, ite_of_neg (by omega), ite_of_neg (by omega),
        hfresh _ _ (by omega)]
      decide
    have hs3 := wf_setLeaf hs2 (t := s.used + 1) (by omega) (Nat.lt_succ_self _) i3 hold hnew
      (fun h2 => absurd (wf_not_level2_level3 hs2 h2 ⟨_, _, ⟨_, hl2⟩, hp2⟩) id)
      (fun _ => Or.inr hgood)
    have heq : ({ s with used := s.used + 2 } : Tables r N).apply
        [Step.zero (s.used + 1), Step.store (s.used + 1) (index3 v) (descriptor k p),
          Step.zero s.used,
          Step.store s.used (index2 v) (tableDescriptor (tableAddress base (s.used + 1))),
          Step.fence, Step.store 0 (index1 v) (tableDescriptor (tableAddress base s.used)),
          Step.sync] =
        ⟨((s.pool.store 0 (index1 v) (tableAt base s.used)).store s.used (index2 v)
          (tableAt base (s.used + 1))).store (s.used + 1) (index3 v) (descriptor k p),
          s.used + 1 + 1⟩ := by
      simp only [Tables.apply, Tables.mk.injEq, and_true]
      apply pool_ext; intro t i ht hi
      rw [get_exec _ _ ht hi]
      simp only [lastAt, stepAt, get_store, tableAt]
      by_cases ha : t = s.used + 1
      · subst ha
        by_cases hb : i = index3 v
        · subst hb; simp [i3, ht]
        · simp [hb, Ne.symm hb, hfresh]
      · by_cases hb : t = s.used
        · subst hb
          by_cases hc : i = index2 v
          · subst hc; simp [Ne.symm hu0, i2, ht]
          · simp [hc, Ne.symm hc, hfresh, hu0, Ne.symm hu0]
        · by_cases hz0 : t = 0
          · subst hz0
            by_cases hc : i = index1 v
            · subst hc; simp [ht, hi, hu0, Ne.symm hu0]
            · simp [hc, Ne.symm hc, hu0, Ne.symm hu0]
          · simp [ha, Ne.symm ha, hb, Ne.symm hb, hz0, Ne.symm hz0]
    rw [heq]; exact hs3
  · obtain ⟨-, h2, rfl⟩ := wf_walk2_some hs hw
    have ht2 := wf_level2_ne_zero hs h2
    have ht2u := (wf_level2_lt h2).1
    dsimp only at h
    split at h
    · rename_i hv
      obtain ⟨hlt, h⟩ := except_jp_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hu : s.used < N := by omega
      have h0 := wf_level2_invalid hs h2 i2 (by simpa using hv)
      have hs1 := wf_link hs (Or.inr h2) i2 h0 hu
      have hp1 := link_pointsAt (s := s) hpool (show t2 < N by omega) i2 hu
      obtain ⟨j, hj⟩ := h2
      have hl1 := pointsAt_store_of_ne (d := tableAt base s.used) (show t2 < N by omega) i2
        (Nat.le_succ _) hj (by omega)
      have hold : isPlainTableDescriptor ((⟨s.pool.store t2 (index2 v) (tableAt base s.used),
          s.used + 1⟩ : Tables r N).entry s.used (index3 v)) = false := by
        rw [entry_store (by omega) i2, ite_of_neg (by omega), wf_entry_free hs (Nat.le_refl _)]
        decide
      have hs2 := wf_setLeaf hs1 (by omega) (Nat.lt_succ_self _) i3 hold hnew
        (fun h2 => absurd (wf_not_level2_level3 hs1 h2 ⟨_, _, ⟨_, hl1⟩, hp1⟩) id)
        (fun _ => Or.inr hgood)
      have heq : ({ s with used := s.used + 1 } : Tables r N).apply
          [Step.zero s.used, Step.store s.used (index3 v) (descriptor k p), Step.fence,
            Step.store t2 (index2 v) (tableDescriptor (tableAddress base s.used)), Step.sync] =
          ⟨(s.pool.store t2 (index2 v) (tableAt base s.used)).store s.used (index3 v)
            (descriptor k p), s.used + 1⟩ := by
        simp only [Tables.apply, Tables.mk.injEq, and_true]
        apply pool_ext; intro t i ht hi
        rw [get_exec _ _ ht hi]
        simp only [lastAt, stepAt, get_store, tableAt]
        have hne : t2 ≠ s.used := by omega
        by_cases ha : t = s.used
        · subst ha
          by_cases hb : i = index3 v
          · subst hb; simp [i3, ht, hne]
          · simp [hb, Ne.symm hb, hfresh, hne, Ne.symm hne]
        · by_cases hb : t = t2
          · subst hb
            by_cases hc : i = index2 v
            · subst hc; simp [ht, hi, hne, Ne.symm hne]
            · simp [hc, Ne.symm hc, hne, Ne.symm hne]
          · simp [ha, Ne.symm ha, hb, Ne.symm hb]
      rw [heq]; exact hs2
    · rename_i hv
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hb
        split at h
        next t3 hc =>
          split at h
          next => simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
          next hv3 =>
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨-, h3⟩ := wf_level2_table hs h2 i2 (by simpa using hv) (by simpa using hb) hc
            have h0 := wf_level3_invalid hs h3 i3 (by simpa using hv3)
            exact wf_setLeaf hs (wf_level3_ne_zero hs h3) (wf_level3_lt h3).1 i3
              (by rw [h0]; decide) hnew (fun h2 => absurd (wf_not_level2_level3 hs h2 h3) id)
              (fun _ => Or.inr hgood)
        next => simp [throw, throwThe, MonadExceptOf.throw] at h

public theorem mapBlockWellFormed : MapBlockWellFormed := by
  intro r N s v p base bits s' plan hs h
  unfold Tables.mapBlock at h
  obtain ⟨u1, hce, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hcp, h⟩ := except_bind_ok.1 h
  obtain ⟨w, hw, h⟩ := except_bind_ok.1 h
  have hp := hs.1
  have hpb := (checkPhysical_ok.1 hcp).2
  have hgood : isReadWriteBlock (blockDescriptor p) = true ∧
      (blockAddress (blockDescriptor p)).toNat < 2 ^ bits.toNat :=
    ⟨isReadWriteBlock_blockDescriptor p, by
      rw [blockAddress_blockDescriptor]; exact Nat.lt_of_le_of_lt (blockAddress_le p) hpb⟩
  have hnew : isPlainTableDescriptor (blockDescriptor p) = false :=
    isPlain_of_isReadWriteBlock hgood.1
  rcases w with _ | ⟨t2, e2⟩
  · obtain ⟨hlt, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hu : s.used < N := by omega
    have h1 := hs.2.1
    have hfresh : ∀ i, s.pool.get s.used i = 0 := fun i => by
      rw [← entry_eq_get]; exact wf_entry_free hs (Nat.le_refl _) i
    have hs1 := wf_link hs (Or.inl rfl) (index1_lt v) (wf_walk2_none hs hw) hu
    have hl1 := link_pointsAt (s := s) hp (show 0 < N by omega) (index1_lt v) hu
    have hold : isPlainTableDescriptor ((⟨s.pool.store 0 (index1 v) (tableAt base s.used),
        s.used + 1⟩ : Tables r N).entry s.used (index2 v)) = false := by
      rw [entry_store (by omega) (index1_lt v), ite_of_neg (by omega),
        wf_entry_free hs (Nat.le_refl _)]
      decide
    have hs2 := wf_setLeaf hs1 (by omega) (Nat.lt_succ_self _) (index2_lt v) hold hnew
      (fun _ => Or.inr hgood) (fun h3 => absurd (wf_not_level2_level3 hs1 ⟨_, hl1⟩ h3) id)
    have heq : ({ s with used := s.used + 1 } : Tables r N).apply
        [Step.zero s.used, Step.store s.used (index2 v) (blockDescriptor p), Step.fence,
          Step.store 0 (index1 v) (tableDescriptor (tableAddress base s.used)), Step.sync] =
        ⟨(s.pool.store 0 (index1 v) (tableAt base s.used)).store s.used (index2 v)
          (blockDescriptor p), s.used + 1⟩ := by
      simp only [Tables.apply, Tables.mk.injEq, and_true]
      apply pool_ext; intro t i ht hi
      rw [get_exec _ _ ht hi]
      simp only [lastAt, stepAt, get_store, tableAt]
      have hu0 : s.used ≠ 0 := by omega
      by_cases ha : t = s.used
      · subst ha
        by_cases hb : i = index2 v
        · subst hb; simp [Ne.symm hu0, index2_lt, ht]
        · simp [hb, Ne.symm hb, hfresh, hu0, Ne.symm hu0]
      · by_cases hz0 : t = 0
        · subst hz0
          by_cases hb : i = index1 v
          · subst hb; simp [ha, Ne.symm ha, ht, hi]
          · simp [ha, Ne.symm ha, hb, Ne.symm hb]
        · simp [ha, Ne.symm ha, hz0, Ne.symm hz0]
    rw [heq]; exact hs2
  · obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨hv, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, h2, rfl⟩ := wf_walk2_some hs hw
    have h0 := wf_level2_invalid hs h2 (index2_lt v) (by simpa using hv)
    exact wf_setLeaf hs (wf_level2_ne_zero hs h2) (wf_level2_lt h2).1 (index2_lt v)
      (by rw [h0]; decide) hnew (fun _ => Or.inr hgood)
      (fun h3 => absurd (wf_not_level2_level3 hs h2 h3) id)

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
  sorry

public theorem directMapWellFormed : DirectMapWellFormed := by
  sorry

end Krepi.Proofs.PageTables.Tables
