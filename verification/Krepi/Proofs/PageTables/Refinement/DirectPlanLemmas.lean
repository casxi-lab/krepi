module

public import Krepi.Proofs.PageTables.Refinement.DirectLemmas
public import Krepi.Proofs.PageTables.Refinement.KernelPlanLemmas
public import Krepi.Proofs.PageTables.Refinement.DirectPlanSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the plan iterator of `direct_map` stands for its plan

The plan iterator that `direct_map` returns, `DirectMapPlan`, stands for the
plan `mapPlan` of `Tables.directMap`. Each call of `DirectMapPlan::next` is
one call of the cursor on numbers, `Cur.step`, with the leaf search
`directFind` of the saved state of the iterator of the usable ranges
(`direct_map_plan_next_spec`); while the cursor keeps `SearchK` and the
ranges that the state skipped end at or below its `lowB`, that search is the
search `usableFind` of all the usable ranges at every address the call reads
(`step_congr_find`); the leaves of the usable ranges that passed the checks
satisfy `SimOk` with that search (`direct_simOk`); and the simulation
`stands_mapPlan` (`Krepi.Proofs.PageTables.Refinement.PlanSimSpecLemmas`)
turns them into `Stands`.

- `direct_plan_next_spec`: `direct_map_plan_next_spec` and, when the 1 GiB
  slot of the cursor stays, the state of the search stays.
- `direct_map_start_spec`: `direct_map_set_spec`, and the set of the
  iterator is the set that `direct_map` returns.
- `direct_map_plan_stands`: from the success of `Tables.directMap` on a
  well-formed boot memory map and an iterator at its start
  (`DirectMapStart`) on a set whose record of tables in use is at or above
  that of the set before the write phase, `Stands DirectMapPlan.next
  StepRepr` of the plan, for a record of the set before the write phase at
  least 2 below the largest `usize`. It reads no bound of the count of the
  checks of the code.
- `direct_map_of_room`: the conclusion of the statement `DirectMap` for a
  record of the set with the room of `DirectRoom` (the premise of the checks
  of the code, `direct_map_set_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-- `DirectMapPlan::next()`: `direct_map_plan_next_spec`
(`Krepi.Proofs.PageTables.Refinement.DirectLemmas`), under the same premises,
and, when the 1 GiB slot of the cursor after the call is that of the cursor
before it, the iterator of the usable ranges and the current range of the
state stay (the code takes the state of the search only when the slot
changes). -/
theorem direct_plan_next_spec {N : Usize} (it : page_tables.DirectMapPlan N)
    (M Rs : List Krepi.Spec.Fdt.Span) (hN : 0 < N.val) (hM : ∀ b ∈ M, b.Valid)
    (hRs : ∀ r ∈ Rs, r.Nonempty) (hm : spansOf it.ranges.managed = M)
    (hr : spansOf it.ranges.reservations = Rs) (hok : SearchOk (searchList M Rs it.ranges it.range))
    (hcur : CurFits it.cursor it.base)
    (hs : it.cursor.phase = .NewPages → it.cursor.slot.val + 2 ^ 21 < 2 ^ 64)
    (hg : it.cursor.phase = .Children ∨ it.cursor.phase = .Entries →
      it.cursor.gib.val + 2 ^ 30 < 2 ^ 64)
    (hseek : ((curOf it.cursor).take (placeOr (tablesOf it.set) (word64 it.base)) (word64 it.base)
        (directFind M Rs it.ranges it.range (curOf it.cursor).search.1
          (curOf it.cursor).search.2.1 (curOf it.cursor).search.2.2)).1 = .seek →
      let c' := ((curOf it.cursor).take (placeOr (tablesOf it.set) (word64 it.base))
        (word64 it.base) (directFind M Rs it.ranges it.range (curOf it.cursor).search.1
          (curOf it.cursor).search.2.1 (curOf it.cursor).search.2.2)).2
      c'.next + 1 ≤ Usize.max ∧ c'.t2 + 1 ≤ Usize.max ∧ c'.gib + 2 ^ 30 < 2 ^ 64) :
    page_tables.boot.direct.DirectMapPlan.next it ⦃ o it' =>
      o.map stepOf = ((curOf it.cursor).step (directFind M Rs it.ranges it.range)
          (placeOr (tablesOf it.set) (word64 it.base)) (word64 it.base)).1 ∧
        curOf it'.cursor = ((curOf it.cursor).step (directFind M Rs it.ranges it.range)
          (placeOr (tablesOf it.set) (word64 it.base)) (word64 it.base)).2 ∧
        it'.set = it.set ∧ it'.base = it.base ∧
        spansOf it'.ranges.managed = M ∧ spansOf it'.ranges.reservations = Rs ∧
        (it'.cursor.gib = it.cursor.gib → it'.ranges = it.ranges ∧ it'.range = it.range) ∧
        ∃ skipped, searchList M Rs it.ranges it.range =
            skipped ++ searchList M Rs it'.ranges it'.range ∧
          ∀ u ∈ skipped, u.endNat ≤ it.cursor.from.val ⦄ := by
  have hv : ∀ u ∈ searchList M Rs it.ranges it.range, u.Valid := fun u hu => (hok u hu).1
  unfold page_tables.boot.direct.DirectMapPlan.next
  step*
  have hfv : «from».val = (curOf it.cursor).search.1 := by rw [← from_post]
  have hlv : limit.val = (curOf it.cursor).search.2.1 := by rw [← from_post]
  have hpv : pages = (curOf it.cursor).search.2.2 := by rw [← from_post]
  have hfrm : (curOf it.cursor).search.1 = it.cursor.from.val := cur_search_frm _
  refine WP.spec_bind (usable_leaf_spec it.ranges it.range «from» limit pages M Rs hM hRs hm hr hv) ?_
  rintro ⟨ar, rg, found⟩ ⟨ha1, ha2, hfound, skipped, hsk, hskb⟩
  obtain ⟨hfl, hfge⟩ := found_of_usableFind hok hfound
  have hfd : foundOf found = directFind M Rs it.ranges it.range (curOf it.cursor).search.1
      (curOf it.cursor).search.2.1 (curOf it.cursor).search.2.2 := by
    rw [hfound, hfv, hlv, hpv]; rfl
  refine WP.spec_bind (take_spec it.cursor it.set it.base found hN hfl hcur) ?_
  rintro ⟨mt, mc⟩ ⟨hmt, hmc⟩
  rw [hfd] at hmt hmc
  -- the state of the search after the call, and what it keeps
  obtain ⟨st, hst, hsm, hsr, hsl, hskp, hsame⟩ : ∃ st : (Slice fdt.Span × Slice fdt.Span ×
      fdt.Cursor × fdt.Span),
      (if (mc.gib != it.cursor.gib) = true then
          ok (ar.managed, ar.reservations, ar.cursor, rg)
        else ok (it.ranges.managed, it.ranges.reservations, it.ranges.cursor, it.range) :
          Result (Slice fdt.Span × Slice fdt.Span × fdt.Cursor × fdt.Span)) = ok st ∧
      spansOf st.1 = M ∧ spansOf st.2.1 = Rs ∧
      (∃ sk, searchList M Rs it.ranges it.range =
          sk ++ searchList M Rs ⟨st.1, st.2.1, st.2.2.1⟩ st.2.2.2 ∧
        ∀ u ∈ sk, u.endNat ≤ it.cursor.from.val) ∧
      (∀ f l p, it.cursor.from.val ≤ f →
        usableFind ((searchList M Rs ⟨st.1, st.2.1, st.2.2.1⟩ st.2.2.2).map spanView) f l p =
          directFind M Rs it.ranges it.range f l p) ∧
      (¬ (mc.gib != it.cursor.gib) = true →
        st = (it.ranges.managed, it.ranges.reservations, it.ranges.cursor, it.range)) := by
    by_cases hgc : (mc.gib != it.cursor.gib) = true
    · have hpf : pages = false := by
        cases hpg : pages
        · rfl
        · exfalso
          have := cur_take_gib (placeOr (tablesOf it.set) (word64 it.base)) (word64 it.base)
            (curOf it.cursor) (directFind M Rs it.ranges it.range (curOf it.cursor).search.1
              (curOf it.cursor).search.2.1 (curOf it.cursor).search.2.2) (by rw [← hpv, hpg])
          rw [← hmc] at this
          exact (u64_bne_iff _ _).1 hgc this
      have hb : ∀ u ∈ skipped, u.endNat ≤ it.cursor.from.val := by
        intro u hu; rw [← hfrm, ← hfv]; exact hskb hpf u hu
      refine ⟨(ar.managed, ar.reservations, ar.cursor, rg), by simp only [hgc, ↓reduceIte], ha1,
        ha2, ⟨skipped, hsk, hb⟩, ?_, fun h => absurd hgc h⟩
      intro f l p hf
      simp only [directFind]
      rw [hsk, List.map_append, usableFind_skip]
      intro r hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
      exact Nat.le_trans (hb u hu) hf
    · refine ⟨(it.ranges.managed, it.ranges.reservations, it.ranges.cursor, it.range),
        by simp only [hgc, Bool.false_eq_true, ↓reduceIte], hm, hr,
        ⟨[], rfl, fun u hu => absurd hu List.not_mem_nil⟩, fun f l p _ => rfl, fun _ => rfl⟩
  rw [uncurry_apply_pair, hst, bind_ok]
  obtain ⟨sm, sr, sc, sg⟩ := st
  simp only at hsm hsr hsl hskp
  simp only [Cur.step]
  cases mt with
  | Give stp =>
    refine spec_of_eq rfl ⟨?_, ?_, rfl, rfl, hsm, hsr, ?_, hsl⟩
    · rw [← hmt]; rfl
    · rw [← hmt]; exact hmc
    · intro hg
      have hs := hsame ((u64_not_bne_iff _ _).2
        (congrArg UScalar.val (show mc.gib = it.cursor.gib from hg)))
      simp only [Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
      exact ⟨rfl, rfl⟩
  | End =>
    refine spec_of_eq rfl ⟨?_, ?_, rfl, rfl, hsm, hsr, ?_, hsl⟩
    · rw [← hmt]; rfl
    · rw [← hmt]; exact hmc
    · intro hg
      have hs := hsame ((u64_not_bne_iff _ _).2
        (congrArg UScalar.val (show mc.gib = it.cursor.gib from hg)))
      simp only [Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
      exact ⟨rfl, rfl⟩
  | Seek =>
    obtain ⟨hn1, ht21, hgib⟩ := hseek hmt.symm
    obtain ⟨l0, hl0, hfr0, hph0⟩ := cur_take_seek _ _ _ _ hmt.symm
    rw [← hmc] at hn1 ht21 hgib hph0 hfr0
    have hmph : mc.phase = .Children := by
      cases h : mc.phase <;> simp only [curOf, phaseOf, h, reduceCtorEq] at hph0 ⊢
    have hs' : mc.phase = .NewPages → mc.slot.val + 2 ^ 21 < 2 ^ 64 := by
      intro h; rw [hmph] at h; cases h
    have hg' : mc.phase = .Children ∨ mc.phase = .Entries → mc.gib.val + 2 ^ 30 < 2 ^ 64 :=
      fun _ => hgib
    -- the search of the children starts at the leaf found, at or above the address
    have hge0 : it.cursor.from.val ≤ (curOf mc).search.1 := by
      rw [cur_search_frm, hfr0]
      obtain ⟨lf, hlf, hlv'⟩ : ∃ lf, found = some lf ∧ l0 = ⟨lf.pa.val, word64 lf.desc, lf.block⟩ := by
        rw [← hfd] at hl0
        cases hfo : found with
        | none => rw [hfo] at hl0; cases hl0
        | some lf =>
          rw [hfo] at hl0
          simp only [foundOf, Option.map_some, Option.some.injEq] at hl0
          exact ⟨lf, rfl, hl0.symm⟩
      rw [hlv']
      have := hfge lf hlf
      rw [hfv, hfrm] at this
      exact this
    step*
    have hfv1 : from1.val = (curOf mc).search.1 := by rw [← from1_post]
    have hlv1 : limit1.val = (curOf mc).search.2.1 := by rw [← from1_post]
    have hpv1 : pages1 = (curOf mc).search.2.2 := by rw [← from1_post]
    have hok2 : SearchOk (searchList M Rs ⟨sm, sr, sc⟩ sg) := by
      obtain ⟨sk, hsk2, -⟩ := hsl
      intro u hu
      exact hok u (by rw [hsk2]; exact List.mem_append_right _ hu)
    refine WP.spec_bind (usable_leaf_spec ⟨sm, sr, sc⟩ sg from1 limit1 pages1 M Rs hM hRs hsm hsr
      (fun u hu => (hok2 u hu).1)) ?_
    rintro ⟨ar1, rg1, found1⟩ ⟨_, _, hfound1, _⟩
    obtain ⟨hfl1, -⟩ := found_of_usableFind hok2 hfound1
    refine WP.spec_bind (children_spec mc found1 hfl1 hn1 ht21) ?_
    rintro ⟨st1, mc1⟩ ⟨hst1, hmc1⟩
    have hfd1 : foundOf found1 = directFind M Rs it.ranges it.range (curOf mc).search.1
        (curOf mc).search.2.1 (curOf mc).search.2.2 := by
      rw [hfound1, hfv1, hlv1, hpv1]
      exact hskp _ _ _ hge0
    rw [hfd1] at hst1 hmc1
    refine spec_of_eq rfl ⟨?_, ?_, rfl, rfl, hsm, hsr, ?_, hsl⟩
    · rw [← hmt, ← hmc]; simp only [turnOf, Option.map_some, hst1]
    · rw [← hmt, ← hmc]; exact hmc1
    · intro hg
      have hgm : mc1.gib.val = mc.gib.val := by
        have := congrArg Cur.gib hmc1
        rw [children_gib] at this
        exact this
      have hs := hsame ((u64_not_bne_iff _ _).2
        (by rw [← hgm]; exact congrArg UScalar.val (show mc1.gib = it.cursor.gib from hg)))
      simp only [Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
      exact ⟨rfl, rfl⟩

/-- `direct_map(set, memory, base, bits)`: `direct_map_set_spec`
(`Krepi.Proofs.PageTables.Refinement.DirectLemmas`), for a map that stands
for a boot memory map that the fdt entries built and a record of the set with
the room of `DirectRoom`, and on success the set of the iterator is the set
that `direct_map` returns. -/
theorem direct_map_start_spec {N : Usize} (s : page_tables.Tables N true) (memory : fdt.MemoryPlan)
    (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8) (hP : MemoryPlanRepr memory P)
    (hB : Witnesses.TableSets.BuiltPlan P) (hov : DirectRoom s.used.val) :
    page_tables.direct_map s memory base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (fun it _ => DirectMapStart s P base it)
        (tableErrorOf · = ·) s r s' ((tablesOf s).directMap P (word64 base) (byte bits)) ∧
        ∀ it, r = .Ok it → it.set = s' ⦄ := by
  have hw := builtPlan_wellFormed hB
  obtain ⟨hne, hpw, hlen⟩ := usable_wf hw
  have hsorted := usable_sorted hw
  obtain ⟨hml, hrl⟩ := memoryPlanRepr_lengths hP
  have hlen' : P.availableRanges.length ≤ 164 := by omega
  have hM : ∀ b ∈ P.managed, b.Valid := fun b hb => (hw.2.2.2.2.2.2.1 b hb).1.2
  have hRs : ∀ r ∈ P.reservations, r.Nonempty :=
    fun r hr => (Krepi.Proofs.Fdt.reservations_wf hw r hr).1
  have hUs : ∀ u ∈ P.availableRanges, u.Valid := fun u hu => (hne u hu).1.2
  unfold page_tables.direct_map
  step*
  · have hp : checkPool N.val (word64 base) (byte bits) = .ok () := by
      obtain ⟨u, hu, -⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post); rw [hu]
    obtain ⟨hwd, hpf⟩ := checkPool_ok_facts hp
    have hN : 0 < N.val := Nat.pos_of_ne_zero ((poolFits_iff _ _ _).1 hpf).1
    have hb : bits.val < 64 := lt_64_of_widthOk hwd
    have hstart : availableFrom P.managed P.reservations ar.cursor.bank.val ar.cursor.at.val =
        P.availableRanges := by
      rw [ar_post2, ar_post3, availableRanges_eq]
    have hcu := check_usable_spec s ar base bits P.managed P.reservations P.availableRanges hN hb
      hM hRs hUs hpw hlen' hov ar_post ar_post1 hstart
    refine WP.spec_bind hcu ?_
    intro r1 hr1
    step*
    · obtain ⟨⟨earlier, leaves⟩, -, hrel⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› hr1)
      exact hrel.2.2.2
    · obtain ⟨⟨earlier, leaves⟩, hy, hrel⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› hr1)
      have hnext : (allocOf s.used.val leaves).next = val.next.val := hrel.2.1.1
      rw [directMap_fold_ok (s := tablesOf s) hp (by rw [hsorted]; exact hy), tablesOf_used, hnext]
      have hr2 := branch_ok cf2_post ‹_›
      by_cases hcond : N.val - s.used.val < val.next.val - s.used.val
      · simp only [hcond, ↓reduceIte] at r2_post
        rw [hr2] at r2_post
        cases r2_post.1
      · simp only [hcond, ↓reduceIte] at r2_post ⊢
        rw [hr2] at r2_post
        obtain ⟨hv1, hs1⟩ := r2_post
        cases hv1
        refine ⟨⟨⟨by rw [hs1], rfl, rfl, ar_post, ar_post1, ar_post2, ar_post3, rfl, rfl⟩, ?_⟩,
          fun it h => by cases h; rfl⟩
        rw [hs1]
        rfl
    · obtain ⟨⟨earlier, leaves⟩, hy, hrel⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› hr1)
      have hnext : (allocOf s.used.val leaves).next = val.next.val := hrel.2.1.1
      rw [directMap_fold_ok (s := tablesOf s) hp (by rw [hsorted]; exact hy), tablesOf_used, hnext]
      have hr2 := branch_err cf2_post ‹_› residual_post
      by_cases hcond : N.val - s.used.val < val.next.val - s.used.val
      · simp only [hcond, ↓reduceIte] at r2_post ⊢
        rw [hr2] at r2_post
        obtain ⟨he, hs1⟩ := r2_post
        cases he
        refine ⟨?_, fun it h => by rw [r3_post] at h; cases h⟩
        rw [r3_post, ← e_post, hs1]
        exact ⟨rfl, rfl⟩
      · simp only [hcond, ↓reduceIte] at r2_post
        rw [hr2] at r2_post
        cases r2_post.1
    · refine ⟨?_, fun it h => by rw [r2_post] at h; cases h⟩
      rw [directMap_fold_error (s := tablesOf s) hp
        (by rw [hsorted]; exact agrees_err_of_branch cf1_post ‹_› residual_post hr1), r2_post,
        e_post]
      exact ⟨rfl, rfl⟩
  · refine ⟨?_, fun it h => by rw [r1_post] at h; cases h⟩
    rw [directMap_pool_error (s := tablesOf s)
      (agrees_err_of_branch cf_post ‹_› residual_post r_post), r1_post, e_post]
    exact ⟨rfl, rfl⟩

/-- **The plan iterator of `direct_map` stands for its plan.** For a
well-formed boot memory map `P`, a success of `Tables.directMap` with the
plan `plan`, and an iterator at its start (`DirectMapStart`) whose set has a
record of tables in use at or above that of the set before the write phase
(the set that `direct_map` returns has the record after it),
`DirectMapPlan::next` stands for `plan`, for a record of the set before the
write phase at least 2 below the largest `usize` (the cursor lemmas of the
code ask for room for two more tables at each call, even where a call takes
none). -/
theorem direct_map_plan_stands (hU : Usize64) {N : Usize} (s : page_tables.Tables N true)
    (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8) (hw : P.WellFormed)
    {S : Tables .upper N.val} {plan : Plan}
    (hd : (tablesOf s).directMap P (word64 base) (byte bits) = .ok (S, plan))
    (it : page_tables.DirectMapPlan N) (hstart : DirectMapStart s P base it)
    (hused : s.used.val ≤ it.set.used.val) (hroom : s.used.val + 2 ≤ Usize.max) :
    Stands page_tables.boot.direct.DirectMapPlan.next StepRepr it plan := by
  have hmax := usize_max hU
  have hsl0 := searchList_start hstart
  obtain ⟨hpool, hbase, hcur, hm0, hr0, -, -, -, -⟩ := hstart
  obtain ⟨-, hpw, -⟩ := usable_wf hw
  have hsorted := usable_sorted hw
  have hUs := usable_ranges_ok hw
  have hlow := directMap_ok_low hw hd
  have hok0 := searchOk_start hw hd
  have hM : ∀ b ∈ P.managed, b.Valid := fun b hb => (hw.2.2.2.2.2.2.1 b hb).1.2
  have hRs : ∀ r ∈ P.reservations, r.Nonempty :=
    fun r hr => (Krepi.Proofs.Fdt.reservations_wf hw r hr).1
  -- the specification: the checks pass, and the plan is `mapPlan` of the placed leaves
  cases hp : checkPool N.val (word64 base) (byte bits) with
  | error x => rw [directMap_pool_error (s := tablesOf s) hp] at hd; cases hd
  | ok u =>
  cases u
  cases hfo : (sortByKey (·.start.toNat) P.availableRanges).foldlM
      ((tablesOf s).checkUsableRange (word64 base) (byte bits)) ([], []) with
  | error x => rw [directMap_fold_error (s := tablesOf s) hp hfo] at hd; cases hd
  | ok res =>
  obtain ⟨earlier, leaves⟩ := res
  rw [directMap_fold_ok (s := tablesOf s) hp hfo, tablesOf_used] at hd
  have hassign1 : (assignTables s.used.val leaves.reverse).1 = (allocOf s.used.val leaves).next := rfl
  have hassign2 : (assignTables s.used.val leaves.reverse).2 =
      (allocOf s.used.val leaves).placed.reverse := rfl
  split at hd
  · cases hd
  · rename_i hfit
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨-, hplan⟩ := hd
    rw [← hassign1] at hfit
    rw [← hassign2] at hplan
    subst hplan
    -- the pool
    obtain ⟨hwd, hpf⟩ := checkPool_ok_facts hp
    obtain ⟨hN0, hfits⟩ := (poolFits_iff _ _ _).1 hpf
    have hb := (widthOk_byte_iff bits).1 hwd
    rw [word64_toNat, byte_toNat] at hfits
    have h48 : 2 ^ bits.val ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hb.2
    have hN : 0 < N.val := Nat.pos_of_ne_zero hN0
    simp only [PAGE_SIZE] at hfits
    -- the leaves
    rw [hsorted] at hfo
    obtain ⟨new, hnew, hmap, hplace⟩ := direct_fold (tablesOf s) (word64 base) (byte bits)
      P.availableRanges [] [] (earlier, leaves) hfo
    simp only [List.append_nil] at hnew
    subst hnew
    have hplace' : ∀ x ∈ leaves.reverse, (tablesOf s).place (word64 base) x.1 = .ok x.2 :=
      fun x hx => hplace x (List.mem_reverse.1 hx)
    have hset : tablesOf it.set =
        ({ tablesOf s with used := it.set.used.val } : Tables .upper N.val) := by
      show (⟨poolOf it.set.pool, it.set.used.val⟩ : Tables .upper N.val) =
        ⟨poolOf s.pool, it.set.used.val⟩
      rw [hpool]
    have hSim := direct_simOk hmap hplace' hUs hlow hpw (u' := it.set.used.val)
      (by rw [tablesOf_used]; exact hused)
    rw [← hset, ← hbase] at hSim
    set NX := (assignTables s.used.val leaves.reverse).1 with hNX
    have hnewTT : s.used.val < NX → NX ≤ N.val := fun h => by omega
    have hNXroom : NX + 2 ≤ Usize.max := by
      by_cases h : s.used.val < NX
      · have := hnewTT h; rw [hmax]; omega
      · have : s.used.val ≤ NX := by
          rw [hNX, assignTables_eq]
          exact next_le_stOf leaves.reverse ⟨s.used.val, none, none, []⟩
        omega
    rw [← hbase]
    refine stands_mapPlan (abs := fun it' => curOf it'.cursor)
      (Inv := fun it' => it'.set = it.set ∧ it'.base = it.base ∧
        spansOf it'.ranges.managed = P.managed ∧ spansOf it'.ranges.reservations = P.reservations ∧
        SearchK (curOf it'.cursor) ∧
        ∃ sk, (⟨0, 0⟩ :: P.availableRanges : List Krepi.Spec.Fdt.Span) =
            sk ++ searchList P.managed P.reservations it'.ranges it'.range ∧
          ∀ u ∈ sk, u.endNat ≤ lowB (curOf it'.cursor))
      hSim s.used.val N.val (fun x hx => placeLe_of_place (hplace' x hx)) hnewTT ?_ it
      ⟨rfl, rfl, hm0, hr0, ?_, [], by rw [hsl0]; rfl, fun u hu => absurd hu List.not_mem_nil⟩ ?_
    · rintro it' ⟨h1, h2, hm', hr', hK, sk, hsk, hskb⟩ hbd
      obtain ⟨⟨hbn, hbt2, hbt3, hbslot, hbgib⟩, L, hsp⟩ := hbd
      have hok : SearchOk (searchList P.managed P.reservations it'.ranges it'.range) :=
        fun u hu => hok0 u (by rw [hsk]; exact List.mem_append_right _ hu)
      have hfo' := findOk_of_split hSim hsp
      have hlowc := searchK_low hK
      have hfind : ∀ f l p, lowB (curOf it'.cursor) ≤ f →
          directFind P.managed P.reservations it'.ranges it'.range f l p =
            usableFind (P.availableRanges.map spanView) f l p :=
        fun f l p hf => directFind_eq_of_skip hsk hskb f l p hf
      have hstep : ∀ (pl : Found → Place) (b : UInt64),
          (curOf it'.cursor).step (directFind P.managed P.reservations it'.ranges it'.range) pl b =
            (curOf it'.cursor).step (fun f l p => usableFind (P.availableRanges.map spanView) f l p)
              pl b :=
        fun pl b => step_congr_find hlowc (fun l p f hf => (hfo' l p f hf).1) hfind
      have hcur' : CurFits it'.cursor it'.base := by
        refine ⟨by simp only [curOf] at hbn; omega, by simp only [curOf] at hbt2; rw [hmax]; omega,
          by simp only [curOf] at hbt3; rw [hmax]; omega, ?_, ?_, ?_, ?_⟩
        · rw [h2, hbase]; simp only [curOf] at hbt2
          have := Nat.mul_le_mul_left 4096 hbt2; omega
        · rw [h2, hbase]; simp only [curOf] at hbt3
          have := Nat.mul_le_mul_left 4096 hbt3; omega
        · intro hph
          have := hbslot (Or.inr (by simp only [curOf, phaseOf, hph]))
          simp only [curOf] at this; omega
        · intro hph
          have := hbgib (Or.inr (Or.inr (by simp only [curOf, phaseOf, hph])))
          simp only [curOf] at this; omega
      have hs' : it'.cursor.phase = .NewPages → it'.cursor.slot.val + 2 ^ 21 < 2 ^ 64 := by
        intro hph
        have := hbslot (Or.inl (by simp only [curOf, phaseOf, hph]))
        simp only [curOf] at this; omega
      have hg' : it'.cursor.phase = .Children ∨ it'.cursor.phase = .Entries →
          it'.cursor.gib.val + 2 ^ 30 < 2 ^ 64 := by
        intro hph
        have := hbgib (by rcases hph with hph | hph <;> simp only [curOf, phaseOf, hph] <;> simp)
        simp only [curOf] at this; omega
      have hspec := direct_plan_next_spec it' P.managed P.reservations hN hM hRs hm' hr' hok hcur'
        hs' hg' (fun hseek => by
          have hfe := hfind (curOf it'.cursor).search.1 (curOf it'.cursor).search.2.1
            (curOf it'.cursor).search.2.2 (by rw [cur_search_frm]; exact hlowc)
          simp only [hfe] at hseek ⊢
          obtain ⟨f, hf, hc'⟩ := take_seek _ _ hseek
          have hfl : f.pa < 2 ^ 39 :=
            (hfo' _ _ f (by rw [← cur_search_frm]; exact hf)).2.2.1
          rw [hc']
          refine ⟨?_, ?_, ?_⟩
          · show it'.cursor.next.val + 1 + 1 ≤ Usize.max
            simp only [curOf] at hbn; omega
          · show it'.cursor.next.val + 1 ≤ Usize.max
            simp only [curOf] at hbn; omega
          · show gibOf f.pa + 2 ^ 30 < 2 ^ 64
            simp only [gibOf, GIB_SIZE]; omega)
      rw [h1, h2, hstep] at hspec
      refine spec_mono hspec ?_
      rintro ⟨o, it''⟩ ⟨ho, hcur'', e1, e2, em, er, hframe, skipped, hsk2, hskb2⟩
      obtain ⟨hK2, hK3⟩ := searchK_step (base := word64 it.base) hSim hK hsp
      have hK2' : SearchK (curOf it''.cursor) := by rw [hcur'']; exact hK2
      have hK3' : (curOf it''.cursor).gib ≠ (curOf it'.cursor).gib →
          (curOf it'.cursor).frm ≤ lowB (curOf it''.cursor) := by rw [hcur'']; exact hK3
      have hfix : curOf it''.cursor = curOf it'.cursor → it'' = it' := by
        intro hcc
        have hcc' := curOf_inj hcc
        obtain ⟨hr1, hr2⟩ := hframe (by rw [hcc'])
        obtain ⟨a1, a2, a3, a4, a5⟩ := it''
        obtain ⟨b1, b2, b3, b4, b5⟩ := it'
        simp only at e1 e2 hcc' h1 h2 hr1 hr2
        simp only [page_tables.DirectMapPlan.mk.injEq]
        exact ⟨e1.trans h1.symm, e2.trans h2.symm, hcc', hr1, hr2⟩
      refine ⟨optionRel_stepRepr ho, hcur'', ⟨e1, e2, em, er, hK2', ?_⟩, hfix⟩
      by_cases hgc : it''.cursor.gib = it'.cursor.gib
      · obtain ⟨hr1, hr2⟩ := hframe hgc
        have hlb : lowB (curOf it''.cursor) = lowB (curOf it'.cursor) := by
          unfold lowB curOf; rw [hgc]
        exact ⟨sk, by rw [hr1, hr2]; exact hsk, fun u hu => by rw [hlb]; exact hskb u hu⟩
      · have hgc' : (curOf it''.cursor).gib ≠ (curOf it'.cursor).gib :=
          fun h => hgc (UScalar.eq_of_val_eq h)
        have hle := hK3' hgc'
        refine ⟨sk ++ skipped, by rw [hsk, hsk2, List.append_assoc], fun u hu => ?_⟩
        rcases List.mem_append.1 hu with hu | hu
        · exact Nat.le_trans (hskb u hu) (Nat.le_trans hlowc hle)
        · exact Nat.le_trans (hskb2 u hu) hle
    · rw [hcur]
      simp only [curOf, startCursor, phaseOf, no_slot_val]
      exact searchK_start _
    · rw [hcur]
      simp only [curOf, startCursor, phaseOf, no_slot_val]
      rfl

/-- **`DirectMap` for a record with room.** The conclusion of the statement
`DirectMap` for a map that stands for a boot memory map that the fdt entries
built and a set whose record of tables in use has the room of `DirectRoom`
(at least `2 ^ 28` below the largest `usize`). That premise, the one of the
checks of the code (`direct_map_set_spec`), is the only one added to those
of the statement. -/
theorem direct_map_of_room (hU : Usize64) {N : Usize} (s : page_tables.Tables N true)
    (memory : fdt.MemoryPlan) (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8)
    (hP : MemoryPlanRepr memory P) (hB : Witnesses.TableSets.BuiltPlan P)
    (hov : DirectRoom s.used.val) :
    page_tables.direct_map s memory base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S)
        (Stands page_tables.boot.direct.DirectMapPlan.next StepRepr)
        (tableErrorOf · = ·) s r s' ((tablesOf s).directMap P (word64 base) (byte bits)) ⦄ := by
  refine spec_mono (direct_map_start_spec s memory P base bits hP hB hov) ?_
  rintro ⟨r, s'⟩ ⟨hw, hset⟩
  cases hk : (tablesOf s).directMap P (word64 base) (byte bits) with
  | error e =>
    rw [hk] at hw
    cases r with
    | Ok it => exact hw.elim
    | Err x => exact hw
  | ok tp =>
    obtain ⟨S, plan⟩ := tp
    rw [hk] at hw
    cases r with
    | Err x => exact hw.elim
    | Ok it =>
      obtain ⟨hstart, hrepr⟩ := hw
      have hs' := hset it rfl
      have hle := directMap_used_le hk
      have hroom : s.used.val + 2 ≤ Usize.max := by unfold DirectRoom at hov; omega
      refine ⟨direct_map_plan_stands hU s P base bits (builtPlan_wellFormed hB) hk it hstart ?_
        hroom, hrepr⟩
      rw [hs']
      show (tablesOf s).used ≤ (tablesOf s').used
      rw [hrepr]
      exact hle

end Krepi.Proofs.PageTables.Refinement
