module

public import Krepi.Statements.PageTables.Boot
public import Krepi.Proofs.PageTables.Refinement.CursorLemmas
public import Krepi.Proofs.PageTables.Refinement.FdtQueryLemmas
public import Krepi.Proofs.PageTables.Refinement.DirectSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the checks and the plan of the direct map

The triples of the generated functions of `boot/direct.rs` and of
`direct_map`, each against the checks of `Tables.directMap` or the leaf
search of its plan.

- The leaves of a usable range: `leaf_at_spec` (`leaf_at`, the leaf of
  `directLeaf`) and `range_leaf_spec` (`range_leaf`, `rangeFind`).
- The checks of the leaves of a range: `UsableRel` (what the record of the
  checks holds against the leaves that passed), `checkPlace_leaf` (the check
  of `check_leaf` on a leaf is the free-slot check of the leaf of the
  specification) and `check_leaves_loop_spec`.
- The checks of a range and of the usable ranges:
  `checkUsableRange_tablesOf`, `direct_check_range_spec`
  (`Tables.checkUsableRange`), `check_usable_loop_spec` and
  `check_usable_spec` (the fold of `Tables.checkUsableRange` over the usable
  ranges that the iterator of the boot memory map gives).
- `DirectRoom` (the one premise on the record of the set that the count of
  new tables of the code needs), `DirectMapStart`, `memoryPlanRepr_lengths`
  and `direct_map_set_spec`: `direct_map` gives the error of
  `Tables.directMap` with the set unchanged, or its set after the write phase
  and a plan iterator at its start, for a boot memory map that the fdt
  entries built.
- The leaf search of the plan: `searchList` (the ranges of a state of the
  search), `usable_leaf_loop_spec` and `usable_leaf_spec` (`usableFind` of
  those ranges; the ranges of the state where the search stopped are a
  suffix of them), `directFind`, `SearchOk`, `found_of_usableFind`, and
  `direct_map_plan_next_spec` (`DirectMapPlan::next` is one `Cur.step` with
  the search `directFind` of its state).
- The search from the start of the plan: `searchList_start`,
  `directFind_eq_of_skip`, `searchOk_start` and `directFind_eq_firstFound`
  (the search of a state is the first leaf at or above an address of
  `usableLeaves` of the usable ranges).
- `direct_map_of_stands`: the conclusion of the statement `DirectMap` for an
  input with the room of `DirectRoom`, from the simulation of `mapPlan` by
  the plan iterator.

The checks of the leaves rely on `check_leaf_spec`, whose count of new tables
starts from the record `used` of the set and cannot overflow only while that
record is far enough below the largest `usize`: `DirectRoom` states that
premise once, and the triples that need it (`check_leaves_loop_spec`,
`direct_check_range_spec`, `check_usable_loop_spec`, `check_usable_spec`,
`direct_map_set_spec`, `direct_map_of_stands`) take it or the bound that it
gives. The leaf search, the plan step and the fdt queries do not need it.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## The leaves of a usable range -/

/-- `leaf_at(pa, end)` for `pa` at or below `end`: the leaf of `directLeaf`,
a block exactly at a multiple of 2 MiB with at least 2 MiB left. -/
@[step] theorem leaf_at_spec (pa e : U64) (h : pa.val ≤ e.val) :
    page_tables.boot.direct.leaf_at pa e ⦃ l =>
      l.pa = pa ∧ l.block = decide (pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val) ∧
        word64 l.desc = (directLeaf e.val pa.val).desc ⦄ := by
  unfold page_tables.boot.direct.leaf_at
  simp only [block_size_eq]
  step*
  · have hc : pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val := by
      simp only [BLOCK_SIZE]; scalar_tac
    refine ⟨(decide_eq_true hc).symm, ?_⟩
    rw [directLeaf_of_block hc, i2_post]; rfl
  · have hc : ¬ (pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val) := by
      simp only [BLOCK_SIZE]; scalar_tac
    refine ⟨(decide_eq_false hc).symm, ?_⟩
    rw [directLeaf_of_page hc, i2_post]; rfl
  · have hc : ¬ (pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val) := by
      simp only [BLOCK_SIZE]; scalar_tac
    refine ⟨(decide_eq_false hc).symm, ?_⟩
    rw [directLeaf_of_page hc, i2_post]; rfl

/-- `range_leaf(pa, end, pages)` for `pa` at or below `end`: `rangeFind`. -/
@[step] theorem range_leaf_spec (pa e : U64) (pages : Bool) (h : pa.val ≤ e.val) :
    page_tables.boot.direct.range_leaf pa e pages ⦃ o =>
      foundOf o = rangeFind e.val pa.val pages ⦄ := by
  unfold page_tables.boot.direct.range_leaf
  simp only [block_size_eq]
  step*
  · -- a block, pages asked, a page at the end
    have ht : tail.val = e.val / BLOCK_SIZE * BLOCK_SIZE := by
      rw [‹tail.val = (e &&& i1).val›, i1_post,
        and_not_val e i (k := 21) (by rw [i_post]; rfl) (by decide)]; rfl
    have hb : decide (pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val) = true := by
      rw [← leaf_post]; exact ‹leaf.block = true›
    have hlt : e.val / BLOCK_SIZE * BLOCK_SIZE < e.val := by rw [← ht]; exact ‹tail < e›
    simp only [rangeFind, leafAtFound, hb, Bool.and_true, ↓reduceIte, hlt, foundOf,
      Option.map_some, Option.some.injEq, Found.mk.injEq]
    refine ⟨by rw [tail_post, ht], by rw [l_post1, ht], by rw [l_post, ht]⟩
  · -- a block, pages asked, no page at the end
    have ht : tail.val = e.val / BLOCK_SIZE * BLOCK_SIZE := by
      rw [‹tail.val = (e &&& i1).val›, i1_post,
        and_not_val e i (k := 21) (by rw [i_post]; rfl) (by decide)]; rfl
    have hb : decide (pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val) = true := by
      rw [← leaf_post]; exact ‹leaf.block = true›
    have hlt : ¬ e.val / BLOCK_SIZE * BLOCK_SIZE < e.val := by rw [← ht]; exact ‹¬tail < e›
    simp only [rangeFind, leafAtFound, hb, Bool.and_true, ↓reduceIte, hlt, foundOf,
      Option.map_none]
  · -- a block, pages not asked
    simp only [rangeFind, Bool.and_false, Bool.false_eq_true, ↓reduceIte, foundOf,
      Option.map_some, Option.some.injEq, leafAtFound, Found.mk.injEq]
    exact ⟨by rw [pa_post], leaf_post1, leaf_post⟩
  · -- a page
    have hb : decide (pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val) = false := by
      rw [← leaf_post]; simpa using ‹¬leaf.block = true›
    simp only [rangeFind, leafAtFound, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      foundOf, Option.map_some, Option.some.injEq, Found.mk.injEq]
    exact ⟨by rw [pa_post], leaf_post1, leaf_post.trans hb⟩

/-! ## The checks of the leaves of a range -/

/-- What the record of the checks of the code holds against the leaves `acc`
that passed, latest first, after usable ranges whose largest end is `reach`:
that end, the record of new tables of `allocOf used acc` at the virtual
addresses `DIRECT_BASE | pa`, and at most two new tables a leaf. -/
def UsableRel (used reach : Nat) (check : page_tables.boot.MapCheck)
    (acc : List (MapLeaf × Place)) : Prop :=
  check.reach.val = reach ∧
    AllocRel DIRECT_BASE.toNat check.next.val check.gib.val check.slot.val (allocOf used acc) ∧
    check.next.val ≤ used + 2 * acc.length ∧ used ≤ check.next.val

/-- The check of one leaf at `pa` of a usable range that ends at `e` by the
code (`check_leaf` without a guard) is the free-slot check of the leaf of
`directLeaf`, for a leaf below `2 ^ 39` and usable ranges before that start
at or below `pa`. -/
theorem checkPlace_leaf {N : Usize} (set : page_tables.Tables N true) (base : U64)
    (earlier : List Krepi.Spec.Fdt.Span) (pa e : U64) (hlow : pa.val < 2 ^ 39)
    (hstart : ∀ x ∈ earlier, x.start.toNat ≤ pa.val) :
    checkPlace (tablesOf set) (word64 base)
        (placeProbe (word64 pa) (decide (pa.val % BLOCK_SIZE = 0 ∧ pa.val + BLOCK_SIZE ≤ e.val)))
        (decide (pa.val < reachSpans earlier) || false) =
      checkPlace (r := .upper) (tablesOf set) (word64 base) (directLeaf e.val pa.val)
        (usableTaken earlier (directLeaf e.val pa.val)) := by
  have ha : (UInt64.ofNat pa.val).toNat = pa.val := UInt64.toNat_ofNat_of_lt' (u64_lt pa)
  have hpa : (directLeaf e.val pa.val).pa.toNat = pa.val := by rw [directLeaf_pa, ha]
  have hl : (UInt64.ofNat pa.val).toNat < 2 ^ 39 := by rw [ha]; exact hlow
  rw [usableTaken, any_meets_spans hpa hstart, Bool.or_false]
  show checkPlace (r := .upper) (tablesOf set) _ _ _ = _
  refine checkPlace_congr _ (place_congr _ _ ?_ ?_ ?_ ?_)
  · rw [directLeaf_va, index1_direct hl]; rfl
  · rw [directLeaf_va, index2_direct hl]; rfl
  · rw [directLeaf_va, index3_direct hl]; rfl
  · rw [directLeaf_form]; simp only [placeProbe, decide_eq_true_eq]

/-- The loop of `check_leaves` from the leaf at `pa` up to `e`, on a pool of
at least one table, for an end at or below `2 ^ 39` on a page boundary, a
leaf on a page boundary from `start`, ranges before that start at or below
`start`, `fuel` at least the leaves left (`leafFuel`) and a record of new
tables that cannot overflow on them: the fold of the free-slot checks of
those leaves (`checkLeavesFrom`), the record standing for the leaves that
passed (`UsableRel`). -/
theorem check_leaves_loop_spec {N : Usize} (set : page_tables.Tables N true)
    (base top : U64) (earlier : List Krepi.Spec.Fdt.Span) (used start : Nat)
    (hN : 0 < N.val) (he : top.val ≤ 2 ^ 39) (he4 : top.val % 4096 = 0)
    (hstart : ∀ x ∈ earlier, x.start.toNat ≤ start)
    (check : page_tables.boot.MapCheck) (pa : U64) (acc : List (MapLeaf × Place)) (fuel : Nat)
    (hpa : start ≤ pa.val) (hpa4 : pa.val % 4096 = 0) (hpae : pa.val ≤ top.val)
    (hfuel : leafFuel top.val pa.val ≤ fuel)
    (hrel : UsableRel used (reachSpans earlier) check acc)
    (hov : used + 2 * (acc.length + fuel) + 2 ≤ Usize.max) :
    page_tables.boot.direct.check_leaves_loop set check top base pa ⦃ r c =>
      Agrees (fun _ acc' => UsableRel used (reachSpans earlier) c acc') tableErrorOf r
        (checkLeavesFrom (tablesOf set) (word64 base) (usableTaken earlier) top.val fuel pa.val
          acc) ⦄ := by
  unfold page_tables.boot.direct.check_leaves_loop
  apply loop.spec_decr_nat
    (measure := fun (x : page_tables.boot.MapCheck × U64) => top.val - x.2.val)
    (inv := fun (x : page_tables.boot.MapCheck × U64) =>
      start ≤ x.2.val ∧ x.2.val % 4096 = 0 ∧ x.2.val ≤ top.val ∧
      ∃ acc' f, leafFuel top.val x.2.val ≤ f ∧ UsableRel used (reachSpans earlier) x.1 acc' ∧
        used + 2 * (acc'.length + f) + 2 ≤ Usize.max ∧
        checkLeavesFrom (tablesOf set) (word64 base) (usableTaken earlier) top.val f x.2.val acc' =
        checkLeavesFrom (tablesOf set) (word64 base) (usableTaken earlier) top.val fuel pa.val acc)
  · rintro ⟨c, p⟩ ⟨h1, h2, h3, acc', f, hf, hr, hov', hspec⟩
    simp only at h1 h2 h3 hf hr hov' hspec
    have hn : c.next.val + 2 ≤ Usize.max := by obtain ⟨-, -, h, -⟩ := hr; omega
    have hst : ∀ x ∈ earlier, x.start.toNat ≤ p.val := fun x hx => Nat.le_trans (hstart x hx) h1
    unfold page_tables.boot.direct.check_leaves_loop.body
    simp only [block_size_eq, page_size_eq]
    step*
    · -- the leaf passed; a block or a page follows
      obtain ⟨P, hP, hreach', hcount⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      have hlt : p.val < top.val := ‹p < top›
      have hlow : p.val < 2 ^ 39 := by omega
      rw [hr.1, leaf_post, checkPlace_leaf set base earlier p top hlow hst] at hP
      have hstep := leafFuel_leaf (stop := top.val) (pa := p.val) h2 he4 hlt
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [checkLeavesFrom_succ (tablesOf set) (word64 base) (usableTaken earlier) top.val g acc' hlt,
        hP] at hspec
      have hspec' : checkLeavesFrom (tablesOf set) (word64 base) (usableTaken earlier) top.val g
          (p.val + (directLeaf top.val p.val).form.size) ((directLeaf top.val p.val, P) :: acc') =
          checkLeavesFrom (tablesOf set) (word64 base) (usableTaken earlier) top.val fuel pa.val
            acc := hspec
      have hc1 := congrArg Prod.fst hcount
      have hc2 := congrArg (fun x => x.2.1) hcount
      have hc3 := congrArg (fun x => x.2.2) hcount
      simp only at hc1 hc2 hc3
      have hle2 := countStep_le leaf.block P p.val c.next.val c.gib.val c.slot.val
      have hge2 := countStep_ge leaf.block P p.val c.next.val c.gib.val c.slot.val
      have hnb := hr.2.2.1
      have hnu := hr.2.2.2
      have hva : (directLeaf top.val p.val).va.toNat = DIRECT_BASE.toNat + p.val :=
        directLeaf_va_toNat hlow
      have hform : (directLeaf top.val p.val).form = if leaf.block then .block else .page := by
        rw [directLeaf_form, leaf_post]; simp only [decide_eq_true_eq]
      have hrel' : UsableRel used (reachSpans earlier) check1
          ((directLeaf top.val p.val, P) :: acc') := by
        refine ⟨by rw [hreach']; exact hr.1, ?_, ?_, ?_⟩
        · rw [allocOf_cons, hc1, hc2, hc3]
          exact allocRel_add hr.2.1 (by decide) hva hform
        · rw [hc1, List.length_cons]; omega
        · rw [hc1]; omega
      have hsz := directLeaf_size top.val p.val
      by_cases hb : p.val % BLOCK_SIZE = 0 ∧ p.val + BLOCK_SIZE ≤ top.val
      · have hlb : leaf.block = true := by rw [leaf_post]; exact decide_eq_true hb
        simp only [hb, and_self, ↓reduceIte] at hsz
        simp only [BLOCK_SIZE] at hb hsz
        simp only [hlb, ↓reduceIte, bind_ok]
        step*
        refine ⟨by omega, by omega, by omega, ⟨_, g, ?_, hrel', ?_, ?_⟩, by omega⟩
        · rw [pa1_post, ← hsz]; omega
        · rw [List.length_cons]; omega
        · rw [pa1_post, ← hsz]; exact hspec'
      · have hlb : leaf.block = false := by rw [leaf_post]; exact decide_eq_false hb
        simp only [hb, ↓reduceIte] at hsz
        simp only [PAGE_SIZE] at hsz
        have hle : p.val + 4096 ≤ top.val := by omega
        simp only [hlb, Bool.false_eq_true, ↓reduceIte, bind_ok]
        step*
        refine ⟨by omega, by omega, by omega, ⟨_, g, ?_, hrel', ?_, ?_⟩, by omega⟩
        · rw [pa1_post, ← hsz]; omega
        · rw [List.length_cons]; omega
        · rw [pa1_post, ← hsz]; exact hspec'
    · -- the error of the leaf
      have hE := agrees_err_of_branch cf_post ‹_› residual_post r_post
      have hlt : p.val < top.val := ‹p < top›
      have hlow : p.val < 2 ^ 39 := by omega
      rw [hr.1, leaf_post, checkPlace_leaf set base earlier p top hlow hst] at hE
      have hstep := leafFuel_leaf (stop := top.val) (pa := p.val) h2 he4 hlt
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [← hspec, checkLeavesFrom_succ (tablesOf set) (word64 base) (usableTaken earlier)
        top.val g acc' hlt, hE, r1_post, e_post]
      rfl
    · -- past the end
      have hge : top.val ≤ p.val := by have := ‹¬p < top›; scalar_tac
      rw [← hspec, checkLeavesFrom_stop (tablesOf set) (word64 base) (usableTaken earlier) f acc'
        hge]
      exact hr
  · exact ⟨hpa, hpa4, hpae, acc, fuel, hfuel, hrel, hov, rfl⟩

/-- The premise on the record `used` of the tables in use of the set that
the checks of `direct_map` need: at least `2 ^ 28` below the largest
`usize`, room for two new tables for each of the at most `164 · 2 ^ 19`
leaves of the usable ranges of a boot memory map. The checks of the code
count the new tables from the record (`MapCheck::new(set.used)`), so a larger
record can overflow their count; every triple of the direct map that needs
the premise takes it through this definition. -/
def DirectRoom (used : Nat) : Prop := used + 2 ^ 28 ≤ Usize.max

/-- `checkUsableRange_eq` on the set of the code, whose region is that of
`regionOf true`. -/
theorem checkUsableRange_tablesOf {N : Usize} (set : page_tables.Tables N true) (base : UInt64)
    (bits : UInt8) (earlier : List Krepi.Spec.Fdt.Span) (leaves : List (MapLeaf × Place))
    (u : Krepi.Spec.Fdt.Span) :
    (tablesOf set).checkUsableRange base bits (earlier, leaves) u =
      if u.start.toNat % PAGE_SIZE ≠ 0 ∨ u.endNat % PAGE_SIZE ≠ 0 then .error .alignment
      else if VA_LIMIT < u.endNat ∨ 2 ^ bits.toNat < u.endNat then .error .addressWidth
      else
        (checkLeavesFrom (tablesOf set) base (usableTaken earlier) u.endNat
          (directFuel (u.endNat - u.start.toNat)) u.start.toNat leaves).map
          (fun ls => (earlier ++ [u], ls)) :=
  checkUsableRange_eq (tablesOf set) base bits earlier leaves u

/-- `check_range(set, check, range, base, bits)` on a pool of at least one
table, for a span whose end fits in 64 bits, after usable ranges that start
at or below it, a width below 64 and a record of new tables that cannot
overflow on the leaves of a range below `2 ^ 39`: the checks of the range,
`Tables.checkUsableRange`, the record standing for the leaves that passed
after the range (`UsableRel`). -/
theorem direct_check_range_spec {N : Usize} (set : page_tables.Tables N true)
    (check : page_tables.boot.MapCheck) (range : fdt.Span) (base : U64) (bits : U8)
    (earlier : List Krepi.Spec.Fdt.Span) (acc : List (MapLeaf × Place)) (used : Nat)
    (hN : 0 < N.val) (hfit : range.start.val + range.size.val < 2 ^ 64) (hb : bits.val < 64)
    (hstart : ∀ x ∈ earlier, x.start.toNat ≤ range.start.val)
    (hrel : UsableRel used (reachSpans earlier) check acc)
    (hov : used + 2 * (acc.length + 2 ^ 19) + 2 ≤ Usize.max) :
    page_tables.boot.direct.check_range set check range base bits ⦃ r c =>
      Agrees (fun _ (x : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place)) =>
          x.1 = earlier ++ [spanOf range] ∧ UsableRel used (reachSpans x.1) c x.2) tableErrorOf r
        ((tablesOf set).checkUsableRange (word64 base) (byte bits) (earlier, acc)
          (spanOf range)) ⦄ := by
  unfold page_tables.boot.direct.check_range
  have hS : (spanOf range).start.toNat = range.start.val := by simp
  have hE : (spanOf range).endNat = range.start.val + range.size.val := spanOf_endNat range
  have hB : (byte bits).toNat = bits.val := byte_toNat bits
  simp only [page_size_eq, va_limit_eq]
  step*
  · have hc : (spanOf range).start.toNat % PAGE_SIZE ≠ 0 ∨ (spanOf range).endNat % PAGE_SIZE ≠ 0 :=
      Or.inl (by rw [hS, show PAGE_SIZE = 4096 from rfl, ← i_post]; exact bne_zero_iff.1 ‹_›)
    rw [checkUsableRange_tablesOf]; simp only [hc, ↓reduceIte]; rfl
  · have hc : (spanOf range).start.toNat % PAGE_SIZE ≠ 0 ∨ (spanOf range).endNat % PAGE_SIZE ≠ 0 :=
      Or.inr (by
        rw [hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i1_post]; exact bne_zero_iff.1 ‹_›)
    rw [checkUsableRange_tablesOf]; simp only [hc, ↓reduceIte]; rfl
  · have hc : ¬ ((spanOf range).start.toNat % PAGE_SIZE ≠ 0 ∨
        (spanOf range).endNat % PAGE_SIZE ≠ 0) := by
      rw [hS, hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i_post, ← i1_post]
      simp only [ne_eq, not_or, Decidable.not_not]
      exact ⟨not_bne_zero_iff.1 ‹_›, not_bne_zero_iff.1 ‹_›⟩
    have hw : VA_LIMIT < (spanOf range).endNat ∨ 2 ^ (byte bits).toNat < (spanOf range).endNat :=
      Or.inl (by
        rw [hE, ← end_post]; have := ‹«end» > 549755813888#u64›; simp only [VA_LIMIT]; scalar_tac)
    rw [checkUsableRange_tablesOf]; simp only [hc, hw, ↓reduceIte]; rfl
  · have hc : ¬ ((spanOf range).start.toNat % PAGE_SIZE ≠ 0 ∨
        (spanOf range).endNat % PAGE_SIZE ≠ 0) := by
      rw [hS, hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i_post, ← i1_post]
      simp only [ne_eq, not_or, Decidable.not_not]
      exact ⟨not_bne_zero_iff.1 ‹_›, not_bne_zero_iff.1 ‹_›⟩
    have h3 : i3.val = 2 ^ bits.val := by rw [i3_post, u64_size]; exact one_shiftLeft hb
    have hw : VA_LIMIT < (spanOf range).endNat ∨ 2 ^ (byte bits).toNat < (spanOf range).endNat :=
      Or.inr (by rw [hE, ← end_post, hB, ← h3]; exact ‹«end» > i3›)
    rw [checkUsableRange_tablesOf]; simp only [hc, hw, ↓reduceIte]; rfl
  · have hc : ¬ ((spanOf range).start.toNat % PAGE_SIZE ≠ 0 ∨
        (spanOf range).endNat % PAGE_SIZE ≠ 0) := by
      rw [hS, hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i_post, ← i1_post]
      simp only [ne_eq, not_or, Decidable.not_not]
      exact ⟨not_bne_zero_iff.1 ‹_›, not_bne_zero_iff.1 ‹_›⟩
    have h3 : i3.val = 2 ^ bits.val := by rw [i3_post, u64_size]; exact one_shiftLeft hb
    have hle : «end».val ≤ 2 ^ 39 := by have := ‹¬«end» > 549755813888#u64›; scalar_tac
    have hle3 : «end».val ≤ 2 ^ bits.val := by rw [← h3]; have := ‹¬«end» > i3›; scalar_tac
    have hw : ¬ (VA_LIMIT < (spanOf range).endNat ∨
        2 ^ (byte bits).toNat < (spanOf range).endNat) := by
      rw [hE, ← end_post, hB]; simp only [VA_LIMIT, not_or, Nat.not_lt]; exact ⟨hle, hle3⟩
    have hs4 : range.start.val % 4096 = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have he4 : «end».val % 4096 = 0 := by rw [← i1_post]; exact not_bne_zero_iff.1 ‹_›
    have hse : range.start.val ≤ «end».val := by rw [end_post]; omega
    have hst : ∀ x ∈ earlier, x.start.toNat ≤ range.start.val := hstart
    have hfuel : directFuel («end».val - range.start.val) ≤ 2 ^ 19 :=
      directFuel_le (Nat.le_trans (Nat.sub_le _ _) hle)
    have hcl := check_leaves_loop_spec set base «end» earlier used range.start.val hN hle he4 hst
      check range.start acc (directFuel («end».val - range.start.val)) (Nat.le_refl _) hs4 hse
      (by
        have := leafFuel_start (stop := «end».val) (pa := range.start.val) hs4 he4
        exact this)
      hrel (by omega)
    rw [checkUsableRange_tablesOf]
    simp only [hc, hw, ↓reduceIte]
    rw [hS, hE, ← end_post]
    refine WP.spec_bind hcl ?_
    rintro ⟨r, check1⟩ hr
    step*
    · obtain ⟨acc', hacc', hrel'⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› hr)
      rw [hacc']
      refine ⟨rfl, ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := hrel'
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [check2_post, h1, reachSpans_append, hE, ← end_post]
      · rw [check2_post1, check2_post2, check2_post3]; exact h2
      · rw [check2_post1]; exact h3
      · rw [check2_post1]; exact h4
    · rw [agrees_err_of_branch cf_post ‹_› residual_post hr, r1_post, e_post]
      rfl

/-- The loop of `check_usable` from the iterator `ranges` of the usable
ranges, on a pool of at least one table, for managed banks within 64 bits,
nonempty reservations, usable ranges `Us` within 64 bits, apart in address
order and at most 164, of which the ranges `y.1` are checked and the rest are
those of the iterator, a width below 64 and a record of the set with the
room of `DirectRoom`: the fold of `Tables.checkUsableRange`
over the ranges left, from the ranges checked and the leaves that passed
(`UsableRel`). -/
theorem check_usable_loop_spec {N : Usize}
    (a : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N) (i : Usize) (base : U64) (bits : U8)
    (M Rs Us : List Krepi.Spec.Fdt.Span) (hN : 0 < N.val) (hb : bits.val < 64)
    (hM : ∀ b ∈ M, b.Valid) (hRs : ∀ r ∈ Rs, r.Nonempty) (hUs : ∀ u ∈ Us, u.Valid)
    (hsort : Us.Pairwise (fun x y => x.endNat ≤ y.start.toNat)) (hlen : Us.length ≤ 164)
    (hov : DirectRoom i.val)
    (ranges : fdt.AvailableRanges) (hm : spansOf ranges.managed = M)
    (hr : spansOf ranges.reservations = Rs) (check : page_tables.boot.MapCheck)
    (y : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place))
    (hsplit : y.1 ++ availableFrom M Rs ranges.cursor.bank.val ranges.cursor.at.val = Us)
    (hy2 : y.2.length ≤ y.1.length * 2 ^ 19)
    (hrel : UsableRel i.val (reachSpans y.1) check y.2) :
    page_tables.boot.direct.check_usable_loop a i base bits ranges check ⦃ r =>
      Agrees (fun c (z : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place)) =>
          UsableRel i.val (reachSpans z.1) c z.2) tableErrorOf r
        ((availableFrom M Rs ranges.cursor.bank.val ranges.cursor.at.val).foldlM
          ((tablesOf ({ pool := a, used := i } : page_tables.Tables N true)).checkUsableRange
            (word64 base) (byte bits)) y) ⦄ := by
  unfold page_tables.boot.direct.check_usable_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.AvailableRanges × page_tables.boot.MapCheck) =>
      (availableFrom M Rs x.1.cursor.bank.val x.1.cursor.at.val).length)
    (inv := fun (x : fdt.AvailableRanges × page_tables.boot.MapCheck) =>
      spansOf x.1.managed = M ∧ spansOf x.1.reservations = Rs ∧
      ∃ y' : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place),
        y'.1 ++ availableFrom M Rs x.1.cursor.bank.val x.1.cursor.at.val = Us ∧
        y'.2.length ≤ y'.1.length * 2 ^ 19 ∧ UsableRel i.val (reachSpans y'.1) x.2 y'.2 ∧
        (availableFrom M Rs x.1.cursor.bank.val x.1.cursor.at.val).foldlM
          ((tablesOf ({ pool := a, used := i } : page_tables.Tables N true)).checkUsableRange
            (word64 base) (byte bits)) y' =
        (availableFrom M Rs ranges.cursor.bank.val ranges.cursor.at.val).foldlM
          ((tablesOf ({ pool := a, used := i } : page_tables.Tables N true)).checkUsableRange
            (word64 base) (byte bits)) y)
  · rintro ⟨rs, c⟩ ⟨h1, h2, ⟨e, l⟩, hy1, hy2', hyr, hspec⟩
    simp only at h1 h2 hy1 hy2' hyr hspec
    unfold page_tables.boot.direct.check_usable_loop.body
    have hM' : ∀ b ∈ spansOf rs.managed, b.Valid := by rw [h1]; exact hM
    have hR' : ∀ r ∈ spansOf rs.reservations, r.Nonempty := by rw [h2]; exact hRs
    refine WP.spec_bind (available_ranges_next_spec rs hM' hR') ?_
    rintro ⟨o, rs1⟩ ⟨f1, f2, ho⟩
    rw [h1, h2] at ho
    cases o with
    | none =>
      simp only
      refine spec_of_eq rfl ?_
      rw [← hspec, ho.1]
      exact hyr
    | some range =>
      simp only at ho ⊢
      have hmem : spanOf range ∈ Us := by
        rw [← hy1, ho]; exact List.mem_append_right _ List.mem_cons_self
      have hfit : range.start.val + range.size.val < 2 ^ 64 :=
        (spanOf_valid_iff range).1 (hUs _ hmem)
      have hpw := hsort
      rw [← hy1, ho, List.pairwise_append] at hpw
      have hst : ∀ x ∈ e, x.start.toNat ≤ range.start.val := by
        intro x hx
        have h := hpw.2.2 x hx (spanOf range) List.mem_cons_self
        have hx' : x.start.toNat ≤ x.endNat := by simp only [Krepi.Spec.Fdt.Span.endNat]; omega
        have : (spanOf range).start.toNat = range.start.val := by simp
        omega
      have he : e.length ≤ 163 := by
        have := congrArg List.length hy1
        rw [ho, List.length_append, List.length_cons] at this
        omega
      have hcr := direct_check_range_spec { pool := a, used := i } c range base bits e l i.val hN
        hfit hb hst hyr (usable_room hov hy2' he)
      refine WP.spec_bind hcr ?_
      rintro ⟨r, check1⟩ hr1
      rw [ho, List.foldlM_cons] at hspec
      step*
      · obtain ⟨y', hy', hy'1, hy'r⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› hr1)
        rw [hy'] at hspec
        obtain ⟨-, hlen'⟩ := checkUsableRange_passed (show _ = Except.ok (y'.1, y'.2) from hy')
        refine ⟨by rw [f1]; exact h1, by rw [f2]; exact h2, ⟨y', ?_, ?_, hy'r, hspec⟩, ?_⟩
        · rw [hy'1, ← hy1, ho, List.append_assoc, List.singleton_append]
        · rw [hy'1, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
        · rw [ho, List.length_cons]; omega
      · rw [← hspec, agrees_err_of_branch cf_post ‹_› residual_post hr1, r1_post, e_post]
        rfl
  · exact ⟨hm, hr, y, hsplit, hy2, hrel, rfl⟩

/-- `check_usable(set, ranges, base, bits)` on a pool of at least one table,
for an iterator at the start of the usable ranges `Us` of managed banks `M`
within 64 bits and nonempty reservations `Rs`, with `Us` within 64 bits,
apart in address order and at most 164, a width below 64 and a record of the
set with the room of `DirectRoom`: the fold of
`Tables.checkUsableRange` over `Us`, with the record of the checks standing
for its result (`UsableRel`). -/
theorem check_usable_spec {N : Usize} (set : page_tables.Tables N true)
    (ranges : fdt.AvailableRanges) (base : U64) (bits : U8) (M Rs Us : List Krepi.Spec.Fdt.Span)
    (hN : 0 < N.val) (hb : bits.val < 64) (hM : ∀ b ∈ M, b.Valid) (hRs : ∀ r ∈ Rs, r.Nonempty)
    (hUs : ∀ u ∈ Us, u.Valid) (hsort : Us.Pairwise (fun x y => x.endNat ≤ y.start.toNat))
    (hlen : Us.length ≤ 164) (hov : DirectRoom set.used.val)
    (hm : spansOf ranges.managed = M) (hr : spansOf ranges.reservations = Rs)
    (hstart : availableFrom M Rs ranges.cursor.bank.val ranges.cursor.at.val = Us) :
    page_tables.boot.direct.check_usable set ranges base bits ⦃ r =>
      Agrees (fun c (z : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place)) =>
          UsableRel set.used.val (reachSpans z.1) c z.2) tableErrorOf r
        (Us.foldlM ((tablesOf set).checkUsableRange (word64 base) (byte bits)) ([], [])) ⦄ := by
  unfold page_tables.boot.direct.check_usable
  step*
  have hrel : UsableRel set.used.val (reachSpans []) check [] := by
    refine ⟨check_post, ?_, ?_, ?_⟩
    · rw [check_post1, ‹check.gib.val = noSlot›, ‹check.slot.val = noSlot›]
      exact allocRel_init _ set.used.val
    · rw [check_post1]; simp
    · rw [check_post1]
  have h := check_usable_loop_spec set.pool set.used base bits M Rs Us hN hb hM hRs hUs hsort hlen
    hov ranges hm hr check ([], []) (by rw [List.nil_append, hstart]) (Nat.zero_le _) hrel
  rw [hstart] at h
  exact h

/-! ## `direct_map` -/


/-- The plan iterator that `direct_map` returns on success, before its first
call: the set after the write phase, `base`, the cursor before the first
leaf with the record of the set before the write phase, the iterator of the
usable ranges at the start of the managed banks and the reservations of the
boot memory map, and the empty span at 0 as its current range. -/
def DirectMapStart {N : Usize} (s : page_tables.Tables N true) (P : Krepi.Spec.Fdt.MemoryPlan)
    (base : U64) (it : page_tables.DirectMapPlan N) : Prop :=
  it.set.pool = s.pool ∧ it.base = base ∧ it.cursor = startCursor s.used ∧
    spansOf it.ranges.managed = P.managed ∧ spansOf it.ranges.reservations = P.reservations ∧
    it.ranges.cursor.bank.val = 0 ∧ it.ranges.cursor.at.val = 0 ∧
    it.range.start.val = 0 ∧ it.range.size.val = 0

/-- The lists of a boot memory map that a map of the code stands for: at most
32 managed banks and 132 reservations. -/
theorem memoryPlanRepr_lengths {p : fdt.MemoryPlan} {P : Krepi.Spec.Fdt.MemoryPlan}
    (h : MemoryPlanRepr p P) : P.managed.length ≤ 32 ∧ P.reservations.length ≤ 132 := by
  obtain ⟨-, h2, h3, h4, rfl⟩ := h
  simp only [Krepi.Spec.Fdt.MemoryPlan.MAX_BANKS, Krepi.Spec.Fdt.MemoryPlan.MAX_BOOT_SPANS,
    Krepi.Spec.Fdt.MemoryPlan.MAX_FIRMWARE] at h2 h4
  simp only [Krepi.Spec.Fdt.MemoryPlan.reservations, List.length_append, List.length_map,
    List.length_take, List.length_drop]
  omega

/-- `direct_map(set, memory, base, bits)` for a map that stands for a boot
memory map that the fdt entries built (`BuiltPlan`) and a record of the set
with the room of `DirectRoom`: the error of `Tables.directMap` with the set
unchanged, or its set after the write phase with a plan iterator at its
start (`DirectMapStart`). That the iterator stands for `mapPlan` (the
simulation) is not proved here. -/
theorem direct_map_set_spec {N : Usize} (s : page_tables.Tables N true) (memory : fdt.MemoryPlan)
    (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8) (hP : MemoryPlanRepr memory P)
    (hB : Witnesses.TableSets.BuiltPlan P) (hov : DirectRoom s.used.val) :
    page_tables.direct_map s memory base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (fun it _ => DirectMapStart s P base it)
        (tableErrorOf · = ·) s r s' ((tablesOf s).directMap P (word64 base) (byte bits)) ⦄ := by
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
        refine ⟨⟨by rw [hs1], rfl, rfl, ar_post, ar_post1, ar_post2, ar_post3, rfl, rfl⟩, ?_⟩
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
        rw [r3_post, ← e_post, hs1]
        exact ⟨rfl, rfl⟩
      · simp only [hcond, ↓reduceIte] at r2_post
        rw [hr2] at r2_post
        cases r2_post.1
    · rw [directMap_fold_error (s := tablesOf s) hp
        (by rw [hsorted]; exact agrees_err_of_branch cf1_post ‹_› residual_post hr1), r2_post,
        e_post]
      exact ⟨rfl, rfl⟩
  · rw [directMap_pool_error (s := tablesOf s)
      (agrees_err_of_branch cf_post ‹_› residual_post r_post), r1_post, e_post]
    exact ⟨rfl, rfl⟩

/-! ## The leaf search of the plan -/

/-- The usable ranges that a state of the leaf search of the plan stands
for: its current range, then the usable ranges from the cursor of its
iterator. -/
def searchList (M Rs : List Krepi.Spec.Fdt.Span) (ranges : fdt.AvailableRanges)
    (range : fdt.Span) : List Krepi.Spec.Fdt.Span :=
  spanOf range :: availableFrom M Rs ranges.cursor.bank.val ranges.cursor.at.val

/-- The loop of `usable_leaf` from the state `(ranges, range, from)`, for an
iterator over managed banks `M` within 64 bits and nonempty reservations
`Rs` and ranges within 64 bits: the slices of the iterator stay; the leaf
found is `usableFind` of the ranges of the state from `from`; the ranges of
the state where the search stopped are those of the state without some
first ranges, which end at or below `from` when the search asks for leaves
of either form. -/
theorem usable_leaf_loop_spec (limit : U64) (pages : Bool) (M Rs : List Krepi.Spec.Fdt.Span)
    (hM : ∀ b ∈ M, b.Valid) (hRs : ∀ r ∈ Rs, r.Nonempty)
    (ranges : fdt.AvailableRanges) (range : fdt.Span) («from» : U64)
    (hm : spansOf ranges.managed = M) (hr : spansOf ranges.reservations = Rs)
    (hv : ∀ u ∈ searchList M Rs ranges range, u.Valid) :
    page_tables.boot.direct.usable_leaf_loop limit pages ranges range «from» ⦃ y =>
      spansOf y.1 = M ∧ spansOf y.2.1 = Rs ∧
      foundOf y.2.2.2.2.2 =
        usableFind ((searchList M Rs ranges range).map spanView) «from».val limit.val pages ∧
      ∃ skipped, searchList M Rs ranges range =
          skipped ++ searchList M Rs ⟨y.1, y.2.1, y.2.2.1⟩ ⟨y.2.2.2.1, y.2.2.2.2.1⟩ ∧
        (pages = false → ∀ u ∈ skipped, u.endNat ≤ «from».val) ⦄ := by
  unfold page_tables.boot.direct.usable_leaf_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.AvailableRanges × fdt.Span × U64) =>
      2 * (availableFrom M Rs x.1.cursor.bank.val x.1.cursor.at.val).length +
        (if x.2.2.val < x.2.1.start.val + x.2.1.size.val then 1 else 0))
    (inv := fun (x : fdt.AvailableRanges × fdt.Span × U64) =>
      spansOf x.1.managed = M ∧ spansOf x.1.reservations = Rs ∧
      (∀ u ∈ searchList M Rs x.1 x.2.1, u.Valid) ∧ (pages = false → x.2.2 = «from») ∧
      ∃ skipped, searchList M Rs ranges range = skipped ++ searchList M Rs x.1 x.2.1 ∧
        (∀ u ∈ skipped, u.endNat ≤ x.2.2.val) ∧
        usableFind ((searchList M Rs x.1 x.2.1).map spanView) x.2.2.val limit.val pages =
          usableFind ((searchList M Rs ranges range).map spanView) «from».val limit.val pages)
  · rintro ⟨rs, rg, fr⟩ ⟨h1, h2, h3, h4, skipped, hsk, hskb, hspec⟩
    simp only at h1 h2 h3 h4 hsk hskb hspec
    unfold page_tables.boot.direct.usable_leaf_loop.body
    have hvr : rg.start.val + rg.size.val < 2 ^ 64 :=
      (spanOf_valid_iff rg).1 (h3 _ List.mem_cons_self)
    have hview : spanView (spanOf rg) = (rg.start.val, rg.start.val + rg.size.val) := by
      simp only [spanView, spanOf_start, word64_toNat, spanOf_endNat]
    have hM' : ∀ b ∈ spansOf rs.managed, b.Valid := by rw [h1]; exact hM
    have hR' : ∀ r ∈ spansOf rs.reservations, r.Nonempty := by rw [h2]; exact hRs
    step as ⟨«end», end_post⟩
    split
    · -- the range ends above the address
      have hlt : fr.val < «end».val := ‹fr < «end»›
      have hat : (if rg.start > fr then ok rg.start else ok fr : Result U64) =
          ok (if rg.start > fr then rg.start else fr) := by split <;> rfl
      rw [hat, bind_ok]
      generalize hA : (if rg.start > fr then rg.start else fr) = pa
      have hpa : pa.val = max rg.start.val fr.val := by
        rw [← hA]
        split
        · rename_i h; rw [gt_iff_lt, UScalar.lt_equiv] at h; omega
        · rename_i h; rw [gt_iff_lt, UScalar.lt_equiv] at h; omega
      have hpe : pa.val ≤ «end».val := by rw [hpa, end_post]; omega
      have hcons : usableFind ((searchList M Rs rs rg).map spanView) fr.val limit.val pages =
          match rangeFind «end».val pa.val pages with
          | some l => if l.pa < limit.val then some l else none
          | none => usableFind ((availableFrom M Rs rs.cursor.bank.val rs.cursor.at.val).map
              spanView) «end».val limit.val pages := by
        simp only [searchList, List.map_cons, hview]
        rw [usableFind_cons_lt (by rw [← end_post]; exact hlt), ← end_post, hpa]
        rfl
      refine WP.spec_bind (range_leaf_spec pa «end» pages hpe) ?_
      intro o ho
      cases o with
      | none =>
        have hpg : pages = true := by
          cases pages
          · rw [rangeFind_false] at ho; cases ho
          · rfl
        refine spec_of_eq rfl ⟨h1, h2, h3, by simp [hpg], ⟨skipped, hsk, ?_, ?_⟩, ?_⟩
        · intro u hu; exact Nat.le_trans (hskb u hu) (Nat.le_of_lt hlt)
        · rw [← hspec, hcons, ← ho]
          simp only [foundOf, Option.map_none, searchList, List.map_cons, hview]
          rw [usableFind_cons_ge (by rw [← end_post]; omega)]
        · simp only [show ¬ «end».val < rg.start.val + rg.size.val by rw [end_post]; omega,
            ↓reduceIte, show fr.val < rg.start.val + rg.size.val by rw [← end_post]; exact hlt]
          omega
      | some leaf =>
        simp only
        split
        · refine spec_of_eq rfl ⟨h1, h2, ?_, skipped, hsk, fun hp u hu => ?_⟩
          · rw [← hspec, hcons, ← ho]
            have hl : leaf.pa.val < limit.val := ‹leaf.pa < limit›
            simp only [foundOf, Option.map_some, hl, ↓reduceIte]
          · rw [← h4 hp]; exact hskb u hu
        · refine spec_of_eq rfl ⟨h1, h2, ?_, skipped, hsk, fun hp u hu => ?_⟩
          · rw [← hspec, hcons, ← ho]
            have hl : ¬ leaf.pa.val < limit.val := ‹¬leaf.pa < limit›
            simp only [foundOf, Option.map_some, Option.map_none, hl, ↓reduceIte]
          · rw [← h4 hp]; exact hskb u hu
    · -- the range ends at or below the address: the next range
      have hge : ¬ fr.val < «end».val := ‹¬fr < «end»›
      refine WP.spec_bind (available_ranges_next_spec rs hM' hR') ?_
      rintro ⟨o, rs1⟩ ⟨f1, f2, ho⟩
      rw [h1, h2] at ho
      cases o with
      | none =>
        have ho' : availableFrom M Rs rs.cursor.bank.val rs.cursor.at.val = [] ∧
            rs.managed.length ≤ rs1.cursor.bank.val := ho
        refine spec_of_eq rfl ⟨by rw [f1]; exact h1, by rw [f2]; exact h2, ?_, skipped, ?_, ?_⟩
        · rw [← hspec]
          simp only [foundOf, Option.map_none, searchList, List.map_cons, hview, ho'.1,
            List.map_nil]
          rw [usableFind_cons_ge (by rw [← end_post]; exact hge)]
          rfl
        · rw [hsk]
          simp only [searchList]
          rw [ho'.1, availableFrom_end (by
            rw [← h1]; simp only [spansOf, List.length_map]; exact ho'.2)]
        · intro hp u hu; rw [← h4 hp]; exact hskb u hu
      | some nx =>
        have hrest : availableFrom M Rs rs.cursor.bank.val rs.cursor.at.val =
            spanOf nx :: availableFrom M Rs rs1.cursor.bank.val rs1.cursor.at.val := ho
        refine spec_of_eq rfl ⟨by rw [f1]; exact h1, by rw [f2]; exact h2, ?_, h4,
          ⟨skipped ++ [spanOf rg], ?_, ?_, ?_⟩, ?_⟩
        · intro u hu
          apply h3
          simp only [searchList] at hu ⊢
          rw [hrest]
          exact List.mem_cons_of_mem _ hu
        · rw [hsk]
          simp only [searchList, List.append_assoc, List.singleton_append, hrest]
        · intro u hu
          rcases List.mem_append.1 hu with hu | hu
          · exact hskb u hu
          · rw [List.mem_singleton] at hu
            subst hu
            show _ ≤ fr.val
            rw [spanOf_endNat, ← end_post]; omega
        · rw [← hspec]
          simp only [searchList, List.map_cons, hview, hrest]
          rw [usableFind_cons_ge (start := rg.start.val) (stop := rg.start.val + rg.size.val)
            (by rw [← end_post]; exact hge)]
        · simp only [hrest, List.length_cons]
          split <;> split <;> omega
  · exact ⟨hm, hr, hv, fun _ => rfl, ⟨[], rfl, fun u hu => absurd hu List.not_mem_nil, rfl⟩⟩

/-- `usable_leaf(ranges, range, from, limit, pages)`: the loop, with the
iterator and the range at which the search stopped. -/
theorem usable_leaf_spec (ranges : fdt.AvailableRanges) (range : fdt.Span) («from» limit : U64)
    (pages : Bool) (M Rs : List Krepi.Spec.Fdt.Span) (hM : ∀ b ∈ M, b.Valid)
    (hRs : ∀ r ∈ Rs, r.Nonempty) (hm : spansOf ranges.managed = M)
    (hr : spansOf ranges.reservations = Rs) (hv : ∀ u ∈ searchList M Rs ranges range, u.Valid) :
    page_tables.boot.direct.usable_leaf ranges range «from» limit pages ⦃ y =>
      spansOf y.1.managed = M ∧ spansOf y.1.reservations = Rs ∧
      foundOf y.2.2 =
        usableFind ((searchList M Rs ranges range).map spanView) «from».val limit.val pages ∧
      ∃ skipped, searchList M Rs ranges range = skipped ++ searchList M Rs y.1 y.2.1 ∧
        (pages = false → ∀ u ∈ skipped, u.endNat ≤ «from».val) ⦄ := by
  unfold page_tables.boot.direct.usable_leaf
  refine WP.spec_bind (usable_leaf_loop_spec limit pages M Rs hM hRs ranges range «from» hm hr hv) ?_
  rintro ⟨s, s1, c, i, i1, o⟩ ⟨h1, h2, h3, skipped, h4, h5⟩
  exact spec_of_eq rfl ⟨h1, h2, h3, skipped, h4, h5⟩

/-- The leaf search of the plan of `direct_map` from a state of its
iterator: `usableFind` of the ranges of the state (`searchList`). -/
def directFind (M Rs : List Krepi.Spec.Fdt.Span) (ranges : fdt.AvailableRanges)
    (range : fdt.Span) : Nat → Nat → Bool → Option Found :=
  fun f l p => usableFind ((searchList M Rs ranges range).map spanView) f l p

/-- The ranges of a state of the leaf search whose leaves the cursor can
take: each within 64 bits, nonempty or ending at 0 (the empty range at 0 of
the start), and ending at or below `2 ^ 39`. -/
def SearchOk (L : List Krepi.Spec.Fdt.Span) : Prop :=
  ∀ u ∈ L, u.Valid ∧ (u.start.toNat < u.endNat ∨ u.endNat = 0) ∧ u.endNat ≤ 2 ^ 39

/-- The leaves that the search finds over ranges of `SearchOk` lie below
`2 ^ 39`, at or above the address of the search. -/
theorem found_of_usableFind {o : Option page_tables.boot.Leaf} {L : List Krepi.Spec.Fdt.Span}
    {frm limit : Nat} {pages : Bool} (hL : SearchOk L)
    (h : foundOf o = usableFind (L.map spanView) frm limit pages) :
    FoundLow o ∧ ∀ l, o = some l → frm ≤ l.pa.val := by
  have hB : ∀ r ∈ L.map spanView, (r.1 < r.2 ∨ r.2 = 0) ∧ r.2 ≤ 2 ^ 39 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
    exact ⟨(hL u hu).2.1, (hL u hu).2.2⟩
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · rw [hl] at h
    exact (usableFind_bounds _ _ _ h.symm hB).2.2
  · rw [hl] at h
    exact (usableFind_bounds _ _ _ h.symm hB).1

/-- `DirectMapPlan::next()` on a pool of at least one table, for an iterator
of the usable ranges over managed banks `M` within 64 bits and nonempty
reservations `Rs`, ranges of the state of `SearchOk`, and a cursor that does
not overflow in this call: one call of `Cur.step` with the leaf search
`directFind` of the state and the place that the cursor reads; the set and
the base stay, and the ranges of the new state are those of the state
without some first ranges, which end at or below the address of the cursor
(`Cur.step` then searches the same leaves from any address at or above it,
`usableFind_skip`). -/
theorem direct_map_plan_next_spec {N : Usize} (it : page_tables.DirectMapPlan N)
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
  obtain ⟨st, hst, hsm, hsr, hsl, hskp⟩ : ∃ st : (Slice fdt.Span × Slice fdt.Span × fdt.Cursor ×
      fdt.Span),
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
          directFind M Rs it.ranges it.range f l p) := by
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
        ha2, ⟨skipped, hsk, hb⟩, ?_⟩
      intro f l p hf
      simp only [directFind]
      rw [hsk, List.map_append, usableFind_skip]
      intro r hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
      exact Nat.le_trans (hb u hu) hf
    · refine ⟨(it.ranges.managed, it.ranges.reservations, it.ranges.cursor, it.range),
        by simp only [hgc, Bool.false_eq_true, ↓reduceIte], hm, hr,
        ⟨[], rfl, fun u hu => absurd hu List.not_mem_nil⟩, fun f l p _ => rfl⟩
  rw [uncurry_apply_pair, hst, bind_ok]
  obtain ⟨sm, sr, sc, sg⟩ := st
  simp only at hsm hsr hsl hskp
  simp only [Cur.step]
  cases mt with
  | Give stp =>
    refine spec_of_eq rfl ⟨?_, ?_, rfl, rfl, hsm, hsr, hsl⟩
    · rw [← hmt]; rfl
    · rw [← hmt]; exact hmc
  | End =>
    refine spec_of_eq rfl ⟨?_, ?_, rfl, rfl, hsm, hsr, hsl⟩
    · rw [← hmt]; rfl
    · rw [← hmt]; exact hmc
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
    refine spec_of_eq rfl ⟨?_, ?_, rfl, rfl, hsm, hsr, hsl⟩
    · rw [← hmt, ← hmc]; simp only [turnOf, Option.map_some, hst1]
    · rw [← hmt, ← hmc]; exact hmc1

/-! ## The search from the start of the plan -/

/-- The ranges of the search of a plan iterator at its start: the empty range
at 0, then the usable ranges. -/
theorem searchList_start {N : Usize} {s : page_tables.Tables N true}
    {P : Krepi.Spec.Fdt.MemoryPlan} {base : U64} {it : page_tables.DirectMapPlan N}
    (h : DirectMapStart s P base it) :
    searchList P.managed P.reservations it.ranges it.range = ⟨0, 0⟩ :: P.availableRanges := by
  obtain ⟨-, -, -, -, -, hb, ha, hs, hz⟩ := h
  have e1 : word64 it.range.start = 0 := by rw [word64, hs]; rfl
  have e2 : word64 it.range.size = 0 := by rw [word64, hz]; rfl
  simp only [searchList, spanOf, e1, e2, hb, ha, ← availableRanges_eq]

/-- The search of a state whose ranges are those of the start without first
ranges that end at or below `b`, from an address at or above `b`, is the
search of the usable ranges `Us`. -/
theorem directFind_eq_of_skip {M Rs Us sk : List Krepi.Spec.Fdt.Span}
    {ranges : fdt.AvailableRanges} {range : fdt.Span} {b : Nat}
    (h : (⟨0, 0⟩ :: Us : List Krepi.Spec.Fdt.Span) = sk ++ searchList M Rs ranges range)
    (hb : ∀ u ∈ sk, u.endNat ≤ b) (f l : Nat) (p : Bool) (hf : b ≤ f) :
    directFind M Rs ranges range f l p = usableFind (Us.map spanView) f l p := by
  have e := congrArg (fun L => usableFind (L.map spanView) f l p) h
  simp only [List.map_cons, List.map_append] at e
  have h0 : spanView ⟨0, 0⟩ = (0, 0) := rfl
  rw [h0, usableFind_zero_cons, usableFind_skip] at e
  · exact e.symm
  · intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
    exact Nat.le_trans (hb u hu) hf

/-- The ranges of the search at the start of the plan of a success of
`Tables.directMap` on a well-formed boot memory map are of `SearchOk`. -/
theorem searchOk_start {N : Usize} {s : page_tables.Tables N true}
    {P : Krepi.Spec.Fdt.MemoryPlan} {base : U64} {bits : U8} {x}
    (hw : P.WellFormed) (hok : (tablesOf s).directMap P (word64 base) (byte bits) = .ok x) :
    SearchOk (⟨0, 0⟩ :: P.availableRanges) := by
  obtain ⟨hne, -, -⟩ := usable_wf hw
  have hlow := directMap_ok_low hw hok
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ⟨by decide, Or.inr rfl, by decide⟩
  · exact ⟨(hne u hu).1.2, Or.inl (Krepi.Proofs.Fdt.nonempty_lt (hne u hu).1), hlow u hu⟩

/-- **The leaf search of the plan as the first leaf at or above an
address.** For a state of the plan whose ranges are those of the start
without first ranges that end at or below `b`, over usable ranges `Us`
nonempty, on pages, within 64 bits and apart in address order, the search
from an address at or above `b` where a leaf starts is `firstFound` of the
leaves of the direct map of `Us`. -/
theorem directFind_eq_firstFound {M Rs Us sk : List Krepi.Spec.Fdt.Span}
    {ranges : fdt.AvailableRanges} {range : fdt.Span} {b : Nat}
    (h : (⟨0, 0⟩ :: Us : List Krepi.Spec.Fdt.Span) = sk ++ searchList M Rs ranges range)
    (hb : ∀ u ∈ sk, u.endNat ≤ b)
    (hUs : ∀ u ∈ Us, u.start.toNat < u.endNat ∧ u.start.toNat % PAGE_SIZE = 0 ∧
      u.endNat % PAGE_SIZE = 0 ∧ u.endNat < 2 ^ 64)
    (hpw : Us.Pairwise (fun a b => a.endNat ≤ b.start.toNat)) (f l : Nat) (p : Bool) (hf : b ≤ f)
    (hls : ∀ u ∈ Us, u.start.toNat < f → f < u.endNat → LeafStart u.start.toNat u.endNat f) :
    directFind M Rs ranges range f l p =
      firstFound ((Us.flatMap usableLeaves).map foundOfLeaf) f l p := by
  rw [directFind_eq_of_skip h hb f l p hf, usableFind_eq_firstFound Us f hUs hpw hls]

/-! ## What `DirectMap` needs besides these triples -/

/-- **The statement `DirectMap` for one input, from the simulation.** For a
map that stands for a boot memory map that the fdt entries built and a record
of the set with the room of `DirectRoom`, `direct_map` satisfies the
conclusion of `DirectMap` as soon as every plan iterator at its start
(`DirectMapStart`) stands for the plan of a success of `Tables.directMap`:
the simulation of `mapPlan` by `DirectMapPlan::next`, whose one step is
`direct_map_plan_next_spec`. -/
theorem direct_map_of_stands {N : Usize} (s : page_tables.Tables N true)
    (memory : fdt.MemoryPlan) (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8)
    (hP : MemoryPlanRepr memory P) (hB : Witnesses.TableSets.BuiltPlan P)
    (hov : DirectRoom s.used.val)
    (hsim : ∀ (it : page_tables.DirectMapPlan N) (S : Tables .upper N.val) (plan : Plan),
      DirectMapStart s P base it →
      (tablesOf s).directMap P (word64 base) (byte bits) = .ok (S, plan) →
      Stands page_tables.boot.direct.DirectMapPlan.next StepRepr it plan) :
    page_tables.direct_map s memory base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (Stands page_tables.boot.direct.DirectMapPlan.next StepRepr)
        (tableErrorOf · = ·) s r s' ((tablesOf s).directMap P (word64 base) (byte bits)) ⦄ := by
  refine spec_mono (direct_map_set_spec s memory P base bits hP hB hov) ?_
  rintro ⟨r, s'⟩ h
  cases hd : (tablesOf s).directMap P (word64 base) (byte bits) with
  | error y =>
    rw [hd] at h
    cases r with
    | Ok a => exact h.elim
    | Err x => exact h
  | ok v =>
    obtain ⟨S, plan⟩ := v
    rw [hd] at h
    cases r with
    | Ok a => exact ⟨hsim a S plan h.1 hd, h.2⟩
    | Err x => exact h.elim

end Krepi.Proofs.PageTables.Refinement
