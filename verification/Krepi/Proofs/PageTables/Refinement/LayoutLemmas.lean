module

public import Krepi.Statements.PageTables.Boot
public import Krepi.Proofs.PageTables.Refinement.CursorLemmas
public import Krepi.Proofs.PageTables.Refinement.LayoutSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the checks of a layout

The triples of the generated functions of `boot/layout.rs` that check a
layout for `kernel_map`, each against the checks of `Tables.kernelMap`.

- `layout_kind_spec` (`LayoutKind::kind`, `layoutKindOf`),
  `holds_guard_spec` (`holds_guard`, `MapLeaf.isGuard` of the page).
- The checks of the pages of a range: `PagesRel` (what the record of the
  checks holds against the leaves that passed), `checkPlace_page` (the check
  of `check_leaf` on a page is the free-slot check of the page of the
  specification), `check_pages_loop_spec` and `check_pages_spec`.
- The checks of a range and of a layout: `checkLayoutRange_tablesOf`,
  `check_range_spec` (`Tables.checkLayoutRange`), `check_layout_loop_spec`
  and `check_layout_spec` (the fold of `Tables.checkLayoutRange` over the
  sorted ranges). These hold for a record of the set at least `2 ^ 33` below
  the largest `usize`, where the count of new tables of the code cannot
  overflow.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-- `LayoutKind::kind()`: the kind of a layout kind. -/
@[step] theorem layout_kind_spec (k : page_tables.LayoutKind) :
    page_tables.boot.layout.LayoutKind.kind k ⦃ k' => kindOf k' = layoutKindOf k ⦄ := by
  cases k <;> exact spec_of_eq rfl rfl

/-- `holds_guard(guards, pa)` for a page whose end fits in 64 bits: whether a
guard address lies in the page at `pa`. -/
@[step] theorem holds_guard_spec (guards : Slice U64) (pa : U64) (hpa : pa.val + 4096 < 2 ^ 64) :
    page_tables.boot.layout.holds_guard guards pa ⦃ b =>
      b = (guards.val.map word64).any
        (fun g => decide (pa.val ≤ g.toNat) && decide (g.toNat < pa.val + PAGE_SIZE)) ⦄ := by
  unfold page_tables.boot.layout.holds_guard page_tables.boot.layout.holds_guard_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => guards.length - i.val)
    (inv := fun (i : Usize) => ((guards.val.map word64).drop i.val).any
        (fun g => decide (pa.val ≤ g.toNat) && decide (g.toNat < pa.val + PAGE_SIZE)) =
      (guards.val.map word64).any
        (fun g => decide (pa.val ≤ g.toNat) && decide (g.toNat < pa.val + PAGE_SIZE)))
  · intro i hinv
    unfold page_tables.boot.layout.holds_guard_loop.body
    simp only [page_size_eq]
    step*
    · have hi : i.val < (guards.val.map word64).length := by simp only [List.length_map]; scalar_tac
      have he : (guards.val.map word64)[i.val]'hi = word64 i1 := by
        simp only [List.getElem_map, i1_post]
      have h1 : pa.val ≤ i1.val := ‹pa ≤ i1›
      have h2 : i1.val < pa.val + 4096 := by have := ‹i1 < i2›; scalar_tac
      rw [← hinv, any_drop_cons hi, he, word64_toNat]
      simp only [PAGE_SIZE, h1, h2, decide_true, Bool.and_self, Bool.true_or]
    · have hi : i.val < (guards.val.map word64).length := by simp only [List.length_map]; scalar_tac
      have he : (guards.val.map word64)[i.val]'hi = word64 i1 := by
        simp only [List.getElem_map, i1_post]
      have h2 : ¬ i1.val < pa.val + 4096 := by have := ‹¬i1 < i2›; scalar_tac
      refine ⟨?_, by scalar_tac⟩
      rw [← hinv, any_drop_cons hi, he, word64_toNat, index1_post]
      simp only [PAGE_SIZE, h2, decide_false, Bool.and_false, Bool.false_or]
    · have hi : i.val < (guards.val.map word64).length := by simp only [List.length_map]; scalar_tac
      have he : (guards.val.map word64)[i.val]'hi = word64 i1 := by
        simp only [List.getElem_map, i1_post]
      have h1 : ¬ pa.val ≤ i1.val := ‹¬pa ≤ i1›
      refine ⟨?_, by scalar_tac⟩
      rw [← hinv, any_drop_cons hi, he, word64_toNat, index1_post]
      simp only [h1, decide_false, Bool.false_and, Bool.false_or]
    · rw [← hinv, List.drop_eq_nil_of_le (by simp only [List.length_map]; scalar_tac)]; rfl
  · rfl

/-- What the record of the checks of the code holds against the leaves `acc`
that passed, latest first, after ranges whose largest end is `reach`: that
end, the record of new tables of `allocOf used acc`, and at most two new
tables a leaf. -/
def PagesRel (used reach : Nat) (check : page_tables.boot.MapCheck)
    (acc : List (MapLeaf × Place)) : Prop :=
  check.reach.val = reach ∧
    AllocRel 0 check.next.val check.gib.val check.slot.val (allocOf used acc) ∧
    check.next.val ≤ used + 2 * acc.length

/-- The check of one page at `pa` by the code (`check_leaf` with the guard
test) is the free-slot check of the page of kind `k` at `pa`, for ranges
before that start at or below `pa`. -/
theorem checkPlace_page {N : Usize} {upper : Bool} (set : page_tables.Tables N upper) (base : U64)
    (k : Kind) (earlier : List PhysRange) (guards : List UInt64) (pa : U64)
    (hstart : ∀ x ∈ earlier, x.start.toNat ≤ pa.val) (b : Bool)
    (hb : b = guards.any (fun g => decide (pa.val ≤ g.toNat) && decide (g.toNat < pa.val + PAGE_SIZE))) :
    checkPlace (tablesOf set) (word64 base) (placeProbe (word64 pa) false)
        (decide (pa.val < reachOf earlier) || b) =
      checkPlace (tablesOf set) (word64 base) (pageLeaf k pa.val)
        (layoutTaken earlier guards (pageLeaf k pa.val)) := by
  have hpa : (pageLeaf k pa.val).pa.toNat = pa.val := UInt64.toNat_ofNat_of_lt' (u64_lt pa)
  rw [layoutTaken, any_meets_eq hpa rfl hstart, isGuard_pageLeaf _ _ _ (u64_lt pa), ← hb]
  exact checkPlace_congr _ (place_congr _ _ rfl rfl rfl rfl)

/-- The loop of `check_pages` from the page at `pa` up to `e`, on a pool of
at least one table, for an end at or below `2 ^ 39`, pages from `start`,
ranges before that start at or below `start`, and a record of new tables
that cannot overflow on the pages left: the fold of the free-slot checks of
those pages (`checkPages`), the record standing for the leaves that passed
(`PagesRel`). -/
theorem check_pages_loop_spec {N : Usize} (set : page_tables.Tables N false) (guards : Slice U64)
    (base e : U64) (k : Kind) (earlier : List PhysRange) (used start : Nat)
    (hN : 0 < N.val) (he : e.val ≤ 2 ^ 39) (he4 : e.val % 4096 = 0)
    (hstart : ∀ x ∈ earlier, x.start.toNat ≤ start)
    (check : page_tables.boot.MapCheck) (pa : U64) (acc : List (MapLeaf × Place))
    (hpa : start ≤ pa.val) (hpa4 : pa.val % 4096 = 0) (hpae : pa.val ≤ e.val)
    (hrel : PagesRel used (reachOf earlier) check acc)
    (hov : used + 2 * (acc.length + (e.val - pa.val) / 4096) + 2 ≤ Usize.max) :
    page_tables.boot.layout.check_pages_loop set check guards base e pa ⦃ r c =>
      Agrees (fun _ acc' => PagesRel used (reachOf earlier) c acc') tableErrorOf r
        (checkPages (tablesOf set) (word64 base) (layoutTaken earlier (guards.val.map word64)) k
          ((e.val - pa.val) / 4096) pa.val acc) ⦄ := by
  unfold page_tables.boot.layout.check_pages_loop
  apply loop.spec_decr_nat
    (measure := fun (x : page_tables.boot.MapCheck × U64) => e.val - x.2.val)
    (inv := fun (x : page_tables.boot.MapCheck × U64) =>
      start ≤ x.2.val ∧ x.2.val % 4096 = 0 ∧ x.2.val ≤ e.val ∧
      ∃ acc', PagesRel used (reachOf earlier) x.1 acc' ∧
        used + 2 * (acc'.length + (e.val - x.2.val) / 4096) + 2 ≤ Usize.max ∧
        checkPages (tablesOf set) (word64 base) (layoutTaken earlier (guards.val.map word64)) k
          ((e.val - x.2.val) / 4096) x.2.val acc' =
        checkPages (tablesOf set) (word64 base) (layoutTaken earlier (guards.val.map word64)) k
          ((e.val - pa.val) / 4096) pa.val acc)
  · rintro ⟨c, p⟩ ⟨h1, h2, h3, acc', hr, hov', hspec⟩
    simp only at h1 h2 h3 hr hov' hspec
    have hn : c.next.val + 2 ≤ Usize.max := by obtain ⟨-, -, h⟩ := hr; omega
    have hm : p.val < e.val → ∃ m, (e.val - p.val) / 4096 = m + 1 := fun h =>
      ⟨(e.val - p.val) / 4096 - 1, by omega⟩
    have hm0 : ¬ p.val < e.val → (e.val - p.val) / 4096 = 0 := fun h => by omega
    have hpe : p.val < e.val → p.val + 4096 ≤ e.val := fun h => by omega
    have hst : ∀ x ∈ earlier, x.start.toNat ≤ p.val := fun x hx => Nat.le_trans (hstart x hx) h1
    have hva : (pageLeaf k p.val).va.toNat = 0 + p.val := by
      rw [Nat.zero_add]; exact UInt64.toNat_ofNat_of_lt' (u64_lt p)
    unfold page_tables.boot.layout.check_pages_loop.body
    simp only [page_size_eq]
    step*
    · obtain ⟨P, hP, hreach', hcount⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      rw [hr.1, checkPlace_page set base k earlier _ p hst b b_post] at hP
      have hlt : p.val < _ := ‹p < _›
      obtain ⟨m, hm'⟩ := hm hlt
      have hle := hpe hlt
      rw [hm', checkPages_succ, hP] at hspec
      have hc1 := congrArg Prod.fst hcount
      have hc2 := congrArg (fun x => x.2.1) hcount
      have hc3 := congrArg (fun x => x.2.2) hcount
      simp only at hc1 hc2 hc3
      have hle2 := countStep_le false P p.val c.next.val c.gib.val c.slot.val
      have hnb := hr.2.2
      have hpa1 : pa1.val = p.val + 4096 := pa1_post
      have hmm : (e.val - pa1.val) / 4096 = m := by rw [hpa1]; exact sub_page_div hm'
      refine ⟨?_, ?_, ?_, ⟨(pageLeaf k p.val, P) :: acc', ⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega
      · rw [hreach']; exact hr.1
      · rw [allocOf_cons, hc1, hc2, hc3]
        exact allocRel_add hr.2.1 (by decide) hva rfl
      · rw [hc1, List.length_cons]; omega
      · rw [List.length_cons]; omega
      · rw [hmm, show pa1.val = p.val + PAGE_SIZE from hpa1]
        exact hspec
      · omega
    · have hE := agrees_err_of_branch cf_post ‹_› residual_post r_post
      rw [hr.1, checkPlace_page set base k earlier _ p hst b b_post] at hE
      obtain ⟨m, hm'⟩ := hm ‹p < _›
      rw [← hspec, hm', checkPages_succ, hE, r1_post, e_post]
      rfl
    · rw [← hspec, hm0 ‹¬p < _›, checkPages_zero]
      exact hr
  · exact ⟨hpa, hpa4, hpae, acc, hrel, hov, rfl⟩

/-- `check_pages(set, check, range, guards, base)` for a range that stands
for a range of the layout, whose ends are page boundaries at or below
`2 ^ 39`, after ranges that start at or below it: the loop over its pages
(`check_pages_loop_spec`). -/
theorem check_pages_spec {N : Usize} (set : page_tables.Tables N false)
    (check : page_tables.boot.MapCheck) (range : page_tables.LayoutRange) (R : LayoutRange)
    (guards : Slice U64) (base : U64) (earlier : List PhysRange) (acc : List (MapLeaf × Place))
    (used : Nat) (hN : 0 < N.val) (hR : LayoutRangeRepr range R)
    (hs4 : range.range.start.val % 4096 = 0)
    (he4 : (range.range.start.val + range.range.len.val) % 4096 = 0)
    (he : range.range.start.val + range.range.len.val ≤ 2 ^ 39)
    (hstart : ∀ x ∈ earlier, x.start.toNat ≤ range.range.start.val)
    (hrel : PagesRel used (reachOf earlier) check acc)
    (hov : used + 2 * (acc.length + range.range.len.val / 4096) + 2 ≤ Usize.max) :
    page_tables.boot.layout.check_pages set check range guards base ⦃ r c =>
      Agrees (fun _ acc' => PagesRel used (reachOf earlier) c acc') tableErrorOf r
        (checkPages (tablesOf set) (word64 base) (layoutTaken earlier (guards.val.map word64))
          R.kind (R.range.len.toNat / PAGE_SIZE) R.range.start.toNat acc) ⦄ := by
  unfold page_tables.boot.layout.check_pages
  have hfit := physRange_fits hR.1
  step*
  have hl := check_pages_loop_spec set guards base «end» R.kind earlier used range.range.start.val hN
    (by rw [end_post]; exact he) (by rw [end_post]; exact he4) hstart check range.range.start acc
    (Nat.le_refl _) hs4 (by rw [end_post]; omega) hrel
    (by rw [end_post, Nat.add_sub_cancel_left]; exact hov)
  rw [end_post, Nat.add_sub_cancel_left] at hl
  rw [physRange_start hR.1, physRange_len hR.1]
  exact hl

/-- `checkLayoutRange_eq` on the set of the code, whose region is that of
`regionOf false`. -/
theorem checkLayoutRange_tablesOf {N : Usize} (set : page_tables.Tables N false) (base : UInt64)
    (bits : UInt8) (guards : List UInt64) (earlier : List PhysRange)
    (leaves : List (MapLeaf × Place)) (j : LayoutRange) :
    (tablesOf set).checkLayoutRange base bits guards (earlier, leaves) j =
      if j.range.start.toNat % PAGE_SIZE ≠ 0 ∨ j.range.endNat % PAGE_SIZE ≠ 0 then
        .error .alignment
      else if VA_LIMIT < j.range.endNat ∨ 2 ^ bits.toNat < j.range.endNat then .error .addressWidth
      else
        (checkPages (tablesOf set) base (layoutTaken earlier guards) j.kind
          (j.range.len.toNat / PAGE_SIZE) j.range.start.toNat leaves).map
          (fun ls => (earlier ++ [j.range], ls)) :=
  checkLayoutRange_eq (tablesOf set) base bits guards earlier leaves j

/-- `check_range(set, check, range, guards, base, bits)` on a pool of at
least one table, for a range that stands for a range of the layout, after
ranges that start at or below it, a width below 64 and a record of new
tables that cannot overflow on the pages of a range below `2 ^ 39`: the
checks of the range, `Tables.checkLayoutRange`, the record standing for the
leaves that passed after the range (`PagesRel`). -/
theorem check_range_spec {N : Usize} (set : page_tables.Tables N false)
    (check : page_tables.boot.MapCheck) (range : page_tables.LayoutRange) (R : LayoutRange)
    (guards : Slice U64) (base : U64) (bits : U8) (earlier : List PhysRange)
    (acc : List (MapLeaf × Place)) (used : Nat) (hN : 0 < N.val) (hR : LayoutRangeRepr range R)
    (hb : bits.val < 64) (hstart : ∀ x ∈ earlier, x.start.toNat ≤ R.range.start.toNat)
    (hrel : PagesRel used (reachOf earlier) check acc)
    (hov : used + 2 * (acc.length + 2 ^ 27) + 2 ≤ Usize.max) :
    page_tables.boot.layout.check_range set check range guards base bits ⦃ r c =>
      Agrees (fun _ (x : List PhysRange × List (MapLeaf × Place)) =>
          x.1 = earlier ++ [R.range] ∧ PagesRel used (reachOf x.1) c x.2) tableErrorOf r
        ((tablesOf set).checkLayoutRange (word64 base) (byte bits) (guards.val.map word64)
          (earlier, acc) R) ⦄ := by
  unfold page_tables.boot.layout.check_range
  have hfit := physRange_fits hR.1
  have hS := physRange_start hR.1
  have hE := physRange_endNat hR.1
  have hB : (byte bits).toNat = bits.val := byte_toNat bits
  simp only [page_size_eq, va_limit_eq]
  step*
  · have hc : R.range.start.toNat % PAGE_SIZE ≠ 0 ∨ R.range.endNat % PAGE_SIZE ≠ 0 :=
      Or.inl (by rw [hS, show PAGE_SIZE = 4096 from rfl, ← i_post]; exact bne_zero_iff.1 ‹_›)
    rw [checkLayoutRange_tablesOf]; simp only [hc, ↓reduceIte]; rfl
  · have hc : R.range.start.toNat % PAGE_SIZE ≠ 0 ∨ R.range.endNat % PAGE_SIZE ≠ 0 :=
      Or.inr (by
        rw [hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i1_post]; exact bne_zero_iff.1 ‹_›)
    rw [checkLayoutRange_tablesOf]; simp only [hc, ↓reduceIte]; rfl
  · have hc : ¬ (R.range.start.toNat % PAGE_SIZE ≠ 0 ∨ R.range.endNat % PAGE_SIZE ≠ 0) := by
      rw [hS, hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i_post, ← i1_post]
      simp only [ne_eq, not_or, Decidable.not_not]
      exact ⟨not_bne_zero_iff.1 ‹_›, not_bne_zero_iff.1 ‹_›⟩
    have hw : VA_LIMIT < R.range.endNat ∨ 2 ^ (byte bits).toNat < R.range.endNat :=
      Or.inl (by rw [hE, ← end_post]; have := ‹«end» > 549755813888#u64›; simp only [VA_LIMIT]; scalar_tac)
    rw [checkLayoutRange_tablesOf]; simp only [hc, hw, ↓reduceIte]; rfl
  · have hc : ¬ (R.range.start.toNat % PAGE_SIZE ≠ 0 ∨ R.range.endNat % PAGE_SIZE ≠ 0) := by
      rw [hS, hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i_post, ← i1_post]
      simp only [ne_eq, not_or, Decidable.not_not]
      exact ⟨not_bne_zero_iff.1 ‹_›, not_bne_zero_iff.1 ‹_›⟩
    have h3 : i3.val = 2 ^ bits.val := by rw [i3_post, u64_size]; exact one_shiftLeft hb
    have hw : VA_LIMIT < R.range.endNat ∨ 2 ^ (byte bits).toNat < R.range.endNat :=
      Or.inr (by rw [hE, ← end_post, hB, ← h3]; exact ‹«end» > i3›)
    rw [checkLayoutRange_tablesOf]; simp only [hc, hw, ↓reduceIte]; rfl
  · have hc : ¬ (R.range.start.toNat % PAGE_SIZE ≠ 0 ∨ R.range.endNat % PAGE_SIZE ≠ 0) := by
      rw [hS, hE, ← end_post, show PAGE_SIZE = 4096 from rfl, ← i_post, ← i1_post]
      simp only [ne_eq, not_or, Decidable.not_not]
      exact ⟨not_bne_zero_iff.1 ‹_›, not_bne_zero_iff.1 ‹_›⟩
    have h3 : i3.val = 2 ^ bits.val := by rw [i3_post, u64_size]; exact one_shiftLeft hb
    have hle : «end».val ≤ 2 ^ 39 := by have := ‹¬«end» > 549755813888#u64›; scalar_tac
    have hle3 : «end».val ≤ 2 ^ bits.val := by rw [← h3]; have := ‹¬«end» > i3›; scalar_tac
    have hw : ¬ (VA_LIMIT < R.range.endNat ∨ 2 ^ (byte bits).toNat < R.range.endNat) := by
      rw [hE, ← end_post, hB]; simp only [VA_LIMIT, not_or, Nat.not_lt]; exact ⟨hle, hle3⟩
    have hs4 : range.range.start.val % 4096 = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have he4 : (range.range.start.val + range.range.len.val) % 4096 = 0 := by
      rw [← end_post, ← i1_post]; exact not_bne_zero_iff.1 ‹_›
    have he : range.range.start.val + range.range.len.val ≤ 2 ^ 39 := by rw [← end_post]; exact hle
    have hst : ∀ x ∈ earlier, x.start.toNat ≤ range.range.start.val := fun x hx => hS ▸ hstart x hx
    have hov' : used + 2 * (acc.length + range.range.len.val / 4096) + 2 ≤ Usize.max := by omega
    have hcp := check_pages_spec set check range R guards base earlier acc used hN hR hs4 he4 he
      hst hrel hov'
    rw [checkLayoutRange_tablesOf]
    simp only [hc, hw, ↓reduceIte]
    refine WP.spec_bind hcp ?_
    rintro ⟨r, check1⟩ hr
    step*
    · obtain ⟨acc', hacc', hrel'⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› hr)
      rw [hacc']
      refine ⟨rfl, ?_⟩
      obtain ⟨h1, h2, h3⟩ := hrel'
      refine ⟨?_, ?_, ?_⟩
      · rw [check2_post, h1, reachOf_append, hE, ← end_post]
      · rw [check2_post1, check2_post2, check2_post3]; exact h2
      · rw [check2_post1]; exact h3
    · rw [agrees_err_of_branch cf_post ‹_› residual_post hr, r1_post, e_post]
      rfl

/-- The loop of `check_layout` from the range at `index`, on a pool of at
least one table, for the first `count` ranges of the code that stand for the
ranges `Rs` sorted by their starts, a width below 64 and a record of the set
at least `2 ^ 33` below the largest `usize`: the fold of
`Tables.checkLayoutRange` over the ranges left, from the ranges before
`index` and the leaves that passed (`PagesRel`). -/
theorem check_layout_loop_spec {N : Usize}
    (a : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N) (i : Usize)
    (ranges : Aeneas.Std.Array page_tables.LayoutRange 16#usize) (count : Usize)
    (guards : Slice U64) (base : U64) (bits : U8) (Rs : List LayoutRange)
    (hN : 0 < N.val) (hb : bits.val < 64) (hc : count.val ≤ 16)
    (hR : ListRel LayoutRangeRepr (ranges.val.take count.val) Rs)
    (hsort : Rs.Pairwise (fun x y => x.range.start.toNat ≤ y.range.start.toNat))
    (hov : i.val + 2 ^ 33 ≤ Usize.max)
    (check : page_tables.boot.MapCheck) (index : Usize)
    (x : List PhysRange × List (MapLeaf × Place)) (hidx : index.val ≤ count.val)
    (hx1 : x.1 = (Rs.take index.val).map (·.range)) (hx2 : x.2.length ≤ index.val * 2 ^ 27)
    (hrel : PagesRel i.val (reachOf x.1) check x.2) :
    page_tables.boot.layout.check_layout_loop a i ranges count guards base bits check index ⦃ r =>
      Agrees (fun c (y : List PhysRange × List (MapLeaf × Place)) =>
          PagesRel i.val (reachOf y.1) c y.2) tableErrorOf r
        ((Rs.drop index.val).foldlM
          ((tablesOf ({ pool := a, used := i } : page_tables.Tables N false)).checkLayoutRange
            (word64 base) (byte bits) (guards.val.map word64)) x) ⦄ := by
  have hlen : Rs.length = count.val := by
    rw [← listRel_length hR, List.length_take]
    have : ranges.val.length = 16 := by simp
    omega
  unfold page_tables.boot.layout.check_layout_loop
  apply loop.spec_decr_nat
    (measure := fun (z : page_tables.boot.MapCheck × Usize) => count.val - z.2.val)
    (inv := fun (z : page_tables.boot.MapCheck × Usize) =>
      z.2.val ≤ count.val ∧ ∃ y : List PhysRange × List (MapLeaf × Place),
        y.1 = (Rs.take z.2.val).map (·.range) ∧ y.2.length ≤ z.2.val * 2 ^ 27 ∧
        PagesRel i.val (reachOf y.1) z.1 y.2 ∧
        (Rs.drop z.2.val).foldlM
          ((tablesOf ({ pool := a, used := i } : page_tables.Tables N false)).checkLayoutRange
            (word64 base) (byte bits) (guards.val.map word64)) y =
        (Rs.drop index.val).foldlM
          ((tablesOf ({ pool := a, used := i } : page_tables.Tables N false)).checkLayoutRange
            (word64 base) (byte bits) (guards.val.map word64)) x)
  · rintro ⟨c, idx⟩ ⟨h1, ⟨e, l⟩, hy1, hy2, hyr, hspec⟩
    simp only at h1 hy1 hy2 hyr hspec
    unfold page_tables.boot.layout.check_layout_loop.body
    step*
    · have hi : idx.val < Rs.length := by rw [hlen]; exact ‹idx < count›
      have hi' : idx.val < (ranges.val.take count.val).length := by
        rw [listRel_length hR]; exact hi
      have hrep : LayoutRangeRepr lr Rs[idx.val] := by
        have := listRel_getElem hR idx.val hi' hi
        rwa [List.getElem_take, ← lr_post] at this
      have hst : ∀ y ∈ e, y.start.toNat ≤ Rs[idx.val].range.start.toNat := by
        intro y hy
        rw [hy1, List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
        have hj' : j < idx.val := by simp only [List.length_take] at hj; omega
        rw [List.getElem_take]
        exact List.pairwise_iff_getElem.1 hsort j idx.val (by omega) hi hj'
      have hidx15 : idx.val ≤ 15 := by have := ‹idx < count›; scalar_tac
      have hov' : i.val + 2 * (l.length + 2 ^ 27) + 2 ≤ Usize.max := layout_room hov hy2 hidx15
      have hcr := check_range_spec { pool := a, used := i } c lr Rs[idx.val] guards base bits e l
        i.val hN hrep hb hst hyr hov'
      refine WP.spec_bind hcr ?_
      rintro ⟨r, check1⟩ hr
      rw [List.drop_eq_getElem_cons hi, List.foldlM_cons] at hspec
      step*
      · obtain ⟨y', hy', hy'1, hy'r⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› hr)
        rw [hy'] at hspec
        obtain ⟨-, hlen'⟩ := checkLayoutRange_ok (show _ = Except.ok (y'.1, y'.2) from hy')
        refine ⟨by scalar_tac, ⟨y', ?_, ?_, hy'r, ?_⟩, by scalar_tac⟩
        · rw [index1_post, hy'1, hy1, List.take_succ_eq_append_getElem hi, List.map_append]; rfl
        · rw [index1_post]; omega
        · rw [index1_post]; exact hspec
      · rw [← hspec, agrees_err_of_branch cf_post ‹_› residual_post hr, r1_post, e_post]
        rfl
    · have hle : count.val ≤ idx.val := by have := ‹¬idx < count›; scalar_tac
      rw [← hspec, List.drop_eq_nil_of_le (by omega)]
      exact hyr
  · exact ⟨hidx, x, hx1, hx2, hrel, rfl⟩

/-- `check_layout(set, ranges, count, guards, base, bits)` on a pool of at
least one table, for the first `count` ranges of the code that stand for the
ranges `Rs` sorted by their starts, a width below 64 and a record of the set
at least `2 ^ 33` below the largest `usize`: the fold of
`Tables.checkLayoutRange` over `Rs` that `Tables.kernelMap` makes, with the
record of the checks standing for its result (`PagesRel`). -/
theorem check_layout_spec {N : Usize} (set : page_tables.Tables N false)
    (ranges : Aeneas.Std.Array page_tables.LayoutRange 16#usize) (count : Usize)
    (guards : Slice U64) (base : U64) (bits : U8) (Rs : List LayoutRange)
    (hN : 0 < N.val) (hb : bits.val < 64) (hc : count.val ≤ 16)
    (hR : ListRel LayoutRangeRepr (ranges.val.take count.val) Rs)
    (hsort : Rs.Pairwise (fun x y => x.range.start.toNat ≤ y.range.start.toNat))
    (hov : set.used.val + 2 ^ 33 ≤ Usize.max) :
    page_tables.boot.layout.check_layout set ranges count guards base bits ⦃ r =>
      Agrees (fun c (y : List PhysRange × List (MapLeaf × Place)) =>
          PagesRel set.used.val (reachOf y.1) c y.2) tableErrorOf r
        (Rs.foldlM ((tablesOf set).checkLayoutRange (word64 base) (byte bits)
          (guards.val.map word64)) ([], [])) ⦄ := by
  unfold page_tables.boot.layout.check_layout
  step*
  have hrel : PagesRel set.used.val (reachOf []) check [] := by
    refine ⟨check_post, ?_, ?_⟩
    · rw [check_post1, ‹check.gib.val = noSlot›, ‹check.slot.val = noSlot›]
      exact allocRel_init 0 set.used.val
    · rw [check_post1]; simp
  exact check_layout_loop_spec set.pool set.used ranges count guards base bits Rs hN hb hc hR hsort
    hov check 0#usize ([], []) (Nat.zero_le _) rfl (Nat.zero_le _) hrel

end Krepi.Proofs.PageTables.Refinement
