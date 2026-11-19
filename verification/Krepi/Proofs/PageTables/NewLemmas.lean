module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.PageTables.RunLemmas
public import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.ListLemmas

/-!
# Page tables: lemmas about the table of `Ownership::new`

What `Ownership.new` builds: its checks, its banks in address order and its
free extents, one for each maximal run of the pages of a bank that no
exclusion touches.

- `new_ok`: a table that `Ownership.new` gives passed every check and is
  the arena, the sorted banks, `initialExtents` of them, the exclusions and
  the counter at 1;
- the pages that an exclusion cuts out of a bank: `cut_some` (a cut is a
  nonempty range of whole pages of the bank, whose pages are those that the
  exclusion touches) and `cut_none` (an exclusion without a cut touches no
  page of the bank);
- the free extents of one bank: `bankExtents_eq` (they are the runs of
  `cutAll` of the cuts of the exclusions), `mem_bankExtents` (each is free,
  of the bank's index, inside the bank and, for a bank on pages, on pages),
  `bankExtents_strict` (in strict address order, apart from each other) and
  `bankExtents_holds_iff` (a page of a bank on pages lies in one exactly when
  it lies in the bank and no exclusion touches it);
- the extents of all banks: `mem_initialExtents` and `mem_initialExtents_go`
  (each is one of the free extents of the bank that it names), `initialExtents_inOrder` (in address
  order for banks in address order) and `initialExtents_holds_iff` (a page
  lies in one exactly when it lies in a bank and no exclusion touches it);
- the banks: `anyOverlap_eq_false` (no two overlap) and
  `sortByKey_banks_inOrder` (sorted by their start, banks that do not
  overlap are in address order).

The private `bankRuns` and `bankRuns_facts` name the runs of one bank and
their shape: nonempty, inside the bank, in strict address order and, for a
bank on pages, on pages.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables

/-- `omega` after the page size is written as its value. -/
local macro "page_omega" : tactic => `(tactic| (simp only [PAGE_SIZE] at *; omega))

theorem new_ok {E X : Nat} {arena : UInt64} {banks : List PhysRange} {exclusions : List Exclusion}
    {t : Ownership E X} (h : Ownership.new arena banks exclusions = .ok t) :
    (∀ b ∈ banks, b.onPages = true) ∧ arena ≠ 0 ∧ banks ≠ [] ∧ banks.length ≤ E ∧
      anyOverlap banks = false ∧ exclusions.length ≤ X ∧
      (initialExtents (sortByKey (·.start.toNat) banks) exclusions).length ≤ E ∧
      t = ⟨arena, sortByKey (·.start.toNat) banks,
        initialExtents (sortByKey (·.start.toNat) banks) exclusions, exclusions, .next 1⟩ := by
  unfold Ownership.new at h
  by_cases h1 : banks.all (·.onPages) = true <;>
  by_cases h2 : arena = 0 <;>
  by_cases h3 : banks.isEmpty = true <;>
  by_cases h4 : E < banks.length <;>
  by_cases h5 : anyOverlap banks = true <;>
  by_cases h6 : X < exclusions.length <;>
  by_cases h7 : E < (initialExtents (sortByKey (·.start.toNat) banks) exclusions).length <;>
  simp only [h1, h2, h3, h4, h5, h6, h7, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
    pure, Except.pure, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false,
    reduceCtorEq, Except.ok.injEq] at h
  subst h
  refine ⟨List.all_eq_true.1 h1, h2, fun h0 => h3 (by simp [h0]), by omega,
    by simpa using h5, by omega, by omega, rfl⟩

theorem cut_some {x : Exclusion} {b : PhysRange} {s t : Nat} (h : x.cut b = some (s, t)) :
    s < t ∧ b.start.toNat ≤ s ∧ t ≤ b.endNat ∧
      (b.onPages = true → s % PAGE_SIZE = 0 ∧ t % PAGE_SIZE = 0) ∧
      ∀ q, q % PAGE_SIZE = 0 →
        (s ≤ q ∧ q < t ↔ x.range.touchesPage q = true ∧ b.start.toNat ≤ q ∧ q < b.endNat) := by
  unfold Exclusion.cut at h
  split at h
  · rename_i ho
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [PhysRange.overlaps, Bool.and_eq_true, decide_eq_true_eq] at ho
    have h1 := range_lt x.range
    have h2 := range_lt b
    simp only [touchesPage_iff, PhysRange.onPages, Bool.and_eq_true, beq_iff_eq, pageDown,
      pageUp, PAGE_SIZE] at ho ⊢
    refine ⟨by omega, by omega, by omega, fun hb => ⟨by omega, by omega⟩, fun q hq => by omega⟩
  · exact absurd h (by simp)

theorem cut_none {x : Exclusion} {b : PhysRange} (h : x.cut b = none) {q : Nat}
    (hq : b.holdsPage q = true) : x.range.touchesPage q = false := by
  unfold Exclusion.cut at h
  split at h
  · exact absurd h (by simp)
  · rename_i ho
    rw [holdsPage_iff] at hq
    simp only [PhysRange.overlaps, Bool.and_eq_true, decide_eq_true_eq] at ho
    rw [← Bool.not_eq_true, touchesPage_iff]
    omega

theorem bankExtents_eq (exclusions : List Exclusion) (i : Nat) (b : PhysRange) :
    bankExtents exclusions i b =
      (cutAll (exclusions.filterMap (·.cut b)) [(b.start.toNat, b.endNat)]).filterMap
        fun r => (rangeOf? r.1 (r.2 - r.1)).map (⟨·, i, .free⟩) := by
  unfold bankExtents
  dsimp only
  congr 1
  generalize [(b.start.toNat, b.endNat)] = init
  induction exclusions generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.filterMap_cons]
    cases h : x.cut b with
    | none => exact ih init
    | some c =>
      obtain ⟨s, t⟩ := c
      exact ih _

/-- The runs of a bank less the cuts of the exclusions. -/
private abbrev bankRuns (exclusions : List Exclusion) (b : PhysRange) : List (Nat × Nat) :=
  cutAll (exclusions.filterMap (·.cut b)) [(b.start.toNat, b.endNat)]

private theorem bankRuns_facts (exclusions : List Exclusion) (b : PhysRange) :
    (∀ r ∈ bankRuns exclusions b, r.1 < r.2 ∧ b.start.toNat ≤ r.1 ∧ r.2 ≤ b.endNat) ∧
      (bankRuns exclusions b).Pairwise (fun x y => x.2 < y.1) ∧
      (b.onPages = true → ∀ r ∈ bankRuns exclusions b, r.1 % PAGE_SIZE = 0 ∧ r.2 % PAGE_SIZE = 0) := by
  have hcut : ∀ c ∈ exclusions.filterMap (·.cut b), ∃ x ∈ exclusions, x.cut b = some c := by
    intro c hc
    simpa using hc
  refine ⟨fun r hr => ⟨?_, ?_⟩, ?_, fun hb => ?_⟩
  · exact cutAll_nonempty _ _ (by simpa using range_lt b) r hr
  · obtain ⟨r', h1, h2⟩ := cutAll_sub _ _ r hr
    simp only [List.mem_singleton] at h1
    subst h1
    exact ⟨h2.1, h2.2⟩
  · refine cutAll_pairwise _ _ (fun c hc => ?_) (by simp)
    obtain ⟨x, _, hx⟩ := hcut c hc
    exact (cut_some hx).1
  · refine cutAll_aligned _ _ (fun c hc => ?_) ?_
    · obtain ⟨x, _, hx⟩ := hcut c hc
      exact (cut_some hx).2.2.2.1 hb
    · simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hb
      simpa using hb

theorem mem_bankExtents {exclusions : List Exclusion} {i : Nat} {b : PhysRange} {e : Extent}
    (he : e ∈ bankExtents exclusions i b) :
    e.bank = i ∧ e.holding = .free ∧ b.start.toNat ≤ e.range.start.toNat ∧
      e.range.endNat ≤ b.endNat ∧ (b.onPages = true → e.range.onPages = true) := by
  rw [bankExtents_eq, List.mem_filterMap] at he
  obtain ⟨r, hr, he⟩ := he
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 he
  obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hg
  obtain ⟨h3, h4, h5⟩ := bankRuns_facts exclusions b
  have := h3 r hr
  refine ⟨rfl, rfl, by simp only; omega, by simp only; omega, fun hb => ?_⟩
  have := h5 hb r hr
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq]
  constructor <;> page_omega

theorem bankExtents_strict (exclusions : List Exclusion) (i : Nat) (b : PhysRange) :
    (bankExtents exclusions i b).Pairwise
      (fun x y => x.range.endNat < y.range.start.toNat) := by
  rw [bankExtents_eq]
  refine List.Pairwise.filterMap _ (fun r r' h e he e' he' => ?_) (bankRuns_facts exclusions b).2.1
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 he
  obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 he'
  obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hg
  obtain ⟨_, _, h3, h4⟩ := rangeOf?_eq_some.1 hg'
  simp only
  omega

theorem bankExtents_holds_iff {exclusions : List Exclusion} {i : Nat} {b : PhysRange}
    (hb : b.onPages = true) {q : Nat} (hq : q % PAGE_SIZE = 0) :
    (∃ e ∈ bankExtents exclusions i b, e.range.holdsPage q = true) ↔
      b.holdsPage q = true ∧ ∀ x ∈ exclusions, x.range.touchesPage q = false := by
  obtain ⟨h3, _, h5⟩ := bankRuns_facts exclusions b
  have h5 := h5 hb
  have hb' := hb
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hb'
  -- the extents that hold the page are those of the runs that hold it
  have step1 : (∃ e ∈ bankExtents exclusions i b, e.range.holdsPage q = true) ↔
      ∃ r ∈ bankRuns exclusions b, r.1 ≤ q ∧ q < r.2 := by
    rw [bankExtents_eq]
    constructor
    · rintro ⟨e, he, hq'⟩
      obtain ⟨r, hr, he⟩ := List.mem_filterMap.1 he
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 he
      obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hg
      rw [holdsPage_iff] at hq'
      exact ⟨r, hr, by simp only at hq'; omega, by simp only at hq'; page_omega⟩
    · rintro ⟨r, hr, h1, h2⟩
      have := h3 r hr
      have := h5 r hr
      have := range_lt b
      have := b.fits
      obtain ⟨g, hg, hg1, hg2⟩ := rangeOf?_exists (s := r.1) (l := r.2 - r.1) (by omega)
        (by unfold PhysRange.endNat at *; omega)
      refine ⟨⟨g, i, .free⟩, List.mem_filterMap.2 ⟨r, hr, by rw [hg]; rfl⟩, ?_⟩
      rw [holdsPage_iff]
      simp only
      page_omega
  rw [step1, cutAll_mem, holdsPage_iff]
  simp only [List.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨⟨h1, h2⟩, hc⟩
    refine ⟨⟨h1, by page_omega⟩, fun x hx => ?_⟩
    cases hxc : x.cut b with
    | none => exact cut_none hxc ((holdsPage_iff b q).2 ⟨h1, by page_omega⟩)
    | some c =>
      obtain ⟨s, t⟩ := c
      have hm : (s, t) ∈ exclusions.filterMap (·.cut b) := List.mem_filterMap.2 ⟨x, hx, hxc⟩
      have hst := (cut_some hxc).2.2.2.2 q hq
      rw [← Bool.not_eq_true]
      intro ht
      exact hc _ hm (hst.2 ⟨ht, h1, h2⟩)
  · rintro ⟨⟨h1, h2⟩, hx⟩
    refine ⟨⟨h1, by page_omega⟩, fun c hc hc' => ?_⟩
    obtain ⟨x, hx', hxc⟩ := List.mem_filterMap.1 hc
    obtain ⟨s, t⟩ := c
    have := ((cut_some hxc).2.2.2.2 q hq).1 hc'
    rw [hx x hx'] at this
    exact absurd this.1 (by simp)

theorem mem_initialExtents_go {exclusions : List Exclusion} {e : Extent} :
    ∀ {banks : List PhysRange} {k : Nat}, e ∈ initialExtents.go exclusions k banks ↔
      ∃ j b, banks[j]? = some b ∧ e ∈ bankExtents exclusions (k + j) b
  | [], k => by simp [initialExtents.go]
  | b :: rest, k => by
    rw [initialExtents.go, List.mem_append, mem_initialExtents_go]
    constructor
    · rintro (h | ⟨j, b', hj, h⟩)
      · exact ⟨0, b, rfl, h⟩
      · exact ⟨j + 1, b', by simpa using hj, by rw [← Nat.add_assoc, Nat.add_right_comm]; exact h⟩
    · rintro ⟨j, b', hj, h⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        exact Or.inl h
      | succ j =>
        refine Or.inr ⟨j, b', by simpa using hj, ?_⟩
        rw [Nat.add_right_comm, Nat.add_assoc]
        exact h

theorem mem_initialExtents {banks : List PhysRange} {exclusions : List Exclusion} {e : Extent} :
    e ∈ initialExtents banks exclusions ↔
      ∃ j b, banks[j]? = some b ∧ e ∈ bankExtents exclusions j b := by
  unfold initialExtents
  rw [mem_initialExtents_go]
  simp only [Nat.zero_add]

theorem initialExtents_inOrder {exclusions : List Exclusion} :
    ∀ {banks : List PhysRange} {k : Nat},
      banks.Pairwise (fun a b => a.endNat ≤ b.start.toNat) →
      ExtentsInOrder (initialExtents.go exclusions k banks)
  | [], _, _ => by simp [initialExtents.go]
  | b :: rest, k, h => by
    rw [List.pairwise_cons] at h
    rw [initialExtents.go, ExtentsInOrder, List.pairwise_append]
    refine ⟨(bankExtents_strict exclusions k b).imp (fun h => Nat.le_of_lt h),
      initialExtents_inOrder h.2, fun x hx y hy => ?_⟩
    obtain ⟨_, _, _, hx2, _⟩ := mem_bankExtents hx
    obtain ⟨j, b', hj, hy⟩ := mem_initialExtents_go.1 hy
    obtain ⟨_, _, hy1, _, _⟩ := mem_bankExtents hy
    have := h.1 b' (List.mem_of_getElem? hj)
    omega

theorem initialExtents_holds_iff {banks : List PhysRange} {exclusions : List Exclusion}
    (hb : ∀ b ∈ banks, b.onPages = true) {q : Nat} (hq : q % PAGE_SIZE = 0) :
    (∃ e ∈ initialExtents banks exclusions, e.range.holdsPage q = true) ↔
      (∃ b ∈ banks, b.holdsPage q = true) ∧ ∀ x ∈ exclusions, x.range.touchesPage q = false := by
  constructor
  · rintro ⟨e, he, hq'⟩
    obtain ⟨j, b, hj, he⟩ := mem_initialExtents.1 he
    have hm := List.mem_of_getElem? hj
    obtain ⟨h1, h2⟩ := (bankExtents_holds_iff (hb b hm) hq).1 ⟨e, he, hq'⟩
    exact ⟨⟨b, hm, h1⟩, h2⟩
  · rintro ⟨⟨b, hm, h1⟩, h2⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
    obtain ⟨e, he, hq'⟩ := (bankExtents_holds_iff (i := j) (hb b hm) hq).2 ⟨h1, h2⟩
    exact ⟨e, mem_initialExtents.2 ⟨j, b, hj, he⟩, hq'⟩

theorem anyOverlap_eq_false : ∀ {banks : List PhysRange}, anyOverlap banks = false →
    banks.Pairwise (fun a b => a.overlaps b = false)
  | [], _ => List.Pairwise.nil
  | r :: rest, h => by
    simp only [anyOverlap, Bool.or_eq_false_iff, List.any_eq_false] at h
    exact List.pairwise_cons.2 ⟨fun b hb => by simpa using h.1 b hb, anyOverlap_eq_false h.2⟩

theorem sortByKey_banks_inOrder {banks : List PhysRange} (h : anyOverlap banks = false) :
    (sortByKey (·.start.toNat) banks).Pairwise (fun a b => a.endNat ≤ b.start.toNat) := by
  have hsym : ∀ {a b : PhysRange}, a.overlaps b = false → b.overlaps a = false := by
    intro a b hab
    simp only [PhysRange.overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hab ⊢
    omega
  have h1 := (List.Perm.pairwise_iff hsym (sortByKey_perm (·.start.toNat) banks)).2
    (anyOverlap_eq_false h)
  refine (h1.and (sortByKey_pairwise (·.start.toNat) banks)).imp fun {a b} h => ?_
  obtain ⟨ho, hs⟩ := h
  simp only [PhysRange.overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ho
  have := range_lt b
  omega

end Krepi.Proofs.PageTables
