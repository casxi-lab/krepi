module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas about the owner function of a page ownership table

What the extents of a page ownership table in address order tell about its
owner function `Ownership.ownerOf` and the owners `Ownership.ownersOf` that
it records, for any table:

- ranges: `range_lt` (a range starts below its end), `range_eq` (a range is
  its start and its end), `rangeOf?_eq_some` and `rangeOf?_exists` (the
  range of `rangeOf?`, and when there is one), `holdsPage_iff` and
  `touchesPage_iff` (the tests of a page as inequalities);
- `pairwise_mem_cases`: two elements of a list in which every pair is
  related are equal or related one way or the other;
- `ExtentsInOrder`, the order of the extents of `Ownership.WellFormed`, with
  `inOrder_split` (the extents before and after an extent of an ordered list)
  and `inOrder_sandwich` (a block of ordered extents between the bounds of
  the extents around it keeps the list ordered);
- the extent that holds a page: `find?_holds_of_mem` (in an ordered list the
  search for the page finds every extent that holds it, so there is one) and
  `filter_holds_length_le` (at most one extent holds a page);
- the owner function: `ownerOf_of_mem` (a page of an extent has its owner),
  `ownerOf_of_forall` (a page of no extent has the owner of the exclusion
  records), `ownerOf_freeOrHeld` (a free or held owner is that of an extent
  that holds the page), `ownerOf_held` (likewise for a holder),
  `freeOrHeld_iff` (a page is free or held exactly when an extent holds it)
  and `ownerOf_congr` (two tables whose extents differ in one block, with the
  same owners of the page in the block, give the page one owner);
- the exclusion records: `firstExcluder_isSome` (they give an owner exactly
  when one touches the page);
- the owners recorded: `ownersOf_length_eq_one` (on ordered extents, a page
  has one recorded owner exactly when an extent holds it or else an
  exclusion record touches it).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables

theorem range_lt (r : PhysRange) : r.start.toNat < r.endNat := by
  have h := r.nonempty
  have : r.len.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.1 (by simpa using h0))
  unfold PhysRange.endNat
  omega

theorem range_eq {r r' : PhysRange} (h1 : r.start.toNat = r'.start.toNat)
    (h2 : r.endNat = r'.endNat) : r = r' := by
  obtain ⟨s, l, _, _⟩ := r
  obtain ⟨s', l', _, _⟩ := r'
  unfold PhysRange.endNat at h2
  simp only at h1 h2
  have hs : s = s' := UInt64.toNat_inj.1 h1
  have hl : l = l' := UInt64.toNat_inj.1 (by omega)
  subst hs hl
  rfl

theorem rangeOf?_eq_some {s l : Nat} {r : PhysRange} :
    rangeOf? s l = some r ↔ 0 < l ∧ s + l < 2 ^ 64 ∧ r.start.toNat = s ∧ r.endNat = s + l := by
  unfold rangeOf?
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨h.1, h.2, by simp, by simp [PhysRange.endNat]⟩
    · rintro ⟨_, _, h1, h2⟩
      exact range_eq (by simp [h1]) (by rw [h2]; simp [PhysRange.endNat])
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    omega

theorem rangeOf?_exists {s l : Nat} (h1 : 0 < l) (h2 : s + l < 2 ^ 64) :
    ∃ r, rangeOf? s l = some r ∧ r.start.toNat = s ∧ r.endNat = s + l := by
  cases h : rangeOf? s l with
  | none =>
    unfold rangeOf? at h
    rw [dite_eq_left ⟨h1, h2⟩] at h
    exact absurd h (by simp)
  | some r =>
    obtain ⟨_, _, h3, h4⟩ := rangeOf?_eq_some.1 h
    exact ⟨r, rfl, h3, h4⟩

theorem pairwise_mem_cases {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (h.1 b hb'))
    · exact Or.inr (Or.inr (h.1 a ha'))
    · exact pairwise_mem_cases h.2 ha' hb'

theorem holdsPage_iff (r : PhysRange) (q : Nat) :
    r.holdsPage q = true ↔ r.start.toNat ≤ q ∧ q + PAGE_SIZE ≤ r.endNat := by
  simp [PhysRange.holdsPage]

theorem touchesPage_iff (r : PhysRange) (q : Nat) :
    r.touchesPage q = true ↔ r.start.toNat < q + PAGE_SIZE ∧ q < r.endNat := by
  simp [PhysRange.touchesPage]

/-- The extents in address order and disjoint, as `Ownership.WellFormed`
keeps them. -/
abbrev ExtentsInOrder (l : List Extent) : Prop :=
  l.Pairwise (fun a b => a.range.endNat ≤ b.range.start.toNat)

theorem inOrder_split {l₁ l₂ : List Extent} {e : Extent} (h : ExtentsInOrder (l₁ ++ e :: l₂)) :
    ExtentsInOrder l₁ ∧ ExtentsInOrder l₂ ∧ (∀ x ∈ l₁, x.range.endNat ≤ e.range.start.toNat) ∧
      ∀ y ∈ l₂, e.range.endNat ≤ y.range.start.toNat := by
  rw [ExtentsInOrder, List.pairwise_append, List.pairwise_cons] at h
  exact ⟨h.1, h.2.1.2, fun x hx => h.2.2 x hx e List.mem_cons_self, h.2.1.1⟩

theorem inOrder_sandwich {l₁ M l₂ : List Extent} {lo hi : Nat} (h₁ : ExtentsInOrder l₁)
    (h₂ : ExtentsInOrder l₂) (hM : ExtentsInOrder M) (hlh : lo ≤ hi)
    (hl₁ : ∀ x ∈ l₁, x.range.endNat ≤ lo) (hl₂ : ∀ y ∈ l₂, hi ≤ y.range.start.toNat)
    (hm : ∀ x ∈ M, lo ≤ x.range.start.toNat ∧ x.range.endNat ≤ hi) :
    ExtentsInOrder (l₁ ++ M ++ l₂) := by
  rw [ExtentsInOrder, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨h₁, hM, fun x hx y hy => ?_⟩, h₂, fun x hx y hy => ?_⟩
  · have := hl₁ x hx; have := hm y hy; omega
  · have := hl₂ y hy
    rcases List.mem_append.1 hx with hx | hx
    · have := hl₁ x hx; omega
    · have := hm x hx; omega

theorem find?_holds_of_mem {q : Nat} : ∀ {l : List Extent} {x : Extent}, ExtentsInOrder l →
    x ∈ l → x.range.holdsPage q = true → l.find? (·.range.holdsPage q) = some x
  | [], _, _, hx, _ => absurd hx (List.not_mem_nil)
  | y :: ys, x, hl, hx, hq => by
    rw [ExtentsInOrder, List.pairwise_cons] at hl
    rw [List.find?_cons]
    by_cases hy : y.range.holdsPage q = true
    · rw [hy]
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · have := hl.1 x hx
        rw [holdsPage_iff] at hq hy
        have : PAGE_SIZE = 4096 := rfl
        omega
    · rw [Bool.not_eq_true] at hy
      rw [hy]
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hq] at hy; exact absurd hy (by simp)
      · exact find?_holds_of_mem hl.2 hx hq

theorem filter_holds_length_le (q : Nat) : ∀ {l : List Extent}, ExtentsInOrder l →
    (l.filter (·.range.holdsPage q)).length ≤ 1
  | [], _ => by simp
  | y :: ys, hl => by
    rw [ExtentsInOrder, List.pairwise_cons] at hl
    rw [List.filter_cons]
    split
    · rename_i hy
      have : ys.filter (·.range.holdsPage q) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx hq
        have := hl.1 x hx
        rw [holdsPage_iff] at hq hy
        have : PAGE_SIZE = 4096 := rfl
        omega
      simp [this]
    · exact filter_holds_length_le q hl.2

theorem ownerOf_of_mem {E X : Nat} {t : Ownership E X} {x : Extent} {q : Nat}
    (hl : ExtentsInOrder t.extents) (hx : x ∈ t.extents) (hq : x.range.holdsPage q = true) :
    t.ownerOf q = some x.holding.owner := by
  unfold Ownership.ownerOf
  rw [find?_holds_of_mem hl hx hq]

theorem ownerOf_of_forall {E X : Nat} {t : Ownership E X} {q : Nat}
    (h : ∀ x ∈ t.extents, x.range.holdsPage q = false) :
    t.ownerOf q = if t.banks.any (·.holdsPage q) then
      (firstExcluder t.exclusions q).map .excluded else none := by
  unfold Ownership.ownerOf
  rw [List.find?_eq_none.2 (fun x hx => by simp [h x hx])]

theorem ownerOf_freeOrHeld {E X : Nat} {t : Ownership E X} {q : Nat} {o : Owner}
    (h : t.ownerOf q = some o) (ho : o.isFreeOrHeld = true) :
    ∃ x ∈ t.extents, x.range.holdsPage q = true ∧ x.holding.owner = o := by
  unfold Ownership.ownerOf at h
  split at h
  · rename_i x hx
    have hq := List.find?_some hx
    exact ⟨x, List.mem_of_find?_eq_some hx, by simpa using hq, Option.some.inj h⟩
  · split at h
    · obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [Owner.isFreeOrHeld] at ho
    · exact absurd h (by simp)

theorem owner_eq_held {h : Holding} {o n : UInt64} {s : HoldState}
    (e : h.owner = .held o n s) : h = .held o n s := by
  cases h <;> simp_all [Holding.owner]

theorem ownerOf_held {E X : Nat} {t : Ownership E X} {q : Nat} {o n : UInt64} {s : HoldState}
    (h : t.ownerOf q = some (.held o n s)) :
    ∃ x ∈ t.extents, x.range.holdsPage q = true ∧ x.holding = .held o n s := by
  obtain ⟨x, hx, hq, he⟩ := ownerOf_freeOrHeld h rfl
  exact ⟨x, hx, hq, owner_eq_held he⟩

theorem freeOrHeld_iff {E X : Nat} (t : Ownership E X) (q : Nat) :
    (∃ o, t.ownerOf q = some o ∧ o.isFreeOrHeld = true) ↔
      ∃ x ∈ t.extents, x.range.holdsPage q = true := by
  constructor
  · rintro ⟨o, h, ho⟩
    obtain ⟨x, hx, hq, _⟩ := ownerOf_freeOrHeld h ho
    exact ⟨x, hx, hq⟩
  · rintro ⟨x, hx, hq⟩
    unfold Ownership.ownerOf
    cases hf : t.extents.find? (·.range.holdsPage q) with
    | none => exact absurd hx (List.find?_eq_none.1 hf x · |> fun h => by simp_all)
    | some y =>
      refine ⟨y.holding.owner, rfl, ?_⟩
      cases y.holding <;> rfl

theorem ownerOf_congr {E X : Nat} {t t' : Ownership E X} {l₁ K M l₂ : List Extent} {q : Nat}
    (ht : t.extents = l₁ ++ K ++ l₂) (ht' : t'.extents = l₁ ++ M ++ l₂)
    (hb : t'.banks = t.banks) (hx : t'.exclusions = t.exclusions)
    (h : (M.find? (·.range.holdsPage q)).map (·.holding.owner) =
      (K.find? (·.range.holdsPage q)).map (·.holding.owner)) :
    t'.ownerOf q = t.ownerOf q := by
  have key : (t'.extents.find? (·.range.holdsPage q)).map (·.holding.owner) =
      (t.extents.find? (·.range.holdsPage q)).map (·.holding.owner) := by
    rw [ht, ht', List.find?_append, List.find?_append, List.find?_append, List.find?_append]
    cases l₁.find? (·.range.holdsPage q) with
    | some _ => rfl
    | none =>
      simp only [Option.none_or]
      cases hM : M.find? (·.range.holdsPage q) <;> cases hK : K.find? (·.range.holdsPage q) <;>
        simp_all
  unfold Ownership.ownerOf
  rw [hb, hx]
  cases h1 : t'.extents.find? (·.range.holdsPage q) <;>
    cases h2 : t.extents.find? (·.range.holdsPage q) <;> rw [h1, h2] at key <;>
    simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at key
  show some _ = some _
  rw [key]

theorem firstExcluder_isSome (xs : List Exclusion) (q : Nat) :
    (firstExcluder xs q).isSome = true ↔ ∃ x ∈ xs, x.range.touchesPage q = true := by
  unfold firstExcluder
  dsimp only
  constructor
  · intro h
    split at h
    · obtain ⟨x, hx, _⟩ := List.any_eq_true.1 ‹_›
      exact ⟨x, (List.mem_filter.1 hx).1, (List.mem_filter.1 hx).2⟩
    · split at h
      · obtain ⟨x, hx, _⟩ := List.any_eq_true.1 ‹_›
        exact ⟨x, (List.mem_filter.1 hx).1, (List.mem_filter.1 hx).2⟩
      · split at h
        · obtain ⟨x, hx, _⟩ := List.any_eq_true.1 ‹_›
          exact ⟨x, (List.mem_filter.1 hx).1, (List.mem_filter.1 hx).2⟩
        · exact absurd h (by simp)
  · rintro ⟨x, hx, hq⟩
    have hm : x ∈ xs.filter (·.range.touchesPage q) := List.mem_filter.2 ⟨hx, hq⟩
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · rename_i h1 h2 h3
          cases hxo : x.owner
          · exact absurd (List.any_eq_true.2 ⟨x, hm, by simp [hxo]⟩) h1
          · exact absurd (List.any_eq_true.2 ⟨x, hm, by simp [hxo]⟩) h2
          · exact absurd (List.any_eq_true.2 ⟨x, hm, by simp [hxo]⟩) h3

theorem ownersOf_length_eq_one {E X : Nat} {t : Ownership E X} (q : Nat)
    (hl : ExtentsInOrder t.extents) :
    (t.ownersOf q).length = 1 ↔
      ((∃ x ∈ t.extents, x.range.holdsPage q = true) ↔
        ¬ ∃ x ∈ t.exclusions, x.range.touchesPage q = true) := by
  have h1 := filter_holds_length_le q hl
  have h2 : (t.extents.filter (·.range.holdsPage q)).length = 0 ↔
      ¬ ∃ x ∈ t.extents, x.range.holdsPage q = true := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    simp
  have h3 := firstExcluder_isSome t.exclusions q
  unfold Ownership.ownersOf
  rw [List.length_append, List.length_map]
  cases hf : firstExcluder t.exclusions q with
  | none =>
    simp only [hf, Option.isSome_none, Bool.false_eq_true, false_iff] at h3
    simp only [Option.map_none, Option.toList_none, List.length_nil, Nat.add_zero, h3,
      not_false_eq_true, iff_true]
    constructor
    · intro h
      by_cases hn : ∃ x ∈ t.extents, x.range.holdsPage q = true
      · exact hn
      · have := h2.2 hn
        omega
    · intro hx
      have : (t.extents.filter (·.range.holdsPage q)).length ≠ 0 := fun h0 => h2.1 h0 hx
      omega
  | some _ =>
    simp only [hf, Option.isSome_some, true_iff] at h3
    simp only [Option.map_some, Option.toList_some, List.length_singleton, h3,
      not_true_eq_false, iff_false]
    constructor
    · intro h
      exact h2.1 (by omega)
    · intro h
      have := h2.2 h
      omega

end Krepi.Proofs.PageTables
