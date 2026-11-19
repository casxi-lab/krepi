module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.PageTables.OwnerLemmas

/-!
# Page tables: lemmas about the writes of the page ownership table

The writes of the page ownership table have three shapes: `take` (of
`assign` and `reserve`) splits the free extent that holds a range into at
most three, `publish` relabels one extent, and `mergeFreed` (of `release`
and `cancel`) frees an extent and joins it with its free neighbours. For
each shape: the extents after the write, their order, pages and banks, the
well-formedness of the table, and its owner function, by which the pages of
the range get the new owner and every other page keeps its owner.

- the search of an extent: `splitFirst_some` (the extents around the one
  found) and `splitFirst_none` (no extent passes the test);
- the pieces of `Extent.take`: `mem_take` (the range taken, or a free part
  before or after it);
- the steps of the entries: `take_ok`, `assign_ok`, `reserve_ok`,
  `findHeld_ok`, `release_ok` and `cancel_ok` (what an entry that succeeds
  checked and wrote), `choose_ok` (the checks and the scan of `choose`), and
  `choose_onPages` (the range of a choice is on pages);
- the counter: `counter_after_eq` (it grows by one);
- joining free extents: `mergeFreed_spec` (the extents that `mergeFreed`
  joins, case by case, with the neighbours that it does not join);
- the entries together: `take_spec`, `assign_spec`, `reserve_spec`,
  `publish_spec`, `free_spec`, `release_spec` and `cancel_spec`, each the
  well-formedness, the fields that the entry keeps, the counter, the extent
  that a value names and the owner function after the entry;
- the extents after a write: `take_extents` (the range was inside a free
  extent, and every extent after is one of the table, free, or the range
  held), `publish_extents` (every extent after is one of the table or the
  one published) and `mem_mergeFreed` (every extent after `mergeFreed` is
  one before it or free).

The private steps follow the same order: the pieces of `Extent.take` (inside
the extent, their number, order, pages and holdings), the publication, the
range of `fit` and of the scan, the counter that never gives the generation
0, the join of two free extents, `mergeFreed` as one block replaced by one
free extent that covers it, the order and the well-formedness of a table
whose block of extents is replaced, case by case for the three shapes, and
the owner function after each shape, for the pages at multiples of 4 KiB
where the shape needs it.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables

/-- `omega` after the page size is written as its value. -/
local macro "page_omega" : tactic => `(tactic| (simp only [PAGE_SIZE] at *; omega))

/-! ## The search of an extent -/

theorem splitFirst_some {p : Extent → Bool} : ∀ {l acc b a : List Extent} {e : Extent},
    splitFirst p l acc = some (b, e, a) → acc.reverse ++ l = b.reverse ++ e :: a ∧ p e = true
  | [], _, _, _, _, h => by simp [splitFirst] at h
  | x :: xs, acc, b, a, e, h => by
    unfold splitFirst at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, ‹_›⟩
    · obtain ⟨h1, h2⟩ := splitFirst_some h
      exact ⟨by simpa using h1, h2⟩

theorem splitFirst_none {p : Extent → Bool} : ∀ {l acc : List Extent},
    splitFirst p l acc = none → ∀ x ∈ l, p x = false
  | [], _, _ => by simp
  | x :: xs, acc, h => by
    unfold splitFirst at h
    split at h
    · exact absurd h (by simp)
    · rename_i hx
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · simpa using hx
      · exact splitFirst_none h y hy

/-! ## The pieces of a taken extent -/

theorem mem_take {e x : Extent} {r : PhysRange} {h : Holding} (hx : x ∈ e.take r h) :
    x = ⟨r, e.bank, h⟩ ∨ (x.bank = e.bank ∧ x.holding = .free ∧
      ((x.range.start.toNat = e.range.start.toNat ∧ x.range.endNat = r.start.toNat) ∨
        (x.range.start.toNat = r.endNat ∧ x.range.endNat = e.range.endNat))) := by
  unfold Extent.take at hx
  simp only [List.mem_append, List.mem_cons, Option.mem_toList, Option.map_eq_some_iff] at hx
  rcases hx with ⟨g, hg, rfl⟩ | rfl | ⟨g, hg, rfl⟩
  · obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hg
    exact Or.inr ⟨rfl, rfl, Or.inl ⟨h1, by dsimp only; omega⟩⟩
  · exact Or.inl rfl
  · obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hg
    exact Or.inr ⟨rfl, rfl, Or.inr ⟨h1, by dsimp only; omega⟩⟩

private theorem take_within {e x : Extent} {r : PhysRange} {h : Holding} (hc : e.range.contains r = true)
    (hx : x ∈ e.take r h) :
    e.range.start.toNat ≤ x.range.start.toNat ∧ x.range.endNat ≤ e.range.endNat ∧
      x.bank = e.bank := by
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  have := range_lt r
  rcases mem_take hx with rfl | ⟨hb, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact ⟨hc.1, hc.2, rfl⟩
  · exact ⟨by omega, by omega, hb⟩
  · exact ⟨by omega, by omega, hb⟩

private theorem take_length {e : Extent} {r : PhysRange} {h : Holding} (hc : e.range.contains r = true) :
    (e.take r h).length = 1 + e.extra r := by
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  have := e.range.fits
  have := r.fits
  unfold Extent.take Extent.extra
  simp only [List.length_append, List.length_cons, Option.length_toList, Option.isSome_map]
  have h1 : (rangeOf? e.range.start.toNat (r.start.toNat - e.range.start.toNat)).isSome =
      decide (e.range.start.toNat < r.start.toNat) := by
    cases hg : rangeOf? e.range.start.toNat (r.start.toNat - e.range.start.toNat) with
    | none =>
      by_cases hl : e.range.start.toNat < r.start.toNat
      · obtain ⟨g, hg', -⟩ := rangeOf?_exists (s := e.range.start.toNat)
          (l := r.start.toNat - e.range.start.toNat) (by omega) (by unfold PhysRange.endNat at *; omega)
        rw [hg] at hg'; exact absurd hg' (by simp)
      · simp [hl]
    | some g =>
      obtain ⟨h1, -, -, -⟩ := rangeOf?_eq_some.1 hg
      simp only [Option.isSome_some]
      exact (decide_eq_true (by omega)).symm
  have h2 : (rangeOf? r.endNat (e.range.endNat - r.endNat)).isSome =
      decide (r.endNat < e.range.endNat) := by
    cases hg : rangeOf? r.endNat (e.range.endNat - r.endNat) with
    | none =>
      by_cases hl : r.endNat < e.range.endNat
      · obtain ⟨g, hg', -⟩ := rangeOf?_exists (s := r.endNat)
          (l := e.range.endNat - r.endNat) (by omega) (by unfold PhysRange.endNat at *; omega)
        rw [hg] at hg'; exact absurd hg' (by simp)
      · simp [hl]
    | some g =>
      obtain ⟨h1, -, -, -⟩ := rangeOf?_eq_some.1 hg
      simp only [Option.isSome_some]
      exact (decide_eq_true (by omega)).symm
  rw [h1, h2]
  by_cases hl : e.range.start.toNat < r.start.toNat <;>
    by_cases hr : r.endNat < e.range.endNat <;> simp [hl, hr]

private theorem pairwise_toList {α : Type} {R : α → α → Prop} (o : Option α) :
    o.toList.Pairwise R := by
  cases o <;> simp

private theorem take_inOrder {e : Extent} {r : PhysRange} {h : Holding} (hc : e.range.contains r = true) :
    ExtentsInOrder (e.take r h) := by
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  unfold Extent.take
  rw [ExtentsInOrder, List.pairwise_append, List.pairwise_cons]
  refine ⟨?_, ⟨fun y hy => ?_, ?_⟩, fun x hx y hy => ?_⟩
  · exact pairwise_toList _
  · simp only [Option.mem_toList, Option.map_eq_some_iff] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    obtain ⟨_, _, h1, -⟩ := rangeOf?_eq_some.1 hg
    simp only; omega
  · exact pairwise_toList _
  · simp only [Option.mem_toList, Option.map_eq_some_iff] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨_, _, -, h2⟩ := rangeOf?_eq_some.1 hg
    rcases List.mem_cons.1 hy with rfl | hy
    · simp only; omega
    · simp only [Option.mem_toList, Option.map_eq_some_iff] at hy
      obtain ⟨g', hg', rfl⟩ := hy
      obtain ⟨_, _, h3, -⟩ := rangeOf?_eq_some.1 hg'
      have := range_lt r
      simp only; omega

private theorem take_onPages {e x : Extent} {r : PhysRange} {h : Holding} (he : e.range.onPages = true)
    (hr : r.onPages = true) (hx : x ∈ e.take r h) : x.range.onPages = true := by
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at he hr ⊢
  rcases mem_take hx with rfl | ⟨-, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact hr
  · rw [h1, h2]; exact ⟨he.1, hr.1⟩
  · rw [h1, h2]; exact ⟨hr.2, he.2⟩

/-- In an extent `e` on pages that a range `r` on pages of it is taken from, a
page of `e` lies in the piece of `r` when `r` holds it and in a free piece
otherwise. -/
private theorem take_holds {e : Extent} {r : PhysRange} {h : Holding} (hc : e.range.contains r = true)
    (he : e.range.onPages = true) (hr : r.onPages = true) {q : Nat} (hq : q % PAGE_SIZE = 0)
    (heq : e.range.holdsPage q = true) :
    ∃ x ∈ e.take r h, x.range.holdsPage q = true ∧
      x.holding = if r.holdsPage q = true then h else .free := by
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at he hr
  rw [holdsPage_iff] at heq
  have := e.range.fits
  by_cases hrq : r.holdsPage q = true
  · refine ⟨⟨r, e.bank, h⟩, ?_, hrq, by simp [hrq]⟩
    unfold Extent.take
    exact List.mem_append_right _ List.mem_cons_self
  · simp only [hrq, ↓reduceIte, Bool.false_eq_true]
    rw [holdsPage_iff] at hrq
    by_cases hlo : q < r.start.toNat
    · obtain ⟨g, hg, h1, h2⟩ := rangeOf?_exists (s := e.range.start.toNat)
        (l := r.start.toNat - e.range.start.toNat) (by omega) (by unfold PhysRange.endNat at *; omega)
      refine ⟨⟨g, e.bank, .free⟩, ?_, ?_, rfl⟩
      · unfold Extent.take
        refine List.mem_append_left _ ?_
        rw [hg]
        exact List.mem_singleton_self _
      · rw [holdsPage_iff]
        simp only
        page_omega
    · obtain ⟨g, hg, h1, h2⟩ := rangeOf?_exists (s := r.endNat)
        (l := e.range.endNat - r.endNat) (by page_omega) (by unfold PhysRange.endNat at *; omega)
      refine ⟨⟨g, e.bank, .free⟩, ?_, ?_, rfl⟩
      · unfold Extent.take
        refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
        rw [hg]
        exact List.mem_singleton_self _
      · rw [holdsPage_iff]
        simp only
        page_omega

/-! ## The entries -/

theorem take_ok {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState} {a : Allocation}
    (h : t.take c s = .ok (t', a)) :
    ∃ l₁ e l₂ g, t.counter = .next g ∧ t.extents = l₁ ++ e :: l₂ ∧ e.holding = .free ∧
      e.range.contains c.range = true ∧ e.extra c.range ≤ E - t.extents.length ∧
      t' = ⟨t.arena, t.banks, l₁ ++ e.take c.range (.held c.owner g s) ++ l₂, t.exclusions,
        Counter.after g⟩ ∧ a = ⟨t.arena, c.owner, g, c.range⟩ := by
  unfold Ownership.take at h
  cases hc : t.counter with
  | exhausted => simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | next g =>
    simp only [hc, pure, Except.pure, bind, Except.bind] at h
    cases hs : splitFirst (fun e => e.holding == .free && e.range.contains c.range) t.extents [] with
    | none => simp [hs, throw, throwThe, MonadExceptOf.throw] at h
    | some v =>
      obtain ⟨before, e, after⟩ := v
      simp only [hs] at h
      by_cases hm : E - t.extents.length < e.extra c.range
      · simp [hm, throw, throwThe, MonadExceptOf.throw] at h
      · simp only [hm, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := splitFirst_some hs
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        refine ⟨before.reverse, e, after, g, rfl, by simpa using h1, h2.1, h2.2, by omega, ?_, rfl⟩
        simp [List.reverseAux_eq]

private theorem counter_after_ne (g : UInt64) : Counter.after g ≠ .next 0 := by
  unfold Counter.after
  split
  · rename_i h
    intro he
    simp only [Counter.next.injEq] at he
    have := congrArg UInt64.toNat he
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt h] at this
    simp at this
  · simp

theorem counter_after_eq {g g' : UInt64} (h : Counter.after g = .next g') :
    g'.toNat = g.toNat + 1 := by
  unfold Counter.after at h
  split at h
  · rename_i hl
    simp only [Counter.next.injEq] at h
    subst h
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hl]
  · simp at h

private theorem fit_onPages {d : Direction} {lo hi bytes align : Nat} {r : PhysRange}
    (hb : bytes % PAGE_SIZE = 0) (ha : align % PAGE_SIZE = 0)
    (h : fit d lo hi bytes align = .range r) : r.onPages = true := by
  have hd : PAGE_SIZE ∣ align := Nat.dvd_of_mod_eq_zero ha
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq]
  unfold fit at h
  split at h
  · cases h
  cases d with
  | low =>
    dsimp only at h
    split at h
    · cases h
    split at h
    · rename_i r' hr'
      split at h
      · cases h
        obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hr'
        have : alignUp lo align % PAGE_SIZE = 0 :=
          Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_mul_left _ _))
        rw [h2, h1]
        constructor <;> page_omega
      · cases h
    · cases h
  | high =>
    dsimp only at h
    split at h
    · cases h
    split at h
    · rename_i r' hr'
      split at h
      · cases h
        obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hr'
        have : alignDown (hi - bytes) align % PAGE_SIZE = 0 :=
          Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_mul_left _ _))
        rw [h2, h1]
        constructor <;> page_omega
      · cases h
    · cases h

private theorem scan_onPages {room bytes align : Nat} {p : Placement} (hb : bytes % PAGE_SIZE = 0)
    (ha : align % PAGE_SIZE = 0) :
    ∀ {l : List Extent} {limited : Bool} {r : PhysRange},
      scan room bytes align p l limited = .ok r → r.onPages = true
  | [], limited, r, h => by
    unfold scan at h
    exact absurd h (by simp)
  | e :: rest, limited, r, h => by
    unfold scan at h
    split at h
    · exact scan_onPages hb ha h
    · dsimp only at h
      split at h
      · exact scan_onPages hb ha h
      · exact absurd h (by simp)
      · rename_i r' hfit
        split at h
        · exact scan_onPages hb ha h
        · cases h
          exact fit_onPages hb ha hfit

theorem choose_ok {E X : Nat} {t : Ownership E X} {owner pages alignment : UInt64} {p : Placement}
    {c : Choice} (h : t.choose owner pages alignment p = .ok c) :
    pages.toNat * PAGE_SIZE < 2 ^ 64 ∧ alignment.toNat * PAGE_SIZE < 2 ^ 64 ∧ pages ≠ 0 ∧
      isPowerOfTwo alignment.toNat = true ∧ t.counter ≠ .exhausted ∧ c.owner = owner ∧
      scan (E - t.extents.length) (pages.toNat * PAGE_SIZE) (alignment.toNat * PAGE_SIZE) p
        (match p.direction with
          | .low => t.extents
          | .high => t.extents.reverse) false = .ok c.range := by
  unfold Ownership.choose at h
  by_cases h1 : (decide (2 ^ 64 ≤ pages.toNat * PAGE_SIZE) ||
      decide (2 ^ 64 ≤ alignment.toNat * PAGE_SIZE)) = true
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h2 : pages = 0
  · simp [h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [h2, ↓reduceIte] at h
  by_cases h3 : (!isPowerOfTwo alignment.toNat) = true
  · simp [h3, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h4 : t.counter = .exhausted
  · simp [h4, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [h4, ↓reduceIte, bind, Except.bind] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at h1
  simp only [Bool.not_eq_true', Bool.not_eq_false] at h3
  split at h
  · exact absurd h (by simp)
  · rename_i r hr
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨h1.1, h1.2, h2, by simpa using h3, h4, rfl, hr⟩

theorem choose_onPages {E X : Nat} {t : Ownership E X} {owner pages alignment : UInt64}
    {p : Placement} {c : Choice} (h : t.choose owner pages alignment p = .ok c) :
    c.range.onPages = true := by
  obtain ⟨-, -, -, -, -, -, h⟩ := choose_ok h
  exact scan_onPages (Nat.mul_mod_left _ _) (Nat.mul_mod_left _ _) h

theorem assign_ok {E X : Nat} {t t' : Ownership E X} {c : Choice} {zeroed : Bool}
    {a : Allocation} (h : t.assign c zeroed = .ok (t', a)) :
    zeroed = true ∧ t.take c .published = .ok (t', a) := by
  unfold Ownership.assign at h
  split at h
  · exact ⟨‹_›, h⟩
  · exact absurd h (by simp)

theorem reserve_ok {E X : Nat} {t t' : Ownership E X} {owner pages alignment : UInt64}
    {p : Placement} {r : Reservation} (h : t.reserve owner pages alignment p = .ok (t', r)) :
    ∃ c a, t.choose owner pages alignment p = .ok c ∧ t.take c .reserved = .ok (t', a) ∧
      r = ⟨a, false, 0⟩ := by
  unfold Ownership.reserve at h
  cases hc : t.choose owner pages alignment p with
  | error e => simp [hc, bind, Except.bind] at h
  | ok c =>
    simp only [hc, bind, Except.bind] at h
    cases ht : t.take c .reserved with
    | error e => simp [ht] at h
    | ok v =>
      obtain ⟨t'', a⟩ := v
      simp only [ht, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c, a, rfl, ht, rfl⟩

theorem findHeld_ok {E X : Nat} {t : Ownership E X} {o : UInt64} {a : Allocation} {s : HoldState}
    {before after : List Extent} {e : Extent} (h : t.findHeld o a s = .ok (before, e, after)) :
    a.arena = t.arena ∧ a.owner = o ∧ t.extents = before.reverse ++ e :: after ∧
      e.range = a.range ∧ e.holding = .held o a.generation s := by
  unfold Ownership.findHeld at h
  by_cases h1 : a.arena = t.arena
  · by_cases h2 : a.owner = o
    · simp only [h1, h2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      cases hs : splitFirst (fun e => e.range == a.range && e.holding == .held o a.generation s)
          t.extents [] with
      | none => simp [hs, throw, throwThe, MonadExceptOf.throw] at h
      | some found =>
        simp only [hs, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨h3, h4⟩ := splitFirst_some hs
        simp only [Bool.and_eq_true, beq_iff_eq] at h4
        exact ⟨h1, h2, by simpa using h3, h4.1, h4.2⟩
    · simp [h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

private theorem publish_ok {E X : Nat} {t t' : Ownership E X} {o : UInt64} {x : Initialized}
    {a : Allocation} (h : t.publish o x = .ok (t', a)) :
    ∃ before e after, t.findHeld o x.allocation .reserved = .ok (before, e, after) ∧
      t' = ⟨t.arena, t.banks,
        before.reverse ++ ⟨e.range, e.bank, .held o x.allocation.generation .published⟩ :: after,
        t.exclusions, t.counter⟩ ∧ a = x.allocation := by
  unfold Ownership.publish at h
  split at h
  · exact absurd h (by simp)
  · rename_i before e after hf
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨before, e, after, hf, by simp [List.reverseAux_eq], rfl⟩

theorem release_ok {E X : Nat} {t t' : Ownership E X} {o : UInt64} {x : Allocation}
    (h : t.release o x = .ok t') :
    ∃ before e after, t.findHeld o x .published = .ok (before, e, after) ∧
      t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩ := by
  unfold Ownership.release at h
  cases hf : t.findHeld o x .published with
  | error e => simp [hf, bind, Except.bind] at h
  | ok v =>
    obtain ⟨before, e, after⟩ := v
    simp only [hf, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨before, e, after, rfl, h.symm⟩

theorem cancel_ok {E X : Nat} {t t' : Ownership E X} {o : UInt64} {r : Reservation}
    (h : t.cancel o r = .ok t') :
    r.attempted = false ∧ ∃ before e after,
      t.findHeld o r.allocation .reserved = .ok (before, e, after) ∧
      t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩ := by
  unfold Ownership.cancel at h
  split at h
  · exact absurd h (by simp)
  · rename_i hr
    split at h
    · exact absurd h (by simp)
    · rename_i before e after hf
      simp only [Except.ok.injEq] at h
      exact ⟨by simpa using hr, before, e, after, hf, h.symm⟩

/-! ## Joining free extents -/

private theorem join_eq_some {a b m : Extent} (h : a.join b = some m) :
    a.holding = .free ∧ b.holding = .free ∧ a.bank = b.bank ∧
      a.range.endNat = b.range.start.toNat ∧ m.holding = .free ∧ m.bank = a.bank ∧
      m.range.start.toNat = a.range.start.toNat ∧ m.range.endNat = b.range.endNat := by
  unfold Extent.join at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, _, h1, h2⟩ := rangeOf?_eq_some.1 hg
    have := range_lt a.range
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, rfl, rfl, h1, by dsimp only; omega⟩
  · exact absurd h (by simp)

private theorem join_eq_none {a b : Extent} (h : a.join b = none) :
    ¬ (a.holding = .free ∧ b.holding = .free ∧ a.bank = b.bank ∧
      a.range.endNat = b.range.start.toNat) := by
  rintro ⟨h1, h2, h3, h4⟩
  unfold Extent.join at h
  rw [ite_eq_left (by simp [h1, h2, h3, h4])] at h
  have := range_lt a.range
  have := range_lt b.range
  have := b.range.fits
  obtain ⟨g, hg, -⟩ := rangeOf?_exists (s := a.range.start.toNat)
    (l := b.range.endNat - a.range.start.toNat) (by omega) (by unfold PhysRange.endNat at *; omega)
  rw [hg] at h
  exact absurd h (by simp)

private theorem left_none {e l : Extent} {ls : List Extent}
    (hj : l.join { e with holding := .free } = none) :
    ∀ x ∈ (l :: ls).head?, ¬ (x.holding = .free ∧ x.bank = e.bank ∧
      x.range.endNat = e.range.start.toNat) := by
  intro x hx ⟨h1, h2, h3⟩
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  subst hx
  exact join_eq_none hj ⟨h1, rfl, h2, h3⟩

private theorem right_none {e f r : Extent} {rs : List Extent} (hf1 : f.holding = .free)
    (hf2 : f.bank = e.bank) (hf3 : f.range.endNat = e.range.endNat) (hj : f.join r = none) :
    ∀ y ∈ (r :: rs).head?, ¬ (y.holding = .free ∧ y.bank = e.bank ∧
      e.range.endNat = y.range.start.toNat) := by
  intro y hy ⟨h1, h2, h3⟩
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hy
  exact join_eq_none hj ⟨hf1, h1, by rw [hf2, h2], by rw [hf3, h3]⟩

/-- What `mergeFreed` does with the extents `before` (in reverse order), `e`
and `after`: it replaces a block `lo ++ e :: hi` of the extents in address
order by one free extent `m` of the bank of `e`, where `lo` is the free
extent of that bank that ends where `e` starts, if it is the one before `e`,
and `hi` the free extent of that bank that starts where `e` ends, if it is
the one after `e`. When there is no such `lo`, the extent before `e`, if
any, is not one, and `m` starts at `e`; likewise for `hi` and the end. -/
theorem mergeFreed_spec (before : List Extent) (e : Extent) (after : List Extent) :
    ∃ (l₁ lo hi l₂ : List Extent) (m : Extent),
      before.reverse ++ e :: after = l₁ ++ (lo ++ e :: hi) ++ l₂ ∧
      mergeFreed before e after = l₁ ++ m :: l₂ ∧
      m.holding = .free ∧ m.bank = e.bank ∧
      ((lo = [] ∧ l₁ = before.reverse ∧ m.range.start.toNat = e.range.start.toNat ∧
          ∀ x ∈ before.head?, ¬ (x.holding = .free ∧ x.bank = e.bank ∧
            x.range.endNat = e.range.start.toNat)) ∨
        ∃ x, lo = [x] ∧ before.head? = some x ∧ l₁ = before.tail.reverse ∧
          x.holding = .free ∧ x.bank = e.bank ∧ x.range.endNat = e.range.start.toNat ∧
          m.range.start.toNat = x.range.start.toNat) ∧
      ((hi = [] ∧ l₂ = after ∧ m.range.endNat = e.range.endNat ∧
          ∀ y ∈ after.head?, ¬ (y.holding = .free ∧ y.bank = e.bank ∧
            e.range.endNat = y.range.start.toNat)) ∨
        ∃ y, hi = [y] ∧ after.head? = some y ∧ l₂ = after.tail ∧
          y.holding = .free ∧ y.bank = e.bank ∧ e.range.endNat = y.range.start.toNat ∧
          m.range.endNat = y.range.endNat) := by
  unfold mergeFreed
  dsimp only
  rcases before with _ | ⟨l, ls⟩
  · rcases after with _ | ⟨r, rs⟩
    · exact ⟨[], [], [], [], _, by simp, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, by simp⟩,
        Or.inl ⟨rfl, rfl, rfl, by simp⟩⟩
    · dsimp only
      cases hj' : Extent.join { e with holding := .free } r with
      | none =>
        exact ⟨[], [], [], r :: rs, { e with holding := .free }, by simp, by simp, rfl, rfl,
          Or.inl ⟨rfl, rfl, rfl, by simp⟩, Or.inl ⟨rfl, rfl, rfl, right_none (f := { e with holding := .free }) rfl rfl rfl hj'⟩⟩
      | some m =>
        obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := join_eq_some hj'
        exact ⟨[], [], [r], rs, m, by simp, by simp, h5, h6, Or.inl ⟨rfl, rfl, h7, by simp⟩,
          Or.inr ⟨r, rfl, rfl, rfl, h2, h3.symm, h4, h8⟩⟩
  · dsimp only
    cases hj : l.join { e with holding := .free } with
    | none =>
      have hL := left_none (ls := ls) hj
      rcases after with _ | ⟨r, rs⟩
      · exact ⟨(l :: ls).reverse, [], [], [], { e with holding := .free }, by simp,
          by simp [List.reverseAux_eq], rfl, rfl, Or.inl ⟨rfl, rfl, rfl, hL⟩,
          Or.inl ⟨rfl, rfl, rfl, by simp⟩⟩
      · dsimp only
        cases hj' : Extent.join { e with holding := .free } r with
        | none =>
          exact ⟨(l :: ls).reverse, [], [], r :: rs, { e with holding := .free }, by simp,
            by simp [List.reverseAux_eq], rfl, rfl, Or.inl ⟨rfl, rfl, rfl, hL⟩,
            Or.inl ⟨rfl, rfl, rfl, right_none (f := { e with holding := .free }) rfl rfl rfl hj'⟩⟩
        | some m =>
          obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := join_eq_some hj'
          exact ⟨(l :: ls).reverse, [], [r], rs, m, by simp, by simp [List.reverseAux_eq], h5, h6,
            Or.inl ⟨rfl, rfl, h7, hL⟩, Or.inr ⟨r, rfl, rfl, rfl, h2, h3.symm, h4, h8⟩⟩
    | some m₁ =>
      obtain ⟨g1, -, g3, g4, g5, g6, g7, g8⟩ := join_eq_some hj
      have hL : ∃ x, [l] = [x] ∧ (l :: ls).head? = some x ∧ ls.reverse = (l :: ls).tail.reverse ∧
          x.holding = .free ∧ x.bank = e.bank ∧ x.range.endNat = e.range.start.toNat ∧
          m₁.range.start.toNat = x.range.start.toNat := ⟨l, rfl, rfl, rfl, g1, g3, g4, g7⟩
      rcases after with _ | ⟨r, rs⟩
      · exact ⟨ls.reverse, [l], [], [], m₁, by simp, by simp [List.reverseAux_eq], g5,
          by rw [g6, g3], Or.inr hL, Or.inl ⟨rfl, rfl, g8, by simp⟩⟩
      · dsimp only
        cases hj' : m₁.join r with
        | none =>
          exact ⟨ls.reverse, [l], [], r :: rs, m₁, by simp, by simp [List.reverseAux_eq], g5,
            by rw [g6, g3], Or.inr hL,
            Or.inl ⟨rfl, rfl, g8, right_none g5 (by rw [g6, g3]) g8 hj'⟩⟩
        | some m =>
          obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := join_eq_some hj'
          obtain ⟨x, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := hL
          exact ⟨ls.reverse, [l], [r], rs, m, by simp, by simp [List.reverseAux_eq], h5,
            by rw [h6, g6, g3],
            Or.inr ⟨x, hx1, hx2, hx3, hx4, hx5, hx6, by rw [h7, hx7]⟩,
            Or.inr ⟨r, rfl, rfl, rfl, h2, by rw [← h3, g6, g3], by rw [← g8, h4], h8⟩⟩

/-- The block that `mergeFreed` replaces, without the cases of
`mergeFreed_spec`: a block `K` of the extents in address order that holds
`e` and otherwise free extents of its bank, replaced by the free extent `m`
of that bank that starts where the block starts, ends where it ends and
whose every address lies in an extent of the block. -/
private theorem mergeFreed_block (before : List Extent) (e : Extent) (after : List Extent)
    (hl : ExtentsInOrder (before.reverse ++ e :: after)) :
    ∃ (l₁ K l₂ : List Extent) (m : Extent),
      before.reverse ++ e :: after = l₁ ++ K ++ l₂ ∧ mergeFreed before e after = l₁ ++ m :: l₂ ∧
      e ∈ K ∧ m.holding = .free ∧ m.bank = e.bank ∧
      (∀ k ∈ K, k.bank = e.bank ∧ (k = e ∨ k.holding = .free) ∧
        m.range.start.toNat ≤ k.range.start.toNat ∧ k.range.endNat ≤ m.range.endNat) ∧
      (∃ k ∈ K, k.range.start.toNat = m.range.start.toNat) ∧
      (∃ k ∈ K, k.range.endNat = m.range.endNat) ∧
      ∀ p, m.range.start.toNat ≤ p → p < m.range.endNat →
        ∃ k ∈ K, k.range.start.toNat ≤ p ∧ p < k.range.endNat := by
  obtain ⟨l₁, lo, hi, l₂, m, h1, h2, h3, h4, hlo, hhi⟩ := mergeFreed_spec before e after
  have he := range_lt e.range
  refine ⟨l₁, lo ++ e :: hi, l₂, m, h1, h2, by simp, h3, h4, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · rcases hlo with ⟨rfl, -⟩ | ⟨x, rfl, -, -, hx1, hx2, hx3, hx4⟩
      · simp at hk
      · simp only [List.mem_singleton] at hk
        subst hk
        have := range_lt k.range
        refine ⟨hx2, Or.inr hx1, by omega, ?_⟩
        rcases hhi with ⟨-, -, hy, -⟩ | ⟨y, -, -, -, -, -, hy1, hy2⟩
        · omega
        · have := range_lt y.range; omega
    · rcases List.mem_cons.1 hk with rfl | hk
      · refine ⟨rfl, Or.inl rfl, ?_, ?_⟩
        · rcases hlo with ⟨-, -, hx, -⟩ | ⟨x, -, -, -, -, -, hx1, hx2⟩
          · omega
          · have := range_lt x.range; omega
        · rcases hhi with ⟨-, -, hy, -⟩ | ⟨y, -, -, -, -, -, hy1, hy2⟩
          · omega
          · have := range_lt y.range; omega
      · rcases hhi with ⟨rfl, -⟩ | ⟨y, rfl, -, -, hy1, hy2, hy3, hy4⟩
        · simp at hk
        · simp only [List.mem_singleton] at hk
          subst hk
          have := range_lt k.range
          refine ⟨hy2, Or.inr hy1, ?_, by omega⟩
          rcases hlo with ⟨-, -, hx, -⟩ | ⟨x, -, -, -, -, -, hx1, hx2⟩
          · omega
          · have := range_lt x.range; omega
  · rcases hlo with ⟨-, -, hx, -⟩ | ⟨x, rfl, -, -, -, -, -, hx⟩
    · exact ⟨e, by simp, hx.symm⟩
    · exact ⟨x, by simp, hx.symm⟩
  · rcases hhi with ⟨-, -, hy, -⟩ | ⟨y, rfl, -, -, -, -, -, hy⟩
    · exact ⟨e, by simp, hy.symm⟩
    · exact ⟨y, by simp, hy.symm⟩
  · intro p hp1 hp2
    by_cases hpe : p < e.range.start.toNat
    · rcases hlo with ⟨-, -, hx, -⟩ | ⟨x, rfl, -, -, -, -, hx1, hx2⟩
      · omega
      · exact ⟨x, by simp, by omega, by omega⟩
    · by_cases hpe' : e.range.endNat ≤ p
      · rcases hhi with ⟨-, -, hy, -⟩ | ⟨y, rfl, -, -, -, -, hy1, hy2⟩
        · omega
        · exact ⟨y, by simp, by omega, by omega⟩
      · exact ⟨e, by simp, by omega, by omega⟩

/-! ## The order of the extents after a write -/

/-- A block `K` of extents in address order replaced by extents in address
order that start at or after an extent of the block and end at or before an
extent of the block keeps the extents in address order. -/
private theorem inOrder_replace {l₁ K M l₂ : List Extent} (hl : ExtentsInOrder (l₁ ++ K ++ l₂))
    (hM : ExtentsInOrder M)
    (hlo : ∃ k ∈ K, ∀ x ∈ M, k.range.start.toNat ≤ x.range.start.toNat)
    (hhi : ∃ k ∈ K, ∀ x ∈ M, x.range.endNat ≤ k.range.endNat) :
    ExtentsInOrder (l₁ ++ M ++ l₂) := by
  rw [ExtentsInOrder, List.pairwise_append, List.pairwise_append] at hl ⊢
  obtain ⟨⟨h1, -, h12⟩, h2, h3⟩ := hl
  obtain ⟨k, hk, hk'⟩ := hlo
  obtain ⟨k', hk2, hk2'⟩ := hhi
  refine ⟨⟨h1, hM, fun x hx y hy => ?_⟩, h2, fun x hx y hy => ?_⟩
  · have := h12 x hx k hk
    have := hk' y hy
    omega
  · rcases List.mem_append.1 hx with hx | hx
    · exact h3 x (List.mem_append_left _ hx) y hy
    · have := h3 k' (List.mem_append_right _ hk2) y hy
      have := hk2' x hx
      omega

private theorem inOrder_take {l₁ l₂ : List Extent} {e : Extent} {r : PhysRange} {h : Holding}
    (hl : ExtentsInOrder (l₁ ++ e :: l₂)) (hc : e.range.contains r = true) :
    ExtentsInOrder (l₁ ++ e.take r h ++ l₂) :=
  inOrder_replace (K := [e]) (by simpa using hl) (take_inOrder hc)
    ⟨e, by simp, fun _ hx => (take_within hc hx).1⟩ ⟨e, by simp, fun _ hx => (take_within hc hx).2.1⟩

private theorem inOrder_relabel {l₁ l₂ : List Extent} {e : Extent} (h : Holding)
    (hl : ExtentsInOrder (l₁ ++ e :: l₂)) :
    ExtentsInOrder (l₁ ++ (⟨e.range, e.bank, h⟩ : Extent) :: l₂) := by
  have := inOrder_replace (K := [e]) (M := [⟨e.range, e.bank, h⟩]) (by simpa using hl)
    (List.pairwise_singleton _ _) ⟨e, by simp, by simp⟩ ⟨e, by simp, by simp⟩
  simpa using this

private theorem inOrder_merge {before after : List Extent} {e : Extent}
    (hl : ExtentsInOrder (before.reverse ++ e :: after)) :
    ExtentsInOrder (mergeFreed before e after) := by
  obtain ⟨l₁, K, l₂, m, h1, h2, -, -, -, -, ⟨k, hk, hk'⟩, ⟨k', hk2, hk2'⟩, -⟩ :=
    mergeFreed_block before e after hl
  rw [h1] at hl
  have := inOrder_replace (M := [m]) hl (List.pairwise_singleton _ _)
    ⟨k, hk, by simp [hk']⟩ ⟨k', hk2, by simp [hk2']⟩
  rw [h2]
  simpa using this

/-! ## Well-formedness after a write -/

private theorem inBank_span {banks : List PhysRange} {x y m : Extent} (hx : x.InBank banks)
    (hy : y.InBank banks) (hxy : x.bank = y.bank) (hm : m.bank = x.bank)
    (h1 : x.range.start.toNat ≤ m.range.start.toNat) (h2 : m.range.endNat ≤ y.range.endNat) :
    m.InBank banks := by
  obtain ⟨b, hb, hbx⟩ := hx
  obtain ⟨b', hb', hby⟩ := hy
  rw [← hxy, hb, Option.some.injEq] at hb'
  subst hb'
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hbx hby
  refine ⟨b, by rw [hm]; exact hb, ?_⟩
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, by omega⟩

/-- A table whose extents differ from those of a well-formed table in one
block, replaced by extents in address order on pages in the banks, at most
as many more as the capacity has free, with the same arena, banks and
exclusion records and a counter that has given no generation 0, is
well-formed. -/
private theorem wellFormed_replace {E X : Nat} {t t' : Ownership E X} {l₁ K M l₂ : List Extent}
    (hwf : t.WellFormed) (ht : t.extents = l₁ ++ K ++ l₂) (ht' : t'.extents = l₁ ++ M ++ l₂)
    (ha : t'.arena = t.arena) (hb : t'.banks = t.banks) (hx : t'.exclusions = t.exclusions)
    (hc : t'.counter ≠ .next 0) (hlen : M.length ≤ K.length + (E - t.extents.length))
    (hM : ∀ x ∈ M, x.range.onPages = true ∧ x.InBank t.banks)
    (hord : ExtentsInOrder t'.extents) : t'.WellFormed := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, -⟩ := hwf
  refine ⟨ha ▸ h1, hb ▸ h2, hb ▸ h3, hb ▸ h4, ?_, fun x hx' => ?_, hord, hx ▸ h8, hc⟩
  · rw [ht']
    rw [ht] at h5 hlen
    simp only [List.length_append] at h5 hlen ⊢
    omega
  · rw [hb]
    rw [ht'] at hx'
    rcases List.mem_append.1 hx' with hx' | hx'
    · rcases List.mem_append.1 hx' with hx' | hx'
      · exact h6 x (by rw [ht]; simp [hx'])
      · exact hM x hx'
    · exact h6 x (by rw [ht]; simp [hx'])

private theorem take_wellFormed {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} (hwf : t.WellFormed) (hr : c.range.onPages = true)
    (h : t.take c s = .ok (t', a)) : t'.WellFormed := by
  obtain ⟨l₁, e, l₂, g, -, ht, -, hc, hroom, rfl, -⟩ := take_ok h
  have hem : e ∈ t.extents := by rw [ht]; simp
  obtain ⟨hep, hei⟩ := hwf.2.2.2.2.2.1 e hem
  have hord := hwf.2.2.2.2.2.2.1
  rw [ht] at hord
  refine wellFormed_replace (l₁ := l₁) (K := [e]) (M := e.take c.range (.held c.owner g s))
    (l₂ := l₂) hwf
    (by rw [ht]; simp) rfl rfl rfl rfl (counter_after_ne g) ?_ (fun x hx => ?_)
    (inOrder_take hord hc)
  · rw [take_length hc]
    simp only [List.length_singleton]
    omega
  · obtain ⟨h1, h2, h3⟩ := take_within hc hx
    exact ⟨take_onPages hep hr hx, inBank_span hei hei rfl h3 h1 h2⟩

private theorem relabel_wellFormed {E X : Nat} {t t' : Ownership E X} {l₁ l₂ : List Extent} {e : Extent}
    {h : Holding} (hwf : t.WellFormed) (ht : t.extents = l₁ ++ e :: l₂)
    (ht' : t' = ⟨t.arena, t.banks, l₁ ++ ⟨e.range, e.bank, h⟩ :: l₂, t.exclusions, t.counter⟩) :
    t'.WellFormed := by
  subst ht'
  have hem : e ∈ t.extents := by rw [ht]; simp
  obtain ⟨hep, hei⟩ := hwf.2.2.2.2.2.1 e hem
  have hord := hwf.2.2.2.2.2.2.1
  rw [ht] at hord
  refine wellFormed_replace (l₁ := l₁) (K := [e]) (M := [⟨e.range, e.bank, h⟩]) (l₂ := l₂) hwf
    (by rw [ht]; simp)
    (by simp) rfl rfl rfl hwf.2.2.2.2.2.2.2.2 (by simp) (fun x hx => ?_) (inOrder_relabel h hord)
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨hep, inBank_span hei hei rfl rfl (Nat.le_refl _) (Nat.le_refl _)⟩

private theorem merge_wellFormed {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e : Extent} (hwf : t.WellFormed) (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩) :
    t'.WellFormed := by
  subst ht'
  have hord := hwf.2.2.2.2.2.2.1
  rw [ht] at hord
  obtain ⟨l₁, K, l₂, m, h1, h2, heK, -, hm2, hK, ⟨k, hk, hk'⟩, ⟨k', hk2, hk2'⟩, -⟩ :=
    mergeFreed_block before e after hord
  have hKt : ∀ x ∈ K, x ∈ t.extents := fun x hx => by rw [ht, h1]; simp [hx]
  refine wellFormed_replace (l₁ := l₁) (K := K) (M := [m]) (l₂ := l₂) hwf (by rw [ht, h1])
    (by simpa using h2) rfl rfl rfl
    hwf.2.2.2.2.2.2.2.2 ?_ (fun x hx => ?_) (by simpa using inOrder_merge hord)
  · have : 0 < K.length := List.length_pos_of_mem heK
    simp only [List.length_singleton]
    omega
  · simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨hkp, hki⟩ := hwf.2.2.2.2.2.1 k (hKt k hk)
    obtain ⟨hkp', hki'⟩ := hwf.2.2.2.2.2.1 k' (hKt k' hk2)
    simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hkp hkp' ⊢
    refine ⟨⟨by rw [← hk']; exact hkp.1, by rw [← hk2']; exact hkp'.2⟩, ?_⟩
    exact inBank_span hki hki' (by rw [(hK k hk).1, (hK k' hk2).1])
      (by rw [hm2, (hK k hk).1]) (by omega) (by omega)

/-! ## The owner function after a write -/

/-- After `take` of the range `r` on pages from the free extent `e` of a
well-formed table with the holding `h`, a page of `r` has the owner of `h`,
and every other page keeps its owner. -/
private theorem ownerOf_take {E X : Nat} {t t' : Ownership E X} {l₁ l₂ : List Extent} {e : Extent}
    {r : PhysRange} {h : Holding} (hwf : t.WellFormed) (ht : t.extents = l₁ ++ e :: l₂)
    (he : e.holding = .free) (hc : e.range.contains r = true) (hr : r.onPages = true)
    (ht' : t'.extents = l₁ ++ e.take r h ++ l₂) (hb : t'.banks = t.banks)
    (hx : t'.exclusions = t.exclusions) {q : Nat} (hq : q % PAGE_SIZE = 0) :
    t'.ownerOf q = if r.holdsPage q = true then some h.owner else t.ownerOf q := by
  have hord := hwf.2.2.2.2.2.2.1
  have hep := (hwf.2.2.2.2.2.1 e (by rw [ht]; simp)).1
  rw [ht] at hord
  have hord' : ExtentsInOrder t'.extents := by rw [ht']; exact inOrder_take hord hc
  split
  · rename_i hrq
    refine ownerOf_of_mem (x := ⟨r, e.bank, h⟩) hord' ?_ hrq
    rw [ht']
    unfold Extent.take
    simp
  · rename_i hrq
    refine ownerOf_congr (K := [e]) (M := e.take r h) (by rw [ht]; simp) ht' hb hx ?_
    by_cases heq : e.range.holdsPage q = true
    · obtain ⟨x, hx, hxq, hxh⟩ := take_holds (h := h) hc hep hr hq heq
      rw [find?_holds_of_mem (take_inOrder hc) hx hxq]
      simp [hxh, heq, hrq, he]
    · rw [List.find?_eq_none.2 fun x hx hxq => heq ?_]
      · simp [heq]
      · obtain ⟨h1, h2, -⟩ := take_within hc hx
        rw [holdsPage_iff] at hxq ⊢
        exact ⟨by omega, by omega⟩

/-- After the extent `e` of a well-formed table takes the holding `h`, a page
of `e` has the owner of `h`, and every other page keeps its owner. -/
private theorem ownerOf_relabel {E X : Nat} {t t' : Ownership E X} {l₁ l₂ : List Extent} {e : Extent}
    {h : Holding} (hwf : t.WellFormed) (ht : t.extents = l₁ ++ e :: l₂)
    (ht' : t'.extents = l₁ ++ (⟨e.range, e.bank, h⟩ : Extent) :: l₂) (hb : t'.banks = t.banks)
    (hx : t'.exclusions = t.exclusions) (q : Nat) :
    t'.ownerOf q = if e.range.holdsPage q = true then some h.owner else t.ownerOf q := by
  have hord := hwf.2.2.2.2.2.2.1
  rw [ht] at hord
  have hord' : ExtentsInOrder t'.extents := by rw [ht']; exact inOrder_relabel h hord
  split
  · rename_i heq
    exact ownerOf_of_mem (x := ⟨e.range, e.bank, h⟩) hord' (by rw [ht']; simp) heq
  · rename_i heq
    refine ownerOf_congr (l₁ := l₁) (K := [e]) (M := [⟨e.range, e.bank, h⟩]) (l₂ := l₂)
      (by rw [ht]; simp) (by rw [ht']; simp) hb hx ?_
    simp [heq]

/-- After `mergeFreed` frees the extent `e` of a well-formed table, a page of
`e` is free, and every other page keeps its owner. -/
private theorem ownerOf_merge {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e : Extent} (hwf : t.WellFormed) (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t'.extents = mergeFreed before e after) (hb : t'.banks = t.banks)
    (hx : t'.exclusions = t.exclusions) {q : Nat} (hq : q % PAGE_SIZE = 0) :
    t'.ownerOf q = if e.range.holdsPage q = true then some .free else t.ownerOf q := by
  have hord := hwf.2.2.2.2.2.2.1
  rw [ht] at hord
  obtain ⟨l₁, K, l₂, m, h1, h2, heK, hm1, -, hK, -, -, hcov⟩ := mergeFreed_block before e after hord
  have hord' : ExtentsInOrder t'.extents := by rw [ht']; exact inOrder_merge hord
  have hKt : ∀ x ∈ K, x ∈ t.extents := fun x hx => by rw [ht, h1]; simp [hx]
  split
  · rename_i heq
    obtain ⟨-, -, hs, he⟩ := hK e heK
    refine (ownerOf_of_mem (x := m) hord' (by rw [ht', h2]; simp) ?_).trans (by rw [hm1]; rfl)
    rw [holdsPage_iff] at heq ⊢
    exact ⟨by omega, by omega⟩
  · rename_i heq
    refine ownerOf_congr (K := K) (M := [m]) (by rw [ht, h1]) (by rw [ht', h2]; simp) hb hx ?_
    by_cases hmq : m.range.holdsPage q = true
    · -- the page lies in an extent of the block other than `e`, which is free
      have hmq' := (holdsPage_iff _ _).1 hmq
      obtain ⟨k, hk, hk1, hk2⟩ := hcov q hmq'.1 (by simp only [PAGE_SIZE] at hmq'; omega)
      have hkp := (hwf.2.2.2.2.2.1 k (hKt k hk)).1
      have hkq : k.range.holdsPage q = true := by
        simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hkp
        rw [holdsPage_iff]
        exact ⟨hk1, by page_omega⟩
      cases hf : K.find? (·.range.holdsPage q) with
      | none => exact absurd hkq (by simpa using List.find?_eq_none.1 hf k hk)
      | some k' =>
        have hk'q := List.find?_some hf
        have hk'K := List.mem_of_find?_eq_some hf
        rcases (hK k' hk'K).2.1 with rfl | hfree
        · exact absurd hk'q heq
        · simp [hmq, hm1, hfree]
    · have hK0 : K.find? (·.range.holdsPage q) = none := List.find?_eq_none.2 fun k hk hkq => by
        obtain ⟨-, -, h3, h4⟩ := hK k hk
        rw [holdsPage_iff] at hkq
        exact hmq ((holdsPage_iff _ _).2 ⟨by omega, by omega⟩)
      rw [hK0]
      simp [hmq]

/-! ## The entries: well-formedness and the owner function -/

/-- `take` on a well-formed table, for a range on pages: the table is
well-formed and keeps its arena, banks and exclusion records; its counter
advances from the generation `g` that the receipt names; and the pages of the
range are held with `g`, every other page keeping its owner. -/
theorem take_spec {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} (hwf : t.WellFormed) (hr : c.range.onPages = true)
    (h : t.take c s = .ok (t', a)) :
    ∃ g, t.counter = .next g ∧ t'.counter = Counter.after g ∧
      a = ⟨t.arena, c.owner, g, c.range⟩ ∧ t'.WellFormed ∧ t'.arena = t.arena ∧
      t'.banks = t.banks ∧ t'.exclusions = t.exclusions ∧
      ∀ q, q % PAGE_SIZE = 0 → t'.ownerOf q =
        if c.range.holdsPage q = true then some (.held c.owner g s) else t.ownerOf q := by
  have hwf' := take_wellFormed hwf hr h
  obtain ⟨l₁, e, l₂, g, hg, ht, he, hc, -, rfl, rfl⟩ := take_ok h
  exact ⟨g, hg, rfl, rfl, hwf', rfl, rfl, rfl, fun q hq =>
    ownerOf_take (t' := ⟨t.arena, t.banks, _, t.exclusions, _⟩) hwf ht he hc hr rfl rfl rfl hq⟩

/-- `assign` of a choice of `choose` on a well-formed table: `take_spec`,
the pages published. -/
theorem assign_spec {E X : Nat} {t t' : Ownership E X} {c : Choice} {zeroed : Bool}
    {a : Allocation} (hwf : t.WellFormed) (hc : t.Chose c)
    (h : t.assign c zeroed = .ok (t', a)) :
    ∃ g, t.counter = .next g ∧ t'.counter = Counter.after g ∧
      a = ⟨t.arena, c.owner, g, c.range⟩ ∧ t'.WellFormed ∧ t'.arena = t.arena ∧
      t'.banks = t.banks ∧ t'.exclusions = t.exclusions ∧
      ∀ q, q % PAGE_SIZE = 0 → t'.ownerOf q =
        if c.range.holdsPage q = true then some (.held c.owner g .published) else t.ownerOf q := by
  obtain ⟨_, _, _, _, hch⟩ := hc
  exact take_spec hwf (choose_onPages hch) (assign_ok h).2

/-- `reserve` on a well-formed table: `take_spec` for the choice of `choose`,
the pages reserved. -/
theorem reserve_spec {E X : Nat} {t t' : Ownership E X} {owner pages alignment : UInt64}
    {p : Placement} {r : Reservation} (hwf : t.WellFormed)
    (h : t.reserve owner pages alignment p = .ok (t', r)) :
    ∃ c g, t.choose owner pages alignment p = .ok c ∧ t.counter = .next g ∧
      t'.counter = Counter.after g ∧ r = ⟨⟨t.arena, c.owner, g, c.range⟩, false, 0⟩ ∧
      t'.WellFormed ∧ t'.arena = t.arena ∧ t'.banks = t.banks ∧ t'.exclusions = t.exclusions ∧
      ∀ q, q % PAGE_SIZE = 0 → t'.ownerOf q =
        if c.range.holdsPage q = true then some (.held c.owner g .reserved) else t.ownerOf q := by
  obtain ⟨c, a, hch, ht, rfl⟩ := reserve_ok h
  obtain ⟨g, h1, h2, rfl, h4⟩ := take_spec hwf (choose_onPages hch) ht
  exact ⟨c, g, hch, h1, h2, rfl, h4⟩

/-- `publish` on a well-formed table: the table is well-formed and keeps its
arena, banks, exclusion records and counter; the packet names an extent of
the table, exactly its range, reserved by its owner identity with its
generation; the pages of that range are published, every other page
keeping its owner; and the packet is of the arena and the owner identity. -/
theorem publish_spec {E X : Nat} {t t' : Ownership E X} {o : UInt64} {x : Initialized}
    {a : Allocation} (hwf : t.WellFormed) (h : t.publish o x = .ok (t', a)) :
    a = x.allocation ∧ t'.WellFormed ∧ t'.arena = t.arena ∧ t'.banks = t.banks ∧
      t'.exclusions = t.exclusions ∧ t'.counter = t.counter ∧
      (∃ e ∈ t.extents, e.range = x.allocation.range ∧
        e.holding = .held o x.allocation.generation .reserved) ∧
      (∀ q, t'.ownerOf q = if x.allocation.range.holdsPage q = true then
        some (.held o x.allocation.generation .published) else t.ownerOf q) ∧
      x.allocation.arena = t.arena ∧ x.allocation.owner = o := by
  obtain ⟨before, e, after, hf, rfl, rfl⟩ := publish_ok h
  obtain ⟨ha, ho, ht, he1, he2⟩ := findHeld_ok hf
  refine ⟨rfl, relabel_wellFormed hwf ht rfl, rfl, rfl, rfl, rfl,
    ⟨e, by rw [ht]; simp, he1, he2⟩, fun q => ?_, ha, ho⟩
  rw [← he1]
  exact ownerOf_relabel (t' := ⟨t.arena, t.banks, _, t.exclusions, t.counter⟩) hwf ht rfl rfl rfl q

/-- The write of `release` and `cancel` on a well-formed table, which frees
the extent `e` found by `findHeld` and merges it with its free neighbours:
the table is well-formed and keeps its arena, banks, exclusion records and
counter; and the pages of `e` are free, every other page keeping its
owner. -/
theorem free_spec {E X : Nat} {t t' : Ownership E X} {before after : List Extent} {e : Extent}
    (hwf : t.WellFormed) (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩) :
    t'.WellFormed ∧ t'.arena = t.arena ∧ t'.banks = t.banks ∧ t'.exclusions = t.exclusions ∧
      t'.counter = t.counter ∧
      ∀ q, q % PAGE_SIZE = 0 → t'.ownerOf q =
        if e.range.holdsPage q = true then some .free else t.ownerOf q := by
  refine ⟨merge_wellFormed hwf ht ht', by rw [ht'], by rw [ht'], by rw [ht'], by rw [ht'],
    fun q hq => ?_⟩
  subst ht'
  exact ownerOf_merge (t' := ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩)
    hwf ht rfl rfl rfl hq

/-- `release` on a well-formed table: `free_spec` for the extent of the
receipt, exactly its range, published by the owner identity with its
generation; and the receipt is of the arena and the owner identity. -/
theorem release_spec {E X : Nat} {t t' : Ownership E X} {o : UInt64} {x : Allocation}
    (hwf : t.WellFormed) (h : t.release o x = .ok t') :
    t'.WellFormed ∧ t'.arena = t.arena ∧ t'.banks = t.banks ∧ t'.exclusions = t.exclusions ∧
      t'.counter = t.counter ∧
      (∃ e ∈ t.extents, e.range = x.range ∧ e.holding = .held o x.generation .published) ∧
      (∀ q, q % PAGE_SIZE = 0 → t'.ownerOf q =
        if x.range.holdsPage q = true then some .free else t.ownerOf q) ∧
      x.arena = t.arena ∧ x.owner = o := by
  obtain ⟨before, e, after, hf, ht'⟩ := release_ok h
  obtain ⟨ha, ho, ht, he1, he2⟩ := findHeld_ok hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := free_spec hwf ht ht'
  exact ⟨h1, h2, h3, h4, h5, ⟨e, by rw [ht]; simp, he1, he2⟩, by rw [← he1]; exact h6, ha, ho⟩

/-- `cancel` on a well-formed table: the reservation was not attempted, and
`free_spec` for the extent of the reservation, exactly its range, reserved by
the owner identity with its generation; and the reservation is of the arena
and the owner identity. -/
theorem cancel_spec {E X : Nat} {t t' : Ownership E X} {o : UInt64} {r : Reservation}
    (hwf : t.WellFormed) (h : t.cancel o r = .ok t') :
    r.attempted = false ∧ t'.WellFormed ∧ t'.arena = t.arena ∧ t'.banks = t.banks ∧
      t'.exclusions = t.exclusions ∧ t'.counter = t.counter ∧
      (∃ e ∈ t.extents, e.range = r.allocation.range ∧
        e.holding = .held o r.allocation.generation .reserved) ∧
      (∀ q, q % PAGE_SIZE = 0 → t'.ownerOf q =
        if r.allocation.range.holdsPage q = true then some .free else t.ownerOf q) ∧
      r.allocation.arena = t.arena ∧ r.allocation.owner = o := by
  obtain ⟨hr, before, e, after, hf, ht'⟩ := cancel_ok h
  obtain ⟨ha, ho, ht, he1, he2⟩ := findHeld_ok hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := free_spec hwf ht ht'
  exact ⟨hr, h1, h2, h3, h4, h5, ⟨e, by rw [ht]; simp, he1, he2⟩, by rw [← he1]; exact h6,
    ha, ho⟩

/-! ## The extents after a write -/

/-- After `take`, the range was inside a free extent of the table, and every
extent is one of the table, a free one, or the range held by the owner
identity of the choice with the generation of the counter. -/
theorem take_extents {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} (h : t.take c s = .ok (t', a)) :
    (∃ e ∈ t.extents, e.holding = .free ∧ e.range.contains c.range = true) ∧
      ∀ x ∈ t'.extents, x ∈ t.extents ∨ x.holding = .free ∨
        (x.range = c.range ∧ ∃ g, t.counter = .next g ∧ x.holding = .held c.owner g s) := by
  obtain ⟨l₁, e, l₂, g, hg, ht, he, hc, -, rfl, -⟩ := take_ok h
  refine ⟨⟨e, by rw [ht]; simp, he, hc⟩, fun x hx => ?_⟩
  simp only [List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact Or.inl (by rw [ht]; simp [hx])
  · rcases mem_take hx with rfl | ⟨-, hf, -⟩
    · exact Or.inr (Or.inr ⟨rfl, g, hg, rfl⟩)
    · exact Or.inr (Or.inl hf)
  · exact Or.inl (by rw [ht]; simp [hx])

/-- After `publish`, every extent is one of the table or the range of the
packet published by the owner identity with its generation. -/
theorem publish_extents {E X : Nat} {t t' : Ownership E X} {o : UInt64} {x : Initialized}
    {a : Allocation} (h : t.publish o x = .ok (t', a)) :
    ∀ y ∈ t'.extents, y ∈ t.extents ∨
      (y.range = x.allocation.range ∧ y.holding = .held o x.allocation.generation .published) := by
  obtain ⟨before, e, after, hf, rfl, -⟩ := publish_ok h
  obtain ⟨-, -, ht, he1, -⟩ := findHeld_ok hf
  intro y hy
  simp only [List.mem_append, List.mem_cons] at hy
  rcases hy with hy | rfl | hy
  · exact Or.inl (by rw [ht]; simp [hy])
  · exact Or.inr ⟨he1, rfl⟩
  · exact Or.inl (by rw [ht]; simp [hy])

/-- After `mergeFreed`, every extent is one of the extents before it or a free
one. -/
theorem mem_mergeFreed {before after : List Extent} {e y : Extent}
    (hy : y ∈ mergeFreed before e after) : y ∈ before.reverse ++ e :: after ∨ y.holding = .free := by
  obtain ⟨l₁, lo, hi, l₂, m, h1, h2, hm, -⟩ := mergeFreed_spec before e after
  rw [h2] at hy
  rw [h1]
  simp only [List.mem_append, List.mem_cons] at hy ⊢
  rcases hy with hy | rfl | hy
  · exact Or.inl (Or.inl (Or.inl hy))
  · exact Or.inr hm
  · exact Or.inl (Or.inr hy)

end Krepi.Proofs.PageTables
