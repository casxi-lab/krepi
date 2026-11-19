module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.PageTables.OwnerLemmas
public import Krepi.Proofs.PageTables.WriteLemmas

/-!
# Page tables: lemmas about the invariants of the page ownership table after a write

What a write of the page ownership table keeps of the functional invariants
of the table, from the owner function and the extents after the write
(`Krepi.Proofs.PageTables.WriteLemmas`):

- for any write: `holds_iff_of_ownerOf` (a write that gives the pages of
  extents a free or held owner and keeps the owner of every other page
  keeps the pages that the extents hold), `oneOwner_of_holds_iff` and
  `freeOrHeldUsable_of_holds_iff` (a write that keeps those pages, the
  banks and the exclusion records keeps one owner for every managed page,
  and the free and held pages), and `holdsPage_start` (an extent on pages
  holds the page at its start);
- for `take`, the write of `assign` and `reserve`, of a range on pages from
  a table that keeps `Ownership.Invariant`: `take_oneOwner` and
  `take_freeOrHeldUsable` (the pages that the extents hold are kept, by the
  private `take_holds_iff`: a page of the range was a page of the free
  extent that it was taken from), `take_holderRanges` (the range is held
  with the generation of the counter, which no holder of the table has),
  `take_generationsBelowCounter` (the counter grows by one) and
  `take_freeExtentsMaximal` (the free pieces of the extent that the range is
  taken from lie inside it, so a neighbour of a piece in its bank is a
  neighbour of that free extent);
- for `mergeFreed`, the write of `release` and `cancel`, which frees an
  extent `e` of a table that keeps `Ownership.Invariant` (its extents
  `before.reverse ++ e :: after`) and joins it with its free neighbours:
  `free_oneOwner` and `free_freeOrHeldUsable` (the pages that the extents
  hold are kept, by the private `free_holds_iff`: a page of `e` stays a
  page of an extent), `free_holderRanges` and
  `free_generationsBelowCounter` (every held extent after the write is one
  of the table, by the private `free_held_mem`, the counter is kept, and a
  page of `e` is free, so no held extent holds it) and
  `free_freeExtentsMaximal` (the merged extent joins the free neighbours of
  `e` in its bank; a neighbour that it does not join is not next to `e`, a
  joined one is not next to another free extent of its bank, and only the
  extents right before and after the merged one can be next to it, by the
  private `head_of_adjacent` and `last_of_adjacent`).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables

/-- `omega` after the page size is written as its value. -/
local macro "page_omega" : tactic => `(tactic| (simp only [PAGE_SIZE] at *; omega))

/-! ## Any write -/

/-- A write that gives the page at `q` a free or held owner when `P` holds,
which only a page of an extent of the table does, and keeps its owner
otherwise, keeps whether an extent holds the page. -/
theorem holds_iff_of_ownerOf {E X : Nat} {t t' : Ownership E X} {q : Nat} {P : Prop}
    [Decidable P] {o : Owner} (ho : o.isFreeOrHeld = true)
    (hP : P → ∃ x ∈ t.extents, x.range.holdsPage q = true)
    (h : t'.ownerOf q = if P then some o else t.ownerOf q) :
    (∃ x ∈ t'.extents, x.range.holdsPage q = true) ↔
      ∃ x ∈ t.extents, x.range.holdsPage q = true := by
  rw [← freeOrHeld_iff, ← freeOrHeld_iff, h]
  split
  · rename_i hp
    exact ⟨fun _ => (freeOrHeld_iff t q).2 (hP hp), fun _ => ⟨o, rfl, ho⟩⟩
  · exact Iff.rfl

/-- A write that keeps the pages that the extents hold, the banks and the
exclusion records of a table with one owner for every managed page keeps
one owner for every managed page. -/
theorem oneOwner_of_holds_iff {E X : Nat} {t t' : Ownership E X}
    (hl : ExtentsInOrder t.extents) (hl' : ExtentsInOrder t'.extents)
    (hb : t'.banks = t.banks) (hx : t'.exclusions = t.exclusions)
    (h : ∀ q, q % PAGE_SIZE = 0 → ((∃ x ∈ t'.extents, x.range.holdsPage q = true) ↔
      ∃ x ∈ t.extents, x.range.holdsPage q = true))
    (hone : t.OneOwner) : t'.OneOwner := by
  rintro q ⟨hq, hm⟩
  have h1 := (ownersOf_length_eq_one q hl).1 (hone q ⟨hq, by rw [← hb]; exact hm⟩)
  rw [ownersOf_length_eq_one q hl', h q hq, hx]
  exact h1

/-- A write that keeps the pages that the extents hold keeps the free and
held pages. -/
theorem freeOrHeldUsable_of_holds_iff {E X : Nat} {t t' : Ownership E X}
    {B : Krepi.Spec.Fdt.MemoryPlan}
    (h : ∀ q, q % PAGE_SIZE = 0 → ((∃ x ∈ t'.extents, x.range.holdsPage q = true) ↔
      ∃ x ∈ t.extents, x.range.holdsPage q = true))
    (hu : t.FreeOrHeldUsable B) : t'.FreeOrHeldUsable B := by
  intro q hq
  rw [freeOrHeld_iff, h q hq, ← freeOrHeld_iff]
  exact hu q hq

/-- A range on pages holds the page at its start. -/
theorem holdsPage_start {r : PhysRange} (hr : r.onPages = true) :
    r.holdsPage r.start.toNat = true := by
  have := range_lt r
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hr
  rw [holdsPage_iff]
  exact ⟨Nat.le_refl _, by page_omega⟩

/-! ## `take` -/

/-- `take` of a range on pages keeps the pages that the extents hold: a page
of the range was a page of the free extent that it was taken from. -/
private theorem take_holds_iff {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} (hwf : t.WellFormed) (hr : c.range.onPages = true)
    (h : t.take c s = .ok (t', a)) {q : Nat} (hq : q % PAGE_SIZE = 0) :
    (∃ x ∈ t'.extents, x.range.holdsPage q = true) ↔
      ∃ x ∈ t.extents, x.range.holdsPage q = true := by
  obtain ⟨g, -, -, -, -, -, -, -, hown⟩ := take_spec hwf hr h
  obtain ⟨⟨e, he, -, hec⟩, -⟩ := take_extents h
  refine holds_iff_of_ownerOf rfl (fun hrq => ⟨e, he, ?_⟩) (hown q hq)
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hec
  rw [holdsPage_iff] at hrq ⊢
  exact ⟨by omega, by omega⟩

theorem take_oneOwner {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} (hinv : t.Invariant) (hr : c.range.onPages = true)
    (h : t.take c s = .ok (t', a)) : t'.OneOwner := by
  obtain ⟨-, -, -, -, hwf', -, hb, hx, -⟩ := take_spec hinv.1 hr h
  exact oneOwner_of_holds_iff hinv.1.2.2.2.2.2.2.1 hwf'.2.2.2.2.2.2.1 hb hx
    (fun _ hq => take_holds_iff hinv.1 hr h hq) hinv.2.1

theorem take_freeOrHeldUsable {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} {B : Krepi.Spec.Fdt.MemoryPlan} (hinv : t.Invariant)
    (hr : c.range.onPages = true) (h : t.take c s = .ok (t', a))
    (hu : t.FreeOrHeldUsable B) : t'.FreeOrHeldUsable B :=
  freeOrHeldUsable_of_holds_iff (fun _ hq => take_holds_iff hinv.1 hr h hq) hu

theorem take_generationsBelowCounter {E X : Nat} {t t' : Ownership E X} {c : Choice}
    {s : HoldState} {a : Allocation} (hinv : t.Invariant) (hr : c.range.onPages = true)
    (h : t.take c s = .ok (t', a)) : t'.GenerationsBelowCounter := by
  obtain ⟨hwf, -, -, hgen, -⟩ := hinv
  obtain ⟨g, hg, hc', -, -, -, -, -, -⟩ := take_spec hwf hr h
  obtain ⟨-, hext⟩ := take_extents h
  intro q o n s' hq
  obtain ⟨y, hy, hyq, hyh⟩ := ownerOf_held hq
  rw [hc']
  rcases hext y hy with hy' | hf | ⟨-, g', hg', hyh'⟩
  · obtain ⟨h1, h2⟩ := hgen q o n s'
      ((ownerOf_of_mem hwf.2.2.2.2.2.2.1 hy' hyq).trans (by rw [hyh]; rfl))
    refine ⟨h1, fun g'' hg'' => ?_⟩
    have := counter_after_eq hg''
    have := h2 g hg
    omega
  · rw [hf] at hyh
    cases hyh
  · rw [hg] at hg'
    cases hg'
    rw [hyh'] at hyh
    cases hyh
    refine ⟨?_, fun g'' hg'' => ?_⟩
    · have h0 := hwf.2.2.2.2.2.2.2.2
      rw [hg] at h0
      have : g.toNat ≠ 0 := fun h =>
        h0 (by rw [UInt64.toNat_inj.1 (h.trans UInt64.toNat_zero.symm)])
      omega
    · have := counter_after_eq hg''
      omega

theorem take_holderRanges {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} (hinv : t.Invariant) (hr : c.range.onPages = true)
    (h : t.take c s = .ok (t', a)) : t'.HolderRanges := by
  obtain ⟨hwf, -, hhold, hgen, -⟩ := hinv
  obtain ⟨g, hg, -, -, -, -, -, -, hown⟩ := take_spec hwf hr h
  obtain ⟨⟨f, hf, hff, hfc⟩, hext⟩ := take_extents h
  have hl := hwf.2.2.2.2.2.2.1
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hfc
  intro y hy o n s' hyh q hq
  rw [hown q hq]
  rcases hext y hy with hy' | hyf | ⟨hyr, g', hg', hyh'⟩
  · -- an extent of the table, whose generation is below the counter
    have hn : n.toNat < g.toNat := (hgen _ o n s' ((ownerOf_of_mem hl hy'
      (holdsPage_start (hwf.2.2.2.2.2.1 y hy').1)).trans (by rw [hyh]; rfl))).2 g hg
    split
    · rename_i hrq
      constructor
      · rintro ⟨o', s'', he⟩
        simp only [Option.some.injEq, Owner.held.injEq] at he
        obtain ⟨-, rfl, -⟩ := he
        omega
      · intro hyq
        have hfq : f.range.holdsPage q = true := by
          rw [holdsPage_iff] at hrq ⊢
          exact ⟨by omega, by omega⟩
        have h1 := ownerOf_of_mem hl hf hfq
        rw [ownerOf_of_mem hl hy' hyq, hyh, hff] at h1
        cases h1
    · exact hhold y hy' o n s' hyh q hq
  · rw [hyf] at hyh
    cases hyh
  · -- the range taken, held with the generation of the counter
    rw [hg] at hg'
    cases hg'
    rw [hyh'] at hyh
    cases hyh
    rw [hyr]
    split
    · rename_i hrq
      exact ⟨fun _ => hrq, fun _ => ⟨_, _, rfl⟩⟩
    · rename_i hrq
      refine ⟨fun ⟨o', s'', he⟩ => ?_, fun h' => absurd h' hrq⟩
      have := (hgen q o' g s'' he).2 g hg
      omega

theorem take_freeExtentsMaximal {E X : Nat} {t t' : Ownership E X} {c : Choice} {s : HoldState}
    {a : Allocation} (hinv : t.Invariant) (h : t.take c s = .ok (t', a)) :
    t'.FreeExtentsMaximal := by
  obtain ⟨hwf, -, -, -, hmax⟩ := hinv
  obtain ⟨l₁, e, l₂, g, -, ht, he, hc, -, rfl, -⟩ := take_ok h
  have hl := hwf.2.2.2.2.2.2.1
  rw [ht, List.pairwise_append, List.pairwise_cons] at hl
  have h1 : ∀ x ∈ l₁, x.range.endNat ≤ e.range.start.toNat := fun x hx =>
    hl.2.2 x hx e (by simp)
  have h2 : ∀ x ∈ l₂, e.range.endNat ≤ x.range.start.toNat := hl.2.1.1
  have hm : ∀ x, x ∈ l₁ ∨ x ∈ l₂ → x ∈ t.extents := fun x hx => by
    rw [ht]
    rcases hx with hx | hx <;> simp [hx]
  have hemem : e ∈ t.extents := by rw [ht]; simp
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hr := range_lt c.range
  have he' := range_lt e.range
  -- a free extent after the write is one of the table or a free piece of `e`
  have cls : ∀ x ∈ l₁ ++ e.take c.range (.held c.owner g s) ++ l₂, x.holding = .free →
      x ∈ l₁ ∨ x ∈ l₂ ∨ (x.bank = e.bank ∧
        ((x.range.start.toNat = e.range.start.toNat ∧ x.range.endNat = c.range.start.toNat) ∨
          (x.range.start.toNat = c.range.endNat ∧ x.range.endNat = e.range.endNat))) := by
    intro x hx hxf
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl hx
    · rcases mem_take hx with rfl | ⟨hb, -, hs⟩
      · cases hxf
      · exact Or.inr (Or.inr ⟨hb, hs⟩)
    · exact Or.inr (Or.inl hx)
  intro x hx y hy hxf hyf hb hxy
  have hxl := range_lt x.range
  have hyl := range_lt y.range
  rcases cls x hx hxf with hx1 | hx1 | ⟨hxb, hxs⟩ <;>
    rcases cls y hy hyf with hy1 | hy1 | ⟨hyb, hys⟩
  · exact hmax x (hm x (Or.inl hx1)) y (hm y (Or.inl hy1)) hxf hyf hb hxy
  · have := h1 x hx1
    have := h2 y hy1
    omega
  · exact hmax x (hm x (Or.inl hx1)) e hemem hxf he (hb.trans hyb)
      (by have := h1 x hx1; rcases hys with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
  · have := h2 x hx1
    have := h1 y hy1
    omega
  · exact hmax x (hm x (Or.inr hx1)) y (hm y (Or.inr hy1)) hxf hyf hb hxy
  · have := h2 x hx1
    rcases hys with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · have := h1 y hy1
    rcases hxs with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · exact hmax e hemem y (hm y (Or.inr hy1)) he hyf (hxb.symm.trans hb)
      (by have := h2 y hy1; rcases hxs with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
  · rcases hxs with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases hys with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-! ## `mergeFreed` -/

/-- `mergeFreed` keeps the pages that the extents hold: a page of the freed
extent is free. -/
private theorem free_holds_iff {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e : Extent} (hwf : t.WellFormed) (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩)
    {q : Nat} (hq : q % PAGE_SIZE = 0) :
    (∃ x ∈ t'.extents, x.range.holdsPage q = true) ↔
      ∃ x ∈ t.extents, x.range.holdsPage q = true := by
  obtain ⟨-, -, -, -, -, hown⟩ := free_spec hwf ht ht'
  exact holds_iff_of_ownerOf rfl (fun hq => ⟨e, by rw [ht]; simp, hq⟩) (hown q hq)

/-- Every held extent after `mergeFreed` is one of the table. -/
private theorem free_held_mem {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e y : Extent} {o n : UInt64} {s : HoldState} (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩)
    (hy : y ∈ t'.extents) (hyh : y.holding = .held o n s) : y ∈ t.extents := by
  subst ht'
  rcases mem_mergeFreed hy with h | h
  · rw [ht]
    exact h
  · rw [h] at hyh
    cases hyh

theorem free_oneOwner {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e : Extent} (hinv : t.Invariant) (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩) :
    t'.OneOwner := by
  obtain ⟨hwf', -, hb, hx, -, -⟩ := free_spec hinv.1 ht ht'
  exact oneOwner_of_holds_iff hinv.1.2.2.2.2.2.2.1 hwf'.2.2.2.2.2.2.1 hb hx
    (fun _ hq => free_holds_iff hinv.1 ht ht' hq) hinv.2.1

theorem free_freeOrHeldUsable {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e : Extent} {B : Krepi.Spec.Fdt.MemoryPlan} (hinv : t.Invariant)
    (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩)
    (hu : t.FreeOrHeldUsable B) : t'.FreeOrHeldUsable B :=
  freeOrHeldUsable_of_holds_iff (fun _ hq => free_holds_iff hinv.1 ht ht' hq) hu

theorem free_generationsBelowCounter {E X : Nat} {t t' : Ownership E X}
    {before after : List Extent} {e : Extent} (hinv : t.Invariant)
    (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩) :
    t'.GenerationsBelowCounter := by
  obtain ⟨hwf, -, -, hgen, -⟩ := hinv
  intro q o n s hq
  obtain ⟨y, hy, hyq, hyh⟩ := ownerOf_held hq
  have hc : t'.counter = t.counter := by rw [ht']
  rw [hc]
  exact hgen q o n s ((ownerOf_of_mem hwf.2.2.2.2.2.2.1 (free_held_mem ht ht' hy hyh) hyq).trans
    (by rw [hyh]; rfl))

theorem free_holderRanges {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e : Extent} (hinv : t.Invariant) (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩) :
    t'.HolderRanges := by
  obtain ⟨hwf, -, hhold, -, -⟩ := hinv
  obtain ⟨hwf', -, -, -, -, hown⟩ := free_spec hwf ht ht'
  intro y hy o n s hyh q hq
  have h1 := hown q hq
  rw [h1]
  split
  · -- a page of the freed extent is free, so no held extent holds it
    rename_i heq
    refine ⟨fun ⟨o', s', h⟩ => (by simp at h), fun hyq => ?_⟩
    have h2 := ownerOf_of_mem hwf'.2.2.2.2.2.2.1 hy hyq
    rw [h1, hyh] at h2
    simp [heq, Holding.owner] at h2
  · exact hhold y (free_held_mem ht ht' hy hyh) o n s hyh q hq

/-- In extents in address order, an extent after `m` that starts where `m`
ends is the one right after `m`. -/
private theorem head_of_adjacent {m b : Extent} {l : List Extent}
    (hl : ExtentsInOrder (m :: l)) (hb : b ∈ l) (h : b.range.start.toNat = m.range.endNat) :
    l.head? = some b := by
  rcases l with _ | ⟨c, l⟩
  · simp at hb
  · rw [ExtentsInOrder, List.pairwise_cons, List.pairwise_cons] at hl
    rcases List.mem_cons.1 hb with rfl | hb
    · rfl
    · have h1 := hl.1 c (by simp)
      have h2 := hl.2.1 b hb
      have := range_lt c.range
      omega

/-- In extents in address order, an extent before `m` that ends where `m`
starts is the one right before `m`: the head of the extents before `m` in
reverse order. -/
private theorem last_of_adjacent {m a : Extent} {before l : List Extent}
    (hl : ExtentsInOrder (before.reverse ++ m :: l)) (ha : a ∈ before.reverse)
    (h : a.range.endNat = m.range.start.toNat) : before.head? = some a := by
  rcases before with _ | ⟨c, before⟩
  · simp at ha
  · simp only [List.reverse_cons, List.append_assoc, List.singleton_append, ExtentsInOrder,
      List.pairwise_append, List.pairwise_cons] at hl
    simp only [List.reverse_cons, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have h1 := hl.2.2 a ha c (by simp)
      have h2 := hl.2.1.1 m (by simp)
      have := range_lt c.range
      omega
    · rfl

theorem free_freeExtentsMaximal {E X : Nat} {t t' : Ownership E X} {before after : List Extent}
    {e : Extent} (hinv : t.Invariant) (ht : t.extents = before.reverse ++ e :: after)
    (ht' : t' = ⟨t.arena, t.banks, mergeFreed before e after, t.exclusions, t.counter⟩) :
    t'.FreeExtentsMaximal := by
  obtain ⟨hwf, -, -, -, hmax⟩ := hinv
  obtain ⟨hwf', -⟩ := free_spec hwf ht ht'
  obtain ⟨l₁, lo, hi, l₂, m, h1, h2, -, hmb, hlo, hhi⟩ := mergeFreed_spec before e after
  have hext : t'.extents = l₁ ++ m :: l₂ := by subst ht'; exact h2
  have hl : ExtentsInOrder (l₁ ++ m :: l₂) := hext ▸ hwf'.2.2.2.2.2.2.1
  have hl2 : ExtentsInOrder (m :: l₂) := (List.pairwise_append.1 hl).2.1
  have hmem : ∀ x, x ∈ l₁ ∨ x ∈ lo ∨ x ∈ hi ∨ x ∈ l₂ → x ∈ t.extents := fun x hx => by
    rw [ht, h1]
    simp only [List.mem_append, List.mem_cons]
    rcases hx with hx | hx | hx | hx <;> simp [hx]
  have o1 : ∀ x ∈ l₁, x.range.endNat ≤ m.range.start.toNat := fun x hx =>
    (List.pairwise_append.1 hl).2.2 x hx m (by simp)
  have o2 : ∀ x ∈ l₂, m.range.endNat ≤ x.range.start.toNat := fun x hx =>
    (List.pairwise_cons.1 hl2).1 x hx
  have hm := range_lt m.range
  intro a ha b hb haf hbf hab hend
  rw [hext, List.mem_append, List.mem_cons] at ha hb
  rcases ha with ha | rfl | ha <;> rcases hb with hb | rfl | hb
  · exact hmax a (hmem a (Or.inl ha)) b (hmem b (Or.inl hb)) haf hbf hab hend
  · -- `a` ends where the merged extent starts
    rcases hlo with ⟨rfl, rfl, hms, hnone⟩ | ⟨x, rfl, -, -, hxf, hxb, hxe, hms⟩
    · exact hnone a (by rw [last_of_adjacent hl ha hend]; rfl) ⟨haf, hab.trans hmb, by omega⟩
    · exact hmax a (hmem a (Or.inl ha)) x (hmem x (Or.inr (Or.inl (by simp)))) haf hxf
        (hab.trans (hmb.trans hxb.symm)) (by omega)
  · exact hmax a (hmem a (Or.inl ha)) b (hmem b (Or.inr (Or.inr (Or.inr hb)))) haf hbf hab hend
  · have := o1 b hb
    have := range_lt b.range
    omega
  · omega
  · -- `b` starts where the merged extent ends
    rcases hhi with ⟨rfl, rfl, hme, hnone⟩ | ⟨y, rfl, -, -, hyf, hyb, hye, hme⟩
    · exact hnone b (by rw [head_of_adjacent hl2 hb hend.symm]; rfl)
        ⟨hbf, hab.symm.trans hmb, by omega⟩
    · exact hmax y (hmem y (Or.inr (Or.inr (Or.inl (by simp))))) b
        (hmem b (Or.inr (Or.inr (Or.inr hb)))) hyf hbf (hyb.trans (hmb.symm.trans hab))
        (by omega)
  · exact hmax a (hmem a (Or.inr (Or.inr (Or.inr ha)))) b (hmem b (Or.inl hb)) haf hbf hab hend
  · have := o2 a ha
    have := range_lt a.range
    omega
  · exact hmax a (hmem a (Or.inr (Or.inr (Or.inr ha)))) b
      (hmem b (Or.inr (Or.inr (Or.inr hb)))) haf hbf hab hend

end Krepi.Proofs.PageTables
