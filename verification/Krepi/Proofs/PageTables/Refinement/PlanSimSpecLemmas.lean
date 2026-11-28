module

public import Krepi.Proofs.PageTables.Refinement.LayoutSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the cursor of a map plan simulates `mapPlan`

The plan iterators of `kernel_map` and `direct_map` (`KernelMapPlan::next`,
`DirectMapPlan::next`) are each one call of the cursor of the code on
numbers, `Cur.step find place base`, for a search `find` of the leaves of
their map (`Krepi.Proofs.PageTables.Refinement.CursorSpecLemmas`). This
module proves, for any search that finds the first leaf after an address and
any place that reads the place of each leaf, that the calls of `Cur.step`
from the cursor before the first leaf give exactly `mapPlan` of the placed
leaves of `assignTables`, then none at a state that stays; and it turns that
into `Stands` for any iterator whose `next` is one such call. It imports no
generated definitions. The cursor's next free table stays at or below the
record after the write phase at each call and after it (`CurBound`), which
is what bounds the tables that the cursor of the code takes.

- Runs of a step function: `CurSteps`, `CurRuns`, `curSteps_nil`,
  `curSteps_cons`, `curSteps_append`, `curSteps_of_step_eq`,
  `curSteps_transfer`, `curRuns_of_steps`, `curSteps_first`, and
  `stands_of_curRuns` (an iterator stands for the list that the run of its
  cursor gives; each call may rely on the invariant before and after it).
- One call of `Cur.step` in each phase: `step_leaf_none`, `step_leaf_root`,
  `step_leaf_level2_block`, `step_leaf_level2_page`, `step_leaf_level3`,
  `step_held_leaf`, `step_held_same`, `step_newPages_some`,
  `step_newPages_none`, `step_newTable`, `step_children_same`,
  `step_children_new`, `step_children_none`, `step_entries_block`,
  `step_entries_page`, `step_entries_none`, `step_root`, `step_done`;
  `leaf_seek` and `take_seek` (a call that seeks is at a root block).
- The placed leaves one by one, without a well-formed set: `pOf`, `plOf`,
  `stOf`, `assignTables_eq`, `plOf_append`, `plOf_leaf`, `stOf_append`,
  `next_le_stOf`, the one-leaf lemmas `add_root_block`, `add_root_page_new`,
  `add_root_page_old`, `add_root_miss`, `add_level2_block`,
  `add_level2_page_new`, `add_level2_page_old`, `add_level3`, and
  `plOf_steady`, `plOf_root_pages`, `pOf_root_t2` for the leaves of a run.
- The leaves and the search: `fOf`, `leafFirst` (the first leaf of a suffix
  below a limit, pages only when asked), `SplitAt` (an address that splits
  the leaves), `PlaceLe`, and `SimOk`, what the simulation assumes of the
  leaves, the search and the place; numbers of the leaves (`leaf_nums`,
  `slotOf_eq_iff`, `gibOf_eq_iff`, `slots_le`, `block_before`,
  `before_block`, `leaf_low`, `leaf_end_slot`, `leaf_end_gib`,
  `slot_end_le`, `gib_end_le`, `end_le_gib`, `index1_gib`, `index2_slot`,
  `index2_fOf`, `index3_fOf`) and of the search (`find_first`, `find_none`).
- The simulation: `CurBound` (what the cursor of the code needs at each
  call), `CurOk` (that and an address that splits the leaves), `Bnd` (the cursor at the first leaf of a 2 MiB slot), the steps of a
  run of pages `pages_loop`, the 2 MiB slots under a level 2 table of the set
  `seg_held_block`, `seg_held_l3`, `seg_held_l2`, `seg_held`, `held_run`, a
  1 GiB slot under a new level 2 table `children_run`, `entries_run`,
  `seg_new`, the end `end_run`, and the whole plan `main_run`,
  **`curRuns_mapPlan`** and **`stands_mapPlan`**.
-/

@[expose] public section

open Krepi.Spec.PageTables Krepi.Statements Krepi.Proofs.Fdt.Refinement
open Aeneas Aeneas.Std Aeneas.Std.WP

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Runs of a step function on cursors -/

/-- `CurSteps step P c l c'`: the calls of `step` from `c` give the steps of
`l`, one a call, and reach `c'`; `P` holds at each state from which a call is
made. -/
def CurSteps (step : Cur → Option Step × Cur) (P : Cur → Prop) : Cur → List Step → Cur → Prop
  | c, [], c' => c = c'
  | c, s :: l, c' => P c ∧ (step c).1 = some s ∧ CurSteps step P (step c).2 l c'

/-- `CurRuns step P c l`: the calls of `step` from `c` give the steps of `l`,
then none, at a state where a call gives none and that state again; `P`
holds at each state from which a call is made. -/
def CurRuns (step : Cur → Option Step × Cur) (P : Cur → Prop) (c : Cur) (l : List Step) : Prop :=
  ∃ c', CurSteps step P c l c' ∧ P c' ∧ (step c').1 = none ∧ P (step c').2 ∧
    step (step c').2 = (none, (step c').2)

section Runs

variable {step : Cur → Option Step × Cur} {P : Cur → Prop}

theorem curSteps_nil (c : Cur) : CurSteps step P c [] c := rfl

theorem curSteps_cons {c c1 c' : Cur} {s : Step} {l : List Step} (hp : P c)
    (hs : step c = (some s, c1)) (h : CurSteps step P c1 l c') : CurSteps step P c (s :: l) c' :=
  ⟨hp, by rw [hs], by rw [hs]; exact h⟩

theorem curSteps_append {c1 c2 : Cur} {l2 : List Step} (h2 : CurSteps step P c1 l2 c2) :
    ∀ {c : Cur} {l1 : List Step}, CurSteps step P c l1 c1 → CurSteps step P c (l1 ++ l2) c2
  | c, [], h1 => by
    have : c = c1 := h1
    subst this; exact h2
  | c, s :: l1, h1 => ⟨h1.1, h1.2.1, curSteps_append h2 h1.2.2⟩

/-- A call that gives what a call from another state gives: the steps from
the other state are the steps from this one. -/
theorem curSteps_of_step_eq {c c1 c' : Cur} {s : Step} {l : List Step} (hp : P c)
    (he : step c = step c1) (h : CurSteps step P c1 (s :: l) c') : CurSteps step P c (s :: l) c' :=
  ⟨hp, by rw [he]; exact h.2.1, by rw [he]; exact h.2.2⟩

theorem curRuns_of_steps {c c' : Cur} {l1 l2 : List Step} (h1 : CurSteps step P c l1 c')
    (h2 : CurRuns step P c' l2) : CurRuns step P c (l1 ++ l2) := by
  obtain ⟨c'', h, hrest⟩ := h2
  exact ⟨c'', curSteps_append h h1, hrest⟩

/-- The first state of steps that reach a state where `P` holds keeps `P`. -/
theorem curSteps_first {c c' : Cur} {l : List Step} (h : CurSteps step P c l c') (hp : P c') :
    P c := by
  cases l with
  | nil => have : c = c' := h; subst this; exact hp
  | cons s l => exact h.1

end Runs

/-- An iterator stands for each list that the run of the cursor of its
state gives, when each call of its `next` from a state that keeps `Inv` and
whose cursor `abs` keeps `P`, as the cursor after `step` does, gives an item
related to the step of `step`, a state that keeps `Inv` whose cursor is the
cursor after `step`, and the same state when the cursor stays. -/
theorem stands_of_curRuns {σ α : Type} {next : σ → Result (Option α × σ)} {rel : α → Step → Prop}
    {abs : σ → Cur} {Inv : σ → Prop} {step : Cur → Option Step × Cur} {P : Cur → Prop}
    (hnext : ∀ it, Inv it → P (abs it) → P (step (abs it)).2 → next it ⦃ o it' =>
      OptionRel rel o (step (abs it)).1 ∧ abs it' = (step (abs it)).2 ∧ Inv it' ∧
        (abs it' = abs it → it' = it) ⦄) :
    ∀ (l : List Step) (it : σ), Inv it → CurRuns step P (abs it) l → Stands next rel it l := by
  have key : ∀ (l : List Step) (it : σ) (c' : Cur), Inv it → CurSteps step P (abs it) l c' →
      P c' → (step c').1 = none → P (step c').2 → step (step c').2 = (none, (step c').2) →
      Stands next rel it l := by
    intro l
    induction l with
    | nil =>
      intro it c' hi hs hp hn hp' hfix
      have hc : abs it = c' := hs
      subst hc
      rw [stands_nil]
      refine spec_mono (hnext it hi hp hp') ?_
      rintro ⟨o, it'⟩ ⟨ho, habs, hi', -⟩
      rw [hn] at ho
      have ho' : o = none := by cases o <;> simp_all
      refine ⟨ho', ?_⟩
      obtain ⟨⟨o2, it2⟩, heq, ho2, habs2, -, hfx⟩ := spec_iff.1 (hnext it' hi' (by rw [habs]; exact hp')
        (by rw [habs, hfix]; exact hp'))
      rw [habs, hfix] at ho2 habs2
      have h1 : o2 = none := by cases o2 <;> simp_all
      have h2 : it2 = it' := hfx (by rw [habs2, habs])
      rw [heq, h1, h2]
    | cons s l ih =>
      intro it c' hi hs hp hn hp' hfix
      obtain ⟨hp0, hs0, hrest⟩ := hs
      rw [stands_cons]
      refine spec_mono (hnext it hi hp0 (curSteps_first hrest hp)) ?_
      rintro ⟨o, it'⟩ ⟨ho, habs, hi', -⟩
      rw [hs0] at ho
      cases o with
      | none => simp at ho
      | some a =>
        refine ⟨a, rfl, ho, ih it' c' hi' ?_ hp hn hp' hfix⟩
        rw [habs]; exact hrest
  intro l it hi ⟨c', hs, hp, hn, hp', hfix⟩
  exact key l it c' hi hs hp hn hp' hfix

/-! ## One call of `Cur.step` in each phase -/

section Step

variable (find : Nat → Nat → Bool → Option Found) (place : Found → Place) (base : UInt64)

theorem step_leaf_none {c : Cur} (hp : c.phase = .leaf) (hf : find c.frm (2 ^ 64 - 1) false = none) :
    Cur.step find place base c = (some .sync, { c with phase := .done }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.leaf]

theorem step_leaf_root {c : Cur} {f : Found} (hp : c.phase = .leaf)
    (hf : find c.frm (2 ^ 64 - 1) false = some f) (hpl : place f = .root)
    (hf' : f.block = false → find f.pa (gibOf f.pa + GIB_SIZE) true = some f) :
    Cur.step find place base c =
      Cur.step find place base ⟨.children, f.pa, c.next + 1, gibOf f.pa, noSlot, c.next, c.t3⟩ := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  cases hb : f.block with
  | true => simp only [Cur.step, Cur.search, hf, Cur.take, Cur.leaf, hpl, hb, ↓reduceIte]
  | false =>
    simp only [Cur.step, Cur.search, hf, Cur.take, Cur.leaf, hpl, hb, hf' hb, Bool.false_eq_true,
      ↓reduceIte, Cur.children, slotOf_ne_noSlot]

theorem step_leaf_level2_block {c : Cur} {f : Found} {t2 : Nat} (hp : c.phase = .leaf)
    (hf : find c.frm (2 ^ 64 - 1) false = some f) (hpl : place f = .level2 t2) (hb : f.block = true) :
    Cur.step find place base c = (some (.store t2 (index2 (UInt64.ofNat f.pa)) f.desc),
      { c with frm := f.pa + BLOCK_SIZE, gib := gibOf f.pa, slot := slotOf f.pa, t2 := t2 }) := by
  obtain ⟨ph, frm, nx, g, sl, t2', t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.leaf, hpl, hb, ↓reduceIte]

theorem step_leaf_level2_page {c : Cur} {f : Found} {t2 : Nat} (hp : c.phase = .leaf)
    (hf : find c.frm (2 ^ 64 - 1) false = some f) (hpl : place f = .level2 t2) (hb : f.block = false) :
    Cur.step find place base c = (some (.zero c.next),
      ⟨.newPages, f.pa, c.next + 1, gibOf f.pa, slotOf f.pa, t2, c.next⟩) := by
  obtain ⟨ph, frm, nx, g, sl, t2', t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.leaf, hpl, hb, Bool.false_eq_true, ↓reduceIte]

theorem step_leaf_level3 {c : Cur} {f : Found} {t2 t3 : Nat} (hp : c.phase = .leaf)
    (hf : find c.frm (2 ^ 64 - 1) false = some f) (hpl : place f = .level3 t2 t3) :
    Cur.step find place base c = (some (.store t3 (index3 (UInt64.ofNat f.pa)) f.desc),
      ⟨.heldPages, f.pa + PAGE_SIZE, c.next, gibOf f.pa, slotOf f.pa, t2, t3⟩) := by
  obtain ⟨ph, frm, nx, g, sl, t2', t3'⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.leaf, hpl]

/-- A call in `heldPages` for no leaf or a leaf of another 2 MiB slot is the
call in `leaf`. -/
theorem step_held_leaf {c : Cur} (hp : c.phase = .heldPages)
    (hf : ∀ f, find c.frm (2 ^ 64 - 1) false = some f → slotOf f.pa ≠ c.slot) :
    Cur.step find place base c = Cur.step find place base { c with phase := .leaf } := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  cases ho : find frm (2 ^ 64 - 1) false with
  | none => simp only [Cur.step, Cur.search, ho, Cur.take, Cur.heldPage]
  | some f =>
    have hne := hf f ho
    simp only [Cur.step, Cur.search, ho, Cur.take, Cur.heldPage, hne, ↓reduceIte]

theorem step_held_same {c : Cur} {f : Found} (hp : c.phase = .heldPages)
    (hf : find c.frm (2 ^ 64 - 1) false = some f) (hs : slotOf f.pa = c.slot) :
    Cur.step find place base c =
      (some (.store c.t3 (index3 (UInt64.ofNat f.pa)) f.desc), { c with frm := f.pa + PAGE_SIZE }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf hs ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.heldPage, hs, ↓reduceIte]

theorem step_newPages_some {c : Cur} {f : Found} (hp : c.phase = .newPages)
    (hf : find c.frm (c.slot + BLOCK_SIZE) false = some f) :
    Cur.step find place base c =
      (some (.store c.t3 (index3 (UInt64.ofNat f.pa)) f.desc), { c with frm := f.pa + PAGE_SIZE }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.newPage]

theorem step_newPages_none {c : Cur} (hp : c.phase = .newPages)
    (hf : find c.frm (c.slot + BLOCK_SIZE) false = none) :
    Cur.step find place base c = (some .fence, { c with phase := .newTable }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.newPage]

theorem step_newTable {c : Cur} (hp : c.phase = .newTable) :
    Cur.step find place base c =
      (some (.store c.t2 (index2 (UInt64.ofNat c.slot)) (tableAt base c.t3)),
        { c with phase := .leaf, frm := c.slot + BLOCK_SIZE }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp ⊢; subst hp
  simp only [Cur.step, Cur.take]

theorem step_children_same {c : Cur} {f : Found} (hp : c.phase = .children)
    (hf : find c.frm (c.gib + GIB_SIZE) true = some f) (hs : slotOf f.pa = c.slot) :
    Cur.step find place base c =
      (some (.store c.t3 (index3 (UInt64.ofNat f.pa)) f.desc), { c with frm := f.pa + PAGE_SIZE }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf hs ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.children, hs, ↓reduceIte]

theorem step_children_new {c : Cur} {f : Found} (hp : c.phase = .children)
    (hf : find c.frm (c.gib + GIB_SIZE) true = some f) (hs : slotOf f.pa ≠ c.slot) :
    Cur.step find place base c =
      (some (.zero c.next),
        { c with frm := f.pa, next := c.next + 1, slot := slotOf f.pa, t3 := c.next }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf hs ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.children, hs, ↓reduceIte]

theorem step_children_none {c : Cur} (hp : c.phase = .children)
    (hf : find c.frm (c.gib + GIB_SIZE) true = none) :
    Cur.step find place base c =
      (some (.zero c.t2), { c with phase := .entries, frm := c.gib, t3 := c.t2 + 1 }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.children]

theorem step_entries_block {c : Cur} {f : Found} (hp : c.phase = .entries)
    (hf : find c.frm (c.gib + GIB_SIZE) false = some f) (hb : f.block = true) :
    Cur.step find place base c =
      (some (.store c.t2 (index2 (UInt64.ofNat f.pa)) f.desc),
        { c with frm := slotOf f.pa + BLOCK_SIZE }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.entry, hb, ↓reduceIte]

theorem step_entries_page {c : Cur} {f : Found} (hp : c.phase = .entries)
    (hf : find c.frm (c.gib + GIB_SIZE) false = some f) (hb : f.block = false) :
    Cur.step find place base c =
      (some (.store c.t2 (index2 (UInt64.ofNat f.pa)) (tableAt base c.t3)),
        { c with frm := slotOf f.pa + BLOCK_SIZE, t3 := c.t3 + 1 }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.entry, hb, Bool.false_eq_true, ↓reduceIte]

theorem step_entries_none {c : Cur} (hp : c.phase = .entries)
    (hf : find c.frm (c.gib + GIB_SIZE) false = none) :
    Cur.step find place base c = (some .fence, { c with phase := .root }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp hf ⊢; subst hp
  simp only [Cur.step, Cur.search, hf, Cur.take, Cur.entry]

theorem step_root {c : Cur} (hp : c.phase = .root) :
    Cur.step find place base c =
      (some (.store 0 (index1 (UInt64.ofNat c.gib)) (tableAt base c.t2)),
        { c with phase := .leaf, frm := c.gib + GIB_SIZE }) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp ⊢; subst hp
  simp only [Cur.step, Cur.take]

theorem step_done {c : Cur} (hp : c.phase = .done) : Cur.step find place base c = (none, c) := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  simp only at hp ⊢; subst hp
  simp only [Cur.step, Cur.take]

/-- A call of `leaf` that seeks is at a root block: the cursor after it is
in `children` at that leaf. -/
theorem leaf_seek (d : Cur) (f : Found) (hd : (d.leaf place (some f)).1 = .seek) :
    (d.leaf place (some f)).2 = ⟨.children, f.pa, d.next + 1, gibOf f.pa, noSlot, d.next, d.t3⟩ := by
  cases hp : place f with
  | root =>
    cases hb : f.block
    · simp only [Cur.leaf, hp, hb, Bool.false_eq_true, ↓reduceIte] at hd; cases hd
    · simp only [Cur.leaf, hp, hb, ↓reduceIte]
  | level2 t2 =>
    cases hb : f.block
    · simp only [Cur.leaf, hp, hb, Bool.false_eq_true, ↓reduceIte] at hd; cases hd
    · simp only [Cur.leaf, hp, hb, ↓reduceIte] at hd; cases hd
  | level3 t2 t3 => simp only [Cur.leaf, hp] at hd; cases hd

/-- A call of `take` that seeks comes from a leaf found: the cursor after it
is in `children` at that leaf. -/
theorem take_seek {c : Cur} {o : Option Found} (h : (c.take place base o).1 = .seek) :
    ∃ f, o = some f ∧ (c.take place base o).2 =
      ⟨.children, f.pa, c.next + 1, gibOf f.pa, noSlot, c.next, c.t3⟩ := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  cases o with
  | none =>
    cases ph <;> simp only [Cur.take, Cur.leaf, Cur.heldPage] at h <;> cases h
  | some f =>
    refine ⟨f, rfl, ?_⟩
    cases ph
    · exact leaf_seek place _ f h
    · by_cases hs : slotOf f.pa = sl
      · simp only [Cur.take, Cur.heldPage, hs, ↓reduceIte] at h; cases h
      · simp only [Cur.take, Cur.heldPage, hs, ↓reduceIte] at h ⊢
        exact leaf_seek place _ f h
    all_goals (simp only [Cur.take] at h; cases h)
end Step

/-! ## The placed leaves one by one -/

/-- The placed leaf that `Alloc.add` puts first for one more leaf. -/
def pOf (a : Alloc) (x : MapLeaf × Place) : Placed :=
  ⟨x.1, (stage2 a x.1 x.2).1, (stage2 a x.1 x.2).2.1, (stage3 (stage2 a x.1 x.2).2.2 x.1 x.2).1,
    (stage3 (stage2 a x.1 x.2).2.2 x.1 x.2).2.1⟩

/-- The placed leaves of the leaves `L`, from the tables `a` of the leaves
before them. -/
def plOf : Alloc → List (MapLeaf × Place) → List Placed
  | _, [] => []
  | a, x :: L => pOf a x :: plOf (a.add x) L

/-- The tables after the leaves `L`, from the tables `a`. -/
def stOf (a : Alloc) (L : List (MapLeaf × Place)) : Alloc := L.foldl Alloc.add a

theorem stage2_placed_eq (a : Alloc) (l : MapLeaf) (p : Place) :
    (stage2 a l p).2.2.placed = a.placed := by
  cases p with
  | root => rw [stage2_root]
  | level2 t => rfl
  | level3 t u => rfl

theorem stage3_placed_eq (a : Alloc) (l : MapLeaf) (p : Place) :
    (stage3 a l p).2.2.placed = a.placed := by
  obtain ⟨n, l2, l3, pl⟩ := a
  cases hf : l.form <;> cases p <;> simp only [stage3, hf] <;>
    (cases l3 with
     | none => rfl
     | some bt => obtain ⟨b, t⟩ := bt; simp only; split <;> rfl)

theorem add_placed_eq (a : Alloc) (x : MapLeaf × Place) : (a.add x).placed = pOf a x :: a.placed := by
  obtain ⟨l, p⟩ := x
  rw [add_eq]
  simp only [stage3_placed_eq, stage2_placed_eq]
  rfl

theorem foldl_placed_eq : ∀ (L : List (MapLeaf × Place)) (a : Alloc),
    (L.foldl Alloc.add a).placed = (plOf a L).reverse ++ a.placed
  | [], a => by simp [plOf]
  | x :: L, a => by
    rw [List.foldl_cons, foldl_placed_eq L, add_placed_eq]
    simp [plOf]

/-- `assignTables` by `stOf` and `plOf`. -/
theorem assignTables_eq (used : Nat) (L : List (MapLeaf × Place)) :
    assignTables used L = ((stOf ⟨used, none, none, []⟩ L).next, plOf ⟨used, none, none, []⟩ L) := by
  simp only [assignTables, stOf, foldl_placed_eq, List.append_nil, List.reverse_reverse]

theorem stOf_nil (a : Alloc) : stOf a [] = a := rfl

theorem stOf_cons (a : Alloc) (x : MapLeaf × Place) (L : List (MapLeaf × Place)) :
    stOf a (x :: L) = stOf (a.add x) L := rfl

theorem stOf_append (a : Alloc) (A B : List (MapLeaf × Place)) :
    stOf a (A ++ B) = stOf (stOf a A) B := List.foldl_append

theorem plOf_append : ∀ (A B : List (MapLeaf × Place)) (a : Alloc),
    plOf a (A ++ B) = plOf a A ++ plOf (stOf a A) B
  | [], B, a => rfl
  | x :: A, B, a => by
    simp only [List.cons_append, plOf, stOf_cons]
    rw [plOf_append A B]

theorem plOf_leaf : ∀ (L : List (MapLeaf × Place)) (a : Alloc),
    (plOf a L).map (·.leaf) = L.map (·.1)
  | [], a => rfl
  | x :: L, a => by simp only [plOf, List.map_cons, plOf_leaf L]; rfl

theorem plOf_length (L : List (MapLeaf × Place)) (a : Alloc) : (plOf a L).length = L.length := by
  have := congrArg List.length (plOf_leaf L a)
  simpa using this

theorem cacheStep_next (c : Option (Nat × Nat)) (s n : Nat) : n ≤ (cacheStep c s n).2.2 := by
  unfold cacheStep
  split
  · split <;> simp
  · simp

theorem cacheStep_hit {c : Option (Nat × Nat)} {s t n : Nat} (h : c = some (s, t)) :
    cacheStep c s n = (t, c, n) := by
  subst h; simp [cacheStep]

theorem cacheStep_miss {c : Option (Nat × Nat)} {s n : Nat} (h : ∀ t, c ≠ some (s, t)) :
    cacheStep c s n = (n, some (s, n), n + 1) := by
  cases c with
  | none => rfl
  | some gt =>
    obtain ⟨g, t⟩ := gt
    have hg : (g == s) = false := beq_eq_false_iff_ne.2 (fun e => h t (by rw [e]))
    simp [cacheStep, hg]

theorem next_le_add (a : Alloc) (x : MapLeaf × Place) : a.next ≤ (a.add x).next := by
  obtain ⟨l, p⟩ := x
  rw [add_eq]
  have h2 : a.next ≤ (stage2 a l p).2.2.next := by
    cases p with
    | root => rw [stage2_root]; exact cacheStep_next _ _ _
    | level2 t => exact le_refl _
    | level3 t u => exact le_refl _
  have h3 : ∀ b : Alloc, b.next ≤ (stage3 b l p).2.2.next := by
    intro b
    cases hf : l.form with
    | block => simp [stage3, hf]
    | page =>
      cases p with
      | level3 t u => simp [stage3, hf]
      | root => rw [stage3_new _ _ _ hf (fun _ _ h => by cases h)]; exact cacheStep_next _ _ _
      | level2 t => rw [stage3_new _ _ _ hf (fun _ _ h => by cases h)]; exact cacheStep_next _ _ _
  exact le_trans h2 (h3 _)

theorem next_le_stOf : ∀ (L : List (MapLeaf × Place)) (a : Alloc), a.next ≤ (stOf a L).next
  | [], _ => le_refl _
  | x :: L, a => le_trans (next_le_add a x) (next_le_stOf L (a.add x))

/-! ### One more leaf, by its place -/

/-- A leaf whose root entry is invalid in the 1 GiB slot of the latest new
level 2 table, a block: the table of the slot, no level 3 table, the tables
unchanged. -/
theorem add_root_block {a : Alloc} {x : MapLeaf × Place} {t : Nat}
    (h2 : a.level2 = some (x.1.gibSlot, t)) (hp : x.2 = .root) (hf : x.1.form = .block) :
    pOf a x = ⟨x.1, t, true, 0, false⟩ ∧ (a.add x).next = a.next ∧ (a.add x).level2 = a.level2 ∧
      (a.add x).level3 = a.level3 := by
  obtain ⟨l, p⟩ := x
  simp only at h2 hp hf; subst hp
  have hs := stage2_root a l
  rw [cacheStep_hit h2] at hs
  simp only [pOf, add_eq, hs, stage3, hf, and_self]

/-- A page whose root entry is invalid in the 1 GiB slot of the latest new
level 2 table, in another 2 MiB slot than the latest new level 3 table: a new
level 3 table, the next free one. -/
theorem add_root_page_new {a : Alloc} {x : MapLeaf × Place} {t : Nat}
    (h2 : a.level2 = some (x.1.gibSlot, t)) (h3 : ∀ u, a.level3 ≠ some (x.1.blockSlot, u))
    (hp : x.2 = .root) (hf : x.1.form = .page) :
    pOf a x = ⟨x.1, t, true, a.next, true⟩ ∧ (a.add x).next = a.next + 1 ∧
      (a.add x).level2 = a.level2 ∧ (a.add x).level3 = some (x.1.blockSlot, a.next) := by
  obtain ⟨l, p⟩ := x
  simp only at h2 h3 hp hf; subst hp
  have hs := stage2_root a l
  rw [cacheStep_hit h2] at hs
  have h3' := stage3_new a l .root hf (fun _ _ h => by cases h)
  rw [cacheStep_miss h3] at h3'
  simp only [pOf, add_eq, hs, h3', and_self]

/-- A page whose root entry is invalid in the 1 GiB slot of the latest new
level 2 table and in the 2 MiB slot of the latest new level 3 table: that
table, the tables unchanged. -/
theorem add_root_page_old {a : Alloc} {x : MapLeaf × Place} {t u : Nat}
    (h2 : a.level2 = some (x.1.gibSlot, t)) (h3 : a.level3 = some (x.1.blockSlot, u))
    (hp : x.2 = .root) (hf : x.1.form = .page) :
    pOf a x = ⟨x.1, t, true, u, true⟩ ∧ (a.add x).next = a.next ∧
      (a.add x).level2 = a.level2 ∧ (a.add x).level3 = a.level3 := by
  obtain ⟨l, p⟩ := x
  simp only at h2 h3 hp hf; subst hp
  have hs := stage2_root a l
  rw [cacheStep_hit h2] at hs
  have h3' := stage3_new a l .root hf (fun _ _ h => by cases h)
  rw [cacheStep_hit h3] at h3'
  simp only [pOf, add_eq, hs, h3', and_self]

/-- A leaf whose root entry is invalid in another 1 GiB slot than the latest
new level 2 table: as from the tables that already took the next free one for
its slot. -/
theorem add_root_miss {a : Alloc} {x : MapLeaf × Place} (h2 : ∀ t, a.level2 ≠ some (x.1.gibSlot, t))
    (hp : x.2 = .root) :
    pOf a x = pOf { a with next := a.next + 1, level2 := some (x.1.gibSlot, a.next) } x ∧
      a.add x = ({ a with next := a.next + 1, level2 := some (x.1.gibSlot, a.next) } : Alloc).add x := by
  obtain ⟨l, p⟩ := x
  simp only at h2 hp; subst hp
  have hs := stage2_root a l
  rw [cacheStep_miss h2] at hs
  have hs' := stage2_root { a with next := a.next + 1, level2 := some (l.gibSlot, a.next) } l
  rw [cacheStep_hit rfl] at hs'
  simp only [pOf, add_eq, hs, hs', and_self]

/-- A block whose level 2 entry is invalid in the level 2 table `t2` of the
set: that table, no level 3 table, the tables unchanged. -/
theorem add_level2_block {a : Alloc} {x : MapLeaf × Place} {t2 : Nat} (hp : x.2 = .level2 t2)
    (hf : x.1.form = .block) :
    pOf a x = ⟨x.1, t2, false, 0, false⟩ ∧ (a.add x).next = a.next ∧ (a.add x).level2 = a.level2 ∧
      (a.add x).level3 = a.level3 := by
  obtain ⟨l, p⟩ := x
  simp only at hp hf; subst hp
  simp only [pOf, add_eq, stage2, stage3, hf, and_self]

/-- A page whose level 2 entry is invalid in the level 2 table `t2` of the
set, in another 2 MiB slot than the latest new level 3 table: a new level 3
table, the next free one. -/
theorem add_level2_page_new {a : Alloc} {x : MapLeaf × Place} {t2 : Nat} (hp : x.2 = .level2 t2)
    (hf : x.1.form = .page) (h3 : ∀ u, a.level3 ≠ some (x.1.blockSlot, u)) :
    pOf a x = ⟨x.1, t2, false, a.next, true⟩ ∧ (a.add x).next = a.next + 1 ∧
      (a.add x).level2 = a.level2 ∧ (a.add x).level3 = some (x.1.blockSlot, a.next) := by
  obtain ⟨l, p⟩ := x
  simp only at hp hf h3; subst hp
  have h3' := stage3_new a l (.level2 t2) hf (fun _ _ h => by cases h)
  rw [cacheStep_miss h3] at h3'
  simp only [pOf, add_eq, stage2, h3', and_self]

/-- A page whose level 2 entry is invalid in the level 2 table `t2` of the
set, in the 2 MiB slot of the latest new level 3 table: that table. -/
theorem add_level2_page_old {a : Alloc} {x : MapLeaf × Place} {t2 u : Nat} (hp : x.2 = .level2 t2)
    (hf : x.1.form = .page) (h3 : a.level3 = some (x.1.blockSlot, u)) :
    pOf a x = ⟨x.1, t2, false, u, true⟩ ∧ (a.add x).next = a.next ∧
      (a.add x).level2 = a.level2 ∧ (a.add x).level3 = a.level3 := by
  obtain ⟨l, p⟩ := x
  simp only at hp hf h3; subst hp
  have h3' := stage3_new a l (.level2 t2) hf (fun _ _ h => by cases h)
  rw [cacheStep_hit h3] at h3'
  simp only [pOf, add_eq, stage2, h3', and_self]

/-- A page whose level 3 entry is invalid in the level 3 table `t3` of the
set: those tables, the tables of the map unchanged. -/
theorem add_level3 {a : Alloc} {x : MapLeaf × Place} {t2 t3 : Nat} (hp : x.2 = .level3 t2 t3)
    (hf : x.1.form = .page) :
    pOf a x = ⟨x.1, t2, false, t3, false⟩ ∧ (a.add x).next = a.next ∧ (a.add x).level2 = a.level2 ∧
      (a.add x).level3 = a.level3 := by
  obtain ⟨l, p⟩ := x
  simp only at hp hf; subst hp
  simp only [pOf, add_eq, stage2, stage3, hf, and_self]


/-! ### Runs of the tables of a 2 MiB slot -/

/-- Leaves whose tables each leave the next free table and the two caches as
they are, and whose placed leaf is `F`: their placed leaves are `F` of each,
and the tables after them are the tables before. -/
theorem plOf_steady {a : Alloc} {F : MapLeaf × Place → Placed} {Q : List (MapLeaf × Place)}
    (h : ∀ b : Alloc, b.next = a.next → b.level2 = a.level2 → b.level3 = a.level3 → ∀ z ∈ Q,
      pOf b z = F z ∧ (b.add z).next = a.next ∧ (b.add z).level2 = a.level2 ∧
        (b.add z).level3 = a.level3) :
    ∀ b : Alloc, b.next = a.next → b.level2 = a.level2 → b.level3 = a.level3 →
      plOf b Q = Q.map F ∧ (stOf b Q).next = a.next ∧ (stOf b Q).level2 = a.level2 ∧
        (stOf b Q).level3 = a.level3 := by
  induction Q with
  | nil => intro b h1 h2 h3; exact ⟨rfl, h1, h2, h3⟩
  | cons z Q ih =>
    intro b h1 h2 h3
    obtain ⟨e, e1, e2, e3⟩ := h b h1 h2 h3 z List.mem_cons_self
    obtain ⟨f, f1, f2, f3⟩ := ih (fun b' g1 g2 g3 z' hz' => h b' g1 g2 g3 z' (List.mem_cons_of_mem _ hz'))
      (b.add z) e1 e2 e3
    refine ⟨?_, f1, f2, f3⟩
    simp only [plOf, List.map_cons, e, f]

/-! ## The leaves of a map and the leaf search -/

/-- A leaf as the search of the code finds it. -/
def fOf (l : MapLeaf) : Found := ⟨l.pa.toNat, l.desc, decide (l.form = .block)⟩

/-- The first leaf of `L` that the search finds below `limit`, pages only when
`pages`. -/
def leafFirst (L : List (MapLeaf × Place)) (limit : Nat) (pages : Bool) : Option Found :=
  match L.find? (fun x => !pages || decide (x.1.form = .page)) with
  | none => none
  | some x => if x.1.pa.toNat < limit then some (fOf x.1) else none

theorem leafFirst_cons {x : MapLeaf × Place} {L : List (MapLeaf × Place)} {limit : Nat}
    {pages : Bool} (h : pages = false ∨ x.1.form = .page) :
    leafFirst (x :: L) limit pages = if x.1.pa.toNat < limit then some (fOf x.1) else none := by
  have hp : (!pages || decide (x.1.form = .page)) = true := by
    rcases h with h | h <;> simp [h]
  simp only [leafFirst, List.find?_cons, hp]

theorem leafFirst_cons_block {x : MapLeaf × Place} {L : List (MapLeaf × Place)} {limit : Nat}
    (h : x.1.form = .block) : leafFirst (x :: L) limit true = leafFirst L limit true := by
  have hp : (!true || decide (x.1.form = .page)) = false := by simp [h]
  simp only [leafFirst, List.find?_cons, hp]

theorem leafFirst_blocks {S0 L : List (MapLeaf × Place)} {limit : Nat}
    (h : ∀ y ∈ S0, y.1.form = .block) : leafFirst (S0 ++ L) limit true = leafFirst L limit true := by
  induction S0 with
  | nil => rfl
  | cons y S0 ih =>
    rw [List.cons_append, leafFirst_cons_block (h y List.mem_cons_self),
      ih (fun y' hy' => h y' (List.mem_cons_of_mem _ hy'))]

theorem leafFirst_ge {L : List (MapLeaf × Place)} {limit : Nat} {pages : Bool}
    (h : ∀ x ∈ L, limit ≤ x.1.pa.toNat) : leafFirst L limit pages = none := by
  unfold leafFirst
  split
  · rfl
  · rename_i x hx
    have := h x (List.mem_of_find?_eq_some hx)
    simp only [show ¬ x.1.pa.toNat < limit by omega, ↓reduceIte]

/-- The address `frm` splits the leaves `LP` before `L`: `L` is a suffix of
`LP`, the leaves before it end at or below `frm`, and its leaves start at or
above `frm`. -/
def SplitAt (LP : List (MapLeaf × Place)) (frm : Nat) (L : List (MapLeaf × Place)) : Prop :=
  ∃ A, LP = A ++ L ∧ (∀ x ∈ A, x.1.pa.toNat + x.1.form.size ≤ frm) ∧
    (∀ x ∈ L, frm ≤ x.1.pa.toNat)

theorem splitAt_skip {LP : List (MapLeaf × Place)} {frm frm' : Nat} {Q L : List (MapLeaf × Place)}
    (h : SplitAt LP frm (Q ++ L)) (h1 : frm ≤ frm')
    (hQ : ∀ x ∈ Q, x.1.pa.toNat + x.1.form.size ≤ frm') (hL : ∀ x ∈ L, frm' ≤ x.1.pa.toNat) :
    SplitAt LP frm' L := by
  obtain ⟨A, hA, hA1, -⟩ := h
  refine ⟨A ++ Q, by rw [hA, List.append_assoc], fun x hx => ?_, hL⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact le_trans (hA1 x hx) h1
  · exact hQ x hx

theorem splitAt_mono {LP : List (MapLeaf × Place)} {frm frm' : Nat} {L : List (MapLeaf × Place)}
    (h : SplitAt LP frm L) (h1 : frm ≤ frm') (hL : ∀ x ∈ L, frm' ≤ x.1.pa.toNat) :
    SplitAt LP frm' L :=
  splitAt_skip (Q := []) h h1 (by simp) hL

theorem splitAt_suffix {LP : List (MapLeaf × Place)} {frm : Nat} {L : List (MapLeaf × Place)}
    (h : SplitAt LP frm L) : ∃ A, LP = A ++ L := ⟨h.choose, h.choose_spec.1⟩

theorem splitAt_mem {LP : List (MapLeaf × Place)} {frm : Nat} {L : List (MapLeaf × Place)}
    (h : SplitAt LP frm L) {x : MapLeaf × Place} (hx : x ∈ L) : x ∈ LP := by
  obtain ⟨A, hA, -⟩ := h
  rw [hA]; exact List.mem_append_right _ hx

theorem splitAt_pairwise {LP : List (MapLeaf × Place)} {R : MapLeaf × Place → MapLeaf × Place → Prop}
    (hs : LP.Pairwise R) {frm : Nat} {L : List (MapLeaf × Place)} (h : SplitAt LP frm L) :
    L.Pairwise R := by
  obtain ⟨A, hA, -⟩ := h
  rw [hA] at hs
  exact (List.pairwise_append.1 hs).2.1

/-! ## What the simulation assumes of the leaves -/

/-- The places of a leaf name the tables `t2`, `t3` of the set at or below
`TT`. -/
def PlaceLe (TT : Nat) : Place → Prop
  | .root => True
  | .level2 t2 => t2 ≤ TT
  | .level3 t2 t3 => t2 ≤ TT ∧ t3 ≤ TT

/-- The leaves `LP` of a map with their places, in address order, and the
search `find` and the place `place` that the cursor reads: each leaf at the
virtual address `off` plus its physical address, `off` a multiple of
`2 ^ 39`; each leaf aligned to its size and ending at or below `2 ^ 39`; the
leaves in ascending order, apart; the leaves of one 1 GiB slot all with an
invalid root entry or none; the leaves of one 2 MiB slot with one place; no
block at level 3; `place` gives the place of each leaf; and `find`, from an
address that splits the leaves, gives the first leaf after it below the
limit, pages only when asked. -/
structure SimOk (off : Nat) (find : Nat → Nat → Bool → Option Found) (place : Found → Place)
    (LP : List (MapLeaf × Place)) : Prop where
  aligned : off % 2 ^ 39 = 0
  va : ∀ x ∈ LP, x.1.va.toNat = off + x.1.pa.toNat
  low : ∀ x ∈ LP, x.1.pa.toNat + x.1.form.size ≤ 2 ^ 39
  align : ∀ x ∈ LP, x.1.pa.toNat % x.1.form.size = 0
  sorted : LP.Pairwise (fun x y => x.1.pa.toNat + x.1.form.size ≤ y.1.pa.toNat)
  gib : ∀ x ∈ LP, ∀ y ∈ LP, x.1.gibSlot = y.1.gibSlot → (x.2 = .root ↔ y.2 = .root)
  block : ∀ x ∈ LP, ∀ y ∈ LP, x.1.blockSlot = y.1.blockSlot → x.2 = y.2
  blockPlace : ∀ x ∈ LP, x.1.form = .block → ∀ t2 t3, x.2 ≠ .level3 t2 t3
  place : ∀ x ∈ LP, place (fOf x.1) = x.2
  find : ∀ frm L, SplitAt LP frm L → ∀ limit pages, find frm limit pages = leafFirst L limit pages

section Leaves

variable {off : Nat} {find : Nat → Nat → Bool → Option Found} {place : Found → Place}
  {LP : List (MapLeaf × Place)}

theorem form_size (l : MapLeaf) :
    (l.form = .page ∧ l.form.size = 4096) ∨ (l.form = .block ∧ l.form.size = 2097152) := by
  cases l.form <;> simp [Form.size, PAGE_SIZE, BLOCK_SIZE]

/-- The numbers of a leaf, for `omega`. -/
theorem leaf_nums (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    ∃ k, off = 549755813888 * k ∧ x.1.va.toNat = off + x.1.pa.toNat ∧
      x.1.pa.toNat + x.1.form.size ≤ 549755813888 ∧ x.1.pa.toNat % x.1.form.size = 0 ∧
      x.1.gibSlot = x.1.va.toNat / 1073741824 ∧ x.1.blockSlot = x.1.va.toNat / 2097152 ∧
      ((x.1.form = .page ∧ x.1.form.size = 4096) ∨ (x.1.form = .block ∧ x.1.form.size = 2097152)) :=
  ⟨off / 549755813888, by have := H.aligned; omega, H.va x hx, H.low x hx, H.align x hx, rfl, rfl,
    form_size x.1⟩

theorem slotOf_eq_iff (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP)
    (hy : y ∈ LP) : slotOf x.1.pa.toNat = slotOf y.1.pa.toNat ↔ x.1.blockSlot = y.1.blockSlot := by
  obtain ⟨k, hk, hv, -, -, -, hb, -⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, -, -, hb', -⟩ := leaf_nums H hy
  simp only [slotOf, BLOCK_SIZE, hb, hb', hv, hv']
  omega

theorem gibOf_eq_iff (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP)
    (hy : y ∈ LP) : gibOf x.1.pa.toNat = gibOf y.1.pa.toNat ↔ x.1.gibSlot = y.1.gibSlot := by
  obtain ⟨k, hk, hv, -, -, hg, -, -⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, -, hg', -, -⟩ := leaf_nums H hy
  simp only [gibOf, GIB_SIZE, hg, hg', hv, hv']
  omega

/-- A leaf before another is in a 1 GiB and a 2 MiB slot at or below its
slots. -/
theorem slots_le (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP) (hy : y ∈ LP)
    (h : x.1.pa.toNat + x.1.form.size ≤ y.1.pa.toNat) :
    x.1.gibSlot ≤ y.1.gibSlot ∧ x.1.blockSlot ≤ y.1.blockSlot := by
  obtain ⟨k, hk, hv, -, -, hg, hb, -⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, -, hg', hb', -⟩ := leaf_nums H hy
  rw [hg, hg', hb, hb', hv, hv']
  omega

/-- A block is alone in its 2 MiB slot: a leaf after it is in a later slot. -/
theorem block_before (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP)
    (hy : y ∈ LP) (h : x.1.pa.toNat + x.1.form.size ≤ y.1.pa.toNat) (hf : x.1.form = .block) :
    x.1.blockSlot < y.1.blockSlot := by
  obtain ⟨k, hk, hv, -, hal, -, hb, hs⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, -, -, hb', -⟩ := leaf_nums H hy
  rw [hb, hb', hv, hv']
  rcases hs with ⟨h1, h2⟩ | ⟨-, h2⟩
  · rw [h1] at hf; cases hf
  · rw [h2] at h hal; omega

/-- A leaf before a block is in an earlier 2 MiB slot. -/
theorem before_block (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP)
    (hy : y ∈ LP) (h : x.1.pa.toNat + x.1.form.size ≤ y.1.pa.toNat) (hf : y.1.form = .block) :
    x.1.blockSlot < y.1.blockSlot := by
  obtain ⟨k, hk, hv, -, -, -, hb, hs⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, hal', -, hb', hs'⟩ := leaf_nums H hy
  rw [hb, hb', hv, hv']
  rcases hs' with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [h1] at hf; cases hf
  · rw [h2] at hal'; rcases hs with ⟨-, h3⟩ | ⟨-, h3⟩ <;> rw [h3] at h <;> omega

/-- The bounds of the addresses of a leaf that the cursor computes. -/
theorem leaf_low (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    x.1.pa.toNat + 4096 ≤ 2 ^ 39 ∧ slotOf x.1.pa.toNat < 2 ^ 39 ∧ gibOf x.1.pa.toNat < 2 ^ 39 ∧
      x.1.pa.toNat < 2 ^ 64 - 1 ∧ x.1.pa.toNat < slotOf x.1.pa.toNat + BLOCK_SIZE ∧
      x.1.pa.toNat < gibOf x.1.pa.toNat + GIB_SIZE ∧ slotOf x.1.pa.toNat < gibOf x.1.pa.toNat + GIB_SIZE ∧
      gibOf x.1.pa.toNat ≤ slotOf x.1.pa.toNat := by
  obtain ⟨k, hk, hv, hl, -, -, -, hs⟩ := leaf_nums H hx
  simp only [slotOf, gibOf, BLOCK_SIZE, GIB_SIZE]
  rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hl <;> omega

/-- A page ends in its 2 MiB slot; a block is its 2 MiB slot. -/
theorem leaf_end_slot (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    x.1.pa.toNat + x.1.form.size ≤ slotOf x.1.pa.toNat + BLOCK_SIZE := by
  obtain ⟨k, hk, hv, hl, hal, -, -, hs⟩ := leaf_nums H hx
  simp only [slotOf, BLOCK_SIZE]
  rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hal ⊢ <;> omega

/-- A leaf ends in its 1 GiB slot. -/
theorem leaf_end_gib (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    x.1.pa.toNat + x.1.form.size ≤ gibOf x.1.pa.toNat + GIB_SIZE := by
  obtain ⟨k, hk, hv, hl, hal, -, -, hs⟩ := leaf_nums H hx
  simp only [gibOf, GIB_SIZE]
  rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hal ⊢ <;> omega

/-- A leaf of a later 2 MiB slot starts at or above the end of the slot. -/
theorem slot_end_le (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP)
    (hy : y ∈ LP) (h : x.1.blockSlot < y.1.blockSlot) :
    slotOf x.1.pa.toNat + BLOCK_SIZE ≤ y.1.pa.toNat := by
  obtain ⟨k, hk, hv, -, -, -, hb, -⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, -, -, hb', -⟩ := leaf_nums H hy
  rw [hb, hb', hv, hv'] at h
  simp only [slotOf, BLOCK_SIZE]
  omega

/-- A leaf of a later 1 GiB slot starts at or above the end of the slot. -/
theorem gib_end_le (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP)
    (hy : y ∈ LP) (h : x.1.gibSlot < y.1.gibSlot) :
    gibOf x.1.pa.toNat + GIB_SIZE ≤ y.1.pa.toNat := by
  obtain ⟨k, hk, hv, -, -, hg, -, -⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, -, hg', -, -⟩ := leaf_nums H hy
  rw [hg, hg', hv, hv'] at h
  simp only [gibOf, GIB_SIZE]
  omega

/-- A leaf of an earlier 1 GiB slot ends at or below the start of the slot. -/
theorem end_le_gib (H : SimOk off find place LP) {x y : MapLeaf × Place} (hx : x ∈ LP)
    (hy : y ∈ LP) (h : x.1.gibSlot < y.1.gibSlot) :
    x.1.pa.toNat + x.1.form.size ≤ gibOf y.1.pa.toNat := by
  obtain ⟨k, hk, hv, -, hal, hg, -, hs⟩ := leaf_nums H hx
  obtain ⟨-, -, hv', -, -, hg', -, -⟩ := leaf_nums H hy
  rw [hg, hg', hv, hv'] at h
  simp only [gibOf, GIB_SIZE]
  rcases hs with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [h'] at hal ⊢ <;> omega

theorem gibSlot_of_blockSlot {x y : MapLeaf × Place} (h : x.1.blockSlot = y.1.blockSlot) :
    x.1.gibSlot = y.1.gibSlot := gib_of_block h

theorem index3_fOf (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    index3 (UInt64.ofNat x.1.pa.toNat) = index3 x.1.va := by
  obtain ⟨k, hk, hv, hl, -, -, -, -⟩ := leaf_nums H hx
  have h64 : x.1.pa.toNat < 2 ^ 64 := by have := (leaf_low H hx).1; omega
  simp only [index3, UInt64.toNat_ofNat_of_lt' h64, hv, PAGE_SIZE, ENTRIES]
  omega

theorem index2_fOf (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    index2 (UInt64.ofNat x.1.pa.toNat) = index2 x.1.va := by
  obtain ⟨k, hk, hv, hl, -, -, -, -⟩ := leaf_nums H hx
  have h64 : x.1.pa.toNat < 2 ^ 64 := by have := (leaf_low H hx).1; omega
  simp only [index2, UInt64.toNat_ofNat_of_lt' h64, hv, BLOCK_SIZE, ENTRIES]
  omega

theorem index2_slot (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    index2 (UInt64.ofNat (slotOf x.1.pa.toNat)) = index2 x.1.va := by
  obtain ⟨k, hk, hv, hl, -, -, -, -⟩ := leaf_nums H hx
  have h64 : slotOf x.1.pa.toNat < 2 ^ 64 := by have := (leaf_low H hx).2.1; omega
  have hd : slotOf x.1.pa.toNat / 2097152 = x.1.pa.toNat / 2097152 :=
    Nat.mul_div_cancel _ (by decide)
  simp only [index2, UInt64.toNat_ofNat_of_lt' h64, hv, BLOCK_SIZE, ENTRIES, hd]
  omega

theorem index1_gib (H : SimOk off find place LP) {x : MapLeaf × Place} (hx : x ∈ LP) :
    index1 (UInt64.ofNat (gibOf x.1.pa.toNat)) = index1 x.1.va := by
  obtain ⟨k, hk, hv, hl, -, -, -, -⟩ := leaf_nums H hx
  have h64 : gibOf x.1.pa.toNat < 2 ^ 64 := by have := (leaf_low H hx).2.2.1; omega
  have hd : gibOf x.1.pa.toNat / 1073741824 = x.1.pa.toNat / 1073741824 :=
    Nat.mul_div_cancel _ (by decide)
  simp only [index1, UInt64.toNat_ofNat_of_lt' h64, hv, GIB_SIZE, ENTRIES, hd]
  omega

/-- The first leaf after an address that splits the leaves. -/
theorem find_first (H : SimOk off find place LP) {frm limit : Nat} {pages : Bool}
    {x : MapLeaf × Place} {L : List (MapLeaf × Place)} (h : SplitAt LP frm (x :: L))
    (hp : pages = false ∨ x.1.form = .page) (hl : x.1.pa.toNat < limit) :
    find frm limit pages = some (fOf x.1) := by
  rw [H.find frm _ h, leafFirst_cons hp]
  simp only [hl, ↓reduceIte]

/-- The leaves after an address that splits the leaves and that lie at or
above the limit: none. -/
theorem find_none (H : SimOk off find place LP) {frm limit : Nat} {pages : Bool}
    {L : List (MapLeaf × Place)} (h : SplitAt LP frm L) (hl : ∀ x ∈ L, limit ≤ x.1.pa.toNat) :
    find frm limit pages = none := by
  rw [H.find frm _ h, leafFirst_ge hl]

theorem fOf_pa (l : MapLeaf) : (fOf l).pa = l.pa.toNat := rfl

theorem fOf_desc (l : MapLeaf) : (fOf l).desc = l.desc := rfl

theorem fOf_block {l : MapLeaf} (h : l.form = .block) : (fOf l).block = true := by
  simp [fOf, h]

theorem fOf_page {l : MapLeaf} (h : l.form = .page) : (fOf l).block = false := by
  simp [fOf, h]

end Leaves


/-! ## Lists in runs and in order -/

/-- A list is a first run of items that satisfy `p`, then a rest whose head
does not. -/
theorem split_run {α : Type} (p : α → Bool) : ∀ L : List α,
    ∃ Q L', L = Q ++ L' ∧ (∀ y ∈ Q, p y = true) ∧ (∀ y ∈ L'.head?, p y = false)
  | [] => ⟨[], [], rfl, by simp, by simp⟩
  | y :: L => by
    by_cases h : p y = true
    · obtain ⟨Q, L', hL, hQ, hL'⟩ := split_run p L
      refine ⟨y :: Q, L', by rw [hL]; rfl, ?_, hL'⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h
      · exact hQ z hz
    · exact ⟨[], y :: L, rfl, by simp, by simpa using h⟩

/-- In a list in ascending order of a key, the items after a run of the key
of its head whose next item has another key have a larger key. -/
theorem after_run {α : Type} (key : α → Nat) {y : α} {Q R : List α}
    (hs : (y :: (Q ++ R)).Pairwise (fun a b => key a ≤ key b))
    (hR : ∀ z ∈ R.head?, key z ≠ key y) : ∀ z ∈ R, key y < key z := by
  cases R with
  | nil => simp
  | cons h R =>
    have hyh : key y ≤ key h := List.rel_of_pairwise_cons hs (by simp)
    have hne : key h ≠ key y := hR h rfl
    have hs' : (h :: R).Pairwise (fun a b => key a ≤ key b) :=
      (List.pairwise_append.1 (List.pairwise_cons.1 hs).2).2.1
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · omega
    · have := List.rel_of_pairwise_cons hs' hz
      omega

/-! ## The simulation -/

/-- What the cursor of the code needs at each call, on numbers: a next free
table at or below `NX`, tables at or below `TT`, and the slots that the phase
reads below `2 ^ 39`. -/
def CurBound (NX TT : Nat) (c : Cur) : Prop :=
  c.next ≤ NX ∧ c.t2 ≤ TT ∧ c.t3 ≤ TT ∧ (c.phase = .newPages ∨ c.phase = .newTable → c.slot < 2 ^ 39) ∧
    (c.phase = .children ∨ c.phase = .entries ∨ c.phase = .root → c.gib < 2 ^ 39)

/-- What the simulation guarantees at each call: `CurBound`, and an address
of the cursor that splits the leaves `LP`. -/
def CurOk (LP : List (MapLeaf × Place)) (NX TT : Nat) (c : Cur) : Prop :=
  CurBound NX TT c ∧ ∃ L, SplitAt LP c.frm L

/-- The cursor `c` at the first leaf of a 2 MiB slot, the leaves `L` left,
the tables `a` of the leaves before them: the address of the cursor splits the
leaves before `L`; the phase `leaf`, or `heldPages` in another 2 MiB slot than
the first leaf left; the next free table that of `a`; the caches of `a` of
slots before every leaf left; the record `used` at or below the next free
table, and the tables after the leaves left at or below `NX`; the tables of
the cursor at or below `TT`. -/
structure Bnd (LP : List (MapLeaf × Place)) (used NX TT : Nat) (c : Cur) (a : Alloc)
    (L : List (MapLeaf × Place)) : Prop where
  split : SplitAt LP c.frm L
  phase : c.phase = .leaf ∨ (c.phase = .heldPages ∧ ∀ x ∈ L.head?, slotOf x.1.pa.toNat ≠ c.slot)
  next : c.next = a.next
  fresh2 : ∀ g t, a.level2 = some (g, t) → ∀ x ∈ L, g < x.1.gibSlot
  fresh3 : ∀ b t, a.level3 = some (b, t) → ∀ x ∈ L, b < x.1.blockSlot
  used : used ≤ a.next
  nx : (stOf a L).next ≤ NX
  t2 : c.t2 ≤ TT
  t3 : c.t3 ≤ TT

section Sim

variable {off : Nat} {find : Nat → Nat → Bool → Option Found} {place : Found → Place}
  {LP : List (MapLeaf × Place)} {base : UInt64} {used NX TT : Nat}

theorem bnd_bound {c : Cur} {a : Alloc} {L : List (MapLeaf × Place)} (hb : Bnd LP used NX TT c a L) :
    CurBound NX TT c := by
  refine ⟨?_, hb.t2, hb.t3, ?_, ?_⟩
  · rw [hb.next]; exact le_trans (next_le_stOf L a) hb.nx
  · rcases hb.phase with h | ⟨h, -⟩ <;> simp [h]
  · rcases hb.phase with h | ⟨h, -⟩ <;> simp [h]

theorem bnd_ok {c : Cur} {a : Alloc} {L : List (MapLeaf × Place)} (hb : Bnd LP used NX TT c a L) :
    CurOk LP NX TT c :=
  ⟨bnd_bound hb, L, hb.split⟩

/-- The leaves of a suffix of the leaves are in ascending order of their
slots. -/
theorem sorted_slots (H : SimOk off find place LP) {frm : Nat} {L : List (MapLeaf × Place)}
    (h : SplitAt LP frm L) :
    L.Pairwise (fun a b => a.1.gibSlot ≤ b.1.gibSlot ∧ a.1.blockSlot ≤ b.1.blockSlot) :=
  List.Pairwise.imp_of_mem (fun ha hb hab => slots_le H (splitAt_mem h ha) (splitAt_mem h hb) hab)
    (splitAt_pairwise H.sorted h)

theorem splitAt_after (H : SimOk off find place LP) {frm : Nat} {z : MapLeaf × Place}
    {L : List (MapLeaf × Place)} (h : SplitAt LP frm (z :: L)) :
    ∀ y ∈ L, z.1.pa.toNat + z.1.form.size ≤ y.1.pa.toNat :=
  fun _ hy => List.rel_of_pairwise_cons (splitAt_pairwise H.sorted h) hy

theorem splitAt_next {frm frm' : Nat} {z : MapLeaf × Place}
    {L : List (MapLeaf × Place)} (h : SplitAt LP frm (z :: L))
    (h1 : z.1.pa.toNat + z.1.form.size ≤ frm') (h2 : ∀ y ∈ L, frm' ≤ y.1.pa.toNat) :
    SplitAt LP frm' L := by
  have hz : frm ≤ z.1.pa.toNat := h.choose_spec.2.2 z List.mem_cons_self
  exact splitAt_skip (Q := [z]) h (by omega) (by simpa using h1) h2

theorem splitAt_next_page (H : SimOk off find place LP) {frm : Nat} {z : MapLeaf × Place}
    {L : List (MapLeaf × Place)} (h : SplitAt LP frm (z :: L)) (hp : z.1.form = .page) :
    SplitAt LP (z.1.pa.toNat + PAGE_SIZE) L := by
  have hs : z.1.form.size = PAGE_SIZE := by rw [hp]; rfl
  exact splitAt_next h (by rw [hs])
    (fun y hy => by have := splitAt_after H h y hy; rw [hs] at this; exact this)

/-- At the first leaf of a 2 MiB slot, the call is the call in `leaf`, and
the search finds the first leaf left. -/
theorem bnd_first (H : SimOk off find place LP) {c : Cur} {a : Alloc} {x : MapLeaf × Place}
    {L : List (MapLeaf × Place)} (hb : Bnd LP used NX TT c a (x :: L)) :
    Cur.step find place base c = Cur.step find place base { c with phase := .leaf } ∧
      find c.frm (2 ^ 64 - 1) false = some (fOf x.1) := by
  have hx : x ∈ LP := splitAt_mem hb.split List.mem_cons_self
  have hf := find_first H hb.split (Or.inl rfl) (leaf_low H hx).2.2.2.1
  refine ⟨?_, hf⟩
  rcases hb.phase with h | ⟨h, hs⟩
  · obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
    simp only at h; subst h; rfl
  · refine step_held_leaf find place base h (fun f hf' => ?_)
    rw [hf] at hf'; cases hf'
    exact hs x rfl

/-- The steps of a run of pages of one 2 MiB slot, one call each, for a phase
whose call stores the page that its search finds into `t3`. -/
theorem pages_loop (H : SimOk off find place LP) {c : Cur} {L' : List (MapLeaf × Place)}
    {good : MapLeaf × Place → Prop} (hP : ∀ f, CurBound NX TT { c with frm := f })
    (hst : ∀ (f : Nat) (z : MapLeaf × Place) (Q3 : List (MapLeaf × Place)), good z →
      z.1.form = .page → SplitAt LP f (z :: (Q3 ++ L')) →
      Cur.step find place base { c with frm := f } =
        (some (.store c.t3 (index3 (UInt64.ofNat z.1.pa.toNat)) z.1.desc),
          { c with frm := z.1.pa.toNat + PAGE_SIZE })) :
    ∀ (Q : List (MapLeaf × Place)) (f : Nat), (∀ z ∈ Q, good z ∧ z.1.form = .page) →
      SplitAt LP f (Q ++ L') →
      ∃ f', CurSteps (Cur.step find place base) (CurOk LP NX TT) { c with frm := f }
        (Q.map (fun z => .store c.t3 (index3 (UInt64.ofNat z.1.pa.toNat)) z.1.desc))
        { c with frm := f' } ∧ SplitAt LP f' L'
  | [], f, _, h => ⟨f, rfl, h⟩
  | z :: Q, f, hQ, h => by
    obtain ⟨hg, hp⟩ := hQ z List.mem_cons_self
    have h1 := hst f z Q hg hp h
    have h2 : SplitAt LP (z.1.pa.toNat + PAGE_SIZE) (Q ++ L') :=
      splitAt_next_page H h hp
    obtain ⟨f', hs, hsp⟩ := pages_loop H hP hst Q _
      (fun z' hz' => hQ z' (List.mem_cons_of_mem _ hz')) h2
    exact ⟨f', curSteps_cons ⟨hP f, _, h⟩ h1 hs, hsp⟩

/-- The steps of the pages of a run, from their placed leaves. -/
theorem map_store_pages (H : SimOk off find place LP) {Q : List (MapLeaf × Place)}
    {F : MapLeaf × Place → Placed} {t3 : Nat} (hQ : ∀ z ∈ Q, z ∈ LP ∧ z.1.form = .page)
    (hF : ∀ z ∈ Q, (F z).leaf = z.1 ∧ (F z).t3 = t3) :
    (Q.map F).map Placed.store =
      Q.map (fun z => .store t3 (index3 (UInt64.ofNat z.1.pa.toNat)) z.1.desc) := by
  rw [List.map_map]
  refine List.map_congr_left (fun z hz => ?_)
  obtain ⟨hl, ht⟩ := hF z hz
  obtain ⟨hzl, hp⟩ := hQ z hz
  simp only [Function.comp, Placed.store, hl, ht, hp, index3_fOf H hzl]

/-! ### A 2 MiB slot under a level 2 table of the set -/

theorem seg_held_block (H : SimOk off find place LP) (hTT : ∀ x ∈ LP, PlaceLe TT x.2) {c : Cur}
    {a : Alloc} {x : MapLeaf × Place} {L' : List (MapLeaf × Place)} {t2 : Nat}
    (hb : Bnd LP used NX TT c a (x :: L')) (hf : x.1.form = .block) (hp : x.2 = .level2 t2) :
    ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c (heldLevel2Steps base (plOf a [x])) c' ∧
      Bnd LP used NX TT c' (stOf a [x]) L' := by
  have hx : x ∈ LP := splitAt_mem hb.split List.mem_cons_self
  obtain ⟨hst, hfind⟩ := bnd_first (base := base) H hb
  obtain ⟨e, e1, e2, e3⟩ := add_level2_block (a := a) hp hf
  have hpl : place (fOf x.1) = .level2 t2 := by rw [H.place x hx, hp]
  have h1 := step_leaf_level2_block find place base (c := { c with phase := .leaf }) rfl hfind hpl
    (fOf_block hf)
  have hplan : heldLevel2Steps base (plOf a [x]) =
      [.store t2 (index2 (UInt64.ofNat x.1.pa.toNat)) x.1.desc] := by
    simp only [plOf, e, heldLevel2Steps, hf, List.map_cons, List.map_nil, Placed.store,
      index2_fOf H hx]
  have hafter := splitAt_after H hb.split
  have hsize : x.1.form.size = BLOCK_SIZE := by rw [hf]; rfl
  refine ⟨_, by rw [hplan]; exact curSteps_cons (bnd_ok hb) (hst.trans h1) (curSteps_nil _), ?_⟩
  refine ⟨splitAt_next hb.split (by rw [hsize]; exact le_refl _)
      (fun y hy => by have := hafter y hy; rw [hsize] at this; exact this), Or.inl rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, hb.t3⟩
  · show c.next = (a.add x).next
    rw [e1, hb.next]
  · intro g t hg y hy
    rw [stOf_cons, stOf_nil, e2] at hg
    exact lt_of_lt_of_le (hb.fresh2 g t hg x List.mem_cons_self)
      (slots_le H hx (splitAt_mem hb.split (List.mem_cons_of_mem _ hy)) (hafter y hy)).1
  · intro g t hg y hy
    rw [stOf_cons, stOf_nil, e3] at hg
    exact lt_of_lt_of_le (hb.fresh3 g t hg x List.mem_cons_self)
      (slots_le H hx (splitAt_mem hb.split (List.mem_cons_of_mem _ hy)) (hafter y hy)).2
  · show used ≤ (a.add x).next
    rw [e1]; exact hb.used
  · rw [← stOf_append]; exact hb.nx
  · have := hTT x hx; rw [hp] at this; exact this

theorem seg_held_l3 (H : SimOk off find place LP) (hTT : ∀ x ∈ LP, PlaceLe TT x.2) {c : Cur}
    {a : Alloc} {y : MapLeaf × Place} {Q' L' : List (MapLeaf × Place)} {t2 t3 : Nat}
    (hb : Bnd LP used NX TT c a ((y :: Q') ++ L'))
    (hQ : ∀ z ∈ y :: Q', z.2 = .level3 t2 t3 ∧ z.1.form = .page ∧ z.1.blockSlot = y.1.blockSlot)
    (hL' : ∀ z ∈ L', y.1.blockSlot < z.1.blockSlot) :
    ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c
      (heldLevel2Steps base (plOf a (y :: Q'))) c' ∧ Bnd LP used NX TT c' (stOf a (y :: Q')) L' := by
  have hy : y ∈ LP := splitAt_mem hb.split List.mem_cons_self
  have hmem : ∀ z ∈ (y :: Q') ++ L', z ∈ LP := fun z hz => splitAt_mem hb.split hz
  obtain ⟨hst, hfind⟩ := bnd_first (base := base) H hb
  obtain ⟨hy2, hyp, -⟩ := hQ y List.mem_cons_self
  obtain ⟨e, e1, e2, e3⟩ := plOf_steady (a := a) (Q := y :: Q')
    (F := fun z => ⟨z.1, t2, false, t3, false⟩)
    (fun b h1 h2 h3 z hz => by
      obtain ⟨f, f1, f2, f3⟩ := add_level3 (a := b) (hQ z hz).1 (hQ z hz).2.1
      exact ⟨f, f1.trans h1, f2.trans h2, f3.trans h3⟩) a rfl rfl rfl
  have hpl : place (fOf y.1) = .level3 t2 t3 := by rw [H.place y hy, hy2]
  have h1 := step_leaf_level3 find place base (c := { c with phase := .leaf }) rfl hfind hpl
  have hQmem : ∀ z ∈ y :: Q', z ∈ LP ∧ z.1.form = .page :=
    fun z hz => ⟨hmem z (List.mem_append_left _ hz), (hQ z hz).2.1⟩
  have hplan : heldLevel2Steps base (plOf a (y :: Q')) =
      (y :: Q').map (fun z => .store t3 (index3 (UInt64.ofNat z.1.pa.toNat)) z.1.desc) := by
    rw [e, ← map_store_pages (F := fun z => ⟨z.1, t2, false, t3, false⟩) (t3 := t3) H hQmem
      (fun z _ => ⟨rfl, rfl⟩)]
    simp only [List.map_cons, heldLevel2Steps, hyp, Bool.false_eq_true, ↓reduceIte]
  let c1 : Cur := ⟨.heldPages, y.1.pa.toNat + PAGE_SIZE, c.next, gibOf y.1.pa.toNat,
    slotOf y.1.pa.toNat, t2, t3⟩
  have hsplit1 : SplitAt LP (y.1.pa.toNat + PAGE_SIZE) (Q' ++ L') :=
    splitAt_next_page H hb.split hyp
  have hbd : ∀ f, CurBound NX TT { c1 with frm := f } := by
    intro f
    have := bnd_bound hb
    have ht := hTT y hy; rw [hy2] at ht
    exact ⟨this.1, ht.1, ht.2, by simp [c1], by simp [c1]⟩
  obtain ⟨f', hloop, hsp⟩ := pages_loop (base := base) H (c := c1) (L' := L')
    (good := fun z => z ∈ LP ∧ slotOf z.1.pa.toNat = slotOf y.1.pa.toNat) hbd
    (fun f z Q3 hg hp hs => step_held_same find place base rfl
      (find_first H hs (Or.inl rfl) (leaf_low H hg.1).2.2.2.1) hg.2)
    Q' _ (fun z hz => ⟨⟨hmem z (List.mem_append_left _ (List.mem_cons_of_mem _ hz)),
      (slotOf_eq_iff H (hmem z (List.mem_append_left _ (List.mem_cons_of_mem _ hz))) hy).2
        (hQ z (List.mem_cons_of_mem _ hz)).2.2⟩, (hQ z (List.mem_cons_of_mem _ hz)).2.1⟩) hsplit1
  refine ⟨_, by rw [hplan, List.map_cons]; exact curSteps_cons (bnd_ok hb) (hst.trans h1) hloop, ?_⟩
  have hafter := splitAt_after H hb.split
  refine ⟨hsp, Or.inr ⟨rfl, fun z hz => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hz : z ∈ L' := List.mem_of_mem_head? hz
    intro he
    have := (slotOf_eq_iff H (hmem z (List.mem_append_right _ hz)) hy).1 he
    have := hL' z hz
    omega
  · show c.next = (stOf a (y :: Q')).next
    rw [e1, hb.next]
  · intro g t hg z hz
    rw [e2] at hg
    exact lt_of_lt_of_le (hb.fresh2 g t hg y List.mem_cons_self)
      (slots_le H hy (hmem z (List.mem_append_right _ hz))
        (hafter z (List.mem_append_right _ hz))).1
  · intro g t hg z hz
    rw [e3] at hg
    exact lt_of_lt_of_le (hb.fresh3 g t hg y List.mem_cons_self)
      (slots_le H hy (hmem z (List.mem_append_right _ hz))
        (hafter z (List.mem_append_right _ hz))).2
  · rw [e1]; exact hb.used
  · rw [← stOf_append]; exact hb.nx
  · have ht := hTT y hy; rw [hy2] at ht; exact ht.1
  · have ht := hTT y hy; rw [hy2] at ht; exact ht.2


/-- A new table at the tables `a` before the leaves left: below `TT`. -/
theorem new_lt_TT (hnew : used < NX → NX ≤ TT) {a : Alloc} (hu : used ≤ a.next)
    (h : a.next + 1 ≤ NX) : a.next < TT := by
  have := hnew (by omega)
  omega

theorem seg_held_l2 (H : SimOk off find place LP) (hTT : ∀ x ∈ LP, PlaceLe TT x.2)
    (hnew : used < NX → NX ≤ TT) {c : Cur} {a : Alloc} {y : MapLeaf × Place}
    {Q' L' : List (MapLeaf × Place)} {t2 : Nat} (hb : Bnd LP used NX TT c a ((y :: Q') ++ L'))
    (hQ : ∀ z ∈ y :: Q', z.2 = .level2 t2 ∧ z.1.form = .page ∧ z.1.blockSlot = y.1.blockSlot)
    (hL' : ∀ z ∈ L', y.1.blockSlot < z.1.blockSlot) :
    ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c
      (heldLevel2Steps base (plOf a (y :: Q'))) c' ∧ Bnd LP used NX TT c' (stOf a (y :: Q')) L' := by
  have hy : y ∈ LP := splitAt_mem hb.split List.mem_cons_self
  have hmem : ∀ z ∈ (y :: Q') ++ L', z ∈ LP := fun z hz => splitAt_mem hb.split hz
  obtain ⟨hst, hfind⟩ := bnd_first (base := base) H hb
  obtain ⟨hy2, hyp, -⟩ := hQ y List.mem_cons_self
  have hmiss : ∀ u, a.level3 ≠ some (y.1.blockSlot, u) := fun u h => by
    have := hb.fresh3 _ u h y List.mem_cons_self; omega
  obtain ⟨e, e1, e2, e3⟩ := add_level2_page_new (a := a) hy2 hyp hmiss
  obtain ⟨f, f1, f2, f3⟩ := plOf_steady (a := a.add y) (Q := Q')
    (F := fun z => ⟨z.1, t2, false, a.next, true⟩)
    (fun b h1 h2 h3 z hz => by
      have hz' := hQ z (List.mem_cons_of_mem _ hz)
      obtain ⟨g, g1, g2, g3⟩ := add_level2_page_old (a := b) (u := a.next) hz'.1 hz'.2.1
        (by rw [h3, e3, hz'.2.2])
      exact ⟨g, g1.trans h1, g2.trans h2, g3.trans h3⟩) (a.add y) rfl rfl rfl
  have hQmem : ∀ z ∈ y :: Q', z ∈ LP ∧ z.1.form = .page :=
    fun z hz => ⟨hmem z (List.mem_append_left _ hz), (hQ z hz).2.1⟩
  have hm := map_store_pages (F := fun z => (⟨z.1, t2, false, a.next, true⟩ : Placed))
    (t3 := a.next) H hQmem (fun z _ => ⟨rfl, rfl⟩)
  have hplan : heldLevel2Steps base (plOf a (y :: Q')) =
      .zero a.next :: ((y :: Q').map (fun z => .store a.next (index3 (UInt64.ofNat z.1.pa.toNat)) z.1.desc) ++
        [.fence, .store t2 (index2 (UInt64.ofNat (slotOf y.1.pa.toNat))) (tableAt base a.next)]) := by
    rw [← hm, index2_slot H hy]
    simp only [plOf, e, f, List.map_cons, heldLevel2Steps, hyp, ↓reduceIte, level2Entry]
    rfl
  have hnx : (stOf a (y :: Q')).next ≤ NX :=
    le_trans (next_le_stOf L' _) (by rw [← stOf_append]; exact hb.nx)
  have hnn : (stOf a (y :: Q')).next = a.next + 1 := by
    show (stOf (a.add y) Q').next = a.next + 1
    rw [f1, e1]
  have hlt : a.next < TT := new_lt_TT hnew hb.used (by omega)
  have hcn : c.next = a.next := hb.next
  have hpl : place (fOf y.1) = .level2 t2 := by rw [H.place y hy, hy2]
  have h1 := step_leaf_level2_page find place base (c := { c with phase := .leaf }) rfl hfind hpl
    (fOf_page hyp)
  let c1 : Cur := ⟨.newPages, y.1.pa.toNat, c.next + 1, gibOf y.1.pa.toNat, slotOf y.1.pa.toNat, t2,
    c.next⟩
  have ht2 : t2 ≤ TT := by have := hTT y hy; rw [hy2] at this; exact this
  have hslot : slotOf y.1.pa.toNat < 2 ^ 39 := (leaf_low H hy).2.1
  have hbd : ∀ f, CurBound NX TT { c1 with frm := f } := by
    intro f
    refine ⟨by simp only [c1]; omega, ht2, by simp only [c1]; omega, fun _ => hslot, ?_⟩
    simp [c1]
  have hsplit0 : SplitAt LP y.1.pa.toNat ((y :: Q') ++ L') :=
    splitAt_mono hb.split (hb.split.choose_spec.2.2 y List.mem_cons_self)
      (fun z hz => by
        rcases List.mem_cons.1 hz with rfl | hz
        · exact le_refl _
        · have := splitAt_after H hb.split z hz; omega)
  obtain ⟨f', hloop, hsp⟩ := pages_loop (base := base) H (c := c1) (L' := L')
    (good := fun z => z ∈ LP ∧ slotOf z.1.pa.toNat = slotOf y.1.pa.toNat) hbd
    (fun f z Q3 hg hp hs => step_newPages_some find place base rfl
      (find_first H hs (Or.inl rfl) (by
        have := (leaf_low H hg.1).2.2.2.2.1; rw [hg.2] at this; exact this)))
    (y :: Q') _ (fun z hz => ⟨⟨(hQmem z hz).1, (slotOf_eq_iff H (hQmem z hz).1 hy).2 (hQ z hz).2.2⟩,
      (hQ z hz).2.1⟩) hsplit0
  have hn := step_newPages_none find place base (c := { c1 with frm := f' }) rfl
    (find_none H hsp (fun z hz => slot_end_le H hy (hmem z (List.mem_append_right _ hz)) (hL' z hz)))
  have hnt := step_newTable find place base (c := { { c1 with frm := f' } with phase := .newTable }) rfl
  refine ⟨⟨.leaf, slotOf y.1.pa.toNat + BLOCK_SIZE, c.next + 1, gibOf y.1.pa.toNat,
      slotOf y.1.pa.toNat, t2, c.next⟩, ?_, ?_⟩
  · rw [hplan, ← hb.next]
    refine curSteps_cons (bnd_ok hb) (hst.trans h1) (curSteps_append ?_ hloop)
    refine curSteps_cons ⟨hbd f', _, hsp⟩ hn
      (curSteps_cons ⟨⟨?_, ht2, ?_, fun _ => hslot, by simp⟩, _, hsp⟩ hnt (curSteps_nil _))
    · show c.next + 1 ≤ NX; omega
    · show c.next ≤ TT; omega
  · have hafter := splitAt_after H hb.split
    refine ⟨splitAt_skip (Q := y :: Q') hb.split ?_ ?_ ?_, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ht2, ?_⟩
    · have h0 := hb.split.choose_spec.2.2 y List.mem_cons_self
      have := (leaf_low H hy).2.2.2.2.1
      show c.frm ≤ slotOf y.1.pa.toNat + BLOCK_SIZE; omega
    · intro z hz
      have := leaf_end_slot H (hQmem z hz).1
      rw [(slotOf_eq_iff H (hQmem z hz).1 hy).2 (hQ z hz).2.2] at this
      exact this
    · exact fun z hz => slot_end_le H hy (hmem z (List.mem_append_right _ hz)) (hL' z hz)
    · show c.next + 1 = (stOf a (y :: Q')).next
      rw [hnn, hb.next]
    · intro g t hg z hz
      rw [show (stOf a (y :: Q')).level2 = a.level2 from f2.trans e2] at hg
      exact lt_of_lt_of_le (hb.fresh2 g t hg y List.mem_cons_self)
        (slots_le H hy (hmem z (List.mem_append_right _ hz))
          (hafter z (List.mem_append_right _ hz))).1
    · intro g t hg z hz
      rw [show (stOf a (y :: Q')).level3 = (a.add y).level3 from f3, e3] at hg
      cases hg
      exact hL' z hz
    · rw [hnn]; have := hb.used; omega
    · rw [← stOf_append]; exact hb.nx
    · show c.next ≤ TT; rw [hb.next]; omega

/-- The leaves of a list after a leaf in it. -/
theorem mem_plOf {q : Placed} : ∀ {L : List (MapLeaf × Place)} {b : Alloc}, q ∈ plOf b L →
    ∃ z ∈ L, q.leaf = z.1
  | [], b, h => by simp [plOf] at h
  | x :: L, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨x, List.mem_cons_self, rfl⟩
    · obtain ⟨z, hz, he⟩ := mem_plOf h
      exact ⟨z, List.mem_cons_of_mem _ hz, he⟩

theorem head_plOf {q : Placed} {L : List (MapLeaf × Place)} {b : Alloc} (h : q ∈ (plOf b L).head?) :
    ∃ z ∈ L.head?, q.leaf = z.1 := by
  cases L with
  | nil => simp [plOf] at h
  | cons x L =>
    simp only [plOf, List.head?_cons, Option.mem_def, Option.some.injEq] at h
    subst h
    exact ⟨x, rfl, rfl⟩

/-- The runs of the placed leaves of a run of one key followed by leaves of
another key. -/
theorem runsBy_plOf (key : MapLeaf → Nat) {a : Alloc} {y : MapLeaf × Place}
    {Q R : List (MapLeaf × Place)} (hQ : ∀ z ∈ Q, key z.1 = key y.1)
    (hR : ∀ z ∈ R.head?, key z.1 ≠ key y.1) :
    runsBy (fun q => key q.leaf) (plOf a ((y :: Q) ++ R)) =
      plOf a (y :: Q) :: runsBy (fun q => key q.leaf) (plOf (stOf a (y :: Q)) R) := by
  rw [plOf_append]
  show runsBy _ ((pOf a y :: plOf (a.add y) Q) ++ _) = _
  rw [runsBy_append_run (fun q : Placed => key q.leaf) _ (pOf a y) (plOf (a.add y) Q)]
  · rfl
  · intro q hq
    obtain ⟨z, hz, he⟩ := mem_plOf hq
    rw [he]; exact hQ z hz
  · intro q hq
    obtain ⟨z, hz, he⟩ := head_plOf hq
    rw [he]; exact hR z hz

/-- One 2 MiB slot under a level 2 table of the set. -/
theorem seg_held (H : SimOk off find place LP) (hTT : ∀ x ∈ LP, PlaceLe TT x.2)
    (hnew : used < NX → NX ≤ TT) {c : Cur} {a : Alloc} {y : MapLeaf × Place}
    {Q' L' : List (MapLeaf × Place)} (hb : Bnd LP used NX TT c a ((y :: Q') ++ L'))
    (hroot : y.2 ≠ .root) (hQ : ∀ z ∈ Q', z.1.blockSlot = y.1.blockSlot)
    (hL' : ∀ z ∈ L', y.1.blockSlot < z.1.blockSlot) :
    ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c
      (heldLevel2Steps base (plOf a (y :: Q'))) c' ∧ Bnd LP used NX TT c' (stOf a (y :: Q')) L' := by
  have hy : y ∈ LP := splitAt_mem hb.split List.mem_cons_self
  have hmem : ∀ z ∈ Q', z ∈ LP := fun z hz =>
    splitAt_mem hb.split (List.mem_append_left _ (List.mem_cons_of_mem _ hz))
  have hafter : ∀ z ∈ Q', y.1.pa.toNat + y.1.form.size ≤ z.1.pa.toNat :=
    fun z hz => splitAt_after H hb.split z (List.mem_append_left _ hz)
  have hall : ∀ z ∈ y :: Q', z.2 = y.2 ∧ z.1.blockSlot = y.1.blockSlot := by
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨rfl, rfl⟩
    · exact ⟨H.block z (hmem z hz) y hy (hQ z hz), hQ z hz⟩
  cases hf : y.1.form with
  | block =>
    cases Q' with
    | cons z Q'' =>
      have := block_before H hy (hmem z List.mem_cons_self) (hafter z List.mem_cons_self) hf
      rw [hQ z List.mem_cons_self] at this; omega
    | nil =>
      cases hp : y.2 with
      | root => exact absurd hp hroot
      | level2 t2 => exact seg_held_block H hTT hb hf hp
      | level3 t2 t3 => exact absurd hp (H.blockPlace y hy hf t2 t3)
  | page =>
    have hpages : ∀ z ∈ y :: Q', z.1.form = .page := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hf
      · cases hzf : z.1.form with
        | page => rfl
        | block =>
          have := before_block H hy (hmem z hz) (hafter z hz) hzf
          rw [hQ z hz] at this; omega
    cases hp : y.2 with
    | root => exact absurd hp hroot
    | level2 t2 =>
      exact seg_held_l2 H hTT hnew hb (fun z hz => ⟨(hall z hz).1.trans hp, hpages z hz, (hall z hz).2⟩) hL'
    | level3 t2 t3 =>
      exact seg_held_l3 H hTT hb (fun z hz => ⟨(hall z hz).1.trans hp, hpages z hz, (hall z hz).2⟩) hL'

/-- The 2 MiB slots of a 1 GiB slot under a level 2 table of the set. -/
theorem held_run (H : SimOk off find place LP) (hTT : ∀ x ∈ LP, PlaceLe TT x.2)
    (hnew : used < NX → NX ≤ TT) {L'' : List (MapLeaf × Place)} :
    ∀ (n : Nat) (R : List (MapLeaf × Place)) (c : Cur) (a : Alloc), R.length ≤ n →
      (∀ z ∈ R, z.2 ≠ .root) → (∀ z ∈ R, ∀ w ∈ L'', z.1.gibSlot < w.1.gibSlot) →
      Bnd LP used NX TT c a (R ++ L'') →
      ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c
        ((runsBy (·.leaf.blockSlot) (plOf a R)).flatMap (heldLevel2Steps base)) c' ∧
        Bnd LP used NX TT c' (stOf a R) L''
  | _, [], c, a, _, _, _, hb => ⟨c, rfl, hb⟩
  | 0, _ :: _, _, _, hn, _, _, _ => absurd hn (by simp)
  | n + 1, y :: R', c, a, hn, hroot, hgib, hb => by
    obtain ⟨Q', R3, hR', hQ', hR3⟩ := split_run (fun z => z.1.blockSlot == y.1.blockSlot) R'
    subst hR'
    have hQbs : ∀ z ∈ Q', z.1.blockSlot = y.1.blockSlot := fun z hz => by simpa using hQ' z hz
    have hy : y ∈ y :: (Q' ++ R3) := List.mem_cons_self
    have hsorted := sorted_slots H hb.split
    have hafter : ∀ z ∈ R3 ++ L'', y.1.blockSlot < z.1.blockSlot := by
      refine after_run (fun z : MapLeaf × Place => z.1.blockSlot) (Q := Q') ?_ ?_
      · have := hsorted.imp (fun h => h.2)
        simpa only [List.cons_append, List.append_assoc] using this
      · intro z hz
        cases R3 with
        | cons r R3' =>
          simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz
          simpa using hR3 r rfl
        | nil =>
          simp only [List.nil_append] at hz
          have hz' := List.mem_of_mem_head? hz
          intro he
          have := hgib y hy z hz'
          rw [gibSlot_of_blockSlot he] at this
          omega
    have hb' : Bnd LP used NX TT c a ((y :: Q') ++ (R3 ++ L'')) := by
      simpa only [List.cons_append, List.append_assoc] using hb
    obtain ⟨c1, hs1, hb1⟩ := seg_held (base := base) H hTT hnew hb' (hroot y hy) hQbs hafter
    have hb1' : Bnd LP used NX TT c1 (stOf a (y :: Q')) (R3 ++ L'') := hb1
    obtain ⟨c', hs2, hb2⟩ := held_run H hTT hnew n R3 c1 (stOf a (y :: Q'))
      (by simp only [List.length_cons, List.length_append] at hn; omega)
      (fun z hz => hroot z (List.mem_cons_of_mem _ (List.mem_append_right _ hz)))
      (fun z hz => hgib z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))) hb1'
    refine ⟨c', ?_, ?_⟩
    · have hrun := runsBy_plOf (fun l : MapLeaf => l.blockSlot) (a := a) (y := y) (Q := Q') (R := R3)
        hQbs (fun z hz he => by
          cases R3 with
          | nil => simp at hz
          | cons r R3' =>
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
            subst hz
            simp [he] at hR3)
      rw [show y :: (Q' ++ R3) = (y :: Q') ++ R3 from rfl, hrun, List.flatMap_cons]
      exact curSteps_append hs2 hs1
    · rw [show y :: (Q' ++ R3) = (y :: Q') ++ R3 from rfl, stOf_append]; exact hb2


/-! ### A 1 GiB slot under a new level 2 table -/

/-- The pages of one 2 MiB slot under the new level 2 table `n0` of their
1 GiB slot `g`, in another 2 MiB slot than the latest new level 3 table:
each in the next free table. -/
theorem plOf_root_pages {a : Alloc} {y : MapLeaf × Place} {Q' : List (MapLeaf × Place)} {g n0 : Nat}
    (h2 : a.level2 = some (g, n0)) (hmiss : ∀ u, a.level3 ≠ some (y.1.blockSlot, u))
    (hQ : ∀ z ∈ y :: Q', z.2 = .root ∧ z.1.form = .page ∧ z.1.gibSlot = g ∧
      z.1.blockSlot = y.1.blockSlot) :
    plOf a (y :: Q') = (y :: Q').map (fun z => ⟨z.1, n0, true, a.next, true⟩) ∧
      (stOf a (y :: Q')).next = a.next + 1 ∧ (stOf a (y :: Q')).level2 = a.level2 ∧
      (stOf a (y :: Q')).level3 = some (y.1.blockSlot, a.next) := by
  obtain ⟨hy1, hy2, hy3, -⟩ := hQ y List.mem_cons_self
  obtain ⟨e, e1, e2, e3⟩ := add_root_page_new (a := a) (t := n0) (by rw [h2, hy3]) hmiss hy1 hy2
  obtain ⟨f, f1, f2, f3⟩ := plOf_steady (a := a.add y) (Q := Q')
    (F := fun z => ⟨z.1, n0, true, a.next, true⟩)
    (fun b k1 k2 k3 z hz => by
      have hz' := hQ z (List.mem_cons_of_mem _ hz)
      obtain ⟨g', g1, g2, g3⟩ := add_root_page_old (a := b) (t := n0) (u := a.next)
        (by rw [k2, e2, h2, hz'.2.2.1]) (by rw [k3, e3, hz'.2.2.2]) hz'.1 hz'.2.1
      exact ⟨g', g1.trans k1, g2.trans k2, g3.trans k3⟩) (a.add y) rfl rfl rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [plOf, e, f, List.map_cons]
  · show (stOf (a.add y) Q').next = _; rw [f1, e1]
  · show (stOf (a.add y) Q').level2 = _; rw [f2, e2]
  · show (stOf (a.add y) Q').level3 = _; rw [f3, e3]

/-- The shape of a 2 MiB run of a suffix of the leaves: a block is alone, and
a run that starts with a page holds pages alone. -/
theorem run_shape (H : SimOk off find place LP) {frm : Nat} {S0 : List (MapLeaf × Place)}
    {y : MapLeaf × Place} {Q' L' : List (MapLeaf × Place)}
    (h : SplitAt LP frm (S0 ++ ((y :: Q') ++ L'))) (hQ : ∀ z ∈ Q', z.1.blockSlot = y.1.blockSlot) :
    (y.1.form = .block → Q' = []) ∧ (y.1.form = .page → ∀ z ∈ y :: Q', z.1.form = .page) := by
  have hp := splitAt_pairwise H.sorted h
  rw [List.pairwise_append] at hp
  have hp2 := hp.2.1
  have hy : y ∈ LP := splitAt_mem h (List.mem_append_right _ List.mem_cons_self)
  have hmem : ∀ z ∈ Q', z ∈ LP := fun z hz =>
    splitAt_mem h (List.mem_append_right _ (List.mem_append_left _ (List.mem_cons_of_mem _ hz)))
  have hafter : ∀ z ∈ Q', y.1.pa.toNat + y.1.form.size ≤ z.1.pa.toNat :=
    fun z hz => List.rel_of_pairwise_cons hp2 (List.mem_append_left _ hz)
  refine ⟨fun hf => ?_, fun hf z hz => ?_⟩
  · cases Q' with
    | nil => rfl
    | cons z Q'' =>
      have := block_before H hy (hmem z List.mem_cons_self) (hafter z List.mem_cons_self) hf
      rw [hQ z List.mem_cons_self] at this; omega
  · rcases List.mem_cons.1 hz with rfl | hz
    · exact hf
    · cases hzf : z.1.form with
      | page => rfl
      | block =>
        have := before_block H hy (hmem z hz) (hafter z hz) hzf
        rw [hQ z hz] at this; omega

/-- The leaves after a run of one 2 MiB slot in a 1 GiB run: in later 2 MiB
slots. -/
theorem after_block_run (H : SimOk off find place LP) {frm : Nat} {S0 : List (MapLeaf × Place)}
    {y : MapLeaf × Place} {Q' R3 L'' : List (MapLeaf × Place)}
    (h : SplitAt LP frm (S0 ++ ((y :: (Q' ++ R3)) ++ L'')))
    (hR3 : ∀ z ∈ R3.head?, (z.1.blockSlot == y.1.blockSlot) = false)
    (hRL : ∀ w ∈ L'', y.1.blockSlot < w.1.blockSlot) :
    ∀ z ∈ R3 ++ L'', y.1.blockSlot < z.1.blockSlot := by
  have hs : SplitAt LP frm (S0 ++ (y :: (Q' ++ R3) ++ L'')) := h
  have hp := (List.pairwise_append.1 (sorted_slots H hs)).2.1
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · refine after_run (fun z : MapLeaf × Place => z.1.blockSlot) (Q := Q') (R := R3) ?_ ?_ z hz
    · have := hp.imp (fun h => h.2)
      exact (List.pairwise_append.1 (by simpa only [List.cons_append] using this)).1
    · intro w hw; simpa using hR3 w hw
  · exact hRL z hz

/-- The children of a new level 2 table, by 2 MiB runs: for the pages of each
run, `Zero` of its new level 3 table and the store of each page. -/
theorem children_run (H : SimOk off find place LP) (hnew : used < NX → NX ≤ TT)
    {L'' : List (MapLeaf × Place)} {g gib n0 : Nat}
    (hL'' : ∀ w ∈ L'', gib + GIB_SIZE ≤ w.1.pa.toNat) (hgib : gib < 2 ^ 39) (hn0 : n0 ≤ TT) :
    ∀ (n : Nat) (R : List (MapLeaf × Place)) (c : Cur) (a : Alloc) (S0 : List (MapLeaf × Place)),
      R.length ≤ n → c.phase = .children → c.gib = gib → c.t2 = n0 → c.next = a.next →
      a.level2 = some (g, n0) →
      (∀ b t, a.level3 = some (b, t) → ∀ z ∈ R ++ L'', b < z.1.blockSlot) →
      (∀ z ∈ R, z.2 = .root ∧ z.1.gibSlot = g ∧ gibOf z.1.pa.toNat = gib) →
      (∀ z ∈ R, ∀ w ∈ L'', z.1.blockSlot < w.1.blockSlot) →
      (∀ z ∈ R, slotOf z.1.pa.toNat ≠ c.slot) →
      (∀ y ∈ S0, y.1.form = .block) → SplitAt LP c.frm (S0 ++ (R ++ L'')) →
      used ≤ a.next → (stOf a R).next ≤ NX → c.t3 ≤ TT →
      ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c
        ((runsBy (·.leaf.blockSlot) (plOf a R)).flatMap childSteps) c' ∧
        c'.phase = .children ∧ c'.gib = gib ∧ c'.t2 = n0 ∧ c'.next = (stOf a R).next ∧ c'.t3 ≤ TT ∧
        (stOf a R).level2 = a.level2 ∧
        (∀ b t, (stOf a R).level3 = some (b, t) → ∀ w ∈ L'', b < w.1.blockSlot) ∧
        ∃ S1, (∀ y ∈ S1, y.1.form = .block) ∧ SplitAt LP c'.frm (S1 ++ L'')
  | _, [], c, a, S0, _, hp, hg, ht2, hn, _, h3, _, _, _, hS0, hs, _, _, ht3 =>
    ⟨c, rfl, hp, hg, ht2, hn, ht3, rfl, fun b t hb w hw => h3 b t hb w hw, S0, hS0, hs⟩
  | 0, _ :: _, _, _, _, hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hn (by simp)
  | n + 1, y :: R', c, a, S0, hlen, hp, hg, ht2, hn, h2, h3, hR, hRL, hsl, hS0, hs, hu, hnx, ht3 => by
    obtain ⟨Q', R3, hR', hQ', hR3⟩ := split_run (fun z => z.1.blockSlot == y.1.blockSlot) R'
    subst hR'
    have hQbs : ∀ z ∈ Q', z.1.blockSlot = y.1.blockSlot := fun z hz => by simpa using hQ' z hz
    have hs' : SplitAt LP c.frm (S0 ++ ((y :: Q') ++ (R3 ++ L''))) := by
      simpa only [List.cons_append, List.append_assoc] using hs
    have hmem : ∀ z ∈ (y :: Q') ++ (R3 ++ L''), z ∈ LP :=
      fun z hz => splitAt_mem hs' (List.mem_append_right _ hz)
    have hy : y ∈ LP := hmem y List.mem_cons_self
    obtain ⟨hyr, hyg, hygib⟩ := hR y List.mem_cons_self
    have hafter : ∀ z ∈ R3 ++ L'', y.1.blockSlot < z.1.blockSlot :=
      after_block_run H hs hR3 (hRL y List.mem_cons_self)
    obtain ⟨hshape1, hshape2⟩ := run_shape H hs' hQbs
    have hrun := runsBy_plOf (fun l : MapLeaf => l.blockSlot) (a := a) (y := y) (Q := Q') (R := R3)
      hQbs (fun z hz he => by
        cases R3 with
        | nil => simp at hz
        | cons r R3' =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz
          simp [he] at hR3)
    have hlen' : R3.length ≤ n := by
      simp only [List.length_cons, List.length_append] at hlen; omega
    have hR3p : ∀ z ∈ R3, z.2 = .root ∧ z.1.gibSlot = g ∧ gibOf z.1.pa.toNat = gib :=
      fun z hz => hR z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))
    have hR3L : ∀ z ∈ R3, ∀ w ∈ L'', z.1.blockSlot < w.1.blockSlot :=
      fun z hz => hRL z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))
    have hstep : stOf a ((y :: Q') ++ R3) = stOf (stOf a (y :: Q')) R3 := stOf_append _ _ _
    rw [show y :: (Q' ++ R3) = (y :: Q') ++ R3 from rfl, hrun, List.flatMap_cons]
    rw [show y :: (Q' ++ R3) = (y :: Q') ++ R3 from rfl, hstep] at hnx
    rw [hstep]
    cases hf : y.1.form with
    | block =>
      have hQ0 := hshape1 hf
      subst hQ0
      obtain ⟨e, e1, e2, e3⟩ := add_root_block (a := a) (t := n0) (by rw [h2, hyg]) hyr hf
      have hc0 : childSteps (plOf a [y]) = [] := by
        simp only [plOf, e, childSteps, hf]; rfl
      obtain ⟨c', hc', hp', hg', ht2', hn', ht3', hl2, hl3, S1, hS1, hs1⟩ :=
        children_run H hnew hL'' hgib hn0 n R3 c (stOf a [y]) (S0 ++ [y]) hlen' hp hg ht2
          (by rw [hn]; exact e1.symm) (by rw [show (stOf a [y]).level2 = a.level2 from e2, h2])
          (fun b t hb z hz => h3 b t (by rw [← e3]; exact hb) z
            (List.mem_cons_of_mem _ (by simpa using hz)))
          hR3p hR3L (fun z hz => hsl z (List.mem_cons_of_mem _ (List.mem_append_right _ hz)))
          (fun w hw => by
            rcases List.mem_append.1 hw with hw | hw
            · exact hS0 w hw
            · rw [List.mem_singleton] at hw; rw [hw]; exact hf)
          (by simpa only [List.cons_append, List.append_assoc, List.nil_append] using hs)
          (by rw [show (stOf a [y]).next = a.next from e1]; exact hu) hnx ht3
      refine ⟨c', by rw [hc0, List.nil_append]; exact hc', hp', hg', ht2', hn', ht3', ?_, hl3,
        S1, hS1, hs1⟩
      rw [hl2]; exact e2
    | page =>
      have hpages := hshape2 hf
      have hmiss : ∀ u, a.level3 ≠ some (y.1.blockSlot, u) := fun u h => by
        have := h3 _ u h y List.mem_cons_self; omega
      have hQp : ∀ z ∈ y :: Q', z.2 = .root ∧ z.1.form = .page ∧ z.1.gibSlot = g ∧
          z.1.blockSlot = y.1.blockSlot := by
        intro z hz
        have hzR : z ∈ y :: (Q' ++ R3) := by
          rcases List.mem_cons.1 hz with rfl | hz
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ hz)
        refine ⟨(hR z hzR).1, hpages z hz, (hR z hzR).2.1, ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · rfl
        · exact hQbs z hz
      obtain ⟨e, e1, e2, e3⟩ := plOf_root_pages h2 hmiss hQp
      have hnx1 : a.next + 1 ≤ NX := by rw [← e1]; exact le_trans (next_le_stOf _ _) hnx
      have hlt : a.next < TT := new_lt_TT hnew hu hnx1
      have hQmem : ∀ z ∈ y :: Q', z ∈ LP ∧ z.1.form = .page :=
        fun z hz => ⟨hmem z (List.mem_append_left _ hz), hpages z hz⟩
      have hm := map_store_pages (F := fun z => (⟨z.1, n0, true, a.next, true⟩ : Placed))
        (t3 := a.next) H hQmem (fun z _ => ⟨rfl, rfl⟩)
      have hc0 : childSteps (plOf a (y :: Q')) = .zero a.next ::
          (y :: Q').map (fun z => .store a.next (index3 (UInt64.ofNat z.1.pa.toNat)) z.1.desc) := by
        rw [← hm, e]
        simp only [List.map_cons, childSteps, hf]
        rfl
      -- the first call: `Zero` of the new level 3 table
      have hlim : y.1.pa.toNat < c.gib + GIB_SIZE := by
        rw [hg, ← hygib]; exact (leaf_low H hy).2.2.2.2.2.1
      have hf1 : find c.frm (c.gib + GIB_SIZE) true = some (fOf y.1) := by
        rw [H.find c.frm _ hs', leafFirst_blocks hS0, List.cons_append, leafFirst_cons (Or.inr hf)]
        simp only [hlim, ↓reduceIte]
      have h1 := step_children_new find place base hp hf1 (hsl y List.mem_cons_self)
      let c1 : Cur :=
        { c with frm := y.1.pa.toNat, next := c.next + 1, slot := slotOf y.1.pa.toNat, t3 := c.next }
      have hbd : ∀ f, CurBound NX TT { c1 with frm := f } := by
        intro f
        refine ⟨by simp only [c1]; omega, by simp only [c1]; omega, by simp only [c1]; omega,
          ?_, fun _ => by simp only [c1]; omega⟩
        simp only [c1, hp]; simp
      have hS0y : ∀ w ∈ S0, w.1.pa.toNat + w.1.form.size ≤ y.1.pa.toNat := by
        have hp0 := splitAt_pairwise H.sorted hs'
        rw [List.pairwise_append] at hp0
        exact fun w hw => hp0.2.2 w hw y (List.mem_cons_self)
      have hsplit0 : SplitAt LP y.1.pa.toNat ((y :: Q') ++ (R3 ++ L'')) := by
        refine splitAt_skip (Q := S0) hs' ?_ hS0y ?_
        · exact hs'.choose_spec.2.2 y (List.mem_append_right _ List.mem_cons_self)
        · intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · exact le_refl _
          · have := List.rel_of_pairwise_cons
              ((List.pairwise_append.1 (splitAt_pairwise H.sorted hs')).2.1) hz
            omega
      obtain ⟨f', hloop, hsp⟩ := pages_loop (base := base) H (c := c1) (L' := R3 ++ L'')
        (good := fun z => z ∈ LP ∧ slotOf z.1.pa.toNat = slotOf y.1.pa.toNat ∧
          gibOf z.1.pa.toNat = gib) hbd
        (fun f z Q3 hgd hzp hsz => step_children_same find place base (by simp only [c1]; exact hp)
          (find_first H hsz (Or.inr hzp) (by
            have := (leaf_low H hgd.1).2.2.2.2.2.1
            simp only [c1, hg]; rw [hgd.2.2] at this; exact this)) hgd.2.1)
        (y :: Q') _ (fun z hz => ⟨⟨(hQmem z hz).1, (slotOf_eq_iff H (hQmem z hz).1 hy).2 (hQp z hz).2.2.2,
          (hR z (by
            rcases List.mem_cons.1 hz with rfl | hz
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_append_left _ hz))).2.2⟩, hpages z hz⟩) hsplit0
      obtain ⟨c', hc', hp', hg', ht2', hn', ht3', hl2, hl3, S1, hS1, hs1⟩ :=
        children_run H hnew hL'' hgib hn0 n R3 { c1 with frm := f' } (stOf a (y :: Q')) []
          hlen' (by simp only [c1]; exact hp) (by simp only [c1]; exact hg)
          (by simp only [c1]; exact ht2) (by simp only [c1]; rw [e1, hn])
          (by rw [e2, h2])
          (fun b t hb z hz => by rw [e3] at hb; cases hb; exact hafter z hz)
          hR3p hR3L
          (fun z hz => by
            simp only [c1]
            intro he
            have := (slotOf_eq_iff H (hmem z (List.mem_append_right _ (List.mem_append_left _ hz)))
              hy).1 he
            have := hafter z (List.mem_append_left _ hz)
            omega)
          (by simp) (by simpa using hsp) (by rw [e1]; omega) hnx (by simp only [c1]; omega)
      refine ⟨c', ?_, hp', hg', ht2', hn', ht3', ?_, hl3, S1, hS1, hs1⟩
      · rw [hc0, ← hn]
        refine curSteps_cons ⟨⟨by omega, by omega, by omega, by simp [hp], fun _ => by omega⟩, _, hs⟩ h1
          (curSteps_append hc' hloop)
      · rw [hl2, e2]


/-- The entries of a new level 2 table, by 2 MiB runs: the block of each run of
a block, the table descriptor of the new level 3 table of each run of pages. -/
theorem entries_run (H : SimOk off find place LP) (hnew : used < NX → NX ≤ TT)
    {L'' : List (MapLeaf × Place)} {g gib n0 NXR : Nat}
    (hL'' : ∀ w ∈ L'', gib + GIB_SIZE ≤ w.1.pa.toNat) (hgib : gib < 2 ^ 39) (hn0 : n0 ≤ TT)
    (hNXR : NXR ≤ NX) :
    ∀ (n : Nat) (R : List (MapLeaf × Place)) (c : Cur) (a : Alloc),
      R.length ≤ n → c.phase = .entries → c.gib = gib → c.t2 = n0 → c.next = NXR → c.t3 = a.next →
      a.level2 = some (g, n0) →
      (∀ b t, a.level3 = some (b, t) → ∀ z ∈ R ++ L'', b < z.1.blockSlot) →
      (∀ z ∈ R, z.2 = .root ∧ z.1.gibSlot = g ∧ gibOf z.1.pa.toNat = gib) →
      (∀ z ∈ R, ∀ w ∈ L'', z.1.blockSlot < w.1.blockSlot) →
      SplitAt LP c.frm (R ++ L'') → used < a.next → (stOf a R).next ≤ NX →
      ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c
        ((runsBy (·.leaf.blockSlot) (plOf a R)).flatMap (level2Entry base)) c' ∧
        c'.phase = .entries ∧ c'.gib = gib ∧ c'.t2 = n0 ∧ c'.next = NXR ∧ c'.t3 = (stOf a R).next ∧
        SplitAt LP c'.frm L''
  | _, [], c, a, _, hp, hg, ht2, hn, ht3, _, _, _, _, hs, _, _ =>
    ⟨c, rfl, hp, hg, ht2, hn, ht3, hs⟩
  | 0, _ :: _, _, _, hn, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hn (by simp)
  | n + 1, y :: R', c, a, hlen, hp, hg, ht2, hn, ht3, h2, h3, hR, hRL, hs, hu, hnx => by
    obtain ⟨Q', R3, hR', hQ', hR3⟩ := split_run (fun z => z.1.blockSlot == y.1.blockSlot) R'
    subst hR'
    have hQbs : ∀ z ∈ Q', z.1.blockSlot = y.1.blockSlot := fun z hz => by simpa using hQ' z hz
    have hs' : SplitAt LP c.frm ([] ++ ((y :: Q') ++ (R3 ++ L''))) := by
      simpa only [List.cons_append, List.append_assoc, List.nil_append] using hs
    have hs0 : SplitAt LP c.frm ([] ++ ((y :: (Q' ++ R3)) ++ L'')) := by simpa using hs
    have hmem : ∀ z ∈ (y :: Q') ++ (R3 ++ L''), z ∈ LP :=
      fun z hz => splitAt_mem hs' (by simpa using hz)
    have hy : y ∈ LP := hmem y List.mem_cons_self
    obtain ⟨hyr, hyg, hygib⟩ := hR y List.mem_cons_self
    have hafter : ∀ z ∈ R3 ++ L'', y.1.blockSlot < z.1.blockSlot :=
      after_block_run H hs0 hR3 (hRL y List.mem_cons_self)
    obtain ⟨hshape1, hshape2⟩ := run_shape H hs' hQbs
    have hrun := runsBy_plOf (fun l : MapLeaf => l.blockSlot) (a := a) (y := y) (Q := Q') (R := R3)
      hQbs (fun z hz he => by
        cases R3 with
        | nil => simp at hz
        | cons r R3' =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz
          simp [he] at hR3)
    have hlen' : R3.length ≤ n := by
      simp only [List.length_cons, List.length_append] at hlen; omega
    have hR3p : ∀ z ∈ R3, z.2 = .root ∧ z.1.gibSlot = g ∧ gibOf z.1.pa.toNat = gib :=
      fun z hz => hR z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))
    have hR3L : ∀ z ∈ R3, ∀ w ∈ L'', z.1.blockSlot < w.1.blockSlot :=
      fun z hz => hRL z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))
    have hstep : stOf a ((y :: Q') ++ R3) = stOf (stOf a (y :: Q')) R3 := stOf_append _ _ _
    rw [show y :: (Q' ++ R3) = (y :: Q') ++ R3 from rfl, hrun, List.flatMap_cons]
    rw [show y :: (Q' ++ R3) = (y :: Q') ++ R3 from rfl, hstep] at hnx
    rw [hstep]
    have hlim : y.1.pa.toNat < c.gib + GIB_SIZE := by
      rw [hg, ← hygib]; exact (leaf_low H hy).2.2.2.2.2.1
    have hf1 : find c.frm (c.gib + GIB_SIZE) false = some (fOf y.1) :=
      find_first H (by simpa using hs') (Or.inl rfl) hlim
    have hanx : a.next ≤ NX := le_trans (next_le_stOf (y :: Q') a) (le_trans (next_le_stOf R3 _) hnx)
    have hTT' : NX ≤ TT := hnew (lt_of_lt_of_le hu hanx)
    have hbd : CurBound NX TT c := by
      refine ⟨by omega, by omega, ?_, by simp [hp], fun _ => by omega⟩
      rw [ht3]; omega
    have hslot : slotOf y.1.pa.toNat + BLOCK_SIZE ≤ gib + GIB_SIZE := by
      have := (leaf_low H hy).2.2.2.2.2.2.1
      rw [← hygib]; simp only [slotOf, gibOf, BLOCK_SIZE, GIB_SIZE] at this ⊢; omega
    have hsplit1 : SplitAt LP (slotOf y.1.pa.toNat + BLOCK_SIZE) (R3 ++ L'') := by
      refine splitAt_skip (Q := y :: Q') (by simpa using hs') ?_ ?_ ?_
      · have h0 := hs.choose_spec.2.2 y List.mem_cons_self
        have := (leaf_low H hy).2.2.2.2.1
        omega
      · intro z hz
        have hz' := hmem z (List.mem_append_left _ hz)
        have := leaf_end_slot H hz'
        rcases List.mem_cons.1 hz with rfl | hz
        · exact this
        · rw [(slotOf_eq_iff H hz' hy).2 (hQbs z hz)] at this; exact this
      · exact fun z hz => slot_end_le H hy (hmem z (List.mem_append_right _ hz)) (hafter z hz)
    cases hf : y.1.form with
    | block =>
      have hQ0 := hshape1 hf
      subst hQ0
      obtain ⟨e, e1, e2, e3⟩ := add_root_block (a := a) (t := n0) (by rw [h2, hyg]) hyr hf
      have hc0 : level2Entry base (plOf a [y]) =
          [.store c.t2 (index2 (UInt64.ofNat y.1.pa.toNat)) y.1.desc] := by
        simp only [plOf, e, level2Entry, hf, Placed.store, index2_fOf H hy, ht2]
      have h1 := step_entries_block find place base hp hf1 (fOf_block hf)
      obtain ⟨c', hc', hp', hg', ht2', hn', ht3', hs1⟩ :=
        entries_run H hnew hL'' hgib hn0 hNXR n R3 { c with frm := slotOf y.1.pa.toNat + BLOCK_SIZE }
          (stOf a [y]) hlen' hp hg ht2 hn (by rw [show (stOf a [y]).next = a.next from e1]; exact ht3)
          (by rw [show (stOf a [y]).level2 = a.level2 from e2, h2])
          (fun b t hb z hz => h3 b t (by rw [← e3]; exact hb) z
            (List.mem_cons_of_mem _ (by simpa using hz)))
          hR3p hR3L hsplit1 (by rw [show (stOf a [y]).next = a.next from e1]; exact hu) hnx
      exact ⟨c', by rw [hc0]; exact curSteps_cons ⟨hbd, _, hs⟩ h1 hc', hp', hg', ht2', hn', ht3', hs1⟩
    | page =>
      have hpages := hshape2 hf
      have hmiss : ∀ u, a.level3 ≠ some (y.1.blockSlot, u) := fun u h => by
        have := h3 _ u h y List.mem_cons_self; omega
      have hQp : ∀ z ∈ y :: Q', z.2 = .root ∧ z.1.form = .page ∧ z.1.gibSlot = g ∧
          z.1.blockSlot = y.1.blockSlot := by
        intro z hz
        have hzR : z ∈ y :: (Q' ++ R3) := by
          rcases List.mem_cons.1 hz with rfl | hz
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ hz)
        refine ⟨(hR z hzR).1, hpages z hz, (hR z hzR).2.1, ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · rfl
        · exact hQbs z hz
      obtain ⟨e, e1, e2, e3⟩ := plOf_root_pages h2 hmiss hQp
      have hc0 : level2Entry base (plOf a (y :: Q')) =
          [.store c.t2 (index2 (UInt64.ofNat y.1.pa.toNat)) (tableAt base c.t3)] := by
        simp only [e, List.map_cons, level2Entry, hf, index2_fOf H hy, ht2, ht3]
      have h1 := step_entries_page find place base hp hf1 (fOf_page hf)
      obtain ⟨c', hc', hp', hg', ht2', hn', ht3', hs1⟩ :=
        entries_run H hnew hL'' hgib hn0 hNXR n R3
          { c with frm := slotOf y.1.pa.toNat + BLOCK_SIZE, t3 := c.t3 + 1 }
          (stOf a (y :: Q')) hlen' hp hg ht2 hn (by simp only; rw [e1, ht3])
          (by rw [e2, h2])
          (fun b t hb z hz => by rw [e3] at hb; cases hb; exact hafter z hz)
          hR3p hR3L hsplit1 (by rw [e1]; omega) hnx
      exact ⟨c', by rw [hc0]; exact curSteps_cons ⟨hbd, _, hs⟩ h1 hc', hp', hg', ht2', hn', ht3', hs1⟩

/-- The value of the level 2 table of a leaf in the 1 GiB slot of the latest
new level 2 table. -/
theorem pOf_root_t2 {a : Alloc} {x : MapLeaf × Place} {t : Nat}
    (h2 : a.level2 = some (x.1.gibSlot, t)) (hp : x.2 = .root) :
    (pOf a x).t2 = t ∧ (pOf a x).new2 = true ∧ (pOf a x).leaf = x.1 := by
  obtain ⟨l, p⟩ := x
  simp only at h2 hp; subst hp
  have hs := stage2_root a l
  rw [cacheStep_hit h2] at hs
  simp only [pOf, hs, and_self]

/-- A transfer of steps between two states whose calls agree. -/
theorem curSteps_transfer {step : Cur → Option Step × Cur} {P : Cur → Prop} {c c1 c' : Cur}
    {l : List Step} (hp : P c) (he : step c = step c1) (h : CurSteps step P c1 l c') (hl : l ≠ []) :
    CurSteps step P c l c' := by
  cases l with
  | nil => exact absurd rfl hl
  | cons s l => exact curSteps_of_step_eq hp he h

/-- One 1 GiB slot under a new level 2 table: the children, `Zero` of the
level 2 table, its entries, `Fence` and the root store. -/
theorem seg_new (H : SimOk off find place LP) (hnew : used < NX → NX ≤ TT) {c : Cur} {a : Alloc} {x : MapLeaf × Place}
    {R' L'' A : List (MapLeaf × Place)} (hb : Bnd LP used NX TT c a ((x :: R') ++ L''))
    (hR : ∀ z ∈ x :: R', z.2 = .root ∧ z.1.gibSlot = x.1.gibSlot)
    (hL'' : ∀ w ∈ L'', x.1.gibSlot < w.1.gibSlot)
    (hA : LP = A ++ ((x :: R') ++ L'')) (hAg : ∀ y ∈ A, y.1.gibSlot < x.1.gibSlot) :
    ∃ c', CurSteps (Cur.step find place base) (CurOk LP NX TT) c
      (newLevel2Steps base (plOf a (x :: R'))) c' ∧ Bnd LP used NX TT c' (stOf a (x :: R')) L'' := by
  have hmem : ∀ z ∈ (x :: R') ++ L'', z ∈ LP := fun z hz => splitAt_mem hb.split hz
  have hx : x ∈ LP := hmem x List.mem_cons_self
  have hmR : ∀ z ∈ x :: R', z ∈ LP := fun z hz => hmem z (List.mem_append_left _ hz)
  have hmL : ∀ w ∈ L'', w ∈ LP := fun w hw => hmem w (List.mem_append_right _ hw)
  have hAm : ∀ y ∈ A, y ∈ LP := fun y hy => by rw [hA]; exact List.mem_append_left _ hy
  obtain ⟨hst, hfind⟩ := bnd_first (base := base) H hb
  obtain ⟨hxr, -⟩ := hR x List.mem_cons_self
  set gib := gibOf x.1.pa.toNat with hgibdef
  set g := x.1.gibSlot with hgdef
  set n0 := a.next with hn0def
  have hlow := leaf_low H hx
  have hgib : gib < 2 ^ 39 := hlow.2.2.1
  have hRgib : ∀ z ∈ x :: R', gibOf z.1.pa.toNat = gib :=
    fun z hz => (gibOf_eq_iff H (hmR z hz) hx).2 (hR z hz).2
  have hLg : ∀ w ∈ L'', gib + GIB_SIZE ≤ w.1.pa.toNat := fun w hw => gib_end_le H hx (hmL w hw) (hL'' w hw)
  have hRL : ∀ z ∈ x :: R', ∀ w ∈ L'', z.1.blockSlot < w.1.blockSlot := by
    intro z hz w hw
    have h1 := hL'' w hw
    rw [← (hR z hz).2] at h1
    simp only [MapLeaf.gibSlot, MapLeaf.blockSlot, GIB_SIZE, BLOCK_SIZE] at h1 ⊢
    omega
  have hmiss2 : ∀ t, a.level2 ≠ some (g, t) := fun t h => by
    have := hb.fresh2 g t h x List.mem_cons_self; omega
  -- the tables: as from the tables that took the new level 2 table
  let a1 : Alloc := { a with next := a.next + 1, level2 := some (g, a.next) }
  obtain ⟨hp1, hadd⟩ := add_root_miss (a := a) (x := x) hmiss2 hxr
  have hpl : plOf a (x :: R') = plOf a1 (x :: R') := by
    show pOf a x :: plOf (a.add x) R' = pOf a1 x :: plOf (a1.add x) R'
    rw [hp1, hadd]
  have hstl : stOf a (x :: R') = stOf a1 (x :: R') := by
    show stOf (a.add x) R' = stOf (a1.add x) R'
    rw [hadd]
  obtain ⟨ht2x, -, hleafx⟩ := pOf_root_t2 (a := a1) (x := x) (t := n0) rfl hxr
  have hnxR : (stOf a1 (x :: R')).next ≤ NX := by
    rw [← hstl]; exact le_trans (next_le_stOf L'' _) (by rw [← stOf_append]; exact hb.nx)
  have hn1 : n0 + 1 ≤ (stOf a1 (x :: R')).next := next_le_stOf (x :: R') a1
  have hn0 : n0 < TT := new_lt_TT hnew hb.used (by omega)
  have hTT' : NX ≤ TT := hnew (by have := hb.used; omega)
  -- the split addresses
  have hsx : SplitAt LP x.1.pa.toNat ((x :: R') ++ L'') := by
    refine splitAt_mono hb.split (hb.split.choose_spec.2.2 x List.mem_cons_self) ?_
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact le_refl _
    · have := splitAt_after H hb.split z hz; omega
  have hsg : SplitAt LP gib ((x :: R') ++ L'') := by
    refine ⟨A, hA, fun y hy => end_le_gib H (hAm y hy) hx (hAg y hy), ?_⟩
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · rw [← hRgib z hz]; simp only [gibOf, GIB_SIZE]; omega
    · have := hLg z hz; omega
  -- the first call: as the call in `children` at the first leaf
  let c1 : Cur := ⟨.children, x.1.pa.toNat, n0 + 1, gib, noSlot, n0, c.t3⟩
  have he1 : Cur.step find place base c = Cur.step find place base c1 := by
    rw [hst]
    refine (step_leaf_root find place base (c := { c with phase := .leaf }) rfl hfind
      (by rw [H.place x hx, hxr]) (fun hb' => ?_)).trans ?_
    · have hxp : x.1.form = .page := by
        cases hfx : x.1.form with
        | page => rfl
        | block => rw [fOf_block hfx] at hb'; cases hb'
      exact find_first H hsx (Or.inr hxp) hlow.2.2.2.2.2.1
    · show Cur.step find place base ⟨.children, x.1.pa.toNat, c.next + 1, gib, noSlot, c.next, c.t3⟩ = _
      rw [hb.next]
  -- children
  obtain ⟨c2, hc2, hp2, hg2, ht22, hn2, ht32, hl22, hl32, S1, hS1, hs2⟩ :=
    children_run (base := base) H hnew hLg hgib (le_of_lt hn0) (x :: R').length (x :: R') c1 a1 []
      (le_refl _) rfl rfl rfl rfl rfl
      (fun b t hb' z hz => hb.fresh3 b t hb' z hz)
      (fun z hz => ⟨(hR z hz).1, (hR z hz).2, hRgib z hz⟩) hRL
      (fun z _ => (slotOf_ne_noSlot _)) (by simp) (by simpa using hsx)
      (by show used ≤ a.next + 1; have := hb.used; omega) hnxR hb.t3
  -- `Zero` of the level 2 table
  have hz := step_children_none find place base (c := c2) hp2
    (by rw [H.find c2.frm _ hs2, leafFirst_blocks hS1, leafFirst_ge (fun w hw => by
      rw [hg2]; exact hLg w hw)])
  -- entries
  obtain ⟨e1, he1s, hpe, hge, ht2e, hne, ht3e, hse⟩ :=
    entries_run (base := base) H hnew hLg hgib (le_of_lt hn0) (le_trans (by rw [hn2]) hnxR)
      (x :: R').length (x :: R') { c2 with phase := .entries, frm := c2.gib, t3 := c2.t2 + 1 } a1
      (le_refl _) rfl hg2 ht22 rfl (by simp only; rw [ht22])
      rfl (fun b t hb' z hz => hb.fresh3 b t hb' z hz)
      (fun z hz => ⟨(hR z hz).1, (hR z hz).2, hRgib z hz⟩) hRL
      (by simp only; rw [hg2]; exact hsg) (by simp only [a1]; have := hb.used; omega) hnxR
  have hfence := step_entries_none find place base (c := e1) hpe
    (find_none H hse (fun w hw => by rw [hge]; exact hLg w hw))
  have hroot := step_root find place base (c := { e1 with phase := .root }) rfl
  -- the plan
  have hplan : newLevel2Steps base (plOf a (x :: R')) =
      (runsBy (·.leaf.blockSlot) (plOf a1 (x :: R'))).flatMap childSteps ++
        Step.zero n0 :: (runsBy (·.leaf.blockSlot) (plOf a1 (x :: R'))).flatMap (level2Entry base) ++
        [Step.fence, Step.store 0 (index1 (UInt64.ofNat gib)) (tableAt base n0)] := by
    rw [hpl]
    show newLevel2Steps base (pOf a1 x :: plOf (a1.add x) R') = _
    rw [newLevel2Steps_eq, ht2x, hleafx, index1_gib H hx]
    rfl
  have hbd2 : CurBound NX TT c2 :=
    ⟨by rw [hn2]; exact hnxR, by rw [ht22]; omega, ht32, by simp [hp2], fun _ => by rw [hg2]; exact hgib⟩
  have hbde : CurBound NX TT e1 :=
    ⟨by rw [hne, hn2]; exact hnxR, by rw [ht2e]; omega, by rw [ht3e]; omega, by simp [hpe],
      fun _ => by rw [hge]; exact hgib⟩
  have hbdr : CurBound NX TT { e1 with phase := .root } :=
    ⟨hbde.1, hbde.2.1, hbde.2.2.1, by simp, fun _ => by simp only; rw [hge]; exact hgib⟩
  have hz' : Cur.step find place base c2 =
      (some (.zero n0), { c2 with phase := .entries, frm := c2.gib, t3 := c2.t2 + 1 }) := by
    rw [hz, ht22]
  have hroot' : Cur.step find place base { e1 with phase := .root } =
      (some (.store 0 (index1 (UInt64.ofNat gib)) (tableAt base n0)),
        { { e1 with phase := .root } with phase := .leaf, frm := e1.gib + GIB_SIZE }) := by
    rw [hroot]; simp only [hge, ht2e]
  refine ⟨{ { e1 with phase := .root } with phase := .leaf, frm := e1.gib + GIB_SIZE }, ?_, ?_⟩
  · rw [hplan]
    refine curSteps_transfer (bnd_ok hb) he1 ?_ (by simp)
    exact curSteps_append (curSteps_cons ⟨hbde, _, hse⟩ hfence
      (curSteps_cons ⟨hbdr, _, hse⟩ hroot' (curSteps_nil _)))
      (curSteps_append (curSteps_cons ⟨hbd2, _, hs2⟩ hz' he1s) hc2)
  · refine ⟨?_, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show SplitAt LP (e1.gib + GIB_SIZE) L''
      rw [hge]
      refine splitAt_skip (Q := x :: R') hsg (by omega) ?_ hLg
      intro z hz
      have := leaf_end_gib H (hmR z hz)
      rw [hRgib z hz] at this; exact this
    · show e1.next = (stOf a (x :: R')).next
      rw [hne, hn2, hstl]
    · intro g' t hg' w hw
      rw [hstl, hl22] at hg'
      simp only [a1, Option.some.injEq, Prod.mk.injEq] at hg'
      rw [← hg'.1]; exact hL'' w hw
    · intro b t hb' w hw
      rw [hstl] at hb'
      exact hl32 b t hb' w hw
    · have := hb.used; have := next_le_stOf (x :: R') a; omega
    · rw [← stOf_append]; exact hb.nx
    · show e1.t2 ≤ TT; rw [ht2e]; omega
    · show e1.t3 ≤ TT; rw [ht3e]; omega


/-! ### The whole plan -/

/-- After the last leaf: `Sync`, then none at a state that stays. -/
theorem end_run (H : SimOk off find place LP) {c : Cur} {a : Alloc}
    (hb : Bnd LP used NX TT c a []) :
    CurRuns (Cur.step find place base) (CurOk LP NX TT) c (mapPlan base (plOf a [])) := by
  have hf : find c.frm (2 ^ 64 - 1) false = none := find_none H hb.split (by simp)
  have hst : Cur.step find place base c = Cur.step find place base { c with phase := .leaf } := by
    rcases hb.phase with h | ⟨h, -⟩
    · obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
      simp only at h; subst h; rfl
    · exact step_held_leaf find place base h (fun f hf' => by rw [hf] at hf'; cases hf')
  have h1 := step_leaf_none find place base (c := { c with phase := .leaf }) rfl hf
  have hbd := bnd_bound hb
  have hbdd : CurBound NX TT { { c with phase := .leaf } with phase := .done } :=
    ⟨hbd.1, hbd.2.1, hbd.2.2.1, by simp, by simp⟩
  have h2 := step_done find place base (c := { { c with phase := .leaf } with phase := .done }) rfl
  have hok : CurOk LP NX TT { { c with phase := .leaf } with phase := .done } := ⟨hbdd, _, hb.split⟩
  refine ⟨_, curSteps_cons (bnd_ok hb) (hst.trans h1) (curSteps_nil _), hok, by rw [h2],
    by rw [h2]; exact hok, by rw [h2, h2]⟩

/-- From the first leaf of a 1 GiB slot to the end: the plan of the leaves
left, then none at a state that stays. -/
theorem main_run (H : SimOk off find place LP) (hTT : ∀ x ∈ LP, PlaceLe TT x.2)
    (hnew : used < NX → NX ≤ TT) :
    ∀ (n : Nat) (L : List (MapLeaf × Place)) (c : Cur) (a : Alloc), L.length ≤ n →
      (∃ A, LP = A ++ L ∧ ∀ y ∈ A, ∀ z ∈ L, y.1.gibSlot < z.1.gibSlot) →
      Bnd LP used NX TT c a L →
      CurRuns (Cur.step find place base) (CurOk LP NX TT) c (mapPlan base (plOf a L))
  | _, [], c, a, _, _, hb => end_run H hb
  | 0, _ :: _, _, _, hn, _, _ => absurd hn (by simp)
  | n + 1, x :: L0, c, a, hn, ⟨A, hA, hAg⟩, hb => by
    obtain ⟨R', L'', hL0, hR', hL''⟩ := split_run (fun z => z.1.gibSlot == x.1.gibSlot) L0
    subst hL0
    have hRg : ∀ z ∈ R', z.1.gibSlot = x.1.gibSlot := fun z hz => by simpa using hR' z hz
    have hb' : Bnd LP used NX TT c a ((x :: R') ++ L'') := by simpa only [List.cons_append] using hb
    have hmem : ∀ z ∈ (x :: R') ++ L'', z ∈ LP := fun z hz => splitAt_mem hb'.split hz
    have hx : x ∈ LP := hmem x List.mem_cons_self
    have hsorted := sorted_slots H hb'.split
    have hafter : ∀ w ∈ L'', x.1.gibSlot < w.1.gibSlot := by
      refine after_run (fun z : MapLeaf × Place => z.1.gibSlot) (Q := R') ?_ ?_
      · have := hsorted.imp (fun h => h.1)
        simpa only [List.cons_append] using this
      · intro w hw; simpa using hL'' w hw
    have hRgib : ∀ z ∈ x :: R', z.1.gibSlot = x.1.gibSlot := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · rfl
      · exact hRg z hz
    have hplan : mapPlan base (plOf a ((x :: R') ++ L'')) =
        runSteps base (plOf a (x :: R')) ++ mapPlan base (plOf (stOf a (x :: R')) L'') := by
      rw [plOf_append]
      show mapPlan base ((pOf a x :: plOf (a.add x) R') ++ _) = runSteps base (pOf a x :: _) ++ _
      refine mapPlan_append_run base (pOf a x) _ _ ?_ ?_
      · intro q hq
        obtain ⟨z, hz, he⟩ := mem_plOf hq
        rw [he]; exact hRg z hz
      · intro q hq
        obtain ⟨z, hz, he⟩ := head_plOf hq
        rw [he]; exact Nat.ne_of_gt (hafter z (List.mem_of_mem_head? hz))
    have hlen : L''.length ≤ n := by
      simp only [List.length_cons, List.length_append] at hn; omega
    have hfront : ∃ A', LP = A' ++ L'' ∧ ∀ y ∈ A', ∀ z ∈ L'', y.1.gibSlot < z.1.gibSlot := by
      refine ⟨A ++ (x :: R'), by rw [hA, List.append_assoc]; rfl, fun y hy z hz => ?_⟩
      rcases List.mem_append.1 hy with hy | hy
      · exact hAg y hy z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))
      · rw [hRgib y hy]; exact hafter z hz
    have hcases : ∃ c1, CurSteps (Cur.step find place base) (CurOk LP NX TT) c
        (runSteps base (plOf a (x :: R'))) c1 ∧ Bnd LP used NX TT c1 (stOf a (x :: R')) L'' := by
      by_cases hroot : x.2 = .root
      · have hall : ∀ z ∈ x :: R', z.2 = .root ∧ z.1.gibSlot = x.1.gibSlot := fun z hz =>
          ⟨(H.gib z (hmem z (List.mem_append_left _ hz)) x hx (hRgib z hz)).2 hroot, hRgib z hz⟩
        have hn2 : (pOf a x).new2 = true := by
          obtain ⟨l, p⟩ := x
          simp only at hroot; subst hroot
          simp only [pOf, stage2_root]
        rw [show plOf a (x :: R') = pOf a x :: plOf (a.add x) R' from rfl, runSteps_new base _ _ hn2,
          ← show plOf a (x :: R') = pOf a x :: plOf (a.add x) R' from rfl]
        exact seg_new H hnew hb' hall hafter (A := A) (by rw [hA]; rfl)
          (fun y hy => hAg y hy x List.mem_cons_self)
      · have hall : ∀ z ∈ x :: R', z.2 ≠ .root := fun z hz hz' =>
          hroot ((H.gib z (hmem z (List.mem_append_left _ hz)) x hx (hRgib z hz)).1 hz')
        have hn2 : (pOf a x).new2 = false := by
          obtain ⟨l, p⟩ := x
          simp only at hroot
          cases p with
          | root => exact absurd rfl hroot
          | level2 t => rfl
          | level3 t u => rfl
        rw [show plOf a (x :: R') = pOf a x :: plOf (a.add x) R' from rfl, runSteps_held base _ _ hn2,
          ← show plOf a (x :: R') = pOf a x :: plOf (a.add x) R' from rfl]
        exact held_run H hTT hnew (x :: R').length (x :: R') c a (le_refl _) hall
          (fun z hz w hw => by rw [hRgib z hz]; exact hafter w hw) hb'
    obtain ⟨c1, hs1, hb1⟩ := hcases
    rw [show x :: (R' ++ L'') = (x :: R') ++ L'' from rfl, hplan]
    exact curRuns_of_steps hs1 (main_run H hTT hnew n L'' c1 _ hlen hfront hb1)

/-- **The simulation.** For leaves `LP` with their places, a search `find`
and a place `place` that satisfy `SimOk`, and the bound `TT` of the tables of
the set that the places name, which is also at or above the next free table
when the map takes a new table: the calls of `Cur.step find place base` from
the cursor before the first leaf, with the record `used`, give `mapPlan` of
the placed leaves of `assignTables used LP`, then none at a state that stays,
each call from a state that keeps `CurOk`. -/
theorem curRuns_mapPlan (H : SimOk off find place LP) (used TT : Nat)
    (hTT : ∀ x ∈ LP, PlaceLe TT x.2)
    (hnew : used < (assignTables used LP).1 → (assignTables used LP).1 ≤ TT) :
    CurRuns (Cur.step find place base) (CurOk LP (assignTables used LP).1 TT)
      ⟨.leaf, 0, used, noSlot, noSlot, 0, 0⟩ (mapPlan base (assignTables used LP).2) := by
  rw [assignTables_eq] at hnew ⊢
  refine main_run H hTT hnew LP.length LP _ _ (le_refl _) ⟨[], rfl, by simp⟩ ?_
  refine ⟨⟨[], rfl, by simp, fun _ _ => Nat.zero_le _⟩, Or.inl rfl, rfl, by simp, by simp, le_refl _,
    le_refl _, Nat.zero_le _, Nat.zero_le _⟩

/-- **`Stands` for a map plan iterator.** An iterator whose call of `next`, from
a state that keeps `Inv` and whose cursor `abs` keeps `CurOk`, as the cursor
after the call does, is one call of `Cur.step find place base` on its cursor
(an item related to the step, a state that keeps `Inv` whose cursor is the
cursor after it, the same state when the cursor stays), at the cursor before
the first leaf with the record `used`, stands for `mapPlan` of the placed
leaves of `assignTables used LP`, for leaves, search and place that satisfy
`SimOk` and a bound `TT` of the tables as in `curRuns_mapPlan`. -/
theorem stands_mapPlan {σ α : Type} {next : σ → Result (Option α × σ)} {rel : α → Step → Prop}
    {abs : σ → Cur} {Inv : σ → Prop} (H : SimOk off find place LP) (used TT : Nat)
    (hTT : ∀ x ∈ LP, PlaceLe TT x.2)
    (hnew : used < (assignTables used LP).1 → (assignTables used LP).1 ≤ TT)
    (hnext : ∀ it, Inv it → CurOk LP (assignTables used LP).1 TT (abs it) →
      CurOk LP (assignTables used LP).1 TT (Cur.step find place base (abs it)).2 → next it ⦃ o it' =>
      OptionRel rel o (Cur.step find place base (abs it)).1 ∧
        abs it' = (Cur.step find place base (abs it)).2 ∧ Inv it' ∧ (abs it' = abs it → it' = it) ⦄)
    (it : σ) (hi : Inv it) (hc : abs it = ⟨.leaf, 0, used, noSlot, noSlot, 0, 0⟩) :
    Stands next rel it (mapPlan base (assignTables used LP).2) :=
  stands_of_curRuns hnext _ it hi (by rw [hc]; exact curRuns_mapPlan H used TT hTT hnew)


end Sim
end Krepi.Proofs.PageTables.Refinement
