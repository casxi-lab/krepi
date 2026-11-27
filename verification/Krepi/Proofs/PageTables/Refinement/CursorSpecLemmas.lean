module

public import Krepi.Proofs.PageTables.Refinement.WalkSpecLemmas
public import Krepi.Spec.PageTables.Boot
public import Krepi.Proofs.PageTables.AssignLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the place of a leaf and the count of new tables, on the specification side

Lemmas about `Tables.place`, `Tables.checkLeaf` and `Alloc.add` of
`Krepi.Spec.PageTables`, in the forms that the triples of the checks of the
two boot maps need (`Krepi.Proofs.PageTables.Refinement.CursorLemmas`). The
module imports no generated definitions, so it is built once and not again
for every mutant of the code.

- The high bits of a word: `and_high_bits` (a 64-bit number with its low `k`
  bits cleared is its multiple of `2 ^ k` below it).
- The place of a leaf: `placeProbe` (the leaf at a physical address that the
  code walks, mapped at that address), `walk2_congr` and `place_congr` (the
  walk and the place read the indices and the form of a leaf alone), and the
  one-step lemmas `place_walk_error`, `place_walk_root`,
  `place_walk_invalid`, `place_walk_block`, `place_walk_backing`,
  `place_walk_covered`, `place_walk_mapped`, `place_walk_level3`.
- The check of one leaf: `checkPlace` (the place, then `AlreadyMapped` for a
  taken leaf) with `checkPlace_error`, `checkPlace_taken`, `checkPlace_ok`,
  and `checkLeaf_eq` (`Tables.checkLeaf` is `checkPlace` with the leaf put
  before the leaves that passed).
- The count of new tables: `noSlot`, `SlotRel`, `AllocRel` (what the record
  of the checks of the code holds about the fold of `Alloc.add`),
  `countStep` (how the code changes that record for one leaf, with
  `countStep_le`, `countStep_ge`), `cacheStep_rel` (one level of it) and
  `allocRel_add` (one leaf keeps `AllocRel`), with `allocRel_init`.
- The cursor of a map plan on numbers, as the code computes it: `gibOf`,
  `slotOf` (with `slotOf_ne_noSlot`, `gibOf_ne_noSlot`), `CurPhase`, `Cur`, `Found`, `Turn`, `placeOr` (the place that
  the cursor reads), and the functions of `MapCursor` on it, `Cur.search`,
  `Cur.children`, `Cur.entry`, `Cur.newPage`, `Cur.leaf`, `Cur.heldPage`
  and `Cur.take`, and one call of the `next` of a plan, `Cur.step`.
- The plan by runs, for the simulation of `mapPlan` by the cursor:
  `runsBy_cons_head`, `runsBy_append_run` (a whole run at the front),
  `mapPlan_append_run`, `runSteps_held`, `runSteps_new`.
-/

@[expose] public section

open Krepi.Spec.PageTables

namespace Krepi.Proofs.PageTables.Refinement

variable {r : Region} {N : Nat}

/-! ## The high bits of a word -/

/-- A number below `2 ^ 64` with its bits below bit `k` cleared, for
`k ≤ 64`: the mask `~~~(2 ^ k - 1)` of 64 bits keeps the multiple of `2 ^ k`
at or below the number. -/
theorem and_high_bits {x k : Nat} (hx : x < 2 ^ 64) (hk : k ≤ 64) :
    x &&& (2 ^ 64 - 1 - (2 ^ k - 1)) = x / 2 ^ k * 2 ^ k := by
  have h64 : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hpos' : 1 ≤ 2 ^ (64 - k) := Nat.one_le_two_pow
  have hm : 2 ^ 64 - 1 - (2 ^ k - 1) = (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, ← h64, Nat.one_mul]; omega
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hj : k ≤ j
  · rw [Nat.sub_add_cancel hj]
    by_cases hj64 : j < 64
    · simp [hj, show j - k < 64 - k by omega]
    · have : x.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hj]

/-! ## The place of a leaf -/

/-- The leaf of the form of `block` at the physical address `pa`, mapped at
`pa`: the leaf whose place the code computes, since it walks a set with the
physical address of a leaf. Its descriptor is not read by the place. -/
def placeProbe (pa : UInt64) (block : Bool) : MapLeaf :=
  ⟨pa, pa, 0, if block then .block else .page⟩

/-- The level 2 step of the walk reads the first two indices of the address
alone. -/
theorem walk2_congr (s : Tables r N) (base : UInt64) {v w : UInt64}
    (h1 : index1 v = index1 w) (h2 : index2 v = index2 w) : s.walk2 base v = s.walk2 base w := by
  simp only [Tables.walk2, h1, h2]

/-- The place of a leaf reads the three indices of its virtual address and its
form alone. -/
theorem place_congr (s : Tables r N) (base : UInt64) {l l' : MapLeaf}
    (h1 : index1 l.va = index1 l'.va) (h2 : index2 l.va = index2 l'.va)
    (h3 : index3 l.va = index3 l'.va) (hf : l.form = l'.form) :
    s.place base l = s.place base l' := by
  simp only [Tables.place, walk2_congr s base h1 h2, h3, hf]

theorem place_walk_error {s : Tables r N} {base : UInt64} {l : MapLeaf} {x : TableError}
    (h : s.walk2 base l.va = .error x) : s.place base l = .error x := by
  simp only [Tables.place, h, bind, Except.bind]

theorem place_walk_root {s : Tables r N} {base : UInt64} {l : MapLeaf}
    (h : s.walk2 base l.va = .ok none) : s.place base l = .ok .root := by
  simp only [Tables.place, h, bind, Except.bind, pure, Except.pure]

theorem place_walk_invalid {s : Tables r N} {base : UInt64} {l : MapLeaf} {t2 : Nat} {e2 : UInt64}
    (h : s.walk2 base l.va = .ok (some (t2, e2))) (hv : isValid e2 = false) :
    s.place base l = .ok (.level2 t2) := by
  unfold Tables.place
  cases hf : l.form <;>
    simp only [h, hv, bind, Except.bind, pure, Except.pure, Bool.not_false, ↓reduceIte]

theorem place_walk_block {s : Tables r N} {base : UInt64} {l : MapLeaf} {t2 : Nat} {e2 : UInt64}
    (h : s.walk2 base l.va = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : typeBits e2 = BLOCK) : s.place base l = .error .alreadyMapped := by
  unfold Tables.place
  cases hf : l.form <;>
    simp only [h, hv, hb, bind, Except.bind, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.false_and, beq_self_eq_true,
      throw, throwThe, MonadExceptOf.throw]

theorem place_walk_backing {s : Tables r N} {base : UInt64} {l : MapLeaf} {t2 : Nat}
    {e2 : UInt64} (h : s.walk2 base l.va = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = none) :
    s.place base l = .error .tableBacking := by
  have hb1 : (typeBits e2 != BLOCK) = true := bne_iff_ne.2 hb
  have hb2 : (typeBits e2 == BLOCK) = false := beq_eq_false_iff_ne.2 hb
  unfold Tables.place
  cases hf : l.form <;>
    simp only [h, hv, hb1, hb2, hc, bind, Except.bind, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, Option.isNone_none, Bool.and_self,
      throw, throwThe, MonadExceptOf.throw]

theorem place_walk_covered {s : Tables r N} {base : UInt64} {l : MapLeaf} {t2 t3 : Nat}
    {e2 : UInt64} (h : s.walk2 base l.va = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = some t3) (hf : l.form = .block) :
    s.place base l = .error .alreadyMapped := by
  have hb1 : (typeBits e2 != BLOCK) = true := bne_iff_ne.2 hb
  simp only [Tables.place, h, hv, hb1, hc, hf, bind, Except.bind, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Option.isNone_some, Bool.and_false,
    throw, throwThe, MonadExceptOf.throw]

theorem place_walk_mapped {s : Tables r N} {base : UInt64} {l : MapLeaf} {t2 t3 : Nat}
    {e2 : UInt64} (h : s.walk2 base l.va = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = some t3) (hf : l.form = .page)
    (h3 : isValid (s.entry t3 (index3 l.va)) = true) :
    s.place base l = .error .alreadyMapped := by
  have hb2 : (typeBits e2 == BLOCK) = false := beq_eq_false_iff_ne.2 hb
  simp only [Tables.place, h, hv, hb2, hc, hf, h3, bind, Except.bind, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]

theorem place_walk_level3 {s : Tables r N} {base : UInt64} {l : MapLeaf} {t2 t3 : Nat}
    {e2 : UInt64} (h : s.walk2 base l.va = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = some t3) (hf : l.form = .page)
    (h3 : isValid (s.entry t3 (index3 l.va)) = false) :
    s.place base l = .ok (.level3 t2 t3) := by
  have hb2 : (typeBits e2 == BLOCK) = false := beq_eq_false_iff_ne.2 hb
  simp only [Tables.place, h, hv, hb2, hc, hf, h3, bind, Except.bind, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, pure, Except.pure]

/-! ## The check of one leaf -/

/-- The free-slot check of one leaf without the list of the leaves that
passed: its place, then `AlreadyMapped` when `taken` holds. -/
def checkPlace (s : Tables r N) (base : UInt64) (l : MapLeaf) (taken : Bool) :
    Except TableError Place := do
  let p ← s.place base l
  if taken then throw .alreadyMapped
  pure p

/-- `Tables.checkLeaf` is `checkPlace` with the leaf and its place put before
the leaves that passed. -/
theorem checkLeaf_eq (s : Tables r N) (base : UInt64) (taken : MapLeaf → Bool)
    (acc : List (MapLeaf × Place)) (l : MapLeaf) :
    s.checkLeaf base taken acc l = (checkPlace s base l (taken l)).map (fun p => (l, p) :: acc) := by
  simp only [Tables.checkLeaf, checkPlace]
  cases s.place base l with
  | error e => rfl
  | ok p => cases taken l <;> rfl

theorem checkPlace_error {s : Tables r N} {base : UInt64} {l : MapLeaf} {x : TableError}
    {taken : Bool} (h : s.place base l = .error x) : checkPlace s base l taken = .error x := by
  simp only [checkPlace, h, bind, Except.bind]

theorem checkPlace_taken {s : Tables r N} {base : UInt64} {l : MapLeaf} {p : Place}
    (h : s.place base l = .ok p) : checkPlace s base l true = .error .alreadyMapped := by
  simp only [checkPlace, h, bind, Except.bind, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]

theorem checkPlace_ok {s : Tables r N} {base : UInt64} {l : MapLeaf} {p : Place}
    (h : s.place base l = .ok p) : checkPlace s base l false = .ok p := by
  simp only [checkPlace, h, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]

/-! ## The count of new tables -/

/-- The slot of no leaf of the code, `NO_SLOT`, the largest 64-bit word. -/
def noSlot : Nat := 2 ^ 64 - 1

/-- A slot of the code, the first address `code` of a slot of `size` bytes or
`NO_SLOT`, against the key of one level of `Alloc` (a slot number with its
table): `NO_SLOT` for none; for a key, the address of a slot whose number,
read at the virtual address `off + code`, is the key. -/
def SlotRel (size off code : Nat) : Option (Nat × Nat) → Prop
  | none => code = noSlot
  | some (k, _) => code % size = 0 ∧ (off + code) / size = k

/-- The record of the new tables that the checks of the code keep, `next`,
the 1 GiB slot `gib` and the 2 MiB slot `slot` (physical addresses), against
the fold `a` of `Alloc.add` over the same leaves, whose virtual addresses are
`off` plus their physical addresses: the same next free index, and slots that
stand for the keys of its two levels. -/
def AllocRel (off next gib slot : Nat) (a : Alloc) : Prop :=
  a.next = next ∧ SlotRel GIB_SIZE off gib a.level2 ∧ SlotRel BLOCK_SIZE off slot a.level3

/-- How the checks of the code change the record `(next, gib, slot)` for a
leaf at the physical address `pa`, a block when `block`, of place `p`: a
leaf whose root entry is invalid takes the new level 2 table of its 1 GiB
slot unless the latest one is of that slot; a page whose root or level 2
entry is invalid takes the new level 3 table of its 2 MiB slot unless the
latest one is of that slot. -/
def countStep (block : Bool) (p : Place) (pa next gib slot : Nat) : Nat × Nat × Nat :=
  match p with
  | .root =>
    let g := pa / GIB_SIZE * GIB_SIZE
    let n := if g = gib then next else next + 1
    if block then (n, g, slot)
    else
      let b := pa / BLOCK_SIZE * BLOCK_SIZE
      (if b = slot then n else n + 1, g, b)
  | .level2 _ =>
    if block then (next, gib, slot)
    else
      let b := pa / BLOCK_SIZE * BLOCK_SIZE
      (if b = slot then next else next + 1, gib, b)
  | .level3 _ _ => (next, gib, slot)

/-- The record before the first leaf: the record `used` of the set and no
slot, against the empty fold. -/
theorem allocRel_init (off used : Nat) :
    AllocRel off used noSlot noSlot ⟨used, none, none, []⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- `countStep` adds at most two new tables. -/
theorem countStep_le (block : Bool) (p : Place) (pa next gib slot : Nat) :
    (countStep block p pa next gib slot).1 ≤ next + 2 := by
  unfold countStep
  cases p <;> cases block <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try split_ifs) <;> omega

/-- `countStep` takes no table back. -/
theorem countStep_ge (block : Bool) (p : Place) (pa next gib slot : Nat) :
    next ≤ (countStep block p pa next gib slot).1 := by
  unfold countStep
  cases p <;> cases block <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try split_ifs) <;> omega

private theorem slot_new {size off pa : Nat} (hs : 0 < size) (hoff : off % size = 0) (t : Nat) :
    SlotRel size off (pa / size * size) (some ((off + pa) / size, t)) := by
  refine ⟨Nat.mul_mod_left _ _, ?_⟩
  obtain ⟨c, rfl⟩ : size ∣ off := Nat.dvd_of_mod_eq_zero hoff
  rw [Nat.mul_comm size c, Nat.add_mul_div_right _ _ hs, Nat.add_comm (c * size) pa,
    Nat.add_mul_div_right _ _ hs, Nat.mul_div_cancel _ hs, Nat.add_comm]

private theorem slot_same_iff {size off pa code k t : Nat} (hs : 0 < size) (hoff : off % size = 0)
    (h : SlotRel size off code (some (k, t))) :
    pa / size * size = code ↔ k = (off + pa) / size := by
  obtain ⟨hc, hk⟩ := h
  obtain ⟨c, rfl⟩ : size ∣ off := Nat.dvd_of_mod_eq_zero hoff
  obtain ⟨d, rfl⟩ : size ∣ code := Nat.dvd_of_mod_eq_zero hc
  subst hk
  rw [Nat.mul_comm size c, Nat.mul_comm size d, ← Nat.add_mul, Nat.mul_div_cancel _ hs,
    Nat.add_comm (c * size) pa, Nat.add_mul_div_right _ _ hs]
  constructor
  · intro h
    have := Nat.eq_of_mul_eq_mul_right hs h
    omega
  · intro h
    have : pa / size = d := by omega
    rw [this]

private theorem slot_none_ne {size pa : Nat} (hs : size % 2 = 0) :
    pa / size * size ≠ noSlot := by
  intro h
  have : pa / size * size % 2 = 0 := by
    rw [Nat.mul_mod, hs, Nat.mul_zero, Nat.zero_mod]
  rw [h] at this
  simp [noSlot] at this

/-- One level of the record: the table of a slot from the cache of the latest
new table (`cacheStep`) keeps `SlotRel` for the slot of the leaf, and takes a
new table exactly when the slot of the code changes. -/
theorem cacheStep_rel {size off code pa next : Nat} {c : Option (Nat × Nat)} (hs : 0 < size)
    (hs2 : size % 2 = 0) (hoff : off % size = 0) (h : SlotRel size off code c) :
    SlotRel size off (pa / size * size) (cacheStep c ((off + pa) / size) next).2.1 ∧
      (cacheStep c ((off + pa) / size) next).2.2 =
        if pa / size * size = code then next else next + 1 := by
  cases c with
  | none =>
    have hne : pa / size * size ≠ code := by rw [show code = noSlot from h]; exact slot_none_ne hs2
    constructor
    · exact slot_new hs hoff next
    · simp only [cacheStep, hne, ↓reduceIte]
  | some kt =>
    obtain ⟨k, t⟩ := kt
    by_cases hk : k = (off + pa) / size
    · have hsame : pa / size * size = code := (slot_same_iff hs hoff h).2 hk
      constructor
      · simp only [cacheStep, hk, beq_self_eq_true, ↓reduceIte]
        rw [hsame, ← hk]; exact h
      · simp only [cacheStep, hk, beq_self_eq_true, ↓reduceIte, hsame]
    · have hne : pa / size * size ≠ code := fun e => hk ((slot_same_iff hs hoff h).1 e)
      have hbeq : (k == (off + pa) / size) = false := beq_eq_false_iff_ne.2 hk
      constructor
      · simp only [cacheStep, hbeq, Bool.false_eq_true, ↓reduceIte]
        exact slot_new hs hoff next
      · simp only [cacheStep, hbeq, Bool.false_eq_true, ↓reduceIte, hne]

/-- One leaf keeps `AllocRel`: the record that `countStep` gives stands for
the fold after `Alloc.add` of the leaf with its place, for a leaf whose
virtual address is `off` plus its physical address `pa`, `off` a multiple of
1 GiB, and whose form is that of `block`. -/
theorem allocRel_add {off next gib slot pa : Nat} {a : Alloc} {l : MapLeaf} {p : Place}
    {block : Bool} (h : AllocRel off next gib slot a) (hoff : off % GIB_SIZE = 0)
    (hva : l.va.toNat = off + pa) (hform : l.form = if block then .block else .page) :
    AllocRel off (countStep block p pa next gib slot).1 (countStep block p pa next gib slot).2.1
      (countStep block p pa next gib slot).2.2 (a.add (l, p)) := by
  have hoffB : off % BLOCK_SIZE = 0 := by
    simp only [GIB_SIZE, BLOCK_SIZE] at hoff ⊢; omega
  have hG : 0 < GIB_SIZE := by decide
  have hB : 0 < BLOCK_SIZE := by decide
  have hG2 : GIB_SIZE % 2 = 0 := by decide
  have hB2 : BLOCK_SIZE % 2 = 0 := by decide
  have hg : l.gibSlot = (off + pa) / GIB_SIZE := by simp only [MapLeaf.gibSlot, hva]
  have hb : l.blockSlot = (off + pa) / BLOCK_SIZE := by simp only [MapLeaf.blockSlot, hva]
  obtain ⟨hn, h2, h3⟩ := h
  subst hn
  rw [add_eq]
  cases p with
  | root =>
    obtain ⟨c2, e2⟩ := cacheStep_rel (pa := pa) (next := a.next) hG hG2 hoff h2
    rw [stage2_root, hg]
    cases block with
    | true =>
      simp only [hform, ↓reduceIte, stage3, countStep]
      exact ⟨e2, c2, h3⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hform
      rw [stage3_new _ _ _ hform (fun _ _ h => Place.noConfusion h), hb]
      obtain ⟨c3, e3⟩ := cacheStep_rel (pa := pa)
        (next := (cacheStep a.level2 ((off + pa) / GIB_SIZE) a.next).2.2) hB hB2 hoffB h3
      simp only [countStep, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, c2, c3⟩
      rw [e3, e2]
  | level2 t =>
    cases block with
    | true =>
      simp only [hform, ↓reduceIte, stage2, stage3, countStep]
      exact ⟨rfl, h2, h3⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hform
      simp only [stage2]
      rw [stage3_new _ _ _ hform (fun _ _ h => Place.noConfusion h), hb]
      obtain ⟨c3, e3⟩ := cacheStep_rel (pa := pa) (next := a.next) hB hB2 hoffB h3
      simp only [countStep, Bool.false_eq_true, ↓reduceIte]
      exact ⟨e3, h2, c3⟩
  | level3 t2 t3 =>
    cases block with
    | true =>
      simp only [hform, ↓reduceIte, stage2, stage3, countStep]
      exact ⟨rfl, h2, h3⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hform
      simp only [hform, stage2, stage3, countStep]
      exact ⟨rfl, h2, h3⟩

/-! ## The cursor of a map plan, on numbers -/

/-- The first address of the 1 GiB slot of a physical address. -/
def gibOf (pa : Nat) : Nat := pa / GIB_SIZE * GIB_SIZE

/-- The first address of the 2 MiB slot of a physical address. -/
def slotOf (pa : Nat) : Nat := pa / BLOCK_SIZE * BLOCK_SIZE

/-- No 2 MiB slot starts at `NO_SLOT`. -/
theorem slotOf_ne_noSlot (x : Nat) : slotOf x ≠ noSlot := slot_none_ne (by decide)

/-- No 1 GiB slot starts at `NO_SLOT`. -/
theorem gibOf_ne_noSlot (x : Nat) : gibOf x ≠ noSlot := slot_none_ne (by decide)

/-- The phases of the cursor of the code (`MapPhase`). -/
inductive CurPhase where
  | leaf | heldPages | newPages | newTable | children | entries | root | done
  deriving DecidableEq, Repr

/-- The cursor of the code (`MapCursor`) on numbers: its phase, the address
`frm` from which the next leaf is looked for, the next free table, the
1 GiB slot of the latest leaf, the 2 MiB slot of the pages that the cursor is
in, and the level 2 and level 3 tables. -/
structure Cur where
  phase : CurPhase
  frm : Nat
  next : Nat
  gib : Nat
  slot : Nat
  t2 : Nat
  t3 : Nat
  deriving DecidableEq, Repr

/-- A leaf that a search of the code found (`Leaf`), on numbers: its
physical address, its descriptor and whether it is a block. -/
structure Found where
  pa : Nat
  desc : UInt64
  block : Bool
  deriving DecidableEq, Repr

/-- What the cursor gives for the leaf that its search found (`MapTurn`): a
step, nothing more, or no step yet. -/
inductive Turn where
  | give (s : Step)
  | stop
  | seek
  deriving DecidableEq, Repr

/-- The place that the cursor reads for a leaf found: the place of the set,
or `root` where the walk fails, as the code reads it. -/
def placeOr (s : Tables r N) (base : UInt64) (f : Found) : Place :=
  match s.place base (placeProbe (UInt64.ofNat f.pa) f.block) with
  | .ok p => p
  | .error _ => .root

/-- The search of each phase (`MapCursor::search`): from `frm`, below the
limit, pages only when the flag holds; the limit 0 where the phase needs no
leaf. -/
def Cur.search (c : Cur) : Nat × Nat × Bool :=
  match c.phase with
  | .leaf | .heldPages => (c.frm, 2 ^ 64 - 1, false)
  | .newPages => (c.frm, c.slot + BLOCK_SIZE, false)
  | .children => (c.frm, c.gib + GIB_SIZE, true)
  | .entries => (c.frm, c.gib + GIB_SIZE, false)
  | .newTable | .root | .done => (c.frm, 0, false)

/-- `MapCursor::children`: under a new level 2 table, the store of a page of
the current 2 MiB slot, or the `Zero` of the new level 3 table of the slot of
the page; with no page left, `Zero` of the level 2 table, and its entries
come next. -/
def Cur.children (c : Cur) : Option Found → Step × Cur
  | none => (.zero c.t2, { c with phase := .entries, frm := c.gib, t3 := c.t2 + 1 })
  | some p =>
    if slotOf p.pa = c.slot then
      (.store c.t3 (index3 (UInt64.ofNat p.pa)) p.desc, { c with frm := p.pa + PAGE_SIZE })
    else
      (.zero c.next, { c with frm := p.pa, next := c.next + 1, slot := slotOf p.pa, t3 := c.next })

/-- `MapCursor::entry`: the entry of the level 2 table for the 2 MiB slot of
the leaf found, its block or the table descriptor of the next new level 3
table; `Fence` after the last. -/
def Cur.entry (base : UInt64) (c : Cur) : Option Found → Step × Cur
  | none => (.fence, { c with phase := .root })
  | some l =>
    if l.block then
      (.store c.t2 (index2 (UInt64.ofNat l.pa)) l.desc, { c with frm := slotOf l.pa + BLOCK_SIZE })
    else
      (.store c.t2 (index2 (UInt64.ofNat l.pa)) (tableAt base c.t3),
        { c with frm := slotOf l.pa + BLOCK_SIZE, t3 := c.t3 + 1 })

/-- `MapCursor::new_page`: the store of a page into the new level 3 table,
or `Fence` after the last. -/
def Cur.newPage (c : Cur) : Option Found → Step × Cur
  | none => (.fence, { c with phase := .newTable })
  | some p => (.store c.t3 (index3 (UInt64.ofNat p.pa)) p.desc, { c with frm := p.pa + PAGE_SIZE })

/-- `MapCursor::leaf`: the step of the first leaf of a 2 MiB slot from its
place; `Sync` after the last leaf. -/
def Cur.leaf (place : Found → Place) (c : Cur) : Option Found → Turn × Cur
  | none => (.give .sync, { c with phase := .done })
  | some l =>
    match place l with
    | .root =>
      let c1 : Cur := ⟨.children, l.pa, c.next + 1, gibOf l.pa, noSlot, c.next, c.t3⟩
      if l.block then (.seek, c1) else (.give (c1.children (some l)).1, (c1.children (some l)).2)
    | .level2 t2 =>
      if l.block then
        (.give (.store t2 (index2 (UInt64.ofNat l.pa)) l.desc),
          { c with frm := l.pa + BLOCK_SIZE, gib := gibOf l.pa, slot := slotOf l.pa, t2 := t2 })
      else
        (.give (.zero c.next),
          { phase := .newPages, frm := l.pa, next := c.next + 1, gib := gibOf l.pa,
            slot := slotOf l.pa, t2 := t2, t3 := c.next })
    | .level3 t2 t3 =>
      (.give (.store t3 (index3 (UInt64.ofNat l.pa)) l.desc),
        (⟨.heldPages, l.pa + PAGE_SIZE, c.next, gibOf l.pa, slotOf l.pa, t2, t3⟩ : Cur))

/-- `MapCursor::held_page`: the store of the next page of the slot into its
level 3 table of the set, or the step of `leaf` for a leaf of another slot or
none. -/
def Cur.heldPage (place : Found → Place) (c : Cur) : Option Found → Turn × Cur
  | some p =>
    if slotOf p.pa = c.slot then
      (.give (.store c.t3 (index3 (UInt64.ofNat p.pa)) p.desc), { c with frm := p.pa + PAGE_SIZE })
    else Cur.leaf place { c with phase := .leaf } (some p)
  | none => Cur.leaf place { c with phase := .leaf } none

/-- `MapCursor::take`: the next step of the plan from the leaf that the search
of the phase found. -/
def Cur.take (place : Found → Place) (base : UInt64) (c : Cur) (found : Option Found) :
    Turn × Cur :=
  match c.phase with
  | .leaf => c.leaf place found
  | .heldPages => c.heldPage place found
  | .newPages => (.give (c.newPage found).1, (c.newPage found).2)
  | .newTable =>
    (.give (.store c.t2 (index2 (UInt64.ofNat c.slot)) (tableAt base c.t3)),
      { c with phase := .leaf, frm := c.slot + BLOCK_SIZE })
  | .children => (.give (c.children found).1, (c.children found).2)
  | .entries => (.give (c.entry base found).1, (c.entry base found).2)
  | .root =>
    (.give (.store 0 (index1 (UInt64.ofNat c.gib)) (tableAt base c.t2)),
      { c with phase := .leaf, frm := c.gib + GIB_SIZE })
  | .done => (.stop, c)

/-- One call of the `next` of a map plan on numbers, with the leaf search
`find frm limit pages` of the map: the search of the phase, the step that
`take` gives for the leaf found, and on a `seek` the search of the cursor
after it and the step of `children`. -/
def Cur.step (find : Nat → Nat → Bool → Option Found) (place : Found → Place) (base : UInt64)
    (c : Cur) : Option Step × Cur :=
  let t := c.take place base (find c.search.1 c.search.2.1 c.search.2.2)
  match t.1 with
  | .give s => (some s, t.2)
  | .stop => (none, t.2)
  | .seek =>
    (some (t.2.children (find t.2.search.1 t.2.search.2.1 t.2.search.2.2)).1,
      (t.2.children (find t.2.search.1 t.2.search.2.1 t.2.search.2.2)).2)

/-! ## The plan by runs -/

section Runs

variable {α : Type}

/-- The first run of a nonempty list starts with its head. -/
theorem runsBy_cons_head (key : α → Nat) (s : α) (S : List α) :
    ∃ run runs, runsBy key (s :: S) = (s :: run) :: runs := by
  simp only [runsBy]
  split
  · rename_i y run runs _
    split
    · exact ⟨y :: run, runs, rfl⟩
    · exact ⟨[], (y :: run) :: runs, rfl⟩
  · exact ⟨[], _, rfl⟩

/-- A run of one key followed by a list that starts with another key is the
first run of the whole. -/
theorem runsBy_append_run (key : α → Nat) (S : List α) :
    ∀ (x : α) (R : List α), (∀ y ∈ R, key y = key x) → (∀ y ∈ S.head?, key y ≠ key x) →
      runsBy key ((x :: R) ++ S) = (x :: R) :: runsBy key S
  | x, [], _, hS => by
    cases S with
    | nil => rfl
    | cons s S' =>
      obtain ⟨run, runs, h⟩ := runsBy_cons_head key s S'
      have hne : (key x == key s) = false :=
        beq_eq_false_iff_ne.2 (fun e => hS s rfl e.symm)
      rw [List.cons_append, List.nil_append, runsBy.eq_2 key x (s :: S'), h]
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
  | x, r :: R, hR, hS => by
    have ih := runsBy_append_run key S r R
      (fun y hy => (hR y (List.mem_cons_of_mem r hy)).trans (hR r List.mem_cons_self).symm)
      (fun y hy e => hS y hy (e.trans (hR r List.mem_cons_self)))
    have hxr : (key x == key r) = true := beq_iff_eq.2 (hR r List.mem_cons_self).symm
    simp only [List.cons_append] at ih ⊢
    rw [runsBy.eq_2 key x (r :: (R ++ S)), ih]
    simp only [hxr, ↓reduceIte]

end Runs

/-- `mapPlan` of placed leaves that start with a whole 1 GiB run: the steps
of that run, then `mapPlan` of the rest. -/
theorem mapPlan_append_run (base : UInt64) (q : Placed) (R S : List Placed)
    (hR : ∀ y ∈ R, y.leaf.gibSlot = q.leaf.gibSlot)
    (hS : ∀ y ∈ S.head?, y.leaf.gibSlot ≠ q.leaf.gibSlot) :
    mapPlan base ((q :: R) ++ S) = runSteps base (q :: R) ++ mapPlan base S := by
  rw [mapPlan_eq, mapPlan_eq, runsBy_append_run (·.leaf.gibSlot) S q R hR hS, List.flatMap_cons,
    List.append_assoc]

/-- The steps of a 1 GiB run under a level 2 table of the set, by its 2 MiB
runs. -/
theorem runSteps_held (base : UInt64) (q : Placed) (R : List Placed) (h : q.new2 = false) :
    runSteps base (q :: R) = (runsBy (·.leaf.blockSlot) (q :: R)).flatMap (heldLevel2Steps base) := by
  simp only [runSteps, h, Bool.false_eq_true, ↓reduceIte]

/-- The steps of a 1 GiB run under a new level 2 table. -/
theorem runSteps_new (base : UInt64) (q : Placed) (R : List Placed) (h : q.new2 = true) :
    runSteps base (q :: R) = newLevel2Steps base (q :: R) := by
  simp only [runSteps, h, ↓reduceIte]

end Krepi.Proofs.PageTables.Refinement
