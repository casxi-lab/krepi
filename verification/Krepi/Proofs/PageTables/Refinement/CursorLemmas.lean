module

public import Krepi.Statements.PageTables.Representation
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.CursorSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the checks and the cursor of the boot maps

The triples of the generated functions of `boot.rs` that `kernel_map` and
`direct_map` share, each a `@[step]` lemma, so that the proof of a caller
steps over the call with the triple of the callee. They take the leaf that a
search found as an argument, so that both maps use them with their own leaf
search, and they hold without the premise `Usize64`.

- Words of the code: `no_slot_val`, `no_limit_val`, `and_not_val` (a mask
  `~~~(2 ^ k - 1)` clears the low bits), `u64_bne_iff`, `u64_not_bne_iff`,
  and `eq_ok_of_continue` (the value of a callee on the branch `Continue` of
  the `?` operator).
- The place of a leaf: `placeOf` (a place of the code as that of the
  specification) and `boot_place_spec` (`Tables::place`, the place of the
  leaf at the physical address that the code walks, `placeProbe`, for a pool
  of at least one table).
- The checks of a map: `map_check_new_spec`, `map_check_passed_spec`,
  `check_leaf_spec` (`check_leaf`: `checkPlace` for the error, and the count
  of new tables after `countStep`, for a count at least 2 below the largest
  `usize`) and `write_phase_spec` (`write_phase`: `OutOfTables` as
  `Tables.mapLeaves` tests it, else `startCursor` and the set whose record
  is the record before plus the count of the checks).
- The cursor on numbers (`Cur` of `CursorSpecLemmas`): `phaseOf`, `curOf`,
  `foundOf`, `turnOf`, `FoundLow` (the leaves found lie below `2 ^ 39`),
  `gib_mask_val`, `slot_mask_val`, `placeCode` and `placeOr_of_agrees` (the
  place that the cursor reads), `curOf_phase`, `curOf_leaf`, `CurFits` (the
  tables and slots of a cursor whose next step does not overflow); and the
  triples of `MapCursor`, each against its function on `Cur`: `search_spec`,
  `children_spec`, `new_page_spec`, `entry_spec`, `leaf_spec`,
  `held_page_spec` and `take_spec`. The ones that can take a new table ask
  that the next free table after the call fit in `usize`, which asks for room
  only on the branches that take a table.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Constants and masks -/

theorem no_slot_val : page_tables.boot.NO_SLOT.val = noSlot := by
  unfold page_tables.boot.NO_SLOT; rfl

theorem no_limit_val : page_tables.boot.NO_LIMIT.val = 2 ^ 64 - 1 := by
  unfold page_tables.boot.NO_LIMIT; rfl

/-- A 64-bit word with its bits below bit `k` cleared by the mask
`~~~(2 ^ k - 1)` of the code. -/
theorem and_not_val (x m : U64) {k : Nat} (hm : m.val = 2 ^ k - 1) (hk : k ≤ 64) :
    (x &&& ~~~m).val = x.val / 2 ^ k * 2 ^ k := by
  rw [← word64_toNat, word64_and, word64_not, UInt64.toNat_and, UInt64.toNat_not, word64_toNat,
    word64_toNat, hm]
  exact and_high_bits (u64_lt x) hk

/-- Two words of the code differ exactly when their values do. -/
theorem u64_bne_iff (x y : U64) : (x != y) = true ↔ x.val ≠ y.val := by
  rw [bne_iff_ne, ne_eq, ne_eq]
  exact ⟨fun h h' => h (UScalar.eq_of_val_eq h'), fun h h' => h (h' ▸ rfl)⟩

theorem u64_not_bne_iff (x y : U64) : ¬ (x != y) = true ↔ x.val = y.val := by
  rw [u64_bne_iff, not_not]

/-- On the branch `Continue v` of the `?` operator, a callee whose result
agrees through a function `f` gives the specification the value `f v`. -/
theorem eq_ok_of_continue {α β ε ε' : Type} {f : α → β} {err : ε → ε'}
    {r : core.result.Result α ε} {E : Except ε' β}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α} {v : α}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Continue v)
    (hr : Agrees (fun a b => f a = b) err r E) : E = .ok (f v) := by
  obtain ⟨b, hb, hb'⟩ := agrees_ok_iff.1 (agrees_of_branch_ok h hc hr)
  rw [hb, hb']

/-! ## The place of a leaf -/

/-- The place of a leaf of the code as that of the specification. -/
def placeOf : page_tables.boot.LeafPlace → Place
  | .Root => .root
  | .Level2 t2 => .level2 t2.val
  | .Level3 t2 t3 => .level3 t2.val t3.val

/-- `Tables::place(base, pa, block)` on a pool of at least one table: the
place of the leaf of the form of `block` at the physical address `pa`
(`placeProbe`), with its error. -/
@[step] theorem boot_place_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (base pa : U64) (block : Bool) (hN : 0 < N.val) :
    page_tables.boot.Tables.place s base pa block ⦃ r =>
      Agrees (fun p P => placeOf p = P) tableErrorOf r
        ((tablesOf s).place (word64 base) (placeProbe (word64 pa) block)) ⦄ := by
  unfold page_tables.boot.Tables.place
  have hpf : ∀ b, (placeProbe (word64 pa) b).va = word64 pa := fun _ => rfl
  step*
  · have hw := agrees_of_branch_ok cf_post ‹_› r_post
    rw [‹val = none›, agrees_ok_iff] at hw
    obtain ⟨w, hw, hw'⟩ := hw
    have hw2 : (tablesOf s).walk2 (word64 base) (placeProbe (word64 pa) block).va =
        .ok none := by rw [hpf, hw, ← hw']; rfl
    rw [place_walk_root hw2]
    rfl
  · have hw := agrees_of_branch_ok cf_post ‹_› r_post
    rw [‹val = some found›, agrees_ok_iff] at hw
    obtain ⟨w, hw, hw'⟩ := hw
    obtain ⟨t, e⟩ := found
    replace hw : ∀ b, (tablesOf s).walk2 (word64 base) (placeProbe (word64 pa) b).va =
        .ok (some (t.val, word64 e)) := fun _ => by
      rw [hpf, hw, ← hw']; rfl
    clear hw'
    step*
    · -- valid entry of type BLOCK
      have hb : typeBits (word64 e) = BLOCK := by
        rw [← i_post, ‹i = page_tables.encoding.BLOCK›, word64_block]
      rw [place_walk_block (hw _) (by rw [← b_post]; exact ‹b = true›) hb]
      rfl
    · -- no table in use under the entry
      have hb : typeBits (word64 e) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 e) = none := by
        rw [← o_post, ‹o = none›]; rfl
      rw [place_walk_backing (hw _) (by rw [← b_post]; exact ‹b = true›) hb hc]
      rfl
    · -- the goal of `massert`
      have hc := o_post
      rw [‹o = some child›, Option.map_some] at hc
      have h1 : child.val < N.val := child?_lt hc.symm
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr h1
    · -- a block under a table: covered
      have hb : typeBits (word64 e) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 e) = some child.val := by
        rw [← o_post, ‹o = some child›]; rfl
      rw [place_walk_covered (hw _) (by rw [← b_post]; exact ‹b = true›) hb hc rfl]
      rfl
    · -- a page whose level 3 entry is valid
      subst a_post i2_post
      have hb : typeBits (word64 e) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 e) = some child.val := by
        rw [← o_post, ‹o = some child›]; rfl
      have h1 : child.val < N.val := child?_lt hc
      have h3 : isValid ((tablesOf s).entry child.val (index3 (placeProbe (word64 pa) false).va)) =
          true := by
        rw [hpf, ← i1_post, tablesOf_entry s (by scalar_tac) (by scalar_tac), ← b1_post]
        exact ‹b1 = true›
      rw [place_walk_mapped (hw _) (by rw [← b_post]; exact ‹b = true›) hb hc rfl h3]
      rfl
    · -- a page whose level 3 entry is free
      subst a_post i2_post
      have hb : typeBits (word64 e) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 e) = some child.val := by
        rw [← o_post, ‹o = some child›]; rfl
      have h1 : child.val < N.val := child?_lt hc
      have h3 : isValid ((tablesOf s).entry child.val (index3 (placeProbe (word64 pa) false).va)) =
          false := by
        rw [hpf, ← i1_post, tablesOf_entry s (by scalar_tac) (by scalar_tac), ← b1_post]
        simpa using ‹¬b1 = true›
      rw [place_walk_level3 (hw _) (by rw [← b_post]; exact ‹b = true›) hb hc rfl h3]
      rfl
    · -- an invalid level 2 entry
      rw [place_walk_invalid (hw _) (by rw [← b_post]; simpa using ‹¬b = true›)]
      rfl
  · have hw : (tablesOf s).walk2 (word64 base) (placeProbe (word64 pa) block).va = _ :=
      agrees_err_of_branch cf_post ‹_› residual_post ‹_›
    rw [place_walk_error hw, r_post, e_post]
    rfl

/-! ## The checks of a map -/

/-- `MapCheck::new()`: nothing checked, no range before, no new table and no
slot. -/
@[step] theorem map_check_new_spec :
    page_tables.boot.MapCheck.new ⦃ c =>
      c.reach.val = 0 ∧ c.new_tables.val = 0 ∧ c.gib.val = noSlot ∧ c.slot.val = noSlot ⦄ := by
  unfold page_tables.boot.MapCheck.new
  exact spec_of_eq rfl ⟨rfl, rfl, no_slot_val, no_slot_val⟩

/-- `MapCheck::passed(end)`: the end of the ranges checked becomes the larger
of the two ends. -/
@[step] theorem map_check_passed_spec (c : page_tables.boot.MapCheck) (e : U64) :
    page_tables.boot.MapCheck.passed c e ⦃ c' =>
      c'.reach.val = max c.reach.val e.val ∧ c'.new_tables = c.new_tables ∧ c'.gib = c.gib ∧
        c'.slot = c.slot ⦄ := by
  unfold page_tables.boot.MapCheck.passed
  step*
  · have : c.reach.val < e.val := ‹e > c.reach›
    simp only [Nat.max_eq_right (Nat.le_of_lt this)]
  · have : e.val ≤ c.reach.val := by have := ‹¬e > c.reach›; scalar_tac
    simp only [Nat.max_eq_left this]

/-- `check_leaf(set, base, check, pa, block, guard)` on a pool of at least one
table, for a count of new tables at least 2 below the largest `usize`: the
check of the leaf of the form of `block` at `pa` (`checkPlace`), taken when
`pa` is below the end `reach` of the ranges before or `guard` holds; on
success the count after `countStep` of its place, with the same `reach`. -/
@[step] theorem check_leaf_spec {N : Usize} {upper : Bool} (set : page_tables.Tables N upper)
    (base : U64) (check : page_tables.boot.MapCheck) (pa : U64) (block guard : Bool)
    (hN : 0 < N.val) (hn : check.new_tables.val + 2 ≤ Usize.max) :
    page_tables.boot.check_leaf set base check pa block guard ⦃ r c =>
      Agrees (fun _ p => c.reach = check.reach ∧
          (c.new_tables.val, c.gib.val, c.slot.val) =
            countStep block p pa.val check.new_tables.val check.gib.val check.slot.val)
        tableErrorOf r
        (checkPlace (tablesOf set) (word64 base) (placeProbe (word64 pa) block)
          (decide (pa.val < check.reach.val) || guard)) ⦄ := by
  unfold page_tables.boot.check_leaf
  simp only [gib_size_eq, block_size_eq]
  step*
  · -- below the end of the ranges before
    have hp := eq_ok_of_continue cf_post ‹_› r_post
    have htk : (decide (pa.val < check.reach.val) || guard) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl ‹pa < check.reach›
    rw [htk, checkPlace_taken hp]; rfl
  · -- a guard page
    have hp := eq_ok_of_continue cf_post ‹_› r_post
    rw [Bool.or_true, checkPlace_taken hp]; rfl
  · -- the root entry is invalid
    have hp := eq_ok_of_continue cf_post ‹_› r_post
    have hr : ¬ pa.val < check.reach.val := ‹¬pa < check.reach›
    rw [Bool.or_false, decide_eq_false hr, checkPlace_ok hp, ‹val = _›]
    have hg : gib.val = pa.val / 2 ^ 30 * 2 ^ 30 := by
      rw [gib_post, i2_post, and_not_val pa i1 (k := 30) (by rw [i1_post]; rfl) (by decide)]
    split
    · step*
      all_goals
        have hne : gib.val ≠ check.gib.val := (u64_bne_iff gib check.gib).1 ‹_›
        simp only [placeOf, countStep, GIB_SIZE, BLOCK_SIZE, Nat.reducePow] at hg ⊢
        simp only [← hg, hne, ↓reduceIte, Bool.false_eq_true, agrees_ok_ok]
      · rw [x_post]
      · have hs : slot.val = pa.val / 2097152 * 2097152 := by
          rw [slot_post, i6_post, and_not_val pa i5 (k := 21) (by rw [i5_post]; rfl) (by decide)]; rfl
        have hne' : slot.val ≠ check.slot.val := (u64_bne_iff slot check.slot).1 ‹_›
        simp only [← hs, hne', ↓reduceIte, i7_post, x_post]
      · have hs : slot.val = pa.val / 2097152 * 2097152 := by
          rw [slot_post, i6_post, and_not_val pa i5 (k := 21) (by rw [i5_post]; rfl) (by decide)]; rfl
        have heq : slot.val = check.slot.val := (u64_not_bne_iff slot check.slot).1 ‹_›
        simp only [← hs, heq, ↓reduceIte, x_post]
    · step*
      all_goals
        have heq : gib.val = check.gib.val := (u64_not_bne_iff gib check.gib).1 ‹_›
        simp only [placeOf, countStep, GIB_SIZE, BLOCK_SIZE, Nat.reducePow] at hg ⊢
        simp only [← hg, heq, ↓reduceIte, Bool.false_eq_true, agrees_ok_ok]
      · have hs : slot.val = pa.val / 2097152 * 2097152 := by
          rw [slot_post, i6_post, and_not_val pa i5 (k := 21) (by rw [i5_post]; rfl) (by decide)]; rfl
        have hne' : slot.val ≠ check.slot.val := (u64_bne_iff slot check.slot).1 ‹_›
        simp only [← hs, hne', ↓reduceIte, i7_post]
      · have hs : slot.val = pa.val / 2097152 * 2097152 := by
          rw [slot_post, i6_post, and_not_val pa i5 (k := 21) (by rw [i5_post]; rfl) (by decide)]; rfl
        have heq' : slot.val = check.slot.val := (u64_not_bne_iff slot check.slot).1 ‹_›
        simp only [← hs, heq', ↓reduceIte]
  · -- a block under a level 2 table of the set
    have hp := eq_ok_of_continue cf_post ‹_› r_post
    have hr : ¬ pa.val < check.reach.val := ‹¬pa < check.reach›
    subst ‹block = true›
    rw [Bool.or_false, decide_eq_false hr, checkPlace_ok hp, ‹val = _›]
    simp only [placeOf, countStep, ↓reduceIte, agrees_ok_ok]
  · -- a page under a level 2 table of the set, in a new 2 MiB slot
    have hp := eq_ok_of_continue cf_post ‹_› r_post
    have hr : ¬ pa.val < check.reach.val := ‹¬pa < check.reach›
    have hb : block = false := by simpa using ‹¬block = true›
    subst hb
    rw [Bool.or_false, decide_eq_false hr, checkPlace_ok hp, ‹val = _›]
    have hs : slot.val = pa.val / 2097152 * 2097152 := by
      rw [slot_post, i1_post, and_not_val pa i (k := 21) (by rw [i_post]; rfl) (by decide)]; rfl
    have hne : slot.val ≠ check.slot.val := (u64_bne_iff slot check.slot).1 ‹_›
    simp only [placeOf, countStep, BLOCK_SIZE, Bool.false_eq_true, ↓reduceIte, agrees_ok_ok]
    simp only [← hs, hne, ↓reduceIte, i2_post]
  · -- a page under a level 2 table of the set, in the same 2 MiB slot
    have hp := eq_ok_of_continue cf_post ‹_› r_post
    have hr : ¬ pa.val < check.reach.val := ‹¬pa < check.reach›
    have hb : block = false := by simpa using ‹¬block = true›
    subst hb
    rw [Bool.or_false, decide_eq_false hr, checkPlace_ok hp, ‹val = _›]
    have hs : slot.val = pa.val / 2097152 * 2097152 := by
      rw [slot_post, i1_post, and_not_val pa i (k := 21) (by rw [i_post]; rfl) (by decide)]; rfl
    have heq : slot.val = check.slot.val := (u64_not_bne_iff slot check.slot).1 ‹_›
    simp only [placeOf, countStep, BLOCK_SIZE, Bool.false_eq_true, ↓reduceIte, agrees_ok_ok]
    simp only [← hs, heq, ↓reduceIte]
  · -- a page under a level 3 table of the set
    have hp := eq_ok_of_continue cf_post ‹_› r_post
    have hr : ¬ pa.val < check.reach.val := ‹¬pa < check.reach›
    rw [Bool.or_false, decide_eq_false hr, checkPlace_ok hp, ‹val = _›]
    simp only [placeOf, countStep, agrees_ok_ok]
  · -- the error of the place
    have hE := agrees_err_of_branch cf_post ‹_› residual_post r_post
    rw [checkPlace_error hE, r1_post, e_post]
    rfl

/-- The cursor of a map plan before its first leaf, on a set of `used`
tables in use: the phase `Leaf` from address 0, the next free table `used`,
no slot. -/
def startCursor (used : Usize) : page_tables.boot.MapCursor :=
  { phase := .Leaf, «from» := 0#u64, next := used, gib := page_tables.boot.NO_SLOT,
    slot := page_tables.boot.NO_SLOT, t2 := 0#usize, t3 := 0#usize }

/-- `write_phase(set, check)`: `OutOfTables` and the set unchanged when the
free tables are fewer than the new tables that the checks counted, as
`Tables.mapLeaves` tests it; else the cursor before the first leaf and the
set whose record is the record before plus that count. The sum does not
overflow: the count is 0 when the record is at or above `N`, and the sum is
at most `N` otherwise. -/
@[step] theorem write_phase_spec {N : Usize} {upper : Bool} (set : page_tables.Tables N upper)
    (check : page_tables.boot.MapCheck) :
    page_tables.boot.write_phase set check ⦃ r s' =>
      if N.val - set.used.val < check.new_tables.val then r = .Err .OutOfTables ∧ s' = set
      else r = .Ok (startCursor set.used) ∧ s'.pool = set.pool ∧
        s'.used.val = set.used.val + check.new_tables.val ⦄ := by
  unfold page_tables.boot.write_phase
  step*
  · -- the sum fits: the count is at most the free tables
    have h1 : ¬ i.val < check.new_tables.val := ‹¬i < check.new_tables›
    scalar_tac
  · have hlt : ¬ N.val - set.used.val < check.new_tables.val := by
      rw [← i_post]; exact ‹¬i < check.new_tables›
    simp only [hlt, ↓reduceIte]
    exact ⟨rfl, i1_post⟩

/-! ## The cursor -/

/-- A phase of the cursor of the code as a phase on numbers. -/
def phaseOf : page_tables.boot.MapPhase → CurPhase
  | .Leaf => .leaf
  | .HeldPages => .heldPages
  | .NewPages => .newPages
  | .NewTable => .newTable
  | .Children => .children
  | .Entries => .entries
  | .Root => .root
  | .Done => .done

/-- The cursor of the code on numbers. -/
def curOf (c : page_tables.boot.MapCursor) : Cur :=
  ⟨phaseOf c.phase, c.from.val, c.next.val, c.gib.val, c.slot.val, c.t2.val, c.t3.val⟩

/-- A leaf that a search of the code found, on numbers. -/
def foundOf (found : Option page_tables.boot.Leaf) : Option Found :=
  found.map fun l => ⟨l.pa.val, word64 l.desc, l.block⟩

/-- A turn of the cursor of the code with its step of the specification. -/
def turnOf : page_tables.boot.MapTurn → Turn
  | .Give s => .give (stepOf s)
  | .End => .stop
  | .Seek => .seek

/-- The leaves that a search found lie below `2 ^ 39`, as every leaf of a map
whose checks passed does. -/
def FoundLow (found : Option page_tables.boot.Leaf) : Prop :=
  ∀ l, found = some l → l.pa.val < 2 ^ 39

theorem gib_mask_val (pa i1 i2 : U64) (h1 : i1.val = 1073741824 - 1) (h2 : i2 = ~~~i1) :
    (pa &&& i2).val = gibOf pa.val := by
  rw [h2, and_not_val pa i1 (k := 30) (by rw [h1]; rfl) (by decide)]; rfl

theorem slot_mask_val (pa i1 i2 : U64) (h1 : i1.val = 2097152 - 1) (h2 : i2 = ~~~i1) :
    (pa &&& i2).val = slotOf pa.val := by
  rw [h2, and_not_val pa i1 (k := 21) (by rw [h1]; rfl) (by decide)]; rfl

/-- `MapCursor::search()`: `Cur.search`, for a 2 MiB slot and a 1 GiB slot
whose ends fit in 64 bits where the phase reads them. -/
@[step] theorem search_spec (c : page_tables.boot.MapCursor)
    (hs : c.phase = .NewPages → c.slot.val + 2 ^ 21 < 2 ^ 64)
    (hg : c.phase = .Children ∨ c.phase = .Entries → c.gib.val + 2 ^ 30 < 2 ^ 64) :
    page_tables.boot.MapCursor.search c ⦃ x =>
      (x.1.val, x.2.1.val, x.2.2) = (curOf c).search ⦄ := by
  unfold page_tables.boot.MapCursor.search
  simp only [gib_size_eq, block_size_eq]
  cases hp : c.phase
  all_goals simp only [Cur.search, curOf, phaseOf, hp, BLOCK_SIZE, GIB_SIZE]
  · exact spec_of_eq rfl (by rw [no_limit_val])
  · exact spec_of_eq rfl (by rw [no_limit_val])
  · have := hs hp
    step*
  · exact spec_of_eq rfl rfl
  · have := hg (Or.inl hp)
    step*
  · have := hg (Or.inr hp)
    step*
  · exact spec_of_eq rfl rfl
  · exact spec_of_eq rfl rfl

/-- `MapCursor::children(found)`: `Cur.children`, for a leaf found below
`2 ^ 39`, a level 2 table that can be incremented, and a next free table after
the call that fits in `usize` (the call takes a table for a page in another
2 MiB slot). -/
@[step] theorem children_spec (c : page_tables.boot.MapCursor) (found : Option page_tables.boot.Leaf)
    (hf : FoundLow found) (hn : ((curOf c).children (foundOf found)).2.next ≤ Usize.max)
    (ht2 : c.t2.val + 1 ≤ Usize.max) :
    page_tables.boot.MapCursor.children c found ⦃ s c' =>
      stepOf s = ((curOf c).children (foundOf found)).1 ∧
        curOf c' = ((curOf c).children (foundOf found)).2 ⦄ := by
  unfold page_tables.boot.MapCursor.children
  simp only [block_size_eq, page_size_eq]
  cases found with
  | none =>
    step*
    exact ⟨rfl, by simp only [curOf, phaseOf, foundOf, Option.map_none, Cur.children, i_post]⟩
  | some p =>
    have hp := hf p rfl
    have hn' : slotOf p.pa.val ≠ c.slot.val → c.next.val + 1 ≤ Usize.max := fun h => by
      simpa only [foundOf, Option.map_some, curOf, Cur.children, h, ↓reduceIte] using hn
    step*
    · have hs : slotOf p.pa.val = c.slot.val := by
        rw [← slot_mask_val p.pa i i1 i_post i1_post, ← slot_post, ‹slot = c.slot›]
      simp only [foundOf, Option.map_some, curOf, Cur.children, hs, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simp only [stepOf, i3_post]; rfl
      · simp only [i2_post, PAGE_SIZE]
    · have hs : slotOf p.pa.val ≠ c.slot.val := by
        rw [← slot_mask_val p.pa i i1 i_post i1_post, ← slot_post]
        exact fun h => ‹¬slot = c.slot› (UScalar.eq_of_val_eq h)
      exact hn' hs
    · have hs : slotOf p.pa.val ≠ c.slot.val := by
        rw [← slot_mask_val p.pa i i1 i_post i1_post, ← slot_post]
        exact fun h => ‹¬slot = c.slot› (UScalar.eq_of_val_eq h)
      simp only [foundOf, Option.map_some, curOf, Cur.children, hs, ↓reduceIte]
      refine ⟨rfl, ?_⟩
      simp only [i2_post, slot_post, slot_mask_val p.pa i i1 i_post i1_post]

/-- `MapCursor::new_page(found)`: `Cur.newPage`, for a leaf found below
`2 ^ 39`. -/
@[step] theorem new_page_spec (c : page_tables.boot.MapCursor) (found : Option page_tables.boot.Leaf)
    (hf : FoundLow found) :
    page_tables.boot.MapCursor.new_page c found ⦃ s c' =>
      stepOf s = ((curOf c).newPage (foundOf found)).1 ∧
        curOf c' = ((curOf c).newPage (foundOf found)).2 ⦄ := by
  unfold page_tables.boot.MapCursor.new_page
  simp only [page_size_eq]
  cases found with
  | none =>
    step*
    exact ⟨rfl, rfl⟩
  | some p =>
    have hp := hf p rfl
    step*
    simp only [foundOf, Option.map_some, curOf, Cur.newPage]
    refine ⟨?_, ?_⟩
    · simp only [stepOf, i1_post]; rfl
    · simp only [i_post, PAGE_SIZE]

/-- `MapCursor::entry(base, found)`: `Cur.entry`, for a leaf found below
`2 ^ 39`, a level 3 table whose address fits in 64 bits and a next level 3
table that does not overflow. -/
@[step] theorem entry_spec (c : page_tables.boot.MapCursor) (base : U64)
    (found : Option page_tables.boot.Leaf) (hf : FoundLow found)
    (ht3 : c.t3.val + 1 ≤ Usize.max) (hb : base.val + 4096 * c.t3.val < 2 ^ 64) :
    page_tables.boot.MapCursor.entry c base found ⦃ s c' =>
      stepOf s = ((curOf c).entry (word64 base) (foundOf found)).1 ∧
        curOf c' = ((curOf c).entry (word64 base) (foundOf found)).2 ⦄ := by
  unfold page_tables.boot.MapCursor.entry
  simp only [block_size_eq]
  cases found with
  | none =>
    step*
    exact ⟨rfl, rfl⟩
  | some l =>
    have hp := hf l rfl
    have hs : slotOf l.pa.val < 2 ^ 39 := by simp only [slotOf, BLOCK_SIZE]; omega
    step*
    · have hi2 : i2.val = slotOf l.pa.val := by rw [i2_post, slot_mask_val l.pa i i1 i_post i1_post]
      simp only [slotOf, BLOCK_SIZE] at hi2 hs
      scalar_tac
    · have hi2 : i2.val = slotOf l.pa.val := by rw [i2_post, slot_mask_val l.pa i i1 i_post i1_post]
      simp only [foundOf, Option.map_some, curOf, Cur.entry, ‹l.block = true›, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simp only [stepOf, i4_post]; rfl
      · simp only [i3_post, hi2, BLOCK_SIZE]
    · have hi2 : i2.val = slotOf l.pa.val := by rw [i2_post, slot_mask_val l.pa i i1 i_post i1_post]
      have hbl : l.block = false := by simpa using ‹¬l.block = true›
      simp only [foundOf, Option.map_some, curOf, Cur.entry, hbl, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simp only [stepOf, i6_post, entry_post, i5_post1, tableAt]; rfl
      · simp only [i3_post, hi2, i4_post, BLOCK_SIZE]

/-- The place that the cursor of the code reads from the result of
`Tables::place`: the place, or `Root` for an error. -/
def placeCode : core.result.Result page_tables.boot.LeafPlace page_tables.TableError →
    page_tables.boot.LeafPlace
  | .Ok p => p
  | .Err _ => .Root

/-- `placeOr` is the place that the code reads from a result of
`Tables::place` that agrees with the place of the specification. -/
theorem placeOr_of_agrees {N : Nat} {r : Region} {s : Tables r N} {base : UInt64} {f : Found}
    {res : core.result.Result page_tables.boot.LeafPlace page_tables.TableError}
    (h : Agrees (fun p P => placeOf p = P) tableErrorOf res
      (s.place base (placeProbe (UInt64.ofNat f.pa) f.block))) :
    placeOr s base f = placeOf (placeCode res) := by
  unfold placeOr
  cases res with
  | Ok p => obtain ⟨P, hP, hp⟩ := agrees_ok_iff.1 h; rw [hP, ← hp]; rfl
  | Err e => rw [agrees_err_iff.1 h]; rfl

/-- `MapCursor::leaf(set, base, found)` on a pool of at least one table:
`Cur.leaf` with the place that the cursor reads (`placeOr`), for a leaf found
below `2 ^ 39` and a next free table after the call that fits in `usize`
(the call takes one or two tables for a leaf whose root or level 2 entry is
invalid). -/
@[step] theorem leaf_spec {N : Usize} {upper : Bool} (c : page_tables.boot.MapCursor)
    (set : page_tables.Tables N upper) (base : U64) (found : Option page_tables.boot.Leaf)
    (hN : 0 < N.val) (hf : FoundLow found)
    (hn : ((curOf c).leaf (placeOr (tablesOf set) (word64 base)) (foundOf found)).2.next ≤
      Usize.max) :
    page_tables.boot.MapCursor.leaf c set base found ⦃ t c' =>
      turnOf t = ((curOf c).leaf (placeOr (tablesOf set) (word64 base)) (foundOf found)).1 ∧
        curOf c' = ((curOf c).leaf (placeOr (tablesOf set) (word64 base)) (foundOf found)).2 ⦄ := by
  unfold page_tables.boot.MapCursor.leaf
  simp only [gib_size_eq, block_size_eq, page_size_eq]
  cases found with
  | none =>
    step*
    exact ⟨rfl, rfl⟩
  | some l =>
    have hp := hf l rfl
    step*
    have hpo := placeOr_of_agrees (f := ⟨l.pa.val, word64 l.desc, l.block⟩) r_post
    clear r_post
    simp only [foundOf, Option.map_some] at hn
    simp only [foundOf, Option.map_some, Cur.leaf, hpo]
    cases r with
    | Ok q =>
      simp only [placeCode, bind_ok]
      cases q with
      | Root =>
        rw [leaf_next_root hpo] at hn
        have h1 : c.next.val + 1 ≤ Usize.max := by simp only [curOf] at hn; split at hn <;> omega
        step*
        · refine ⟨rfl, ?_⟩
          simp only [placeOf, curOf, phaseOf, i7_post, i3_post,
            gib_mask_val l.pa i1 i2 i1_post i2_post, no_slot_val]
        · have hb : l.block = false := by simpa using ‹¬l.block = true›
          simp only [curOf, hb, Bool.false_eq_true, ↓reduceIte] at hn
          simp only [curOf, foundOf, Option.map_some, Cur.children, no_slot_val, slotOf_ne_noSlot,
            ↓reduceIte, i7_post]
          omega
        · have hc1 : curOf ⟨.Children, l.pa, i7, i3, page_tables.boot.NO_SLOT, c.next, c.t3⟩ =
              ⟨.children, l.pa.val, c.next.val + 1, gibOf l.pa.val, noSlot, c.next.val, c.t3.val⟩ := by
            simp only [curOf, phaseOf, i7_post, i3_post, gib_mask_val l.pa i1 i2 i1_post i2_post,
              no_slot_val]
          have hb : l.block = false := by simpa using ‹¬l.block = true›
          rw [hc1] at s_post s_post1
          simp only [foundOf, Option.map_some, hb] at s_post s_post1
          rw [s_post1]
          simp only [placeOf, turnOf, s_post, curOf, Cur.children, slotOf_ne_noSlot, ↓reduceIte,
            and_self]
      | Level2 t2 =>
        rw [leaf_next_level2 hpo] at hn
        step*
        · refine ⟨?_, ?_⟩
          · simp only [placeOf, turnOf, stepOf, i8_post]; rfl
          · simp only [placeOf, curOf, i7_post, i3_post, i6_post,
              gib_mask_val l.pa i1 i2 i1_post i2_post, slot_mask_val l.pa i4 i5 i4_post i5_post,
              BLOCK_SIZE]
        · have hb : l.block = false := by simpa using ‹¬l.block = true›
          simp only [curOf, hb, Bool.false_eq_true, ↓reduceIte] at hn
          exact hn
        · refine ⟨rfl, ?_⟩
          simp only [placeOf, curOf, phaseOf, i7_post, i3_post, i6_post,
            gib_mask_val l.pa i1 i2 i1_post i2_post, slot_mask_val l.pa i4 i5 i4_post i5_post]
      | Level3 t2 t3 =>
        step*
        refine ⟨?_, ?_⟩
        · simp only [placeOf, turnOf, stepOf, i8_post]; rfl
        · simp only [placeOf, curOf, phaseOf, i7_post, i3_post, i6_post,
            gib_mask_val l.pa i1 i2 i1_post i2_post, slot_mask_val l.pa i4 i5 i4_post i5_post,
            PAGE_SIZE]
    | Err e =>
      simp only [placeCode, bind_ok]
      rw [leaf_next_root hpo] at hn
      have h1 : c.next.val + 1 ≤ Usize.max := by simp only [curOf] at hn; split at hn <;> omega
      step*
      · refine ⟨rfl, ?_⟩
        simp only [placeOf, curOf, phaseOf, i7_post, i3_post,
          gib_mask_val l.pa i1 i2 i1_post i2_post, no_slot_val]
      · have hb : l.block = false := by simpa using ‹¬l.block = true›
        simp only [curOf, hb, Bool.false_eq_true, ↓reduceIte] at hn
        simp only [curOf, foundOf, Option.map_some, Cur.children, no_slot_val, slotOf_ne_noSlot,
          ↓reduceIte, i7_post]
        omega
      · have hc1 : curOf ⟨.Children, l.pa, i7, i3, page_tables.boot.NO_SLOT, c.next, c.t3⟩ =
            ⟨.children, l.pa.val, c.next.val + 1, gibOf l.pa.val, noSlot, c.next.val, c.t3.val⟩ := by
          simp only [curOf, phaseOf, i7_post, i3_post, gib_mask_val l.pa i1 i2 i1_post i2_post,
            no_slot_val]
        have hb : l.block = false := by simpa using ‹¬l.block = true›
        rw [hc1] at s_post s_post1
        simp only [foundOf, Option.map_some, hb] at s_post s_post1
        rw [s_post1]
        simp only [placeOf, turnOf, s_post, curOf, Cur.children, slotOf_ne_noSlot, ↓reduceIte,
          and_self]

theorem curOf_phase (c : page_tables.boot.MapCursor) : (curOf c).phase = phaseOf c.phase := rfl

theorem curOf_leaf (c : page_tables.boot.MapCursor) :
    curOf { c with phase := .Leaf } = { curOf c with phase := .leaf } := rfl

/-- `MapCursor::held_page(set, base, found)` on a pool of at least one table:
`Cur.heldPage`, for a leaf found below `2 ^ 39` and a next free table after
the call that fits in `usize`. -/
@[step] theorem held_page_spec {N : Usize} {upper : Bool} (c : page_tables.boot.MapCursor)
    (set : page_tables.Tables N upper) (base : U64) (found : Option page_tables.boot.Leaf)
    (hN : 0 < N.val) (hf : FoundLow found)
    (hn : ((curOf c).heldPage (placeOr (tablesOf set) (word64 base)) (foundOf found)).2.next ≤
      Usize.max) :
    page_tables.boot.MapCursor.held_page c set base found ⦃ t c' =>
      turnOf t = ((curOf c).heldPage (placeOr (tablesOf set) (word64 base)) (foundOf found)).1 ∧
        curOf c' =
          ((curOf c).heldPage (placeOr (tablesOf set) (word64 base)) (foundOf found)).2 ⦄ := by
  unfold page_tables.boot.MapCursor.held_page
  simp only [block_size_eq, page_size_eq]
  cases found with
  | none =>
    have hn' : ((curOf { c with phase := .Leaf }).leaf (placeOr (tablesOf set) (word64 base))
        (foundOf none)).2.next ≤ Usize.max := by rw [curOf_leaf]; exact hn
    step*
    rw [curOf_leaf] at t_post t_post1
    exact ⟨t_post, t_post1⟩
  | some p =>
    have hp := hf p rfl
    have hn' : slotOf p.pa.val ≠ (curOf c).slot → ((curOf { c with phase := .Leaf }).leaf
        (placeOr (tablesOf set) (word64 base)) (foundOf (some p))).2.next ≤ Usize.max := by
      intro h
      rw [curOf_leaf]
      simpa only [foundOf, Option.map_some, Cur.heldPage, h, ↓reduceIte] using hn
    step*
    · have hs : slotOf p.pa.val = (curOf c).slot := by
        rw [← slot_mask_val p.pa i i1 i_post i1_post, ← i2_post, ‹i2 = c.slot›]; rfl
      simp only [foundOf, Option.map_some, Cur.heldPage, hs, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simp only [turnOf, stepOf, i4_post]; rfl
      · simp only [curOf, i3_post, PAGE_SIZE]
    · have hs : slotOf p.pa.val ≠ (curOf c).slot := by
        rw [← slot_mask_val p.pa i i1 i_post i1_post, ← i2_post]
        exact fun h => ‹¬i2 = c.slot› (UScalar.eq_of_val_eq h)
      exact hn' hs
    · have hs : slotOf p.pa.val ≠ (curOf c).slot := by
        rw [← slot_mask_val p.pa i i1 i_post i1_post, ← i2_post]
        exact fun h => ‹¬i2 = c.slot› (UScalar.eq_of_val_eq h)
      simp only [foundOf, Option.map_some, Cur.heldPage, hs, ↓reduceIte]
      rw [curOf_leaf] at t_post t_post1
      exact ⟨t_post, t_post1⟩

/-- What the cursor of the code needs for one step without overflow besides
its next free table: a level 2 and a level 3 table that can be incremented
and whose addresses at `base` fit in 64 bits, and the end of the 2 MiB slot
after the pages of a new level 3 table and of the 1 GiB slot after the
entries of a new level 2 table that fit in 64 bits. -/
def CurFits (c : page_tables.boot.MapCursor) (base : U64) : Prop :=
  c.t2.val + 1 ≤ Usize.max ∧ c.t3.val + 1 ≤ Usize.max ∧
    base.val + 4096 * c.t2.val < 2 ^ 64 ∧ base.val + 4096 * c.t3.val < 2 ^ 64 ∧
    (c.phase = .NewTable → c.slot.val + 2 ^ 21 < 2 ^ 64) ∧
    (c.phase = .Root → c.gib.val + 2 ^ 30 < 2 ^ 64)

/-- `MapCursor::take(set, base, found)` on a pool of at least one table:
`Cur.take` with the place that the cursor reads, for a leaf found below
`2 ^ 39`, a cursor whose tables and slots do not overflow (`CurFits`) and a
next free table after the call that fits in `usize`. -/
@[step] theorem take_spec {N : Usize} {upper : Bool} (c : page_tables.boot.MapCursor)
    (set : page_tables.Tables N upper) (base : U64) (found : Option page_tables.boot.Leaf)
    (hN : 0 < N.val) (hf : FoundLow found) (hc : CurFits c base)
    (hn : ((curOf c).take (placeOr (tablesOf set) (word64 base)) (word64 base)
      (foundOf found)).2.next ≤ Usize.max) :
    page_tables.boot.MapCursor.take c set base found ⦃ t c' =>
      turnOf t = ((curOf c).take (placeOr (tablesOf set) (word64 base)) (word64 base)
          (foundOf found)).1 ∧
        curOf c' = ((curOf c).take (placeOr (tablesOf set) (word64 base)) (word64 base)
          (foundOf found)).2 ⦄ := by
  obtain ⟨ht2, ht3, hb2, hb3, hsl, hgb⟩ := hc
  unfold page_tables.boot.MapCursor.take
  simp only [gib_size_eq, block_size_eq]
  cases hp : c.phase
  all_goals simp only [Cur.take, curOf_phase, hp, phaseOf] at hn ⊢
  · step*
  · step*
  · step*
    simp only [turnOf, s_post, s_post1, and_self]
  · have := hsl hp
    step*
    refine ⟨?_, ?_⟩
    · simp only [turnOf, stepOf, i2_post, table_post, i1_post1, tableAt]; rfl
    · simp only [curOf, phaseOf, i_post, BLOCK_SIZE]
  · step*
    simp only [turnOf, s_post, s_post1, and_self]
  · step*
    simp only [turnOf, s_post, s_post1, and_self]
  · have := hgb hp
    step*
    refine ⟨?_, ?_⟩
    · simp only [turnOf, stepOf, i3_post, table_post, i2_post1, tableAt]; rfl
    · simp only [curOf, phaseOf, i1_post, GIB_SIZE]
  · exact spec_of_eq rfl ⟨rfl, rfl⟩

end Krepi.Proofs.PageTables.Refinement
