module

public import Krepi.Proofs.PageTables.Refinement.WalkSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the lookups and the writes of a set, case by case

The entries of `Krepi.Spec.PageTables` that read a set or build a write
plan for it, `Tables.pageLeaf`, `lookupPage`, `lookupBlock`, `mapPage`,
`mapBlock` and `unmapPage`, rewritten case by case from the outcome of
their first checks and of their walk, in the forms that the triples of the
generated functions need. The module imports no generated definitions, so
it is built once and not again for every mutant of the code.

- Results of the code: `ok_of_agrees_unit` and `ok_of_branch_unit` (a
  check of the code that succeeds agrees with a check of the specification
  that succeeds), `eq_of_branch_map` (the value of a step of the
  specification after the `?` operator), `writes_error_of` and
  `writes_ok_of` (the two cases of `Writes`).
- The first checks: `checkEntry_passes` (what they give when they pass) and
  `checkEntry_fits` (the pool holds a table and ends below $2^{64}$).
- The page leaf: `pageLeaf_error`, `pageLeaf_root`, `pageLeaf_level2`,
  `pageLeaf_block`, `pageLeaf_backing`, `pageLeaf_leaf`,
  `pageLeaf_notLeaf`.
- The lookups: `lookupPage_check`, `lookupPage_leaf`,
  `lookupPage_leaf_error`; `lookupBlock_check`, `lookupBlock_walk_error`,
  `lookupBlock_root`, `lookupBlock_some`.
- A page: `mapPage_check`, `mapPage_physical`, `mapPage_walk_error`,
  `mapPage_root_full` and `mapPage_root_new` (no level 2 table: too few
  free tables, or two new tables), and `mapPage_some`, which hands the case
  of a level 2 table over to `mapBelow`, the rest of `mapPage` below a level
  2 entry, with `mapBelow_invalid_full`, `mapBelow_invalid`,
  `mapBelow_block`, `mapBelow_backing`, `mapBelow_level3`.
- A block: `mapBlock_check`, `mapBlock_physical`, `mapBlock_walk_error`,
  `mapBlock_root_full` and `mapBlock_root_new` (no level 2 table),
  `mapBlock_invalid`, `mapBlock_block`, `mapBlock_backing`,
  `mapBlock_table` (the four cases of a level 2 entry).
- An unmap: `unmapPage_check`, `unmapPage_leaf`, `unmapPage_leaf_error`.
-/

@[expose] public section

open Krepi.Spec.PageTables Krepi.Statements Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

variable {r : Region} {N : Nat}

/-! ## Results of the code -/

section Results

open Aeneas.Std

variable {α β ε ε' : Type}

/-- A success of the code that agrees, with no relation on the values, with
a check of the specification is a success of that check. -/
theorem ok_of_agrees_unit {err : ε → ε'} {a : α} {e : Except ε' Unit}
    (h : Agrees (fun _ _ => True) err (.Ok a) e) : e = .ok () := by
  cases e with
  | error x => exact (agrees_ok_error.1 h).elim
  | ok u => rfl

/-- On the branch `Continue` of the `?` operator after a check, the check of
the specification succeeds. -/
theorem ok_of_branch_unit {err : ε → ε'} {r : core.result.Result α ε} {e : Except ε' Unit}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α} {a : α}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Continue a)
    (hr : Agrees (fun _ _ => True) err r e) : e = .ok () :=
  ok_of_agrees_unit (agrees_of_branch_ok h hc hr)

/-- On the branch `Continue v` of the `?` operator after a callee whose
value is a function `f` of the value of the specification's step, that step
gives `f v`. -/
theorem eq_of_branch_map {err : ε → ε'} {f : α → β} {r : core.result.Result α ε}
    {e : Except ε' β} {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α}
    {a : α}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Continue a)
    (hr : Agrees (fun a b => f a = b) err r e) : e = .ok (f a) := by
  obtain ⟨b, rfl, hb⟩ := agrees_ok_iff.1 (agrees_of_branch_ok h hc hr)
  rw [hb]

/-- A failure of a write that agrees with the failure of its specification
and leaves the state as it was. -/
theorem writes_error_of {σ τ : Type} {repr : σ → τ → Prop} {rel : α → β → Prop}
    {err : ε → ε' → Prop} {s : σ} {x : ε} {y : ε'} (h : err x y) :
    Writes repr rel err s (.Err x) s (.error y) := And.intro h rfl

/-- A success of a write whose value and state stand for those of the
success of its specification. -/
theorem writes_ok_of {σ τ : Type} {repr : σ → τ → Prop} {rel : α → β → Prop}
    {err : ε → ε' → Prop} {s s' : σ} {a : α} {t : τ} {b : β} (h1 : rel a b)
    (h2 : repr s' t) :
    Writes repr rel err s (.Ok a) s' (.ok (t, b)) := And.intro h1 h2

end Results

/-! ## The first checks -/

/-- What the first checks of an entry that pass give: the alignments, the
width and the pool. -/
theorem checkEntry_passes {v : UInt64} {align : Nat} {base : UInt64} {bits : UInt8}
    (h : checkEntry r N v align base bits = .ok ()) :
    v.toNat % align = 0 ∧ base.toNat % PAGE_SIZE = 0 ∧ widthOk bits = true ∧
      poolFits N base bits = true := by
  rw [checkEntry_eq] at h
  have h1 : ¬ (v.toNat % align ≠ 0 ∨ base.toNat % PAGE_SIZE ≠ 0) := fun h1 => by
    simp only [h1, ↓reduceIte, reduceCtorEq] at h
  have h2 : ¬ (r.holds v = false ∨ widthOk bits = false) := fun h2 => by
    simp only [h1, h2, ↓reduceIte, reduceCtorEq] at h
  have h3 : ¬ poolFits N base bits = false := fun h3 => by
    simp only [h1, h2, h3, ↓reduceIte, reduceCtorEq] at h
  simp only [ne_eq, not_or, not_not, Bool.not_eq_false] at h1 h2 h3
  exact ⟨h1.1, h1.2, h2.2, h3⟩

/-- After the first checks of an entry pass, the pool holds a table and its
end fits in 64 bits. -/
theorem checkEntry_fits {v : UInt64} {align : Nat} {base : UInt64} {bits : UInt8}
    (h : checkEntry r N v align base bits = .ok ()) :
    0 < N ∧ base.toNat + PAGE_SIZE * N < 2 ^ 64 := by
  obtain ⟨-, -, hw, hp⟩ := checkEntry_passes h
  rw [poolFits_iff] at hp
  have hb : bits.toNat ≤ 48 := by
    rw [widthOk_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw; exact hw.2
  have h48 : 2 ^ bits.toNat ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hb
  have h64 : (2 : Nat) ^ 48 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by decide)
  exact ⟨Nat.pos_of_ne_zero hp.1, by omega⟩

/-! ## The page leaf -/

section PageLeaf

variable {s : Tables r N} {base v : UInt64}

theorem pageLeaf_error {x : TableError} (h : s.walk2 base v = .error x) :
    s.pageLeaf base v = .error x := by
  unfold Tables.pageLeaf; rw [walk_error h]; rfl

theorem pageLeaf_root (h : s.walk2 base v = .ok none) :
    s.pageLeaf base v = .error .notMapped := by
  unfold Tables.pageLeaf; rw [walk_root h]; rfl

theorem pageLeaf_level2 {t2 : Nat} {e2 : UInt64} (h : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = false) : s.pageLeaf base v = .error .notMapped := by
  unfold Tables.pageLeaf; rw [walk_level2 h hv]; rfl

theorem pageLeaf_block {t2 : Nat} {e2 : UInt64} (h : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = true) (hb : typeBits e2 = BLOCK) :
    s.pageLeaf base v = .error .notMapped := by
  unfold Tables.pageLeaf; rw [walk_block h hv (by rw [hb]; rfl)]; rfl

theorem pageLeaf_backing {t2 : Nat} {e2 : UInt64} (h : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = true) (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = none) :
    s.pageLeaf base v = .error .tableBacking := by
  unfold Tables.pageLeaf; rw [walk_backing h hv (by simpa using hb) hc]; rfl

/-- The page leaf of a walk that reaches a level 3 entry with a page
descriptor. -/
theorem pageLeaf_leaf {t2 t3 : Nat} {e2 : UInt64} (h : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = true) (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = some t3)
    (hd : typeBits (s.entry t3 (index3 v)) = TABLE_OR_PAGE) :
    s.pageLeaf base v = .ok (t3, s.entry t3 (index3 v)) := by
  unfold Tables.pageLeaf
  rw [walk_level3 h hv (by simpa using hb) hc]
  simp only [bind, Except.bind, hd, beq_self_eq_true, ↓reduceIte]
  rfl

/-- No page leaf for a walk that reaches a level 3 entry without a page
descriptor. -/
theorem pageLeaf_notLeaf {t2 t3 : Nat} {e2 : UInt64} (h : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = true) (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = some t3)
    (hd : typeBits (s.entry t3 (index3 v)) ≠ TABLE_OR_PAGE) :
    s.pageLeaf base v = .error .notMapped := by
  unfold Tables.pageLeaf
  rw [walk_level3 h hv (by simpa using hb) hc]
  simp only [bind, Except.bind, beq_iff_eq, hd, ↓reduceIte]
  rfl

end PageLeaf

/-! ## The lookups -/

section Lookup

variable {s : Tables r N} {v base : UInt64} {bits : UInt8}

theorem lookupPage_check {x : TableError} (h : checkEntry r N v PAGE_SIZE base bits = .error x) :
    s.lookupPage v base bits = .error x := by
  unfold Tables.lookupPage; rw [h]; rfl

theorem lookupPage_leaf {P : Nat × UInt64} (h : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (hl : s.pageLeaf base v = .ok P) : s.lookupPage v base bits = .ok P.2 := by
  unfold Tables.lookupPage; rw [h]; simp only [bind, Except.bind, hl]; rfl

theorem lookupPage_leaf_error {x : TableError} (h : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (hl : s.pageLeaf base v = .error x) : s.lookupPage v base bits = .error x := by
  unfold Tables.lookupPage; rw [h]; simp only [bind, Except.bind, hl]

theorem lookupBlock_check {x : TableError} (h : checkEntry r N v BLOCK_SIZE base bits = .error x) :
    s.lookupBlock v base bits = .error x := by
  unfold Tables.lookupBlock; rw [h]; rfl

theorem lookupBlock_walk_error {x : TableError} (h : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (hw : s.walk2 base v = .error x) : s.lookupBlock v base bits = .error x := by
  unfold Tables.lookupBlock; rw [h]; simp only [bind, Except.bind, hw]

theorem lookupBlock_root (h : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (hw : s.walk2 base v = .ok none) : s.lookupBlock v base bits = .error .notMapped := by
  unfold Tables.lookupBlock; rw [h]; simp only [bind, Except.bind, hw]; rfl

theorem lookupBlock_some {t2 : Nat} {e2 : UInt64}
    (h : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (hw : s.walk2 base v = .ok (some (t2, e2))) :
    s.lookupBlock v base bits =
      if typeBits e2 = BLOCK then .ok e2
      else if isValid e2 = true ∧ s.child? base e2 = none then .error .tableBacking
      else .error .notMapped := by
  unfold Tables.lookupBlock; rw [h]; simp only [bind, Except.bind, hw]
  by_cases hb : typeBits e2 = BLOCK
  · simp only [hb, beq_self_eq_true, ↓reduceIte]; rfl
  · by_cases hc : isValid e2 = true ∧ s.child? base e2 = none
    · simp only [beq_iff_eq, hb, ↓reduceIte, hc, Option.isNone_none, Bool.and_self, true_and]
      rfl
    · have hc' : (isValid e2 && (s.child? base e2).isNone) = false := by
        cases hv : isValid e2 <;> cases hc2 : s.child? base e2 <;> simp_all
      simp only [beq_iff_eq, hb, ↓reduceIte, hc, hc', Bool.false_eq_true]; rfl

end Lookup

/-! ## A page -/

/-- The rest of `Tables.mapPage` below the level 2 entry `e2` of `v`, in
table `t2`, for the page descriptor `page`: a new level 3 table for an
invalid entry, `AlreadyMapped` for a block, `TableBacking` for a table
descriptor outside the tables in use, and the level 3 entry otherwise. -/
def mapBelow (s : Tables r N) (t2 : Nat) (e2 v page base : UInt64) :
    Except TableError (Tables r N × Plan) :=
  if !isValid e2 then do
    if N - s.used < 1 then throw .outOfTables
    let t3 := s.used
    pure ({ s with used := s.used + 1 },
      [.zero t3, .store t3 (index3 v) page,
        .fence, .store t2 (index2 v) (tableDescriptor (tableAddress base t3)), .sync])
  else if typeBits e2 == BLOCK then throw .alreadyMapped
  else do
    let some t3 := s.child? base e2 | throw .tableBacking
    if isValid (s.entry t3 (index3 v)) then throw .alreadyMapped
    pure (s, [.store t3 (index3 v) page, .sync])

section MapPage

variable {s : Tables r N} {v p base : UInt64} {k : Kind} {bits : UInt8}

theorem mapPage_check {x : TableError} (h : checkEntry r N v PAGE_SIZE base bits = .error x) :
    s.mapPage v p k base bits = .error x := by
  unfold Tables.mapPage; rw [h]; rfl

theorem mapPage_physical {x : TableError} (h1 : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (h2 : checkPhysical p PAGE_SIZE bits = .error x) : s.mapPage v p k base bits = .error x := by
  unfold Tables.mapPage; rw [h1, h2]; rfl

theorem mapPage_walk_error {x : TableError} (h1 : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (h2 : checkPhysical p PAGE_SIZE bits = .ok ()) (hw : s.walk2 base v = .error x) :
    s.mapPage v p k base bits = .error x := by
  unfold Tables.mapPage; rw [h1, h2, hw]; rfl

theorem mapPage_root_full (h1 : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (h2 : checkPhysical p PAGE_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok none)
    (hn : N - s.used < 2) : s.mapPage v p k base bits = .error .outOfTables := by
  unfold Tables.mapPage; rw [h1, h2, hw]; simp only [bind, Except.bind, hn, ↓reduceIte]; rfl

theorem mapPage_root_new (h1 : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (h2 : checkPhysical p PAGE_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok none)
    (hn : ¬ N - s.used < 2) :
    s.mapPage v p k base bits = .ok ({ s with used := s.used + 2 },
      [.zero (s.used + 1), .store (s.used + 1) (index3 v) (descriptor k p),
        .zero s.used, .store s.used (index2 v) (tableDescriptor (tableAddress base (s.used + 1))),
        .fence, .store 0 (index1 v) (tableDescriptor (tableAddress base s.used)), .sync]) := by
  unfold Tables.mapPage; rw [h1, h2, hw]; simp only [bind, Except.bind, hn, ↓reduceIte]; rfl

theorem mapPage_some {t2 : Nat} {e2 : UInt64} (h1 : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (h2 : checkPhysical p PAGE_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok (some (t2, e2))) :
    s.mapPage v p k base bits = mapBelow s t2 e2 v (descriptor k p) base := by
  unfold Tables.mapPage; rw [h1, h2, hw]; rfl

end MapPage

section MapBelow

variable {s : Tables r N} {t2 : Nat} {e2 v page base : UInt64}

theorem mapBelow_invalid_full (hv : isValid e2 = false) (hn : N - s.used < 1) :
    mapBelow s t2 e2 v page base = .error .outOfTables := by
  simp only [mapBelow, hv, Bool.not_false, ↓reduceIte, bind, Except.bind, hn]; rfl

theorem mapBelow_invalid (hv : isValid e2 = false) (hn : ¬ N - s.used < 1) :
    mapBelow s t2 e2 v page base = .ok ({ s with used := s.used + 1 },
      [.zero s.used, .store s.used (index3 v) page,
        .fence, .store t2 (index2 v) (tableDescriptor (tableAddress base s.used)), .sync]) := by
  simp only [mapBelow, hv, Bool.not_false, ↓reduceIte, hn]; rfl

theorem mapBelow_block (hv : isValid e2 = true) (hb : typeBits e2 = BLOCK) :
    mapBelow s t2 e2 v page base = .error .alreadyMapped := by
  simp only [mapBelow, hv, hb, Bool.not_true, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
  rfl

theorem mapBelow_backing (hv : isValid e2 = true) (hb : typeBits e2 ≠ BLOCK)
    (hc : s.child? base e2 = none) : mapBelow s t2 e2 v page base = .error .tableBacking := by
  simp only [mapBelow, hv, hb, hc, Bool.not_true, Bool.false_eq_true, beq_iff_eq, ↓reduceIte]
  rfl

theorem mapBelow_level3 {t3 : Nat} (hv : isValid e2 = true) (hb : typeBits e2 ≠ BLOCK)
    (hc : s.child? base e2 = some t3) :
    mapBelow s t2 e2 v page base =
      if isValid (s.entry t3 (index3 v)) = true then .error .alreadyMapped
      else .ok (s, [.store t3 (index3 v) page, .sync]) := by
  simp only [mapBelow, hv, hb, hc, Bool.not_true, Bool.false_eq_true, beq_iff_eq, ↓reduceIte]
  by_cases hl : isValid (s.entry t3 (index3 v)) = true
  · simp only [hl, ↓reduceIte, bind, Except.bind]; rfl
  · simp only [hl, ↓reduceIte, Bool.false_eq_true]; rfl

end MapBelow

/-! ## A block -/

section MapBlock

variable {s : Tables r N} {v p base : UInt64} {bits : UInt8}

theorem mapBlock_check {x : TableError} (h : checkEntry r N v BLOCK_SIZE base bits = .error x) :
    s.mapBlock v p base bits = .error x := by
  unfold Tables.mapBlock; rw [h]; rfl

theorem mapBlock_physical {x : TableError} (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .error x) : s.mapBlock v p base bits = .error x := by
  unfold Tables.mapBlock; rw [h1, h2]; rfl

theorem mapBlock_walk_error {x : TableError} (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .error x) :
    s.mapBlock v p base bits = .error x := by
  unfold Tables.mapBlock; rw [h1, h2, hw]; rfl

theorem mapBlock_root_full (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok none)
    (hn : N - s.used < 1) : s.mapBlock v p base bits = .error .outOfTables := by
  unfold Tables.mapBlock; rw [h1, h2, hw]; simp only [bind, Except.bind, hn, ↓reduceIte]; rfl

theorem mapBlock_root_new (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok none)
    (hn : ¬ N - s.used < 1) :
    s.mapBlock v p base bits = .ok ({ s with used := s.used + 1 },
      [.zero s.used, .store s.used (index2 v) (blockDescriptor p),
        .fence, .store 0 (index1 v) (tableDescriptor (tableAddress base s.used)), .sync]) := by
  unfold Tables.mapBlock; rw [h1, h2, hw]; simp only [bind, Except.bind, hn, ↓reduceIte]; rfl

theorem mapBlock_invalid {t2 : Nat} {e2 : UInt64}
    (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = false) :
    s.mapBlock v p base bits = .ok (s, [.store t2 (index2 v) (blockDescriptor p), .sync]) := by
  unfold Tables.mapBlock; rw [h1, h2, hw]
  simp only [bind, Except.bind, hv, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl

theorem mapBlock_block {t2 : Nat} {e2 : UInt64}
    (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = true) (hb : typeBits e2 = BLOCK) :
    s.mapBlock v p base bits = .error .alreadyMapped := by
  unfold Tables.mapBlock; rw [h1, h2, hw]
  simp only [bind, Except.bind, hv, hb, bne_self_eq_false, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]; rfl

theorem mapBlock_backing {t2 : Nat} {e2 : UInt64}
    (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = true) (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = none) :
    s.mapBlock v p base bits = .error .tableBacking := by
  unfold Tables.mapBlock; rw [h1, h2, hw]
  have hb' : (typeBits e2 != BLOCK) = true := by simpa using hb
  simp only [bind, Except.bind, hv, hb', hc, Option.isNone_none, Bool.and_self, ↓reduceIte]; rfl

theorem mapBlock_table {t2 t3 : Nat} {e2 : UInt64}
    (h1 : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (h2 : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok (some (t2, e2)))
    (hv : isValid e2 = true) (hb : typeBits e2 ≠ BLOCK) (hc : s.child? base e2 = some t3) :
    s.mapBlock v p base bits = .error .alreadyMapped := by
  unfold Tables.mapBlock; rw [h1, h2, hw]
  have hb' : (typeBits e2 != BLOCK) = true := by simpa using hb
  simp only [bind, Except.bind, hv, hb', hc, Option.isNone_some, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]; rfl

end MapBlock

/-! ## An unmap -/

section Unmap

variable {s : Tables r N} {v base : UInt64} {bits : UInt8}

theorem unmapPage_check {x : TableError} (h : checkEntry r N v PAGE_SIZE base bits = .error x) :
    s.unmapPage v base bits = .error x := by
  unfold Tables.unmapPage; rw [h]; rfl

theorem unmapPage_leaf {P : Nat × UInt64} (h : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (hl : s.pageLeaf base v = .ok P) :
    s.unmapPage v base bits =
      .ok ([.store P.1 (index3 v) INVALID, .invalidate v], outputAddress P.2) := by
  unfold Tables.unmapPage; rw [h]; simp only [bind, Except.bind, hl]; rfl

theorem unmapPage_leaf_error {x : TableError} (h : checkEntry r N v PAGE_SIZE base bits = .ok ())
    (hl : s.pageLeaf base v = .error x) : s.unmapPage v base bits = .error x := by
  unfold Tables.unmapPage; rw [h]; simp only [bind, Except.bind, hl]

end Unmap

end Krepi.Proofs.PageTables.Refinement
