module

public import Krepi.Proofs.PageTables.Refinement.BasicLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas

/-!
# Page tables: one-step lemmas of the walk and the checks of the specification

Lemmas about the walk, the first checks and the encodings of
`Krepi.Spec.PageTables`, in the forms that the triples of the generated
functions need, for the proofs below `Krepi.Proofs.PageTables.Refinement`.
The module imports no generated definitions, so it is built once and not
again for every mutant of the code.

- The table that a table descriptor points at: `childIndex`, the index that
  the code computes from an address, a base and a limit, and `child?_eq`
  (`Tables.child?` is `childIndex` with the limit `min used N`),
  `childIndex_lt` (the index is below the limit).
- The level 2 step of the walk: `walk2_invalid`, `walk2_backing`,
  `walk2_some`, and `walk2_lt` (the table of a success is below `N`).
- The walk after its level 2 step: `walk_root`, `walk_level2`,
  `walk_block`, `walk_backing`, `walk_level3`, `walk_error`.
- The first checks as nested conditions: `checkEntry_eq`, `checkPool_eq`,
  `checkPhysical_eq`, with `poolFits_eq`, `poolFits_iff`, `widthOk_eq`, `widthOk_byte_iff`,
  `lt_64_of_widthOk` (a physical width of the code is below 64),
  `holds_lower` and `holds_upper`.
- The direct address: `directAddress_eq`; the indices and the level 2
  step of the walk of an address `DIRECT_BASE | a` of the direct map, those
  of `a` (`index1_direct`, `index2_direct`, `index3_direct`,
  `walk2_direct`), which the code walks with the physical address.
-/

@[expose] public section

open Krepi.Spec.PageTables

namespace Krepi.Proofs.PageTables.Refinement

variable {r : Region} {N : Nat}

/-! ## The table of a table descriptor -/

/-- The index of the table at the address `a` of a pool at `base`, when the
table is one of the first `limit`: the index that `walk::child_index`
computes. -/
def childIndex (a base limit : Nat) : Option Nat :=
  if base ≤ a ∧ (a - base) / PAGE_SIZE < limit then some ((a - base) / PAGE_SIZE) else none

/-- `Tables.child?` is the index of the table at the output address of the
descriptor among the tables in use. -/
theorem child?_eq (s : Tables r N) (base d : UInt64) :
    s.child? base d = childIndex (outputAddress d).toNat base.toNat (min s.used N) := by
  simp only [Tables.child?, childIndex, Bool.and_eq_true, decide_eq_true_eq]

theorem childIndex_lt {a base limit t : Nat} (h : childIndex a base limit = some t) :
    t < limit := by
  unfold childIndex at h
  split at h
  · cases h; omega
  · cases h

/-- The table that `Tables.child?` gives is a table of the pool. -/
theorem child?_lt {s : Tables r N} {base d : UInt64} {t : Nat} (h : s.child? base d = some t) :
    t < N := by
  rw [child?_eq] at h
  exact Nat.lt_of_lt_of_le (childIndex_lt h) (Nat.min_le_right _ _)

/-! ## The level 2 step of the walk -/

theorem walk2_invalid {s : Tables r N} {base v : UInt64}
    (h : isValid (s.entry 0 (index1 v)) = false) : s.walk2 base v = .ok none := by
  simp only [Tables.walk2, h, Bool.not_false, ↓reduceIte, pure, Except.pure]

theorem walk2_backing {s : Tables r N} {base v : UInt64}
    (hv : isValid (s.entry 0 (index1 v)) = true) (hc : s.child? base (s.entry 0 (index1 v)) = none) :
    s.walk2 base v = .error .tableBacking := by
  simp only [Tables.walk2, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hc, throw,
    throwThe, MonadExceptOf.throw]

theorem walk2_some {s : Tables r N} {base v : UInt64} {t : Nat}
    (hv : isValid (s.entry 0 (index1 v)) = true) (hc : s.child? base (s.entry 0 (index1 v)) = some t) :
    s.walk2 base v = .ok (some (t, s.entry t (index2 v))) := by
  simp only [Tables.walk2, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hc, pure,
    Except.pure]

/-- The level 2 table of a success of the level 2 step is a table of the
pool. -/
theorem walk2_lt {s : Tables r N} {base v : UInt64} {t : Nat} {e : UInt64}
    (h : s.walk2 base v = .ok (some (t, e))) : t < N := by
  cases hv : isValid (s.entry 0 (index1 v))
  · rw [walk2_invalid hv] at h; cases h
  · cases hc : s.child? base (s.entry 0 (index1 v)) with
    | none => rw [walk2_backing hv hc] at h; cases h
    | some t' =>
      rw [walk2_some hv hc] at h
      cases h
      exact child?_lt hc

/-! ## The walk after its level 2 step -/

theorem walk_error {s : Tables r N} {base v : UInt64} {x : TableError}
    (h : s.walk2 base v = .error x) : s.walk base v = .error x := by
  simp only [Tables.walk, h, bind, Except.bind]

theorem walk_root {s : Tables r N} {base v : UInt64} (h : s.walk2 base v = .ok none) :
    s.walk base v = .ok .root := by
  simp only [Tables.walk, h, bind, Except.bind, pure, Except.pure]

theorem walk_level2 {s : Tables r N} {base v : UInt64} {t2 : Nat} {e2 : UInt64}
    (h : s.walk2 base v = .ok (some (t2, e2))) (hv : isValid e2 = false) :
    s.walk base v = .ok (.level2 t2) := by
  simp only [Tables.walk, h, hv, bind, Except.bind, pure, Except.pure, Bool.not_false,
    ↓reduceIte]

theorem walk_block {s : Tables r N} {base v : UInt64} {t2 : Nat} {e2 : UInt64}
    (h : s.walk2 base v = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : (typeBits e2 == BLOCK) = true) :
    s.walk base v = .ok (.block t2 e2) := by
  simp only [Tables.walk, h, hv, hb, bind, Except.bind, pure, Except.pure, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

theorem walk_backing {s : Tables r N} {base v : UInt64} {t2 : Nat} {e2 : UInt64}
    (h : s.walk2 base v = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : (typeBits e2 == BLOCK) = false) (hc : s.child? base e2 = none) :
    s.walk base v = .error .tableBacking := by
  simp only [Tables.walk, h, hv, hb, hc, bind, Except.bind, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]

theorem walk_level3 {s : Tables r N} {base v : UInt64} {t2 t3 : Nat} {e2 : UInt64}
    (h : s.walk2 base v = .ok (some (t2, e2))) (hv : isValid e2 = true)
    (hb : (typeBits e2 == BLOCK) = false) (hc : s.child? base e2 = some t3) :
    s.walk base v = .ok (.level3 t2 t3 (s.entry t3 (index3 v))) := by
  simp only [Tables.walk, h, hv, hb, hc, bind, Except.bind, pure, Except.pure, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

/-! ## Addresses of the direct map -/

theorem index1_direct {a : UInt64} (h : a.toNat < 2 ^ 39) :
    index1 (DIRECT_BASE ||| a) = index1 a := by
  rw [index1_eq, index1_eq, direct_or h, DIRECT_BASE_toNat]; omega

theorem index2_direct {a : UInt64} (h : a.toNat < 2 ^ 39) :
    index2 (DIRECT_BASE ||| a) = index2 a := by
  rw [index2_eq, index2_eq, direct_or h, DIRECT_BASE_toNat]; omega

theorem index3_direct {a : UInt64} (h : a.toNat < 2 ^ 39) :
    index3 (DIRECT_BASE ||| a) = index3 a := by
  rw [index3_eq, index3_eq, direct_or h, DIRECT_BASE_toNat]; omega

/-- The level 2 step of the walk of the address `DIRECT_BASE | a` of the
direct map is that of `a`, for `a` below $2^{39}$: the walk reads the
indices of an address alone. -/
theorem walk2_direct {s : Tables r N} {base a : UInt64} (h : a.toNat < 2 ^ 39) :
    s.walk2 base (DIRECT_BASE ||| a) = s.walk2 base a := by
  simp only [Tables.walk2, index1_direct h, index2_direct h]

/-! ## The first checks -/

theorem poolFits_eq (N : Nat) (base : UInt64) (bits : UInt8) :
    poolFits N base bits = (N != 0 && decide (base.toNat + PAGE_SIZE * N ≤ 2 ^ bits.toNat)) :=
  rfl

theorem widthOk_eq (bits : UInt8) :
    widthOk bits = (decide (32 ≤ bits.toNat) && decide (bits.toNat ≤ 48)) := rfl

theorem holds_lower (v : UInt64) : Region.holds .lower v = decide (v.toNat < 2 ^ 39) := rfl

theorem holds_upper (v : UInt64) :
    Region.holds .upper v = decide (18446743523953737728 ≤ v.toNat) := rfl

theorem poolFits_iff (N : Nat) (base : UInt64) (bits : UInt8) :
    poolFits N base bits = true ↔ N ≠ 0 ∧ base.toNat + PAGE_SIZE * N ≤ 2 ^ bits.toNat := by
  simp only [poolFits_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]

/-- A width of the code is a physical width when it is 32 to 48. -/
theorem widthOk_byte_iff (x : Aeneas.Std.U8) :
    widthOk (Krepi.Statements.byte x) = true ↔ 32 ≤ x.val ∧ x.val ≤ 48 := by
  simp only [widthOk_eq, Krepi.Proofs.Fdt.Refinement.byte_toNat, Bool.and_eq_true,
    decide_eq_true_eq]

/-- A physical width is below 64. -/
theorem lt_64_of_widthOk {x : Aeneas.Std.U8} (h : widthOk (Krepi.Statements.byte x) = true) :
    x.val < 64 := by
  have := (widthOk_byte_iff x).1 h; omega

/-- The first checks of an entry on a set, as nested conditions. -/
theorem checkEntry_eq (r : Region) (N : Nat) (v : UInt64) (align : Nat) (base : UInt64)
    (bits : UInt8) :
    checkEntry r N v align base bits =
      if v.toNat % align ≠ 0 ∨ base.toNat % PAGE_SIZE ≠ 0 then .error .alignment
      else if r.holds v = false ∨ widthOk bits = false then .error .addressWidth
      else if poolFits N base bits = false then .error .tableBacking
      else .ok () := by
  unfold checkEntry
  by_cases h1 : v.toNat % align = 0 <;> by_cases h2 : base.toNat % PAGE_SIZE = 0 <;>
    by_cases h3 : r.holds v = true <;> by_cases h4 : widthOk bits = true <;>
    by_cases h5 : poolFits N base bits = true <;>
    simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- The first checks of an entry on a pool, as nested conditions. -/
theorem checkPool_eq (N : Nat) (base : UInt64) (bits : UInt8) :
    checkPool N base bits =
      if base.toNat % PAGE_SIZE ≠ 0 then .error .alignment
      else if widthOk bits = false then .error .addressWidth
      else if poolFits N base bits = false then .error .tableBacking
      else .ok () := by
  unfold checkPool
  by_cases h1 : base.toNat % PAGE_SIZE = 0 <;> by_cases h2 : widthOk bits = true <;>
    by_cases h3 : poolFits N base bits = true <;>
    simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- The checks of a physical address, as nested conditions. -/
theorem checkPhysical_eq (p : UInt64) (align : Nat) (bits : UInt8) :
    checkPhysical p align bits =
      if p.toNat % align ≠ 0 then .error .alignment
      else if 2 ^ bits.toNat ≤ p.toNat then .error .addressWidth
      else .ok () := by
  unfold checkPhysical
  by_cases h1 : p.toNat % align = 0 <;> by_cases h2 : 2 ^ bits.toNat ≤ p.toNat <;>
    simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-! ## The direct address -/

theorem directAddress_eq (R : PhysRange) :
    directAddress R = if R.endNat ≤ 2 ^ 39 then some (DIRECT_BASE ||| R.start) else none := rfl

end Krepi.Proofs.PageTables.Refinement
