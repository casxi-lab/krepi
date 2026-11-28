module

public import Krepi.Statements.Basic
public import Krepi.Spec.PageTables.Map
public import Krepi.Proofs.Fdt.Refinement.BasicLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas about the vocabulary of the refinement statements

Lemmas about the machine values and the tables of the `page-tables`
component that need no generated definition, for the proofs below
`Krepi.Proofs.PageTables.Refinement`. The module imports no generated
definitions, so it is built once and not again for every mutant of the code.
It imports `Krepi.Proofs.Fdt.Refinement.BasicLemmas` (no generated
definitions either), whose lemmas about triples, `Agrees`, the `?` operator,
iterators (`stands_of_sim`, `advances_of_stands`), options, lists, words and
the platform hold for every target.

- Words and their bit operations: `word64_mk` (the word of the
  specification is the bit vector of the code), `word64_and`, `word64_or`,
  `word64_not`, `word64_inj`, `word64_congr`, `word64_le_iff`, `word64_lt_iff`,
  `bne_zero_iff` and `not_bne_zero_iff` (a `!=` of the code against 0), and
  `byte_lt_iff`, `byte_le_iff`.
- The width of `usize`: `usize_numBits_le` (at most 64 bits),
  `usize_cast_u64_val` (a `usize` read as a 64-bit word keeps its value),
  `lt_usize_pow` (a number below $2^{32}$ fits in `usize`) and
  `usize_max_ge` (the largest `usize` is at least $2^{32} - 1$).
- Bits as numbers: `and_511` (a mask of the low nine bits is the rest
  modulo 512), `shiftRight_and_511` (an index of nine bits), `one_shiftLeft`
  (`1 <<< b` is `2 ^ b` below 64 bits).
- Constants of the specification as numbers: `ADDRESS_MASK_toNat`,
  `DIRECT_BASE_toNat`.
- Indices of a virtual address: `index1_eq`, `index2_eq`, `index3_eq`.
- Physical ranges: `endNat_of` (the end of a range from the numbers of its
  start and length), `endAddr_toNat`.
- The pool of a set of the code read as tables of descriptors:
  `poolView`, which is the body of `poolOf`, with `table_poolView` and
  `entry_poolView` (an entry of the set is the word of the descriptor of the
  code at the same table and index).
-/

@[expose] public section

open Aeneas Aeneas.Std
open Krepi.Statements Krepi.Spec.PageTables Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Words -/

/-- The word of the specification of a 64-bit word of the code is its bit
vector. -/
theorem word64_mk (x : U64) : word64 x = ⟨x.bv⟩ := by
  apply UInt64.toNat_inj.1
  rw [word64_toNat]; rfl

theorem word64_and (x y : U64) : word64 (x &&& y) = word64 x &&& word64 y := by
  rw [word64_mk, word64_mk, word64_mk]; rfl

theorem word64_or (x y : U64) : word64 (x ||| y) = word64 x ||| word64 y := by
  rw [word64_mk, word64_mk, word64_mk]; rfl

theorem word64_not (x : U64) : word64 (~~~x) = ~~~(word64 x) := by
  rw [word64_mk, word64_mk]; rfl

theorem word64_inj {x y : U64} : word64 x = word64 y ↔ x = y := by
  rw [word64_eq_iff, word64_toNat]
  exact ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩

theorem word64_le_iff {x y : U64} : word64 x ≤ word64 y ↔ x.val ≤ y.val := by
  rw [UInt64.le_iff_toNat_le, word64_toNat, word64_toNat]

theorem word64_lt_iff {x y : U64} : word64 x < word64 y ↔ x.val < y.val := by
  rw [UInt64.lt_iff_toNat_lt, word64_toNat, word64_toNat]

/-- A word that is not zero, as a `!=` of the code. -/
theorem bne_zero_iff {x : U64} : (x != 0#u64) = true ↔ x.val ≠ 0 := by
  rw [bne_iff_ne, ne_eq, ne_eq, u64_eq_zero_iff]

/-- A word that is zero, as a `!=` of the code that does not hold. -/
theorem not_bne_zero_iff {x : U64} : ¬ (x != 0#u64) = true ↔ x.val = 0 := by
  rw [bne_zero_iff, not_not]

theorem byte_le_iff {x : U8} {n : Nat} : n ≤ (byte x).toNat ↔ n ≤ x.val := by
  rw [byte_toNat]

theorem byte_lt_iff {x : U8} {n : Nat} : (byte x).toNat < n ↔ x.val < n := by
  rw [byte_toNat]

/-- Words with one value are one word. -/
theorem word64_congr {x y : U64} (h : x.val = y.val) : word64 x = word64 y := by
  rw [word64_eq_iff, word64_toNat, h]

/-! ## The platform -/

/-- `usize` is at most 64 bits wide. -/
theorem usize_numBits_le : UScalarTy.Usize.numBits ≤ UScalarTy.U64.numBits := by
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> decide

/-- A `usize` read as a 64-bit word keeps its value. -/
theorem usize_cast_u64_val (x : Usize) : (UScalar.cast .U64 x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ usize_numBits_le

/-- A number below $2^{32}$ fits in `usize`. -/
theorem lt_usize_pow {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega

/-- The largest `usize` is at least $2^{32} - 1$, on either width. -/
theorem usize_max_ge : 2 ^ 32 - 1 ≤ Usize.max := by
  rw [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h' | h'
  · rw [h']
  · rw [h']; exact Nat.le_of_ble_eq_true rfl

/-! ## Bits as numbers -/

/-- A mask of the low nine bits is the rest modulo 512. -/
theorem and_511 (n : Nat) : n &&& 511 = n % 512 :=
  Nat.and_two_pow_sub_one_eq_mod n 9

/-- The nine bits of a number from bit `k`. -/
theorem shiftRight_and_511 (n k : Nat) : (n >>> k) &&& 511 = n / 2 ^ k % 512 := by
  rw [and_511, Nat.shiftRight_eq_div_pow]

/-- `1 <<< b` is `2 ^ b` for a shift below 64 bits. -/
theorem one_shiftLeft {b : Nat} (h : b < 64) : (1 <<< b) % 2 ^ 64 = 2 ^ b := by
  rw [Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)

/-! ## Constants of the specification -/

theorem ADDRESS_MASK_toNat : ADDRESS_MASK.toNat = 281474976706560 := rfl

theorem DIRECT_BASE_toNat : DIRECT_BASE.toNat = 18446743523953737728 := rfl

/-! ## Indices -/

theorem index1_eq (v : UInt64) : index1 v = v.toNat / 2 ^ 30 % 512 := rfl

theorem index2_eq (v : UInt64) : index2 v = v.toNat / 2 ^ 21 % 512 := rfl

theorem index3_eq (v : UInt64) : index3 v = v.toNat / 2 ^ 12 % 512 := rfl

/-! ## Physical ranges -/

/-- The end of a range from the numbers of the code's start and length. -/
theorem endNat_of {R : PhysRange} {a b : U64} (h1 : R.start = word64 a) (h2 : R.len = word64 b) :
    R.endNat = a.val + b.val := by
  rw [PhysRange.endNat, h1, h2, word64_toNat, word64_toNat]

/-- The end of a range, which fits in 64 bits, as a number. -/
theorem endAddr_toNat (R : PhysRange) : R.endAddr.toNat = R.endNat := by
  rw [PhysRange.endAddr, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt R.fits

/-! ## The pool of a set of the code -/

/-- The pool of a set of the code read as tables of descriptors: the body of
`Krepi.Statements.PageTables.poolOf`, stated without the generated
definitions so that its lemmas are built once. -/
def poolView {N : Usize} (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N) :
    Pool N.val :=
  Vector.ofFn fun t => Vector.ofFn fun i =>
    word64 ((pool.val[t.val]?.bind fun table => table.val[i.val]?).getD 0#u64)

/-- A table of the pool of a set of the code, at an index of the pool. -/
theorem table_poolView {N : Usize} (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N)
    {r : Region} (u : Nat) {t : Nat} (ht : t < pool.val.length) :
    (⟨poolView pool, u⟩ : Tables r N.val).table t =
      Vector.ofFn fun i : Fin ENTRIES => word64 (((pool.val[t]'ht).val[i.val]?).getD 0#u64) := by
  have ht' : t < N.val := by have := pool.property; omega
  simp only [Tables.table, ht', ↓reduceDIte, poolView, Vector.getElem_ofFn,
    List.getElem?_eq_getElem ht, Option.bind_some]

/-- An entry of a set of the code: the word of the descriptor of the code at
the same table and index. -/
theorem entry_poolView {N : Usize} (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N)
    {r : Region} (u : Nat) {t i : Nat} (ht : t < pool.val.length)
    (hi : i < (pool.val[t]'ht).val.length) :
    (⟨poolView pool, u⟩ : Tables r N.val).entry t i = word64 ((pool.val[t]'ht).val[i]'hi) := by
  have hi' : i < ENTRIES := by
    have := (pool.val[t]'ht).property
    have h512 : (512#usize : Usize).val = 512 := rfl
    simp only [ENTRIES]; omega
  simp only [Tables.entry, hi', ↓reduceDIte, table_poolView pool u ht, Vector.getElem_ofFn,
    List.getElem?_eq_getElem hi, Option.getD_some]

end Krepi.Proofs.PageTables.Refinement
