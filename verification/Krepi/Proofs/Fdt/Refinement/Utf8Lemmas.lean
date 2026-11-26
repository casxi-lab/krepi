module

public import Krepi.Proofs.Fdt.Refinement.BasicLemmas
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: the byte reads of the specification

Lemmas about the byte reads of the specification of the `fdt` component
(`Krepi.Spec.Fdt.Bytes`) and the definitions that the triples of the
generated functions of `fdt::format` are stated with, for the proofs below
`Krepi.Proofs.Fdt.Refinement`. The module imports no generated definitions,
so it is built once and not again for every mutant of the code.

- Triples and machine values: `usize_numBits_ge`, `ite_spec_pos` and
  `ite_spec_neg` (the triple of the branch that an `if` takes).
- Bytes of a slice: `byte_at` (a byte that the code read), `toList_eq_data`,
  `byteArray_eq_iff`, `bytesOf_getElem!`, `bytesOf_getElem?_of_lt`,
  `bytesOf_getElem?_of_lt'`, `byte_eq_zero_iff`, `bytesOf_extract_eq_iff`
  (the bytes `[i, j)` of a slice are those of another slice),
  `drop_take_cons` (the step of a loop over the items `[i, e)` of a list),
  `bytesOf_extract_all` and `bytesOf_extract_any`.
- Strings: `findNul_step`, `findNul_zero`, `findNul_end`, `findNul_some` and
  `findNul_of` (the NUL that `findNul` finds), `toByteArray_of_fromUTF8?`,
  `utf8ByteSize_of_fromUTF8?`, `fromUTF8?_isSome`, `nameAt_iff`, the
  comparison of a byte string with the string that `cString` reads at an
  offset, and `nameAt_bytesOf_iff`, the same comparison byte by byte.
- UTF-8: `scalarEnd`, the index after the encoding of the scalar value at an
  index as the code checks it, by the table of its first byte
  (`scalarTail`, `continuesByte`), and `scalarEnd_eq`, that this is the
  length of the character that `ByteArray.utf8DecodeChar?` of Lean core
  decodes there. With it, `isValidUTF8_iff_decode` (bytes are UTF-8 exactly
  when their first character decodes and the rest is UTF-8),
  `scalarEnd_some`, `scalarEnd_none` and `isValidUTF8_extract_of_le`, the
  steps of the check of a range. The decoder is evaluated on numbers:
  `parseFirstByte_eq`, `isInvalidContinuationByte_eq`,
  `assemble₂Unchecked_toNat` and its two siblings, `assemble₂_map` and its two
  siblings, and the lemmas `scalarEnd_two` to `scalarEnd_bad` of each class of
  first byte.
- Names: `nameChar`, the character sets of `isNodeNameChar` and
  `isPropertyNameChar` (`nameChar_true`, `nameChar_false`);
  `isAlphanum_ofNat` and `nameChar_ofNat`, their values on a byte as the code
  tests it; `nameChar_lt` (every character of a name is ASCII) and
  `all_nameChar`, that the bytes of a UTF-8 string are all name characters
  exactly when its characters are.
- Padding: `land_mask4` (the bits of `align4`), `le_align4`, `align4_lt` and
  `align4_mod`.
- Tokens: `Piece` and `pieceAt`, the token at an offset of a structure block
  as `fdt::nodes::piece_at` reads it without checking it again; `u32At_ok_le`,
  `cString_ok`, `cString_nul`, `cString_extract`, `paddedEnd_ok` and
  `checkedAdd_ok`, what a success of a read tells; and `TokenPiece` with
  `pieceAt_of_decodeToken`, that `pieceAt` reads each token that
  `decodeToken` gives: the same kind, the offset of the next, the NUL after
  the name of a begin node, and the name offset and value offsets of a
  property.
-/

@[expose] public section

open Aeneas Aeneas.Std
open Krepi.Statements Krepi.Spec.Fdt
open ByteArray.utf8DecodeChar?

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Triples and machine values -/

/-- The width of `usize` is at least 32 bits. -/
theorem usize_numBits_ge : 32 ≤ UScalarTy.Usize.numBits := by
  have := System.Platform.numBits_eq
  rw [UScalarTy.Usize_numBits_eq]
  omega

/-- A triple of the branch that an `if` takes. -/
theorem ite_spec_pos {α : Type} {c : Prop} [Decidable c] {a b : Result α} {p : α → Prop}
    (h : c) (ha : a ⦃ p ⦄) : (if c then a else b) ⦃ p ⦄ := by
  simp only [h, ↓reduceIte]; exact ha

/-- A triple of the branch that an `if` takes. -/
theorem ite_spec_neg {α : Type} {c : Prop} [Decidable c] {a b : Result α} {p : α → Prop}
    (h : ¬ c) (hb : b ⦃ p ⦄) : (if c then a else b) ⦃ p ⦄ := by
  simp only [h, ↓reduceIte]; exact hb

/-! ## Bytes of a slice -/

/-- The bytes of a byte array, as the list of its array. -/
theorem toList_eq_data (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop_eq]

/-- Two byte arrays are equal when their lists of bytes are. -/
theorem byteArray_eq_iff {a b : ByteArray} : a = b ↔ a.toList = b.toList := by
  rw [toList_eq_data, toList_eq_data, Array.toList_inj]
  exact ⟨fun h => h ▸ rfl, fun h => by cases a; cases b; cases h; rfl⟩

/-- The byte at an index of the bytes of a slice, as a number; both sides are
`0` past the end. -/
theorem bytesOf_getElem! (s : Slice U8) (i : Nat) :
    ((bytesOf s)[i]!).toNat = (s.val[i]!).val := by
  rw [getElem!_def, getElem!_def, bytesOf_getElem?]
  cases s.val[i]? with
  | none => rfl
  | some x => simp

/-- A byte that the code read from a slice, as a byte of the specification. -/
theorem byte_at {bytes : Slice U8} {x : U8} {k n : Nat} {h : k < bytes.val.length}
    (hx : x = bytes.val[k]'h) (hk : k = n) : ((bytesOf bytes)[n]!).toNat = x.val := by
  subst hk; rw [bytesOf_getElem!, hx, getElem!_pos]

/-- The byte at an index inside a slice. -/
theorem bytesOf_getElem?_of_lt {s : Slice U8} {i : Nat} (h : i < s.val.length) :
    (bytesOf s)[i]? = some (byte s.val[i]) := by
  rw [bytesOf_getElem?, List.getElem?_eq_getElem h, Option.map_some]

theorem byte_eq_zero_iff {x : U8} : byte x = 0 ↔ x.val = 0 := byte_eq_iff

/-- The byte at an index inside a slice, read with `!`. -/
theorem bytesOf_getElem?_of_lt' {s : Slice U8} {i : Nat} (h : i < s.val.length) :
    (bytesOf s)[i]? = some (byte s.val[i]!) := by
  rw [bytesOf_getElem?_of_lt h, getElem!_pos s.val i h]

/-- The bytes `[i, j)` of a slice, which lie inside it, are those of `o`
exactly when they are as many and agree one by one. -/
theorem bytesOf_extract_eq_iff {s o : Slice U8} {i j : Nat} (hij : i ≤ j) (hj : j ≤ s.length) :
    (bytesOf s).extract i j = bytesOf o ↔
      j - i = o.length ∧ ∀ k < o.length, s.val[i + k]! = o.val[k]! := by
  show _ ↔ j - i = o.val.length ∧ ∀ k < o.val.length, s.val[i + k]! = o.val[k]!
  have hj' : j ≤ s.val.length := hj
  have hl : ((s.val.drop i).take (j - i)).length = j - i := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [byteArray_eq_iff, bytesOf_extract, bytesOf_toList]
  constructor
  · intro h
    have hlen := congrArg List.length h
    simp only [List.length_map, hl] at hlen
    refine ⟨hlen, fun k hk => ?_⟩
    have := congrArg (·[k]?) h
    simp only [List.getElem?_map, List.getElem?_take, List.getElem?_drop,
      show k < j - i by omega, ↓reduceIte] at this
    rw [getElem!_pos o.val k hk, getElem!_pos s.val (i + k) (by omega)]
    rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (show i + k < s.val.length by omega)]
      at this
    simp only [Option.map_some, Option.some.injEq, byte_eq_iff, byte_toNat] at this
    exact UScalar.eq_of_val_eq this
  · rintro ⟨hlen, h⟩
    congr 1
    apply List.ext_getElem (by rw [hl, hlen])
    intro k h1 h2
    have := h k h2
    rw [List.getElem_take, List.getElem_drop, ← getElem!_pos s.val (i + k) (by omega),
      ← getElem!_pos o.val k h2, this]

/-- The items `[i, e)` of a list, for `i < e`, start with the item at `i`. -/
theorem drop_take_cons {α : Type} {l : List α} {i e : Nat} (h1 : i < e) (h2 : e ≤ l.length) :
    (l.drop i).take (e - i) = l[i] :: (l.drop (i + 1)).take (e - (i + 1)) := by
  rw [List.drop_eq_getElem_cons (by omega), show e - i = (e - (i + 1)) + 1 by omega,
    List.take_succ_cons]

/-- A test of every byte of `[i, j)` of a slice. -/
theorem bytesOf_extract_all (s : Slice U8) (i j : Nat) (f : Nat → Bool) :
    ((bytesOf s).extract i j).toList.all (fun x => f x.toNat) =
      ((s.val.drop i).take (j - i)).all (fun x => f x.val) := by
  rw [bytesOf_extract, List.all_map]
  congr 1
  funext x
  simp only [Function.comp, byte_toNat]

/-- The nonzero bytes of `[i, j)` of a slice. -/
theorem bytesOf_extract_any (s : Slice U8) (i j : Nat) :
    ((bytesOf s).extract i j).toList.any (· ≠ 0) =
      ((s.val.drop i).take (j - i)).any (fun x => x.val ≠ 0) := by
  rw [bytesOf_extract, List.any_map]
  congr 1
  funext x
  simp only [Function.comp, ne_eq, decide_not, byte_eq_zero_iff]

/-! ## Strings -/

section Strings

variable {b : ByteArray}

/-- A byte other than NUL: the search goes on at the next index. -/
theorem findNul_step {i : Nat} (hi : i < b.size) (h : b[i]? ≠ some 0) :
    findNul b i = findNul b (i + 1) := by
  unfold findNul
  rw [show b.size - i = (b.size - (i + 1)) + 1 by omega, findNulFrom]
  simp only [h, ↓reduceIte]

/-- A NUL byte at `i`: the search ends there. -/
theorem findNul_zero {i : Nat} (hi : i < b.size) (h : b[i]? = some 0) : findNul b i = some i := by
  unfold findNul
  rw [show b.size - i = (b.size - (i + 1)) + 1 by omega, findNulFrom]
  simp only [h, ↓reduceIte]

/-- From the end of the bytes on, there is no NUL. -/
theorem findNul_end {i : Nat} (hi : b.size ≤ i) : findNul b i = none := by
  unfold findNul
  rw [show b.size - i = 0 by omega, findNulFrom]

/-- The NUL that the search finds: a NUL byte at or after the start, with no
NUL before it. -/
theorem findNul_some {s n : Nat} (h : findNul b s = some n) :
    s ≤ n ∧ n < b.size ∧ b[n]? = some 0 ∧ ∀ k, s ≤ k → k < n → b[k]? ≠ some 0 := by
  induction hm : b.size - s generalizing s with
  | zero => rw [findNul_end (by omega)] at h; cases h
  | succ m ih =>
    by_cases h0 : b[s]? = some 0
    · rw [findNul_zero (by omega) h0] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, h0, fun k h1 h2 => absurd h2 (by omega)⟩
    · rw [findNul_step (by omega) h0] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih h (by omega)
      refine ⟨by omega, h2, h3, fun k hk1 hk2 => ?_⟩
      by_cases hk : k = s
      · rw [hk]; exact h0
      · exact h4 k (by omega) hk2

/-- A NUL byte at `n`, at or after the start and with no NUL before it, is the
NUL that the search finds. -/
theorem findNul_of {s n : Nat} (h1 : s ≤ n) (h2 : b[n]? = some 0)
    (h3 : ∀ k, s ≤ k → k < n → b[k]? ≠ some 0) : findNul b s = some n := by
  have hn : n < b.size := by
    by_contra hc
    rw [getElem?_neg b n (by omega)] at h2
    cases h2
  induction hm : n - s generalizing s with
  | zero => rw [show s = n by omega]; exact findNul_zero hn h2
  | succ m ih =>
    rw [findNul_step (by omega) (h3 s (Nat.le_refl _) (by omega))]
    exact ih (by omega) (fun k hk1 hk2 => h3 k (by omega) hk2) (by omega)

/-- The bytes that decode to a string are its bytes. -/
theorem toByteArray_of_fromUTF8? {a : ByteArray} {s : String} (h : String.fromUTF8? a = some s) :
    s.toByteArray = a := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

/-- A string decoded from bytes has their size. -/
theorem utf8ByteSize_of_fromUTF8? {a : ByteArray} {s : String} (h : String.fromUTF8? a = some s) :
    s.utf8ByteSize = a.size := by
  rw [← String.size_toByteArray, toByteArray_of_fromUTF8? h]

/-- Bytes decode to a string exactly when they are UTF-8. -/
theorem fromUTF8?_isSome {a : ByteArray} : (String.fromUTF8? a).isSome ↔ a.IsValidUTF8 := by
  unfold String.fromUTF8?
  split <;> simp_all

/-- The string at `off` that `cString` reads is the byte string `k` exactly
when its NUL lies `k.size` bytes after `off` and the bytes before the NUL are
those of `k`: the comparison of a name with the string at an offset of the
strings block. -/
theorem nameAt_iff {off e : Nat} {s : String} (h : cString b off = .ok (s, e)) (k : ByteArray) :
    (findNul b off = some (off + k.size) ∧ b.extract off (off + k.size) = k) ↔
      s.toByteArray = k := by
  unfold cString at h
  split at h
  · cases h
  · rename_i nul hnul
    split at h
    · cases h
    · rename_i s' hs
      cases h
      have hb := toByteArray_of_fromUTF8? hs
      obtain ⟨h1, h2, -, -⟩ := findNul_some hnul
      rw [hnul, hb]
      constructor
      · rintro ⟨hn, hk⟩
        cases hn
        exact hk
      · intro hk
        have hsz := congrArg ByteArray.size hk
        rw [ByteArray.size_extract] at hsz
        have : nul = off + k.size := by omega
        subst this
        exact ⟨rfl, hk⟩

/-- The string at `off` of the bytes of a slice, whose NUL lies at
`off + key.length`, is `key` exactly when the bytes of `key` are nonzero and
agree with those of the slice from `off`. -/
theorem nameAt_bytesOf_iff {strings key : Slice U8} {off : Nat}
    (hlt : off + key.length < strings.length) (h0 : (strings.val[off + key.length]!).val = 0) :
    (findNul (bytesOf strings) off = some (off + key.length) ∧
        (bytesOf strings).extract off (off + key.length) = bytesOf key) ↔
      ∀ k < key.length, (key.val[k]!).val ≠ 0 ∧ strings.val[off + k]! = key.val[k]! := by
  have hlt' : off + key.val.length < strings.val.length := hlt
  have e1 : key.length = key.val.length := rfl
  have e2 : strings.length = strings.val.length := rfl
  rw [bytesOf_extract_eq_iff (by omega) (by omega), Nat.add_sub_cancel_left]
  constructor
  · rintro ⟨hf, -, heq⟩ k hk
    obtain ⟨-, -, -, hnz⟩ := findNul_some hf
    have h1 := hnz (off + k) (by omega) (by omega)
    refine ⟨fun hz => h1 ?_, heq k hk⟩
    rw [bytesOf_getElem?_of_lt' (by have : k < key.val.length := hk; omega), heq k hk,
      byte_eq_zero_iff.mpr hz]
  · intro h
    refine ⟨findNul_of (by omega) ?_ ?_, rfl, fun k hk => (h k hk).2⟩
    · rw [bytesOf_getElem?_of_lt' hlt', byte_eq_zero_iff.mpr h0]
    · intro k hk1 hk2
      have := h (k - off) (by omega)
      rw [bytesOf_getElem?_of_lt' (by omega), show k = off + (k - off) by omega, this.2, ne_eq,
        Option.some.injEq, byte_eq_zero_iff]
      exact this.1

end Strings

/-! ## UTF-8 -/

/-- Whether `x` continues the encoding of a scalar value: `0x80` to `0xbf`. -/
def continuesByte (x : Nat) : Bool := decide (0x80 ≤ x ∧ x ≤ 0xbf)

/-- The masks of the first and continuation bytes of `parseFirstByte` and
`isInvalidContinuationByte`, as ranges of the byte. -/
theorem byte_masks : ∀ n, n < 256 →
    (n &&& 0x80 = 0 ↔ n < 0x80) ∧ (n &&& 0xe0 = 0xc0 ↔ 0xc0 ≤ n ∧ n < 0xe0) ∧
    (n &&& 0xf0 = 0xe0 ↔ 0xe0 ≤ n ∧ n < 0xf0) ∧ (n &&& 0xf8 = 0xf0 ↔ 0xf0 ≤ n ∧ n < 0xf8) ∧
    (n &&& 0xc0 = 0x80 ↔ 0x80 ≤ n ∧ n < 0xc0) := by
  decide +kernel

theorem and_beq_eq (w m v : UInt8) :
    (w &&& m == v) = decide (w.toNat &&& m.toNat = v.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt8.toNat_inj, UInt8.toNat_and]

/-- The class of a first byte, by its value. -/
theorem parseFirstByte_eq (w : UInt8) : parseFirstByte w =
    if w.toNat < 0x80 then .done else if w.toNat < 0xc0 then .invalid
    else if w.toNat < 0xe0 then .oneMore else if w.toNat < 0xf0 then .twoMore
    else if w.toNat < 0xf8 then .threeMore else .invalid := by
  obtain ⟨h1, h2, h3, h4, -⟩ := byte_masks w.toNat w.toNat_lt
  unfold parseFirstByte
  simp only [and_beq_eq, UInt8.reduceToNat, h1, h2, h3, h4, decide_eq_true_eq]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- A continuation byte, by its value. -/
theorem isInvalidContinuationByte_eq (x : UInt8) :
    isInvalidContinuationByte x = !continuesByte x.toNat := by
  have := (byte_masks x.toNat x.toNat_lt).2.2.2.2
  unfold isInvalidContinuationByte continuesByte
  simp only [bne, and_beq_eq, UInt8.reduceToNat, this]
  congr 1

theorem and_mod (n : Nat) (k : Nat) : n &&& (2 ^ k - 1) = n % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod n k

theorem and_7 (n : Nat) : n &&& 7 = n % 8 := and_mod n 3
theorem and_15 (n : Nat) : n &&& 15 = n % 16 := and_mod n 4
theorem and_31 (n : Nat) : n &&& 31 = n % 32 := and_mod n 5
theorem and_63 (n : Nat) : n &&& 63 = n % 64 := and_mod n 6

/-- The `|||` of a multiple of `2 ^ k` and a number below `2 ^ k` is their sum. -/
theorem or_eq_add {a b c k : Nat} (hc : c = 2 ^ k) (ha : a % c = 0) (hb : b < c) :
    a ||| b = a + b := by
  subst hc
  obtain ⟨q, rfl⟩ : ∃ q, a = q * 2 ^ k :=
    ⟨a / 2 ^ k, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ha)).symm⟩
  exact or_add k hb

theorem assemble₂Unchecked_toNat (w x : UInt8) :
    (assemble₂Unchecked w x).toNat = w.toNat % 32 * 64 + x.toNat % 64 := by
  unfold assemble₂Unchecked
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow,
    and_31, and_63]
  rw [Nat.mod_eq_of_lt (a := w.toNat % 32 * 64) (by omega),
    or_eq_add (k := 6) rfl (by omega) (by omega)]

theorem assemble₃Unchecked_toNat (w x y : UInt8) :
    (assemble₃Unchecked w x y).toNat = w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 := by
  unfold assemble₃Unchecked
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow,
    and_15, and_63]
  rw [Nat.mod_eq_of_lt (a := w.toNat % 16 * 4096) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat % 64 * 64) (by omega),
    or_eq_add (a := w.toNat % 16 * 4096) (k := 12) rfl (by omega) (by omega),
    or_eq_add (k := 6) rfl (by omega) (by omega)]

theorem assemble₄Unchecked_toNat (w x y z : UInt8) :
    (assemble₄Unchecked w x y z).toNat =
      w.toNat % 8 * 262144 + x.toNat % 64 * 4096 + y.toNat % 64 * 64 + z.toNat % 64 := by
  unfold assemble₄Unchecked
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow,
    and_7, and_63]
  rw [Nat.mod_eq_of_lt (a := w.toNat % 8 * 262144) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat % 64 * 4096) (by omega),
    Nat.mod_eq_of_lt (a := y.toNat % 64 * 64) (by omega),
    or_eq_add (a := w.toNat % 8 * 262144) (k := 18) rfl (by omega) (by omega),
    or_eq_add (a := w.toNat % 8 * 262144 + x.toNat % 64 * 4096) (k := 12) rfl (by omega) (by omega),
    or_eq_add (k := 6) rfl (by omega) (by omega)]

/-- The size of the encoding of a character, by its value. -/
theorem utf8Size_eq (c : Char) : c.utf8Size =
    if c.val.toNat ≤ 0x7f then 1 else if c.val.toNat ≤ 0x7ff then 2
    else if c.val.toNat ≤ 0xffff then 3 else 4 := by
  unfold Char.utf8Size
  simp only [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]

/-- The size of the character that two bytes decode to, none when they decode
to none. -/
theorem assemble₂_map (w x : UInt8) : (assemble₂ w x).map Char.utf8Size =
    if continuesByte x.toNat ∧ 0x80 ≤ w.toNat % 32 * 64 + x.toNat % 64 then some 2 else none := by
  have e := assemble₂Unchecked_toNat w x
  unfold assemble₂
  split_ifs <;> simp_all [isInvalidContinuationByte_eq, UInt32.lt_iff_toNat_lt, utf8Size_eq]
  split_ifs <;> omega

theorem assemble₃_map (w x y : UInt8) : (assemble₃ w x y).map Char.utf8Size =
    if continuesByte x.toNat ∧ continuesByte y.toNat ∧
      0x800 ≤ w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 ∧
      ¬ (0xd800 ≤ w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 ∧
        w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 ≤ 0xdfff) then some 3 else none := by
  have e := assemble₃Unchecked_toNat w x y
  unfold assemble₃
  split_ifs <;> simp_all [isInvalidContinuationByte_eq, UInt32.lt_iff_toNat_lt,
    UInt32.le_iff_toNat_le, utf8Size_eq]
  split_ifs <;> omega

theorem assemble₄_map (w x y z : UInt8) : (assemble₄ w x y z).map Char.utf8Size =
    if continuesByte x.toNat ∧ continuesByte y.toNat ∧ continuesByte z.toNat ∧
      0x10000 ≤ w.toNat % 8 * 262144 + x.toNat % 64 * 4096 + y.toNat % 64 * 64 + z.toNat % 64 ∧
      w.toNat % 8 * 262144 + x.toNat % 64 * 4096 + y.toNat % 64 * 64 + z.toNat % 64 ≤ 0x10ffff
    then some 4 else none := by
  have e := assemble₄Unchecked_toNat w x y z
  unfold assemble₄
  split_ifs <;> simp_all [isInvalidContinuationByte_eq, UInt32.lt_iff_toNat_lt, utf8Size_eq]
  split_ifs <;> omega

/-- The rest of `scalar_end` after the first byte, for a sequence of `len`
bytes whose second byte lies in `[lo, hi]`. -/
def scalarTail (b : ByteArray) (i e len lo hi : Nat) : Option Nat :=
  if e - i < len then none
  else if b[i + 1]!.toNat < lo then none
  else if hi < b[i + 1]!.toNat then none
  else if 3 ≤ len then
    if continuesByte b[i + 2]!.toNat then
      if len = 4 then (if continuesByte b[i + 3]!.toNat then some (i + len) else none)
      else some (i + len)
    else none
  else if len = 4 then (if continuesByte b[i + 3]!.toNat then some (i + len) else none)
  else some (i + len)

/-- The index after the UTF-8 encoding of the scalar value at `i`, which lies
before `e`, or none when the bytes there encode none, by the table of the
first byte of `scalar_end`. -/
def scalarEnd (b : ByteArray) (i e : Nat) : Option Nat :=
  if b[i]!.toNat < 0x80 then some (i + 1)
  else if 0xc2 ≤ b[i]!.toNat ∧ b[i]!.toNat ≤ 0xdf then scalarTail b i e 2 0x80 0xbf
  else if b[i]!.toNat = 0xe0 then scalarTail b i e 3 0xa0 0xbf
  else if b[i]!.toNat = 0xed then scalarTail b i e 3 0x80 0x9f
  else if 0xe1 ≤ b[i]!.toNat ∧ b[i]!.toNat ≤ 0xef then scalarTail b i e 3 0x80 0xbf
  else if b[i]!.toNat = 0xf0 then scalarTail b i e 4 0x90 0xbf
  else if 0xf1 ≤ b[i]!.toNat ∧ b[i]!.toNat ≤ 0xf3 then scalarTail b i e 4 0x80 0xbf
  else if b[i]!.toNat = 0xf4 then scalarTail b i e 4 0x80 0x8f
  else none

/-- A byte inside the bytes `[i, e)`. -/
theorem extract_getElem! {b : ByteArray} {i e k : Nat} (h : k < (b.extract i e).size) :
    (b.extract i e)[k] = b[i + k]! := by
  rw [ByteArray.getElem_extract, getElem!_pos]

theorem assemble₁_map (w : UInt8) (h) (hw : w.toNat < 0x80) :
    (assemble₁ w h).map Char.utf8Size = some 1 := by
  simp only [assemble₁, Option.map_some, utf8Size_eq, UInt8.toNat_toUInt32,
    show w.toNat ≤ 0x7f by omega, ↓reduceIte]

/-! The first byte -/

section First

variable {b : ByteArray} {i e : Nat}

theorem scalarEnd_ascii (h : b[i]!.toNat < 0x80) : scalarEnd b i e = some (i + 1) := by
  simp only [scalarEnd, h, ↓reduceIte]

end First

theorem scalarTail_short {b : ByteArray} {i e len lo hi : Nat} (h : e - i < len) :
    scalarTail b i e len lo hi = none := by
  simp only [scalarTail, h, ↓reduceIte]

theorem scalarTail_two {b : ByteArray} {i e lo hi : Nat} (h : ¬ e - i < 2) :
    scalarTail b i e 2 lo hi =
      if lo ≤ b[i + 1]!.toNat ∧ b[i + 1]!.toNat ≤ hi then some (i + 2) else none := by
  unfold scalarTail
  split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarTail_three {b : ByteArray} {i e lo hi : Nat} (h : ¬ e - i < 3) :
    scalarTail b i e 3 lo hi =
      if lo ≤ b[i + 1]!.toNat ∧ b[i + 1]!.toNat ≤ hi ∧
        0x80 ≤ b[i + 2]!.toNat ∧ b[i + 2]!.toNat ≤ 0xbf then some (i + 3) else none := by
  unfold scalarTail continuesByte
  simp only [decide_eq_true_eq]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarTail_four {b : ByteArray} {i e lo hi : Nat} (h : ¬ e - i < 4) :
    scalarTail b i e 4 lo hi =
      if lo ≤ b[i + 1]!.toNat ∧ b[i + 1]!.toNat ≤ hi ∧
        0x80 ≤ b[i + 2]!.toNat ∧ b[i + 2]!.toNat ≤ 0xbf ∧
        0x80 ≤ b[i + 3]!.toNat ∧ b[i + 3]!.toNat ≤ 0xbf then some (i + 4) else none := by
  unfold scalarTail continuesByte
  simp only [decide_eq_true_eq]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem ite_some_map {P Q : Prop} [Decidable P] [Decidable Q] (i k : Nat) (h : P ↔ Q) :
    (if P then some (i + k) else none) = Option.map (i + ·) (if Q then some k else none) := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · simp [hp, mt h.mpr hp]

theorem none_eq_map {Q : Prop} [Decidable Q] (f : Nat → Nat) (k : Nat) (h : ¬ Q) :
    none = Option.map f (if Q then some k else none) := by
  simp [h]

section Classes

variable {b : ByteArray} {i e : Nat}

theorem scalarEnd_two (h : 0xc2 ≤ b[i]!.toNat ∧ b[i]!.toNat ≤ 0xdf) :
    scalarEnd b i e = scalarTail b i e 2 0x80 0xbf := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarEnd_e0 (h : b[i]!.toNat = 0xe0) : scalarEnd b i e = scalarTail b i e 3 0xa0 0xbf := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarEnd_ed (h : b[i]!.toNat = 0xed) : scalarEnd b i e = scalarTail b i e 3 0x80 0x9f := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarEnd_three (h : 0xe1 ≤ b[i]!.toNat ∧ b[i]!.toNat ≤ 0xef) (h' : b[i]!.toNat ≠ 0xed) :
    scalarEnd b i e = scalarTail b i e 3 0x80 0xbf := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarEnd_f0 (h : b[i]!.toNat = 0xf0) : scalarEnd b i e = scalarTail b i e 4 0x90 0xbf := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarEnd_four (h : 0xf1 ≤ b[i]!.toNat ∧ b[i]!.toNat ≤ 0xf3) :
    scalarEnd b i e = scalarTail b i e 4 0x80 0xbf := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarEnd_f4 (h : b[i]!.toNat = 0xf4) : scalarEnd b i e = scalarTail b i e 4 0x80 0x8f := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

theorem scalarEnd_bad (h : (0x80 ≤ b[i]!.toNat ∧ b[i]!.toNat < 0xc2) ∨ 0xf5 ≤ b[i]!.toNat) :
    scalarEnd b i e = none := by
  unfold scalarEnd; split_ifs <;> first | rfl | (exfalso; omega)

end Classes

theorem decode_two {b : ByteArray} {i e : Nat} (hw : 0xc0 ≤ b[i]!.toNat ∧ b[i]!.toNat < 0xe0) :
    scalarEnd b i e = Option.map (i + ·)
      (if 1 < e - i then (assemble₂ b[i]! b[i + 1]!).map Char.utf8Size else none) := by
  have := (b[i + 1]!).toNat_lt
  by_cases h2 : 1 < e - i
  · simp only [h2, ↓reduceIte, assemble₂_map]
    by_cases hc : 0xc2 ≤ b[i]!.toNat
    · rw [scalarEnd_two ⟨hc, by omega⟩, scalarTail_two (by omega)]
      exact ite_some_map i 2 (by simp only [continuesByte, decide_eq_true_eq]; omega)
    · rw [scalarEnd_bad (by omega)]
      exact none_eq_map _ _ (by simp only [continuesByte, decide_eq_true_eq]; omega)
  · simp only [h2, ↓reduceIte, Option.map_none]
    by_cases hc : 0xc2 ≤ b[i]!.toNat
    · rw [scalarEnd_two ⟨hc, by omega⟩, scalarTail_short (by omega)]
    · rw [scalarEnd_bad (by omega)]

theorem decode_three {b : ByteArray} {i e : Nat} (hw : 0xe0 ≤ b[i]!.toNat ∧ b[i]!.toNat < 0xf0) :
    scalarEnd b i e = Option.map (i + ·)
      (if 2 < e - i then (assemble₃ b[i]! b[i + 1]! b[i + 2]!).map Char.utf8Size else none) := by
  have := (b[i + 1]!).toNat_lt
  have := (b[i + 2]!).toNat_lt
  have hrw : scalarEnd b i e = scalarTail b i e 3 (if b[i]!.toNat = 0xe0 then 0xa0 else 0x80)
      (if b[i]!.toNat = 0xed then 0x9f else 0xbf) := by
    by_cases h0 : b[i]!.toNat = 0xe0
    · rw [scalarEnd_e0 h0]; simp only [h0]; rfl
    · by_cases h1 : b[i]!.toNat = 0xed
      · rw [scalarEnd_ed h1]; simp only [h1]; rfl
      · rw [scalarEnd_three (by omega) h1]; simp only [h0, h1, ↓reduceIte]
  rw [hrw]
  by_cases h2 : 2 < e - i
  · simp only [h2, ↓reduceIte, assemble₃_map]
    rw [scalarTail_three (by omega)]
    refine ite_some_map i 3 ?_
    simp only [continuesByte, decide_eq_true_eq]
    split_ifs <;> omega
  · simp only [h2, ↓reduceIte, Option.map_none]
    rw [scalarTail_short (by omega)]

theorem decode_four {b : ByteArray} {i e : Nat} (hw : 0xf0 ≤ b[i]!.toNat ∧ b[i]!.toNat < 0xf8) :
    scalarEnd b i e = Option.map (i + ·)
      (if 3 < e - i then (assemble₄ b[i]! b[i + 1]! b[i + 2]! b[i + 3]!).map Char.utf8Size
       else none) := by
  have := (b[i + 1]!).toNat_lt
  have := (b[i + 2]!).toNat_lt
  have := (b[i + 3]!).toNat_lt
  by_cases hbad : 0xf5 ≤ b[i]!.toNat
  · rw [scalarEnd_bad (Or.inr hbad)]
    split_ifs
    · rw [assemble₄_map]
      exact none_eq_map _ _ (by simp only [continuesByte, decide_eq_true_eq]; omega)
    · rfl
  have hrw : scalarEnd b i e = scalarTail b i e 4 (if b[i]!.toNat = 0xf0 then 0x90 else 0x80)
      (if b[i]!.toNat = 0xf4 then 0x8f else 0xbf) := by
    by_cases h0 : b[i]!.toNat = 0xf0
    · rw [scalarEnd_f0 h0]; simp only [h0]; rfl
    · by_cases h1 : b[i]!.toNat = 0xf4
      · rw [scalarEnd_f4 h1]; simp only [h1]; rfl
      · rw [scalarEnd_four (by omega)]; simp only [h0, h1, ↓reduceIte]
  rw [hrw]
  by_cases h2 : 3 < e - i
  · simp only [h2, ↓reduceIte, assemble₄_map]
    rw [scalarTail_four (by omega)]
    refine ite_some_map i 4 ?_
    simp only [continuesByte, decide_eq_true_eq]
    split_ifs <;> omega
  · simp only [h2, ↓reduceIte, Option.map_none]
    rw [scalarTail_short (by omega)]

/-- `scalarEnd` is the index after the character that
`ByteArray.utf8DecodeChar?` decodes at the start of the bytes `[i, e)`. -/
theorem scalarEnd_eq {b : ByteArray} {i e : Nat} (hi : i < e) (he : e ≤ b.size) :
    scalarEnd b i e = ((b.extract i e).utf8DecodeChar? 0).map (i + ·.utf8Size) := by
  have hs : (b.extract i e).size = e - i := by simp only [ByteArray.size_extract]; omega
  rw [show (fun c : Char => i + c.utf8Size) = (i + ·) ∘ Char.utf8Size from rfl, ← Option.map_map]
  unfold ByteArray.utf8DecodeChar?
  simp only [show 0 < (b.extract i e).size by omega, ↓reduceDIte]
  have w0 := (b[i]!).toNat_lt
  split
  all_goals rename_i h
  all_goals rw [parseFirstByte_eq, extract_getElem!, Nat.add_zero] at h
  · simp only [Option.map_none]
    split_ifs at h <;> cases h
    all_goals exact scalarEnd_bad (by omega)
  · split_ifs at h
    rw [assemble₁_map _ _ (by rw [extract_getElem!, Nat.add_zero]; omega), scalarEnd_ascii ‹_›]
    rfl
  · split_ifs at h
    rw [decode_two (by omega)]
    congr 1
    by_cases h1 : 1 < e - i
    · simp only [h1, ↓reduceIte, show 0 + 1 < (b.extract i e).size by omega, ↓reduceDIte]
      rw [extract_getElem!, extract_getElem!]
      simp only [Nat.add_zero, Nat.zero_add]
    · simp only [h1, ↓reduceIte, show ¬ 0 + 1 < (b.extract i e).size by omega, ↓reduceDIte,
        Option.map_none]
  · split_ifs at h
    rw [decode_three (by omega)]
    congr 1
    by_cases h1 : 2 < e - i
    · simp only [h1, ↓reduceIte, show 0 + 2 < (b.extract i e).size by omega, ↓reduceDIte]
      rw [extract_getElem!, extract_getElem!, extract_getElem!]
      simp only [Nat.add_zero, Nat.zero_add]
    · simp only [h1, ↓reduceIte, show ¬ 0 + 2 < (b.extract i e).size by omega, ↓reduceDIte,
        Option.map_none]
  · split_ifs at h
    rw [decode_four (by omega)]
    congr 1
    by_cases h1 : 3 < e - i
    · simp only [h1, ↓reduceIte, show 0 + 3 < (b.extract i e).size by omega, ↓reduceDIte]
      rw [extract_getElem!, extract_getElem!, extract_getElem!, extract_getElem!]
      simp only [Nat.add_zero, Nat.zero_add]
    · simp only [h1, ↓reduceIte, show ¬ 0 + 3 < (b.extract i e).size by omega, ↓reduceDIte,
        Option.map_none]


/-- Nonempty bytes are UTF-8 exactly when their first character decodes and the
bytes after it are UTF-8. -/
theorem isValidUTF8_iff_decode {a : ByteArray} (h : 0 < a.size) :
    a.IsValidUTF8 ↔
      ∃ c, a.utf8DecodeChar? 0 = some c ∧ (a.extract c.utf8Size a.size).IsValidUTF8 := by
  constructor
  · rintro ⟨m, rfl⟩
    match m with
    | [] => simp at h
    | c :: l =>
      refine ⟨c, List.utf8DecodeChar?_utf8Encode_cons, ?_⟩
      have hc : ([c].utf8Encode).size = c.utf8Size := by
        simp [List.utf8Encode_singleton, String.length_utf8EncodeChar]
      rw [List.utf8Encode_cons, ByteArray.extract_append_eq_right hc.symm (by simp [hc])]
      exact ByteArray.isValidUTF8_utf8Encode
  · rintro ⟨c, hc, hv⟩
    rw [ByteArray.eq_of_utf8DecodeChar?_eq_some hc]
    exact Char.isValidUTF8_toByteArray_utf8EncodeChar.append hv

/-- A step of the check of a range: the encoding at `i` ends at `n`, after `i`
and at most at `e`, and the range is UTF-8 exactly when the rest is. -/
theorem scalarEnd_some {b : ByteArray} {i e n : Nat} (hi : i < e) (he : e ≤ b.size)
    (h : scalarEnd b i e = some n) :
    i < n ∧ n ≤ e ∧ ((b.extract i e).IsValidUTF8 ↔ (b.extract n e).IsValidUTF8) := by
  have hs : (b.extract i e).size = e - i := by simp only [ByteArray.size_extract]; omega
  rw [scalarEnd_eq hi he] at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some hc
  have hpos := c.utf8Size_pos
  have hx : (b.extract i e).extract c.utf8Size (b.extract i e).size =
      b.extract (i + c.utf8Size) e := by
    rw [ByteArray.extract_extract, hs, show i + (e - i) = e by omega, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  rw [isValidUTF8_iff_decode (by omega), ← hx]
  constructor
  · rintro ⟨c', hc', hv⟩
    rw [hc] at hc'
    cases hc'
    exact hv
  · intro hv
    exact ⟨c, hc, hv⟩

/-- A range whose first bytes encode no scalar value is not UTF-8. -/
theorem scalarEnd_none {b : ByteArray} {i e : Nat} (hi : i < e) (he : e ≤ b.size)
    (h : scalarEnd b i e = none) : ¬ (b.extract i e).IsValidUTF8 := by
  have hs : (b.extract i e).size = e - i := by simp only [ByteArray.size_extract]; omega
  rw [scalarEnd_eq hi he, Option.map_eq_none_iff] at h
  rw [isValidUTF8_iff_decode (by omega), h]
  simp

/-- An empty range is UTF-8. -/
theorem isValidUTF8_extract_of_le {b : ByteArray} {i e : Nat} (h : e ≤ i) :
    (b.extract i e).IsValidUTF8 := by
  rw [(ByteArray.extract_eq_empty_iff).mpr (Nat.le_trans (Nat.min_le_left _ _) h)]
  exact ByteArray.isValidUTF8_empty

/-! ## Names -/

/-- A character of a property name, or with `property` false of a node name. -/
def nameChar (property : Bool) (c : Char) : Bool :=
  if property then isPropertyNameChar c else isNodeNameChar c

theorem isAlphanum_ofNat_all : ∀ n, n < 256 → (Char.ofNat n).isAlphanum =
    decide ((48 ≤ n ∧ n ≤ 57) ∨ (97 ≤ n ∧ n ≤ 122) ∨ (65 ≤ n ∧ n ≤ 90)) := by
  decide +kernel

/-- An ASCII letter or digit, on a byte as `alphanumeric` tests it. -/
theorem isAlphanum_ofNat {n : Nat} (h : n < 256) : (Char.ofNat n).isAlphanum =
    decide ((48 ≤ n ∧ n ≤ 57) ∨ (97 ≤ n ∧ n ≤ 122) ∨ (65 ≤ n ∧ n ≤ 90)) :=
  isAlphanum_ofNat_all n h

theorem nameChar_ofNat_all : ∀ p : Bool, ∀ n, n < 256 → nameChar p (Char.ofNat n) =
    decide (((48 ≤ n ∧ n ≤ 57) ∨ (97 ≤ n ∧ n ≤ 122) ∨ (65 ≤ n ∧ n ≤ 90)) ∨ n = 44 ∨ n = 46 ∨
      n = 95 ∨ n = 43 ∨ n = 45 ∨ (p = true ∧ (n = 63 ∨ n = 35)) ∨ (p = false ∧ n = 64)) := by
  decide +kernel

/-- A character of a name, on a byte as `name_byte` tests it. -/
theorem nameChar_ofNat (p : Bool) {n : Nat} (h : n < 256) : nameChar p (Char.ofNat n) =
    decide (((48 ≤ n ∧ n ≤ 57) ∨ (97 ≤ n ∧ n ≤ 122) ∨ (65 ≤ n ∧ n ≤ 90)) ∨ n = 44 ∨ n = 46 ∨
      n = 95 ∨ n = 43 ∨ n = 45 ∨ (p = true ∧ (n = 63 ∨ n = 35)) ∨ (p = false ∧ n = 64)) :=
  nameChar_ofNat_all p n h

/-- The character of a number below the surrogates. -/
theorem toNat_ofNat_lt {n : Nat} (h : n < 0xd800) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  simp only [show n.isValidChar from Or.inl h, ↓reduceDIte]
  simp [Char.ofNatAux, Char.toNat]

@[simp] theorem nameChar_true : nameChar true = isPropertyNameChar := rfl

@[simp] theorem nameChar_false : nameChar false = isNodeNameChar := rfl

/-- Every character of a name is ASCII. -/
theorem nameChar_lt {p : Bool} {c : Char} (h : nameChar p c = true) : c.toNat < 128 := by
  cases p <;> simp only [nameChar, isNodeNameChar, isPropertyNameChar, Char.isAlphanum,
    Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit, Bool.false_eq_true, ↓reduceIte,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_cons, List.contains_nil,
    Bool.or_false, beq_iff_eq, UInt32.le_iff_toNat_le, Char.toNat_val, ← Char.toNat_inj,
    Char.reduceToNat] at h
  all_goals omega

/-- The bytes of a string, character by character. -/
theorem toList_toByteArray_string (s : String) :
    s.toByteArray.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [← String.utf8Encode_toList, List.utf8Encode, toList_eq_data, List.data_toByteArray]

theorem nameChar_ofNat_false {p : Bool} {n : Nat} (h1 : 128 ≤ n) (h2 : n < 0xd800) :
    nameChar p (Char.ofNat n) = false := by
  cases hn : nameChar p (Char.ofNat n)
  · rfl
  · have := nameChar_lt hn
    rw [toNat_ofNat_lt h2] at this
    omega

/-- The bytes of the encoding of a character are all name characters exactly
when the character is one. -/
theorem all_utf8EncodeChar (p : Bool) (c : Char) :
    (String.utf8EncodeChar c).all (fun x => nameChar p (Char.ofNat x.toNat)) = nameChar p c := by
  by_cases h : c.val.toNat ≤ 0x7f
  · simp only [String.utf8EncodeChar, h, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Char.toNat_val, Char.ofNat_toNat]
  · have hf : nameChar p c = false := by
      cases hn : nameChar p c
      · rfl
      · have := nameChar_lt hn
        rw [← Char.toNat_val] at this
        omega
    rw [hf]
    unfold String.utf8EncodeChar
    simp only [h, ↓reduceIte]
    split_ifs
    all_goals
      rw [List.all_cons, UInt8.toNat_ofNat', nameChar_ofNat_false (by omega) (by omega),
        Bool.false_and]

/-- The bytes of a UTF-8 string are all name characters exactly when its
characters are. -/
theorem all_nameChar {a : ByteArray} {s : String} (h : String.fromUTF8? a = some s) (p : Bool) :
    a.toList.all (fun x => nameChar p (Char.ofNat x.toNat)) = s.toList.all (nameChar p) := by
  rw [← toByteArray_of_fromUTF8? h, toList_toByteArray_string, List.all_flatMap]
  simp only [all_utf8EncodeChar]

/-! ## Padding -/

/-- The `&&&` of a number of `w` bits with all ones but the two low bits
clears those two bits: the rounding down to a multiple of 4 of `align4`. -/
theorem land_mask4 {x w : Nat} (hw : 2 ≤ w) (hx : x < 2 ^ w) :
    x &&& (2 ^ w - 1 - 3) = x / 4 * 4 := by
  have e1 : 2 ^ w - 1 - 3 = (2 ^ (w - 2) - 1) <<< 2 := by
    have : 2 ^ w = 2 ^ (w - 2) * 4 := by
      rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add, Nat.sub_add_cancel hw]
    have h1 : 1 ≤ 2 ^ (w - 2) := Nat.one_le_two_pow
    rw [Nat.shiftLeft_eq, this]
    show 2 ^ (w - 2) * 4 - 1 - 3 = (2 ^ (w - 2) - 1) * 4
    rw [Nat.sub_mul]; omega
  have e2 : x / 4 * 4 = (x >>> 2) <<< 2 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [e1, e2]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 2 ≤ i
  · rw [show 2 + (i - 2) = i by omega]
    by_cases hiw : i < w
    · simp [hi, show i - 2 < w - 2 by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  · simp [hi]

theorem le_align4 (n : Nat) : n ≤ align4 n := by unfold align4; omega

theorem align4_lt (n : Nat) : align4 n < n + 4 := by unfold align4; omega

theorem align4_mod (n : Nat) : align4 n % 4 = 0 := by unfold align4; omega

/-! ## Tokens of a checked structure block -/

/-- A word that `u32At` reads lies inside the bytes. -/
theorem u32At_ok_le {b : ByteArray} {i : Nat} {w : UInt32} (h : u32At b i = .ok w) :
    i + 4 ≤ b.size := by
  unfold u32At at h
  split at h
  · assumption
  · cases h

/-- A token of a structure block that the parse checked, read without checking
it again, as `fdt::nodes::Piece`: a begin node with the offset of the NUL after
its name, an end node, a property with the offset of its name in the strings
block and the offsets of its value, a no-operation, and the end token. -/
inductive Piece where
  | beginNode (nameEnd : Nat)
  | endNode
  | property (nameOffset valueStart valueEnd : Nat)
  | nop
  | endToken
  deriving DecidableEq

/-- `piece_at`: the token at `cursor` of the structure block `b` and the
offset of the next, or none where the block ends. -/
def pieceAt (b : ByteArray) (cursor : Nat) : Option (Piece × Nat) :=
  match u32At b cursor with
  | .error _ => none
  | .ok tag =>
    if tag.toNat = 1 then
      (findNul b (cursor + 4)).map fun nul => (.beginNode nul, align4 (nul + 1))
    else if tag.toNat = 3 then
      match u32At b (cursor + 4), u32At b (cursor + 8) with
      | .ok length, .ok off =>
        if b.size < cursor + 12 + length.toNat then none
        else some (.property off.toNat (cursor + 12) (cursor + 12 + length.toNat),
          align4 (cursor + 12 + length.toNat))
      | _, _ => none
    else if tag.toNat = 2 then some (.endNode, cursor + 4)
    else if tag.toNat = 4 then some (.nop, cursor + 4)
    else some (.endToken, cursor + 4)

/-- A string that `cString` reads: the NUL that `findNul` finds, the index after
it, and the string of the bytes before it. -/
theorem cString_ok {b : ByteArray} {start e : Nat} {s : String}
    (h : cString b start = .ok (s, e)) :
    ∃ nul, findNul b start = some nul ∧ e = nul + 1 ∧
      String.fromUTF8? (b.extract start nul) = some s := by
  unfold cString at h
  split at h
  · cases h
  · rename_i nul hnul
    split at h
    · cases h
    · rename_i s' hs
      cases h
      exact ⟨nul, hnul, rfl, hs⟩

/-- The NUL of a string that `cString` reads lies `s.utf8ByteSize` bytes after
its start. -/
theorem cString_nul {b : ByteArray} {start e : Nat} {s : String}
    (h : cString b start = .ok (s, e)) : findNul b start = some (start + s.utf8ByteSize) ∧
      e = start + s.utf8ByteSize + 1 := by
  obtain ⟨nul, hnul, rfl, hs⟩ := cString_ok h
  obtain ⟨h1, h2, -, -⟩ := findNul_some hnul
  have hsz := utf8ByteSize_of_fromUTF8? hs
  rw [ByteArray.size_extract] at hsz
  have : nul = start + s.utf8ByteSize := by omega
  subst this
  exact ⟨hnul, rfl⟩

/-- The bytes of a string that `cString` reads are those of the string. -/
theorem cString_extract {b : ByteArray} {start e : Nat} {s : String}
    (h : cString b start = .ok (s, e)) :
    b.extract start (start + s.utf8ByteSize) = s.toByteArray := by
  obtain ⟨nul, hnul, -, hs⟩ := cString_ok h
  have := (cString_nul h).1
  rw [hnul] at this
  cases this
  exact (toByteArray_of_fromUTF8? hs).symm

/-- The end of the padding that `paddedEnd` gives. -/
theorem paddedEnd_ok {b : ByteArray} {e a : Nat} {z : Bool} (h : paddedEnd b e z = .ok a) :
    a = align4 e ∧ align4 e ≤ b.size := by
  unfold paddedEnd at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact ⟨rfl, by omega⟩

/-- The sum that `checkedAdd` gives. -/
theorem checkedAdd_ok {a b v : Nat} (h : checkedAdd a b = .ok v) : v = a + b := by
  unfold checkedAdd at h
  split at h
  · cases h; rfl
  · cases h

/-- What `pieceAt` reads of a token that `decodeToken` gives: the same kind of
token, the offset of the next, and for a begin node the NUL after its nm,
for a property the offset of its name, whose string is the name, and the
offsets of its value. -/
def TokenPiece (str strs : ByteArray) (c next : Nat) : Token → Prop
  | .beginNode nm => pieceAt str c = some (.beginNode (c + 4 + nm.utf8ByteSize), next)
  | .endNode => pieceAt str c = some (.endNode, next)
  | .property nm value => ∃ off e, cString strs off = .ok (nm, e) ∧
      value = str.extract (c + 12) (c + 12 + value.size) ∧
      pieceAt str c = some (.property off (c + 12) (c + 12 + value.size), next)
  | .nop => pieceAt str c = some (.nop, next)
  | .endStructure => pieceAt str c = some (.endToken, next)

/-- `pieceAt` reads each token that `decodeToken` gives, without checking it
again. -/
theorem pieceAt_of_decodeToken {str strs : ByteArray} {c next : Nat} {tok : Token}
    (h : decodeToken str strs c = .ok (tok, next)) : TokenPiece str strs c next tok := by
  unfold decodeToken at h
  obtain ⟨tag, htag, h⟩ := except_bind_ok.1 h
  split at h
  · rename_i ht
    obtain ⟨⟨nm, e⟩, hcs, h⟩ := except_bind_ok.1 h
    obtain ⟨a, hpe, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    cases except_pure_ok.1 h
    obtain ⟨hnul, rfl⟩ := cString_nul hcs
    obtain ⟨rfl, -⟩ := paddedEnd_ok hpe
    simp only [TokenPiece, pieceAt, htag, ht, ↓reduceIte, hnul, Option.map_some]
  · rename_i ht
    cases except_pure_ok.1 h
    simp only [TokenPiece, pieceAt, htag, ht, Nat.reduceEqDiff, ↓reduceIte]
  · rename_i ht
    obtain ⟨len, hlen, h⟩ := except_bind_ok.1 h
    obtain ⟨off, hoff, h⟩ := except_bind_ok.1 h
    obtain ⟨ve, hve, h⟩ := except_bind_ok.1 h
    obtain ⟨hsz, h⟩ := except_jp_ok h
    obtain ⟨⟨nm, e'⟩, hcs, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨a, hpe, h⟩ := except_bind_ok.1 h
    cases except_pure_ok.1 h
    obtain rfl := checkedAdd_ok hve
    obtain ⟨rfl, -⟩ := paddedEnd_ok hpe
    have hvs : (str.extract (c + 4 + 8) (c + 4 + 8 + len.toNat)).size = len.toNat := by
      rw [ByteArray.size_extract]; omega
    have hoff' : u32At str (c + 8) = .ok off := by
      rw [show c + 8 = c + 4 + 4 by omega]; exact hoff
    have hsz' : ¬ str.size < c + 12 + len.toNat := by omega
    refine ⟨off.toNat, e', hcs, ?_, ?_⟩
    · rw [hvs, show c + 4 + 8 = c + 12 by omega]
    · rw [hvs]
      simp only [pieceAt, htag, ht, hlen, hoff', hsz', Nat.reduceEqDiff, ↓reduceIte,
        show c + 4 + 8 = c + 12 by omega]
  · rename_i ht
    cases except_pure_ok.1 h
    simp only [TokenPiece, pieceAt, htag, ht, Nat.reduceEqDiff, ↓reduceIte]
  · rename_i ht
    cases except_pure_ok.1 h
    simp only [TokenPiece, pieceAt, htag, ht, Nat.reduceEqDiff, ↓reduceIte]
  · exact absurd h (except_throw_ne _ _)

end Krepi.Proofs.Fdt.Refinement
