module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: lemmas about the reads of the parse

Lemmas that evaluate the reads of the parse of the `fdt` component on byte
arrays, mostly on byte arrays of a list of bytes, `ByteArray.mk l.toArray`,
the form of the trees that the statements build:

- forward steps of the monad `Except`, which rewrite a `do` block one step at
  a time without copying its join points: `bind_eq_of_ok`, `bind_eq_of_error`,
  `jp_eq_of_not`, `jp_eq_of`, `ite_else_eq` and `ite_then_eq`;
- words: `beNat_eq` (a word is the big-endian number `beOf` of the bytes),
  `u32At_mk`, `u64At_mk`, `u32At_of_take`, `beOf_be32`, `beOf_be64`, the words
  of a header written by `be32` (`u32At_words`, `read_word`), and the reads of
  a prefix of the input (`u32At_prefix`);
- lists of bytes: `drop_flatMap_const` (dropping entries of one length),
  `take_drop_of_take`, `extract_mk`, `extract_mk_mid`, `flatMap_split`;
- strings and padding: `cString_mk` (a NUL-terminated UTF-8 string without a
  NUL byte), `fromUTF8?_toByteArray`, `paddedEnd_mk`, `paddedEnd_false`.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Forward steps -/

/-- A bind on a step that succeeds is its continuation on the value. -/
theorem bind_eq_of_ok {ε α β : Type} {x : Except ε α} {a : α} {f : α → Except ε β}
    {r : Except ε β} (hx : x = .ok a) (h : f a = r) : x >>= f = r := by
  subst hx; exact h

/-- A bind on a step that fails fails with its error. -/
theorem bind_eq_of_error {ε α β : Type} {x : Except ε α} {e : ε} {f : α → Except ε β}
    (hx : x = .error e) : x >>= f = .error e := by
  subst hx; rfl

/-- The join point that `do` writes for `if c then throw e` without `else` is the rest of the block
when `c` is false. -/
theorem jp_eq_of_not {ε β : Type} {c : Prop} [Decidable c] {e : ε} {k : Unit → Except ε β}
    {r : Except ε β} (hc : ¬ c) (h : k () = r) : (if c then (throw e >>= k) else k ()) = r := by
  split
  · exact absurd ‹c› hc
  · exact h

/-- The join point that `do` writes for `if c then throw e` without `else` fails with `e` when `c`
holds. -/
theorem jp_eq_of {ε β : Type} {c : Prop} [Decidable c] {e : ε} {k : Unit → Except ε β}
    (hc : c) : (if c then (throw e >>= k) else k ()) = .error e := by
  split
  · rfl
  · exact absurd hc ‹¬c›

/-- An `if` whose condition is false is its `else` branch. -/
theorem ite_else_eq {α : Type} {c : Prop} [Decidable c] {a b r : α} (hc : ¬ c) (h : b = r) :
    (if c then a else b) = r := by
  split
  · exact absurd ‹c› hc
  · exact h

/-- An `if` whose condition holds is its `then` branch. -/
theorem ite_then_eq {α : Type} {c : Prop} [Decidable c] {a b r : α} (hc : c) (h : a = r) :
    (if c then a else b) = r := by
  split
  · exact h
  · exact absurd hc ‹¬c›

/-! ## Words -/

/-- The loop of `ByteArray.toList` from index `i`. -/
theorem toList_loop (b : ByteArray) : ∀ (i : Nat) (r : List UInt8),
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  intro i r
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hi ih =>
    rw [ih]
    have hl : i < b.data.toList.length := by simpa using hi
    have : b.data.toList.drop i = b.get! i :: b.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hl]
      congr 1
      simp [ByteArray.get!, hi]
    simp [this]
  | case2 i r hi =>
    have : b.data.toList.length ≤ i := by simp; exact Nat.le_of_not_lt hi
    simp [List.drop_eq_nil_of_le this]

/-- `ByteArray.toList` is the list of the data. -/
theorem byteArray_toList (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop]

/-- The number that a list of bytes writes in big-endian order. -/
def beOf (l : List UInt8) : Nat := l.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `beNat` is `beOf` of the bytes that it reads. -/
theorem beNat_eq (b : ByteArray) (i n : Nat) :
    beNat b i n = beOf ((b.data.toList.drop i).take n) := by
  simp [beNat, beOf, byteArray_toList, ByteArray.data_extract, Array.toList_extract]

/-- A prefix of the input that the input holds has the asked length. -/
theorem size_prefix {input : ByteArray} {n : Nat} (hn : n ≤ input.size) :
    (input.extract 0 n).size = n := by
  simp [ByteArray.size_extract]; omega

/-- A prefix of the input reads the words that lie inside it as the input does. -/
theorem u32At_prefix {input : ByteArray} {n i : Nat} (hn : n ≤ input.size) (hi : i + 4 ≤ n) :
    u32At (input.extract 0 n) i = u32At input i := by
  have hs := size_prefix hn
  have hb : beNat (input.extract 0 n) i 4 = beNat input i 4 := by
    simp only [beNat_eq, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      List.drop_take, List.take_take, Nat.sub_zero]
    congr 2
    omega
  unfold u32At
  rw [hs, hb]
  split
  · split
    · rfl
    · omega
  · omega

/-- The size of a byte array of a list is its length. -/
theorem size_mk (l : List UInt8) : (ByteArray.mk l.toArray).size = l.length := by
  simp [ByteArray.size]

/-- `ByteArray.extract` of a byte array of a list is the slice of the list. -/
theorem extract_mk (l : List UInt8) (i j : Nat) :
    (ByteArray.mk l.toArray).extract i j = ByteArray.mk ((l.drop i).take (j - i)).toArray := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, List.extract_toArray]

/-- A 32-bit word of a byte array of a list within its length. -/
theorem u32At_mk (l : List UInt8) (i : Nat) (h : i + 4 ≤ l.length) :
    u32At (ByteArray.mk l.toArray) i = .ok (UInt32.ofNat (beOf ((l.drop i).take 4))) := by
  unfold u32At
  rw [size_mk, beNat_eq]
  simp [h]

/-- A 64-bit word of a byte array of a list within its length. -/
theorem u64At_mk (l : List UInt8) (i : Nat) (h : i + 8 ≤ l.length) :
    u64At (ByteArray.mk l.toArray) i = .ok (UInt64.ofNat (beOf ((l.drop i).take 8))) := by
  unfold u64At
  rw [size_mk, beNat_eq]
  simp [h]

/-- `be32` writes 4 bytes. -/
theorem length_be32 (n : Nat) : (be32 n).length = 4 := rfl

/-- `be32 n` reads back as `n` modulo `2 ^ 32`. -/
theorem beOf_be32 (n : Nat) : beOf (be32 n) = n % 2 ^ 32 := by
  simp [be32, beOf, UInt8.toNat_ofNat']
  omega

/-- The big-endian fold from an initial value. -/
theorem foldl_be (l : List UInt8) : ∀ init : Nat,
    l.foldl (fun acc x => acc * 256 + x.toNat) init = init * 256 ^ l.length + beOf l := by
  induction l with
  | nil => simp [beOf]
  | cons x l ih =>
    intro init
    simp only [List.foldl_cons, beOf, List.length_cons]
    rw [ih, ih (0 * 256 + x.toNat), Nat.pow_succ, Nat.mul_comm (256 ^ l.length) 256]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc]
    omega

/-- The big-endian number of two lists of bytes one after the other. -/
theorem beOf_append (l l' : List UInt8) : beOf (l ++ l') = beOf l * 256 ^ l'.length + beOf l' := by
  rw [beOf, List.foldl_append, foldl_be]
  rfl

/-- `be64 n` reads back as `n` modulo `2 ^ 64`. -/
theorem beOf_be64 (n : Nat) : beOf (be64 n) = n % 2 ^ 64 := by
  rw [be64, beOf_append, beOf_be32, beOf_be32, length_be32]
  omega

/-- `be64 n` reads back as the 64-bit word of `n`. -/
theorem ofNat_beOf_be64 (n : Nat) : UInt64.ofNat (beOf (be64 n)) = UInt64.ofNat n := by
  rw [beOf_be64]
  apply UInt64.toNat_inj.1
  simp

/-- Words written by `be32` take 4 bytes each. -/
theorem length_words (ws : List Nat) : (ws.flatMap be32).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, ih, length_be32,
      List.length_cons]; omega

/-- The word of index `k` of words written by `be32`. -/
theorem drop_take_words (R : List UInt8) :
    ∀ (ws : List Nat) (k : Nat) (h : k < ws.length),
      ((ws.flatMap be32 ++ R).drop (4 * k)).take 4 = be32 ws[k]
  | [], _, h => absurd h (by simp)
  | w :: ws, 0, _ => by
    simp only [List.flatMap_cons, List.append_assoc, Nat.mul_zero, List.drop_zero,
      List.getElem_cons_zero]
    exact List.take_left' (length_be32 w)
  | w :: ws, k + 1, h => by
    have := drop_take_words R ws k (by simpa using h)
    simp only [List.flatMap_cons, List.append_assoc]
    rw [show 4 * (k + 1) = (be32 w).length + 4 * k by rw [length_be32]; omega,
      List.drop_length_add_append]
    simpa using this

/-- The word of index `k` of a byte array that starts with words written by `be32`. -/
theorem u32At_words (ws : List Nat) (R : List UInt8) (k : Nat) (h : k < ws.length) :
    u32At (ByteArray.mk (ws.flatMap be32 ++ R).toArray) (4 * k) = .ok (UInt32.ofNat ws[k]) := by
  rw [u32At_mk _ _ ?_, drop_take_words R ws k h, beOf_be32]
  · congr 1
    apply UInt32.toNat_inj.1
    simp
  · simp only [List.length_append, length_words]
    omega

/-- A 32-bit word whose 4 bytes are `be32 v`. -/
theorem u32At_of_take {l : List UInt8} {i v : Nat} (h : (l.drop i).take 4 = be32 v)
    (hv : v < 2 ^ 32) (hl : i + 4 ≤ l.length) :
    u32At (ByteArray.mk l.toArray) i = .ok (UInt32.ofNat v) := by
  rw [u32At_mk _ _ hl, h, beOf_be32, Nat.mod_eq_of_lt hv]

/-! ## Lists of bytes -/

/-- Bytes inside a known prefix of a suffix of a list. -/
theorem take_drop_of_take {l : List UInt8} {c n : Nat} {pre : List UInt8}
    (h : (l.drop c).take n = pre) (a b : Nat) (hab : a + b ≤ n) :
    (l.drop (c + a)).take b = (pre.drop a).take b := by
  rw [← h, ← List.drop_drop, List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- The word of index `k` of words written by `be32` at offset `c` of a list. -/
theorem read_word {l : List UInt8} {c : Nat} {ws : List Nat}
    (h : (l.drop c).take (4 * ws.length) = ws.flatMap be32) (k : Nat) (hk : k < ws.length) :
    (l.drop (c + 4 * k)).take 4 = be32 ws[k] := by
  rw [take_drop_of_take h (4 * k) 4 (by omega)]
  have := drop_take_words [] ws k hk
  simpa using this

/-- Dropping the bytes of the first `k` entries of a list of entries that each write `L` bytes. -/
theorem drop_flatMap_const {α : Type} (f : α → List UInt8) (L : Nat) (T : List UInt8) :
    ∀ (E : List α) (k : Nat), (∀ a ∈ E, (f a).length = L) → k ≤ E.length →
      (E.flatMap f ++ T).drop (L * k) = (E.drop k).flatMap f ++ T
  | E, 0, _, _ => by simp
  | [], _ + 1, _, h => absurd h (by simp)
  | e :: E, k + 1, hf, h => by
    simp only [List.flatMap_cons, List.append_assoc, List.drop_succ_cons]
    rw [show L * (k + 1) = (f e).length + L * k by
        rw [hf e List.mem_cons_self, Nat.mul_succ]; omega,
      List.drop_length_add_append]
    exact drop_flatMap_const f L T E k (fun a ha => hf a (List.mem_cons_of_mem _ ha))
      (by simpa using h)

/-- A block of a byte array of a list between two known parts. -/
theorem extract_mk_mid (P C D : List UInt8) :
    (ByteArray.mk (P ++ (C ++ D)).toArray).extract P.length (P.length + C.length) =
      ByteArray.mk C.toArray := by
  rw [extract_mk, List.drop_left, Nat.add_sub_cancel_left, List.take_left]

/-- The image of the first `k + 1` entries of a list. -/
theorem take_succ_map {α β : Type} (E : List α) (f : α → β) (k : Nat) (hk : k < E.length) :
    (E.take k).map f ++ [f E[k]] = (E.take (k + 1)).map f := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.map_append]
  rfl

/-- The bytes of a list of entries around its entry of index `k`. -/
theorem flatMap_split {α : Type} (f : α → List UInt8) (l : List α) (k : Nat)
    (hk : k < l.length) :
    l.flatMap f = (l.take k).flatMap f ++ (f l[k] ++ (l.drop (k + 1)).flatMap f) := by
  have h := congrArg (List.flatMap f) (List.take_append_drop k l)
  rw [List.drop_eq_getElem_cons hk, List.flatMap_append, List.flatMap_cons] at h
  exact h.symm

/-- Offsets one of which ends before the other starts do not intersect. -/
theorem intersects_false {a ae b be : Nat} (h : ae ≤ b ∨ be ≤ a) :
    intersects a ae b be = false := by
  unfold intersects
  rcases h with h | h
  · have : ¬ b < ae := Nat.not_lt.2 h
    simp [this]
  · have : ¬ a < be := Nat.not_lt.2 h
    simp [this]

/-! ## Strings and padding -/

/-- A byte of a byte array of a list. -/
theorem getElem?_mk (l : List UInt8) (i : Nat) : (ByteArray.mk l.toArray)[i]? = l[i]? := by
  by_cases h : i < l.length
  · rw [getElem?_pos (ByteArray.mk l.toArray) i (by simpa [ByteArray.size] using h),
      List.getElem?_eq_getElem h]
    rfl
  · rw [getElem?_neg (ByteArray.mk l.toArray) i (by simpa [ByteArray.size] using h),
      List.getElem?_eq_none (by omega)]

/-- `findNulFrom` finds the first NUL byte that its fuel reaches. -/
theorem findNulFrom_mk (l : List UInt8) :
    ∀ (fuel i j : Nat), i ≤ j → j < i + fuel →
      (∀ k, i ≤ k → k < j → l[k]? ≠ some 0) →
      l[j]? = some 0 → findNulFrom (ByteArray.mk l.toArray) fuel i = some j
  | 0, _, _, _, h, _, _ => absurd h (by omega)
  | fuel + 1, i, j, hij, hj, hk, h0 => by
    rw [findNulFrom, getElem?_mk]
    by_cases hi : i = j
    · subst hi; simp [h0]
    · have := hk i (Nat.le_refl _) (by omega)
      simp only [this, ite_false]
      exact findNulFrom_mk l fuel (i + 1) j (by omega) (by omega)
        (fun k h1 h2 => hk k (by omega) h2) h0

/-- The bytes of a string decode to it. -/
theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  unfold String.fromUTF8?
  split
  · rfl
  · exact absurd s.isValidUTF8 ‹_›

/-- The bytes of a string are `utf8ByteSize` many. -/
theorem length_toByteArray_toList (s : String) : s.toByteArray.toList.length = s.utf8ByteSize := by
  rw [byteArray_toList]; simp [String.size_toByteArray]

/-- The NUL-terminated string at an offset of a byte array of a list, when its bytes hold no NUL. -/
theorem cString_mk (P R : List UInt8) (s : String) (hs : 0 ∉ s.toByteArray.toList) :
    cString (ByteArray.mk (P ++ (s.toByteArray.toList ++ (0 :: R))).toArray) P.length =
      .ok (s, P.length + s.utf8ByteSize + 1) := by
  have hl := length_toByteArray_toList s
  unfold cString findNul
  rw [findNulFrom_mk _ _ _ (P.length + s.utf8ByteSize) (by omega)
    (by simp only [size_mk, List.length_append, List.length_cons]; omega)]
  · simp only
    rw [extract_mk, List.drop_left, Nat.add_sub_cancel_left, ← hl, List.take_left]
    have : ByteArray.mk s.toByteArray.toList.toArray = s.toByteArray := by
      rw [byteArray_toList]
    rw [this, fromUTF8?_toByteArray]
  · intro k h1 h2 h3
    rw [List.getElem?_append_right h1, List.getElem?_append_left (by omega)] at h3
    exact hs (List.mem_of_getElem? h3)
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp [hl]

/-- The padding after `e` up to a multiple of 4 within the block and of zero bytes. -/
theorem paddedEnd_mk {l : List UInt8} {e : Nat} (h : align4 e ≤ l.length)
    (hz : ∀ x ∈ (l.drop e).take (align4 e - e), x = 0) (z : Bool) :
    paddedEnd (ByteArray.mk l.toArray) e z = .ok (align4 e) := by
  unfold paddedEnd
  rw [size_mk]
  simp only [Nat.not_lt.2 h, ite_false]
  rw [extract_mk, byteArray_toList]
  simp only [Bool.and_eq_true, List.any_eq_true, ne_eq]
  split
  · rename_i hc
    obtain ⟨-, x, hx, hx0⟩ := hc
    exact absurd (hz x hx) (of_decide_eq_true hx0)
  · rfl

/-- The padding after `e` up to a multiple of 4 within the block, unchecked. -/
theorem paddedEnd_false {l : List UInt8} {e : Nat} (h : align4 e ≤ l.length) :
    paddedEnd (ByteArray.mk l.toArray) e false = .ok (align4 e) := by
  unfold paddedEnd
  rw [size_mk]
  simp [Nat.not_lt.2 h]

end Krepi.Proofs.Fdt
