module

public import Krepi.Proofs.Fdt.Refinement.MemorySpecLemmas
public import Krepi.Proofs.Fdt.Refinement.CpusSpecLemmas
public import Krepi.Spec.Fdt.BootMemory
public import Krepi.SpecProperties.Fdt.Invariants
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: lemmas about the specification of the boot memory

Lemmas about `Krepi.Spec.Fdt.BootMemory` for the refinement proofs of
`Fdt::discover_boot_memory`, `BootMemory::is_available` and
`BootMemory::find_available`. The module imports no generated definitions,
so it is built once and not again for every mutant of the code.

- The pieces of a byte string: `splitAtNul_ne_nil`, `splitAtNul_zero_cons`,
  `splitAtNul_cons_ne`, `splitAtNul_append_zero` (the bytes up to the first
  NUL are the first piece), `splitAtNul_of_not_mem` and `splitAtNul_cut` (the
  piece at a cursor and the pieces after its NUL).
- The discovery: `handOverCheck` (its checks before the memory map, in the
  order of the code) and `checkStorage` (its checks on the memory map), with
  `discoverBootMemory_eq`, `Fdt.discoverBootMemory` as these steps.
- Bytes as the code reads them: `bytesOf_extract_toList`,
  `bytesOf_getElem?_toList`, `findNul_none` (no NUL from a cursor on),
  `findNul_le_of_zero` and `cut_bytes`, the piece at a cursor as the code
  finds it with `find_nul`.
- The entries of `compatible`: `mk_toList_toArray`, `compatibleEntries_bytes`,
  `isEmpty_of_fromUTF8?`, `compatibleEntries_invalid`,
  `compatibleEntries_empty` and `compatibleEntries_valid` (one piece),
  `entries_bind_assoc`, `agrees_true_bind_pure`, `compatibleEntries_any` (a
  required entry matches an entry exactly when it is that entry's piece),
  `all_filter_cons_piece` and `extract_toList_eq_nil`.
- Checks and words of the code: `check_neg_spec` (an `if` of the code that
  goes on when its condition holds, against an `if c then throw e` of the
  specification), `word32_bne_two`, `u64_not_val`, `u64_ite_gt_val`,
  `u64_ite_lt_val` and `bind_ite_ok_prop`.
- Bits without `bv_decide`: `and_two_pow_sub_two_pow` (the bits from `k` up
  of a 64-bit number), `testBit_of_between`, `isPowerOfTwo_iff` (a power of
  two as the code tests it, `a ≠ 0` and `a &&& (a - 1) = 0`),
  `isPowerOfTwo_exists`, `alignUp_pow_ok` and `alignUp_pow_error` (`alignUp`
  to a power of two as the code computes it).
- The exclusions that a candidate touches: `furthestStep` (one exclusion as
  the code keeps it), `foldl_furthestStep`, `furthestOf` (the furthest end, or
  none) with `furthestOf_eq` and `furthestOf_of_foldl`, and `searchRange_succ`,
  one step of `BootMemory.searchRange`.
- The invariants: `consistent_image_valid`, `consistent_dtb_valid`,
  `wellFormed_reserved_valid` and `wellFormed_ram_valid`, the ends that the
  code adds without a check.
-/

@[expose] public section

open Aeneas.Std (Slice U8)
open Krepi.Statements Krepi.Spec.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The pieces of a byte string -/

theorem splitAtNul_ne_nil : ∀ l : List UInt8, splitAtNul l ≠ []
  | [] => by simp [splitAtNul]
  | b :: rest => by
    unfold splitAtNul
    rcases h : splitAtNul rest with _ | ⟨w, ws⟩
    · exact absurd h (splitAtNul_ne_nil rest)
    · simp only
      split <;> simp

/-- A string that starts with a NUL starts with an empty piece. -/
theorem splitAtNul_zero_cons (l : List UInt8) : splitAtNul (0 :: l) = [] :: splitAtNul l := by
  rw [splitAtNul]
  rcases h : splitAtNul l with _ | ⟨w, ws⟩
  · exact absurd h (splitAtNul_ne_nil l)
  · rfl

/-- A byte other than NUL joins the first piece of the rest. -/
theorem splitAtNul_cons_ne {x : UInt8} (hx : x ≠ 0) (l : List UInt8) :
    ∃ w ws, splitAtNul l = w :: ws ∧ splitAtNul (x :: l) = (x :: w) :: ws := by
  rcases h : splitAtNul l with _ | ⟨w, ws⟩
  · exact absurd h (splitAtNul_ne_nil l)
  · refine ⟨w, ws, rfl, ?_⟩
    rw [splitAtNul, h]
    simp [hx]

/-- The bytes up to the first NUL are the first piece. -/
theorem splitAtNul_append_zero : ∀ {a : List UInt8}, 0 ∉ a → ∀ b : List UInt8,
    splitAtNul (a ++ 0 :: b) = a :: splitAtNul b
  | [], _, b => splitAtNul_zero_cons b
  | x :: a, h, b => by
    have hx : x ≠ 0 := fun hx => h (hx ▸ List.mem_cons_self)
    have ih := splitAtNul_append_zero (a := a) (fun h' => h (List.mem_cons_of_mem _ h')) b
    obtain ⟨w, ws, hw, hc⟩ := splitAtNul_cons_ne hx (a ++ 0 :: b)
    rw [List.cons_append, hc]
    rw [ih] at hw
    injection hw with h1 h2
    rw [h1, h2]

/-- A string without a NUL is one piece. -/
theorem splitAtNul_of_not_mem : ∀ {a : List UInt8}, 0 ∉ a → splitAtNul a = [a]
  | [], _ => rfl
  | x :: a, h => by
    have hx : x ≠ 0 := fun hx => h (hx ▸ List.mem_cons_self)
    have ih := splitAtNul_of_not_mem (a := a) (fun h' => h (List.mem_cons_of_mem _ h'))
    obtain ⟨w, ws, hw, hc⟩ := splitAtNul_cons_ne hx a
    rw [hc]
    rw [ih] at hw
    injection hw with h1 h2
    rw [h1, h2]

/-- One piece of a byte string from a cursor: the bytes from `start` up to
`stop`, where the next NUL before `e` is, or `e` without one, and then the
pieces after that NUL. -/
theorem splitAtNul_cut {l : List UInt8} {e start stop : Nat} (h1 : start ≤ stop) (h2 : stop ≤ e)
    (h3 : e ≤ l.length) (hz : stop < e → l[stop]? = some 0)
    (hnz : ∀ k, start ≤ k → k < stop → l[k]? ≠ some 0) :
    splitAtNul ((l.take e).drop start) = (l.drop start).take (stop - start) ::
      (if stop < e then splitAtNul ((l.take e).drop (stop + 1)) else []) := by
  have hsplit : (l.take e).drop start =
      (l.drop start).take (stop - start) ++ (l.take e).drop stop := by
    rw [← List.take_append_drop (stop - start) ((l.take e).drop start), List.drop_drop,
      List.drop_take, List.take_take, Nat.add_sub_cancel' h1, Nat.min_eq_left (by omega)]
  have hnot : 0 ∉ (l.drop start).take (stop - start) := by
    intro hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_take] at hi
    split at hi
    · rw [List.getElem?_drop] at hi
      exact hnz (start + i) (by omega) (by omega) hi
    · cases hi
  rw [hsplit]
  by_cases hs : stop < e
  · have hlt : stop < (l.take e).length := by rw [List.length_take]; omega
    rw [List.drop_eq_getElem_cons hlt]
    have h0 : (l.take e)[stop] = 0 := by
      have := hz hs
      rw [List.getElem_take]
      rw [List.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    rw [h0, splitAtNul_append_zero hnot]
    simp only [hs, ↓reduceIte]
  · have hse : stop = e := by omega
    subst hse
    simp only [hs, ↓reduceIte]
    have hd : (l.take stop).drop stop = [] :=
      List.drop_eq_nil_of_le (by rw [List.length_take]; omega)
    rw [hd, List.append_nil, splitAtNul_of_not_mem hnot]

/-! ## The discovery of the boot memory -/

/-- The checks of `Fdt.discoverBootMemory` before the memory map, in its
order: the span of the tree, or the error of the first check that fails. -/
def handOverCheck (t : Fdt) (handOver : HandOverProfile) (dtbAddress : UInt64) (image : Span) :
    Except Krepi.Spec.Fdt.Error Span := do
  if handOver.maxBlobSize < t.totalSize then throw .limitExceeded
  if dtbAddress.toNat % 2 ^ handOver.alignmentLog2.toNat != 0 then throw .badAlignment
  let some root ← t.findNode "/" | throw .badTree
  if (← root.addressCells) != 2 then throw .unsupportedCells
  if (← root.sizeCells) != 2 then throw .unsupportedCells
  let some compatible := root.property "compatible" | throw .missingProperty
  checkCompatible handOver.compatible compatible
  let dtb ← Span.new dtbAddress t.totalSize
  if image.size = 0 then throw .emptyRegion
  let _ ← image.endAddr
  if image.touches dtb then throw .overlap
  pure dtb

/-- The checks of `Fdt.discoverBootMemory` on the memory map: the tree, then
the image, inside one RAM range. -/
def checkStorage (memory : MemoryMap) (dtb image : Span) : Except Krepi.Spec.Fdt.Error Unit := do
  if !inOneRange memory.ram dtb then throw .unmapped
  if !inOneRange memory.ram image then throw .unmapped

/-- `Fdt.discoverBootMemory` in the steps of the code: the checks of the
hand-over tree, the memory map, the checks on it and the sum of the RAM
ranges. -/
theorem discoverBootMemory_eq (t : Fdt) (handOver : HandOverProfile) (dtbAddress : UInt64)
    (image : Span) :
    t.discoverBootMemory handOver dtbAddress image =
      handOverCheck t handOver dtbAddress image >>= fun dtb => (do
        let memory ← t.discoverMemory
        checkStorage memory dtb image
        let ramBytes ← memory.ram.foldlM (fun sum s => checkedAdd sum s.size.toNat) 0
        pure { memory, dtb, image, ramBytes := UInt64.ofNat ramBytes,
               maxBlobSize := handOver.maxBlobSize, alignmentLog2 := handOver.alignmentLog2 }) := by
  unfold Fdt.discoverBootMemory handOverCheck checkStorage
  by_cases h1 : handOver.maxBlobSize < t.totalSize
  · simp only [h1, ↓reduceIte]; rfl
  simp only [h1, ↓reduceIte]
  by_cases h2 : (dtbAddress.toNat % 2 ^ handOver.alignmentLog2.toNat != 0) = true
  · simp only [h2, ↓reduceIte]; rfl
  simp only [h2, ↓reduceIte, Bool.false_eq_true]
  rw [findNode_slash_eq_root]
  rcases t.root with _ | root
  · rfl
  rw [except_ok_bind, except_ok_bind]
  dsimp only
  rcases h3 : root.addressCells with e | c
  · rfl
  rw [except_ok_bind, except_ok_bind]
  by_cases h4 : (c != 2) = true
  · simp only [h4, ↓reduceIte]; rfl
  simp only [h4, ↓reduceIte, Bool.false_eq_true]
  rcases h5 : root.sizeCells with e | c'
  · rfl
  rw [except_ok_bind, except_ok_bind]
  by_cases h6 : (c' != 2) = true
  · simp only [h6, ↓reduceIte]; rfl
  simp only [h6, ↓reduceIte, Bool.false_eq_true]
  rcases h7 : root.property "compatible" with _ | v
  · rfl
  dsimp only
  rcases h8 : checkCompatible handOver.compatible v with e | u
  · rfl
  rw [except_ok_bind, except_ok_bind]
  rcases h9 : Span.new dtbAddress t.totalSize with e | dtb
  · rfl
  rw [except_ok_bind, except_ok_bind]
  by_cases h10 : image.size = 0
  · simp only [h10, ↓reduceIte]; rfl
  simp only [h10, ↓reduceIte]
  rcases h11 : image.endAddr with e | x
  · rfl
  rw [except_ok_bind, except_ok_bind]
  by_cases h12 : image.touches dtb = true
  · simp only [h12, ↓reduceIte]; rfl
  simp only [h12, ↓reduceIte, Bool.false_eq_true]
  rcases h13 : t.discoverMemory with e | memory
  · rfl
  simp only [except_ok_bind, pure_bind]
  by_cases h14 : (!inOneRange memory.ram dtb) = true
  · simp only [h14, ↓reduceIte]; rfl
  simp only [h14, ↓reduceIte, Bool.false_eq_true]
  by_cases h15 : (!inOneRange memory.ram image) = true
  · simp only [h15, ↓reduceIte]
  simp only [h15, ↓reduceIte, Bool.false_eq_true]
  rfl

/-! ## Bytes as the code reads them -/

/-- The bytes `[i, j)` of a slice as a list. -/
theorem bytesOf_extract_toList (s : Slice U8) (i j : Nat) :
    ((bytesOf s).extract i j).toList = (((bytesOf s).toList.drop i).take (j - i)) := by
  rw [bytesOf_extract, bytesOf_toList, List.map_take, List.map_drop]

theorem bytesOf_getElem?_toList (s : Slice U8) (i : Nat) :
    (bytesOf s)[i]? = (bytesOf s).toList[i]? := by
  rw [bytesOf_getElem?, bytesOf_toList, List.getElem?_map]

/-- Without a NUL from `s` on, no byte from there is NUL. -/
theorem findNul_none {b : ByteArray} {s : Nat} (h : findNul b s = none) :
    ∀ k, s ≤ k → b[k]? ≠ some 0 := by
  induction hm : b.size - s generalizing s with
  | zero =>
    intro k hk hz
    by_cases hc : k < b.size
    · omega
    · rw [getElem?_neg b k hc] at hz; cases hz
  | succ m ih =>
    have hs : s < b.size := by omega
    by_cases h0 : b[s]? = some 0
    · rw [findNul_zero hs h0] at h; cases h
    · rw [findNul_step hs h0] at h
      intro k hk
      by_cases hks : k = s
      · rw [hks]; exact h0
      · exact ih h (by omega) k (by omega)

/-- The piece at a cursor of the bytes of a slice as the code finds it: the
bytes from `start` up to the next NUL, or up to `e` without one before it, and
after that NUL the pieces of the rest up to `e`. -/
theorem cut_bytes (s : Slice U8) {e start : Nat} (he : e ≤ s.length) (hs : start ≤ e)
    (hfe : ∀ n, findNul (bytesOf s) start = some n → n ≤ e) :
    start ≤ (findNul (bytesOf s) start).getD e ∧ (findNul (bytesOf s) start).getD e ≤ e ∧
    splitAtNul (((bytesOf s).toList.take e).drop start) =
      ((bytesOf s).extract start ((findNul (bytesOf s) start).getD e)).toList ::
        (if (findNul (bytesOf s) start).getD e < e then
          splitAtNul (((bytesOf s).toList.take e).drop ((findNul (bytesOf s) start).getD e + 1))
        else []) := by
  have hl : e ≤ (bytesOf s).toList.length := by rw [bytesOf_toList, List.length_map]; exact he
  rcases hf : findNul (bytesOf s) start with _ | n
  · simp only [Option.getD_none]
    refine ⟨hs, Nat.le_refl _, ?_⟩
    rw [bytesOf_extract_toList]
    refine splitAtNul_cut hs (Nat.le_refl _) hl (fun h => absurd h (Nat.lt_irrefl _)) ?_
    intro k hk _
    rw [← bytesOf_getElem?_toList]
    exact findNul_none hf k hk
  · simp only [Option.getD_some]
    obtain ⟨h1, -, h3, h4⟩ := findNul_some hf
    have hn := hfe n hf
    refine ⟨h1, hn, ?_⟩
    rw [bytesOf_extract_toList]
    refine splitAtNul_cut h1 hn hl (fun _ => by rw [← bytesOf_getElem?_toList]; exact h3) ?_
    intro k hk1 hk2
    rw [← bytesOf_getElem?_toList]
    exact h4 k hk1 hk2

/-- A NUL at `e` bounds every NUL that a search from at most `e` finds. -/
theorem findNul_le_of_zero {b : ByteArray} {e start n : Nat} (hz : b[e]? = some 0)
    (hs : start ≤ e) (h : findNul b start = some n) : n ≤ e := by
  obtain ⟨-, -, -, h4⟩ := findNul_some h
  by_contra hc
  exact h4 e hs (by omega) hz

/-! ## The entries of `compatible` -/

theorem mk_toList_toArray (b : ByteArray) : ByteArray.mk b.toList.toArray = b := by
  rw [byteArray_eq_iff, toList_eq_data (ByteArray.mk _), toList_eq_data b]

/-- The entries of the pieces of a value, at a piece that the code reads as
the bytes `b`. -/
theorem compatibleEntries_bytes (b : ByteArray) (ps : List (List UInt8)) :
    compatibleEntries (b.toList :: ps) =
      match String.fromUTF8? b with
      | none => .error .badString
      | some s => if s.isEmpty then .error .badProperty else
          compatibleEntries ps >>= fun more => pure (s :: more) := by
  rw [compatibleEntries, mk_toList_toArray]
  rfl

/-- A decoded string is empty exactly when its bytes are. -/
theorem isEmpty_of_fromUTF8? {a : ByteArray} {s : String} (h : String.fromUTF8? a = some s) :
    s.isEmpty = decide (a.size = 0) := by
  rw [String.isEmpty, utf8ByteSize_of_fromUTF8? h]
  by_cases h0 : a.size = 0 <;> simp [h0]

/-- The required entries that the entries of the pieces of a value hold are
the pieces themselves: entries are UTF-8, and a byte string decodes to an
entry exactly when it is that entry's piece. -/
theorem compatibleEntries_any : ∀ {ps : List (List UInt8)} {E : List String},
    compatibleEntries ps = .ok E → ∀ r : List UInt8,
      (E.any fun e => String.fromUTF8? ⟨r.toArray⟩ == some e) = ps.any (· == r)
  | [], E, h, r => by
    simp only [compatibleEntries, Except.ok.injEq] at h
    subst h; rfl
  | p :: ps, E, h, r => by
    unfold compatibleEntries at h
    rcases hp : String.fromUTF8? (ByteArray.mk p.toArray) with _ | s <;> rw [hp] at h
    · cases h
    · simp only at h
      split at h
      · cases h
      · rcases hm : compatibleEntries ps with e | E' <;> rw [hm] at h
        · cases h
        · simp only [except_ok_bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          rw [List.any_cons, List.any_cons, compatibleEntries_any hm r]
          congr 1
          by_cases hr : String.fromUTF8? ⟨r.toArray⟩ = some s
          · have h1 := toByteArray_of_fromUTF8? hr
            have h2 := toByteArray_of_fromUTF8? hp
            rw [h1] at h2
            have : r = p := by
              have := congrArg ByteArray.data h2
              simpa using this
            subst this
            simp [hp]
          · have : (p == r) = false := by
              rw [beq_eq_false_iff_ne]
              intro hpr
              subst hpr
              exact hr hp
            rw [this]
            simp only [beq_eq_false_iff_ne]
            exact fun h' => hr (by simpa using h')

/-- A piece that is not UTF-8: `BadString`. -/
theorem compatibleEntries_invalid {b : ByteArray} (h : ¬ b.IsValidUTF8) (ps : List (List UInt8)) :
    compatibleEntries (b.toList :: ps) = .error .badString := by
  rw [compatibleEntries_bytes]
  have : String.fromUTF8? b = none := by
    rcases hb : String.fromUTF8? b with _ | s
    · rfl
    · exact absurd (fromUTF8?_isSome.mp (by rw [hb]; rfl)) h
  rw [this]

/-- An empty piece: `BadProperty`. -/
theorem compatibleEntries_empty {b : ByteArray} (h : b.size = 0) (ps : List (List UInt8)) :
    compatibleEntries (b.toList :: ps) = .error .badProperty := by
  rw [compatibleEntries_bytes]
  have hv : b.IsValidUTF8 := by
    have : b = ByteArray.empty := by
      obtain ⟨d⟩ := b
      have : d = #[] := Array.eq_empty_of_size_eq_zero h
      subst this; rfl
    rw [this]; exact ByteArray.isValidUTF8_empty
  rcases hb : String.fromUTF8? b with _ | s
  · exact absurd (fromUTF8?_isSome.mpr hv) (by rw [hb]; simp)
  · simp only [isEmpty_of_fromUTF8? hb, h, decide_true, ↓reduceIte]

/-- A nonempty UTF-8 piece: its string, then the entries of the rest. -/
theorem compatibleEntries_valid {b : ByteArray} (hv : b.IsValidUTF8) (h : b.size ≠ 0)
    (ps : List (List UInt8)) : ∃ s, compatibleEntries (b.toList :: ps) =
      compatibleEntries ps >>= fun more => pure (s :: more) := by
  rw [compatibleEntries_bytes]
  rcases hb : String.fromUTF8? b with _ | s
  · exact absurd (fromUTF8?_isSome.mpr hv) (by rw [hb]; simp)
  · refine ⟨s, ?_⟩
    simp only [isEmpty_of_fromUTF8? hb, h, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- The entries before a cursor, and one more. -/
theorem entries_bind_assoc (X : Except Krepi.Spec.Fdt.Error (List String)) (s : String)
    (pre : List String) :
    ((X >>= fun more => pure (s :: more)) >>= fun more => pure (pre ++ more)) =
      X >>= fun more => pure ((pre ++ [s]) ++ more) := by
  cases X <;> simp

/-- The agreement of a result whose value is not compared does not see the
entries before a cursor. -/
theorem agrees_true_bind_pure {α β γ ε : Type} {err : ε → Krepi.Spec.Fdt.Error}
    {r : Aeneas.Std.core.result.Result α ε} {X : Except Krepi.Spec.Fdt.Error β} {g : β → γ} :
    Agrees (fun _ _ => True) err r (X >>= fun m => pure (g m)) ↔
      Agrees (fun _ _ => True) err r X := by
  cases r <;> cases X <;> rfl

/-- The nonempty pieces of a list of pieces, tested one piece at a time. -/
theorem all_filter_cons_piece (P : List UInt8) (R : List (List UInt8)) (Q : List UInt8 → Bool) :
    ((P :: R).filter (· != [])).all Q =
      if P = [] then (R.filter (· != [])).all Q else (Q P && (R.filter (· != [])).all Q) := by
  by_cases hP : P = [] <;> simp [hP]

/-- A piece `[i, j)` of the bytes of a slice is empty exactly when `j ≤ i`. -/
theorem extract_toList_eq_nil (s : Slice U8) {i j : Nat} (hj : j ≤ s.length) :
    ((bytesOf s).extract i j).toList = [] ↔ j ≤ i := by
  rw [← List.length_eq_zero_iff, toList_eq_data, Array.length_toList, ← ByteArray.size,
    ByteArray.size_extract, bytesOf_size]
  omega

/-! ## Checks and words of the code -/

section Checks

open Aeneas Aeneas.Std Aeneas.Std.WP

variable {γ δ ε ε' : Type} {rel : γ → δ → Prop} {err : ε → ε'}

/-- An `if` of the code that goes on when its condition holds and returns an
error otherwise, against the join point of an `if c then throw e` of the
specification whose condition is the negation. -/
theorem check_neg_spec {c c' : Prop} [Decidable c] [Decidable c'] (hc : ¬ c ↔ c') {e : ε}
    {e' : ε'} (he : err e = e') {rest : Result (core.result.Result γ ε)}
    {K : Unit → Except ε' δ} {S : Except ε' δ}
    (hrest : c → ¬ c' → rest ⦃ out => Agrees rel err out S ⦄) :
    (if c then rest else Result.ok (.Err e)) ⦃ out =>
      Agrees rel err out (if c' then (throw e' >>= K) else S) ⦄ := by
  by_cases h : c
  · have : ¬ c' := fun x => hc.mpr x h
    simp only [h, this, ↓reduceIte]; exact hrest h this
  · have : c' := hc.mp h
    simp only [h, this, ↓reduceIte, spec_ok]; rw [← he]; rfl

/-- The test of a number of cells against 2. -/
theorem word32_bne_two (c : U32) : ((word32 c != 2) = true) ↔ ((c != 2#u32) = true) := by
  simp only [bne_iff_ne, ne_eq, word32_eq_iff]
  constructor
  · intro h h2; exact h (by rw [h2]; rfl)
  · intro h h2; exact h (UScalar.eq_of_val_eq h2)

/-- The complement of a 64-bit word. -/
theorem u64_not_val (x : U64) : (~~~x).val = 2 ^ 64 - 1 - x.val := by
  show (~~~x.bv).toNat = _
  rw [BitVec.toNat_not]
  rfl

/-- The greater of two words as the code chooses it. -/
theorem u64_ite_gt_val (a b : U64) : (if a > b then a else b).val = max a.val b.val := by
  by_cases h : a > b
  · simp only [h, ↓reduceIte]
    rw [gt_iff_lt, UScalar.lt_equiv] at h
    exact (Nat.max_eq_left (Nat.le_of_lt h)).symm
  · simp only [h, ↓reduceIte]
    rw [gt_iff_lt, UScalar.lt_equiv] at h
    exact (Nat.max_eq_right (Nat.le_of_not_lt h)).symm

/-- The lesser of two words as the code chooses it. -/
theorem u64_ite_lt_val (a b : U64) : (if a < b then a else b).val = min a.val b.val := by
  by_cases h : a < b
  · simp only [h, ↓reduceIte]
    rw [UScalar.lt_equiv] at h
    exact (Nat.min_eq_left (Nat.le_of_lt h)).symm
  · simp only [h, ↓reduceIte]
    rw [UScalar.lt_equiv] at h
    exact (Nat.min_eq_right (Nat.le_of_not_lt h)).symm

/-- A bind on a choice of two values, by a proposition. -/
theorem bind_ite_ok_prop {α β : Type} {c : Prop} [Decidable c] (a b : α) (f : α → Result β) :
    Std.bind (if c then Result.ok a else Result.ok b) f = f (if c then a else b) := by
  by_cases h : c <;> simp only [h, ↓reduceIte, bind_ok]

end Checks

/-! ## Bits -/

/-- The bits from `k` up of a 64-bit number. -/
theorem and_two_pow_sub_two_pow {n k : Nat} (hk : k ≤ 64) (hn : n < 2 ^ 64) :
    n &&& (2 ^ 64 - 2 ^ k) = n / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hm : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [Nat.testBit_and, hm, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hki : k ≤ i
  · rw [Nat.sub_add_cancel hki]
    by_cases hi : i < 64
    · simp [hki, show i - k < 64 - k by omega]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide)
        (by omega)))]
      simp
  · simp [hki]

/-- The bit `k` of a number between `2 ^ k` and `2 ^ (k + 1)`. -/
theorem testBit_of_between {x k : Nat} (h1 : 2 ^ k ≤ x) (h2 : x < 2 ^ (k + 1)) :
    x.testBit k = true := by
  have hd : x / 2 ^ k = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.pow_succ] at h2; omega
  have := Nat.testBit_div_two_pow (n := k) x 0
  rw [hd, Nat.zero_add] at this
  rw [← this]
  rfl

/-- `isPowerOfTwo` as the code tests it: a number other than 0 that shares
no bit with its predecessor. -/
theorem isPowerOfTwo_iff (a : UInt64) :
    isPowerOfTwo a = true ↔ a.toNat ≠ 0 ∧ a.toNat &&& (a.toNat - 1) = 0 := by
  simp only [isPowerOfTwo, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨k, -, hk⟩
    rw [hk, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
    exact ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k), rfl⟩
  · rintro ⟨h0, hand⟩
    have hlt : a.toNat < 2 ^ 64 := UInt64.toNat_lt a
    have hle := Nat.log2_self_le h0
    have hgt := @Nat.lt_log2_self a.toNat
    by_cases he : a.toNat = 2 ^ a.toNat.log2
    · refine ⟨a.toNat.log2, ?_, he⟩
      by_contra hc
      have : 2 ^ 64 ≤ 2 ^ a.toNat.log2 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exfalso
      have t1 := testBit_of_between hle hgt
      have t2 := testBit_of_between (x := a.toNat - 1) (k := a.toNat.log2) (by omega) (by omega)
      have := Nat.testBit_and a.toNat (a.toNat - 1) a.toNat.log2
      rw [hand, t1, t2, Nat.zero_testBit] at this
      cases this

/-- A power of two that `isPowerOfTwo` accepts. -/
theorem isPowerOfTwo_exists {a : UInt64} (h : isPowerOfTwo a = true) :
    ∃ k, k < 64 ∧ a.toNat = 2 ^ k := by
  simp only [isPowerOfTwo, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

/-- `alignUp` to a power of two below `2 ^ 64` whose sum stays within 64
bits: the bits from the alignment up of the sum. -/
theorem alignUp_pow_ok {a k : Nat} (hk : k < 64) (h : a + 2 ^ k - 1 < 2 ^ 64) :
    alignUp a (2 ^ k) = .ok ((a + 2 ^ k - 1) &&& (2 ^ 64 - 2 ^ k)) := by
  rw [and_two_pow_sub_two_pow (by omega) h]
  unfold alignUp
  have : (a + 2 ^ k - 1) / 2 ^ k * 2 ^ k ≤ a + 2 ^ k - 1 := Nat.div_mul_le_self _ _
  simp only [show (a + 2 ^ k - 1) / 2 ^ k * 2 ^ k < 2 ^ 64 by omega, ↓reduceIte]

/-- `alignUp` to a power of two below `2 ^ 64` whose sum leaves 64 bits:
`Overflow`. -/
theorem alignUp_pow_error {a k : Nat} (hk : k < 64) (h : 2 ^ 64 ≤ a + 2 ^ k - 1) :
    alignUp a (2 ^ k) = .error .overflow := by
  unfold alignUp
  have h1 : 2 ^ 64 / 2 ^ k ≤ (a + 2 ^ k - 1) / 2 ^ k := Nat.div_le_div_right h
  have h2 : 2 ^ 64 / 2 ^ k * 2 ^ k = 2 ^ 64 :=
    Nat.div_mul_cancel (Nat.pow_dvd_pow 2 (by omega))
  have h3 := Nat.mul_le_mul_right (2 ^ k) h1
  simp only [show ¬ (a + 2 ^ k - 1) / 2 ^ k * 2 ^ k < 2 ^ 64 by omega, ↓reduceIte]

/-! ## The exclusions that a candidate touches -/

/-- One exclusion in the search of the furthest end that a candidate touches,
as the code keeps it: whether one was touched, and the furthest end. -/
def furthestStep (c : Span) (st : Bool × Nat) (x : Span) : Bool × Nat :=
  if x.touches c then (true, if st.1 then max st.2 x.endNat else x.endNat) else st

/-- The search of the furthest end from a state that holds 0 until an
exclusion is touched. -/
theorem foldl_furthestStep (c : Span) : ∀ (xs : List Span) (st : Bool × Nat),
    (st.1 = false → st.2 = 0) →
    xs.foldl (furthestStep c) st = (st.1 || !(xs.filter (·.touches c)).isEmpty,
      (xs.filter (·.touches c)).foldl (fun e s => max e s.endNat) st.2)
  | [], st, _ => by simp
  | x :: xs, st, h0 => by
    rw [List.foldl_cons]
    by_cases hx : x.touches c = true
    · have ih := foldl_furthestStep c xs (true, if st.1 then max st.2 x.endNat else x.endNat)
        (fun h => by cases h)
      simp only [furthestStep, hx, ↓reduceIte] at ih ⊢
      rw [ih]
      have : (if st.1 = true then max st.2 x.endNat else x.endNat) = max st.2 x.endNat := by
        cases h1 : st.1
        · rw [h0 h1]; simp
        · rfl
      rw [this]
      simp [hx]
    · have hx' : x.touches c = false := by simpa using hx
      have ih := foldl_furthestStep c xs st h0
      simp only [furthestStep, hx', Bool.false_eq_true, ↓reduceIte] at ih ⊢
      rw [ih]
      simp [hx']

/-- The furthest end of the exclusions that a candidate touches, none when it
touches none: the step of `BootMemory.searchRange` after a candidate. -/
def furthestOf (xs : List Span) (c : Span) : Option Nat :=
  if (xs.filter (·.touches c)).isEmpty then none
  else some ((xs.filter (·.touches c)).foldl (fun e s => max e s.endNat) 0)

/-- `furthestOf` as the search of the code keeps it. -/
theorem furthestOf_eq (xs : List Span) (c : Span) :
    furthestOf xs c = if (xs.foldl (furthestStep c) (false, 0)).1 then
      some (xs.foldl (furthestStep c) (false, 0)).2 else none := by
  rw [foldl_furthestStep c xs (false, 0) (fun _ => rfl), furthestOf]
  cases (xs.filter (·.touches c)).isEmpty <;> rfl

/-- The end of the search of the furthest end: the answer of `furthestOf`. -/
theorem furthestOf_of_foldl {xs : List Span} {c : Span} {t : Bool} {e : Nat}
    (h : (t, e) = xs.foldl (furthestStep c) (false, 0)) :
    (if t then some e else none) = furthestOf xs c := by
  rw [furthestOf_eq, ← h]

/-- One step of the search of one RAM range, after a candidate that fits:
the candidate when it touches no exclusion, and otherwise the search from the
furthest end that it touches, aligned up. -/
theorem searchRange_succ (m : BootMemory) (size al bound fuel start : Nat) :
    m.searchRange size al bound (fuel + 1) start =
      if 2 ^ 64 ≤ start + size || bound < start + size then .ok none
      else match furthestOf m.exclusions ⟨UInt64.ofNat start, UInt64.ofNat size⟩ with
        | none => .ok (some ⟨UInt64.ofNat start, UInt64.ofNat size⟩)
        | some e => alignUp e al >>= fun next => m.searchRange size al bound fuel next := by
  rw [BootMemory.searchRange]
  unfold furthestOf
  split
  · rfl
  · dsimp only
    split <;> rfl

/-! ## The invariants -/

theorem consistent_image_valid {M : BootMemory} (h : M.Consistent) : M.image.Valid :=
  h.2.2.2.1.2

theorem consistent_dtb_valid {M : BootMemory} (h : M.Consistent) : M.dtb.Valid := h.1

theorem wellFormed_reserved_valid {M : MemoryMap} (h : M.WellFormed) :
    ∀ r ∈ M.reserved, r.span.Valid := fun r hr => (h.2.2.2.2.2.1 r hr).1.2

theorem wellFormed_ram_valid {M : MemoryMap} (h : M.WellFormed) : ∀ s ∈ M.ram, s.Valid :=
  fun s hs => (h.2.2.1 s hs).2

end Krepi.Proofs.Fdt.Refinement
