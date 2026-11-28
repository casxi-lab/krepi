module

public import Krepi.Proofs.PageTables.Refinement.OwnershipSpecLemmas
public import Krepi.Proofs.PageTables.OwnerLemmas
import Mathlib.Util.CountHeartbeats
import all Aeneas.Std.Scalar.SaturatingOps

/-!
# Page tables: lemmas about the placement of the page ownership table

Lemmas about `Ownership.choose`, `fit`, `scan`, `Ownership.take`,
`Ownership.assign` and `Ownership.reserve` of `Krepi.Spec.PageTables`, in
the forms that the triples of the generated functions of the placement
need, for the proofs below `Krepi.Proofs.PageTables.Refinement`. The module
imports no generated definitions, so it is built once and not again for
every mutant of the code.

- Bits without `bv_decide`: `u64_complement_val` (the complement of a
  64-bit word), `place_and_high_bits` (the bits from `k` up of a 64-bit number),
  `pow_two_of_and_pred` (a number other than 0 that shares no bit with its
  predecessor is a power of two), `isPowerOfTwo_iff_and`, and
  `alignDown_and` (rounding down to a power of two as a mask).
- Words of the code: `u64_max_val`, `u64_min_val` (the greater and the
  lesser of two words as the code chooses them), `ite_ok_eq`,
  `u64_saturating_add_val` (`saturating_add` of the library, whose body
  the module reads with `import all`, as the library does not expose it).
- Rounding: `alignUp_eq_alignDown`, `alignUp_overflow` (a rounding up whose
  sum leaves 64 bits gives `2 ^ 64` or more, for an alignment that divides
  `2 ^ 64`), `alignDown_le_self`.
- The fit of a request: `fit_empty`, `fit_low_overflow`, `fit_low_none`,
  `fit_low_range`, `fit_high_small`, `fit_high_below` and `fit_high_range`,
  each the outcome of `fit` in one case of the code.
- The scan: `placeOrder` (the extents in the order of a direction),
  `placeOrder_length`, `getElem_placeOrder_low`, `getElem_placeOrder_high`,
  `getElem?_placeOrder_low`, `getElem?_placeOrder_high`, `drop_of_getElem?`
  (a list from an index at which it has an element), and `scan_nil_eq`,
  `scan_held`, `scan_free_none`, `scan_free_overflow`, `scan_free_more` and
  `scan_free_ok`, one step of `scan` for each case.
- The pieces of a taken extent: `before_none`, `before_some`, `after_none`,
  `after_some` (the free parts before and after the range, by
  `rangeOf?`).
- The entries: `reserve_ok_eq`, `reserve_error_eq` (`Ownership.reserve`
  after the choice), `choose_eq` (`Ownership.choose` as the nested checks of the
  code), `take_exhausted`, `take_none`, `take_more` and `take_some` (the
  outcomes of `Ownership.take`), `extra_eq` (`Extent.extra` on numbers).
-/

@[expose] public section

open Aeneas Aeneas.Std
open Krepi.Statements Krepi.Spec.PageTables Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Bits -/

/-- The complement of a 64-bit word. -/
theorem u64_complement_val (x : U64) : (~~~x).val = 2 ^ 64 - 1 - x.val := by
  show (~~~x.bv).toNat = _
  rw [BitVec.toNat_not]
  rfl

/-- The bits from `k` up of a 64-bit number. -/
theorem place_and_high_bits {n k : Nat} (hk : k ≤ 64) (hn : n < 2 ^ 64) :
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

private theorem testBit_between {x k : Nat} (h1 : 2 ^ k ≤ x) (h2 : x < 2 ^ (k + 1)) :
    x.testBit k = true := by
  have hd : x / 2 ^ k = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.pow_succ] at h2; omega
  have := Nat.testBit_div_two_pow (n := k) x 0
  rw [hd, Nat.zero_add] at this
  rw [← this]
  rfl

/-- A number other than 0 that shares no bit with its predecessor is a power
of two. -/
theorem pow_two_of_and_pred {n : Nat} (h0 : n ≠ 0) (hand : n &&& (n - 1) = 0) :
    ∃ k, n = 2 ^ k := by
  have hle := Nat.log2_self_le h0
  have hgt := @Nat.lt_log2_self n
  by_cases he : n = 2 ^ n.log2
  · exact ⟨_, he⟩
  · exfalso
    have t1 := testBit_between hle hgt
    have t2 := testBit_between (x := n - 1) (k := n.log2) (by omega) (by omega)
    have := Nat.testBit_and n (n - 1) n.log2
    rw [hand, t1, t2, Nat.zero_testBit] at this
    cases this

theorem isPowerOfTwo_iff_and (n : Nat) :
    isPowerOfTwo n = true ↔ n ≠ 0 ∧ n &&& (n - 1) = 0 := by
  simp only [isPowerOfTwo, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]

/-- Rounding down to a power of two below `2 ^ 64` as the code computes it:
a mask with the complement of the alignment less one. -/
theorem alignDown_and {x a k : Nat} (hx : x < 2 ^ 64) (ha : a = 2 ^ k) (hk : k ≤ 64) :
    x &&& (2 ^ 64 - 1 - (a - 1)) = alignDown x a := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  rw [show 2 ^ 64 - 1 - (a - 1) = 2 ^ 64 - 2 ^ k by omega, place_and_high_bits hk hx, alignDown, ha]

/-- The greater of two words as the code chooses it. -/
theorem u64_max_val (a b : U64) : (if a > b then a else b).val = max b.val a.val := by
  by_cases h : a > b
  · simp only [h, ↓reduceIte]
    rw [gt_iff_lt, UScalar.lt_equiv] at h
    omega
  · simp only [h, ↓reduceIte]
    rw [gt_iff_lt, UScalar.lt_equiv] at h
    omega

/-- The lesser of two words as the code chooses it. -/
theorem u64_min_val (a b : U64) : (if a < b then a else b).val = min b.val a.val := by
  by_cases h : a < b
  · simp only [h, ↓reduceIte]
    rw [UScalar.lt_equiv] at h
    omega
  · simp only [h, ↓reduceIte]
    rw [UScalar.lt_equiv] at h
    omega

/-- A choice of two results that return. -/
theorem ite_ok_eq {α : Type} {c : Prop} [Decidable c] (a b : α) :
    (if c then (Result.ok a : Result α) else Result.ok b) = Result.ok (if c then a else b) := by
  split <;> rfl

/-- `saturating_add` of 64-bit words: the sum, or the largest word. -/
theorem u64_saturating_add_val (x y : U64) :
    (core.num.U64.saturating_add x y).val = min (2 ^ 64 - 1) (x.val + y.val) := by
  unfold core.num.U64.saturating_add UScalar.saturating_add
  simp only [UScalar.val, BitVec.toNat_ofNat, UScalar.max, UScalarTy.numBits]
  omega

/-! ## Rounding -/

theorem alignUp_eq_alignDown (lo a : Nat) : alignUp lo a = alignDown (lo + a - 1) a := rfl

theorem alignDown_le_self (x a : Nat) : alignDown x a ≤ x := Nat.div_mul_le_self _ _

/-- A rounding up whose sum leaves 64 bits, to an alignment that divides
`2 ^ 64`, gives `2 ^ 64` or more. -/
theorem alignUp_overflow {lo a : Nat} (ha : a ∣ 2 ^ 64) (h : 2 ^ 64 ≤ lo + a - 1) :
    2 ^ 64 ≤ alignUp lo a := by
  unfold alignUp
  have h1 : 2 ^ 64 / a ≤ (lo + a - 1) / a := Nat.div_le_div_right h
  have h2 : 2 ^ 64 / a * a = 2 ^ 64 := Nat.div_mul_cancel ha
  have h3 := Nat.mul_le_mul_right a h1
  omega

/-! ## The fit of a request -/

theorem fit_empty (d : Direction) {lo hi bytes align : Nat} (h : hi ≤ lo) :
    fit d lo hi bytes align = .none := by
  simp only [fit, h, ↓reduceIte]

theorem fit_low_overflow {lo hi bytes align : Nat} (h : lo < hi)
    (ho : 2 ^ 64 ≤ alignUp lo align + bytes) : fit .low lo hi bytes align = .overflow := by
  simp only [fit, Nat.not_le.mpr h, ↓reduceIte, ho]

theorem fit_low_none {lo hi bytes align : Nat} (h : lo < hi)
    (ho : alignUp lo align + bytes < 2 ^ 64) (hh : hi < alignUp lo align + bytes) :
    fit .low lo hi bytes align = .none := by
  simp only [fit, Nat.not_le.mpr h, ↓reduceIte, Nat.not_le.mpr ho]
  split
  · rename_i r _
    simp only [Nat.not_le.mpr hh, ↓reduceIte]
  · rfl

theorem fit_low_range {lo hi bytes align : Nat} (h : lo < hi) (hb : 0 < bytes)
    (ho : alignUp lo align + bytes < 2 ^ 64) (hh : alignUp lo align + bytes ≤ hi) :
    ∃ r, fit .low lo hi bytes align = .range r ∧ r.start.toNat = alignUp lo align ∧
      r.len.toNat = bytes := by
  obtain ⟨r, hr, h1, h2⟩ := rangeOf?_exists hb ho
  refine ⟨r, ?_, h1, by unfold PhysRange.endNat at h2; omega⟩
  simp only [fit, Nat.not_le.mpr h, ↓reduceIte, Nat.not_le.mpr ho, hr, hh]

theorem fit_high_small {lo hi bytes align : Nat} (h : lo < hi) (hb : hi < bytes) :
    fit .high lo hi bytes align = .none := by
  simp only [fit, Nat.not_le.mpr h, ↓reduceIte, hb]

theorem fit_high_below {lo hi bytes align : Nat} (h : lo < hi) (hbh : bytes ≤ hi)
    (hs : alignDown (hi - bytes) align < lo) : fit .high lo hi bytes align = .none := by
  simp only [fit, Nat.not_le.mpr h, ↓reduceIte, Nat.not_lt.mpr hbh]
  split
  · simp only [Nat.not_le.mpr hs, ↓reduceIte]
  · rfl

theorem fit_high_range {lo hi bytes align : Nat} (h : lo < hi) (hbh : bytes ≤ hi)
    (hb : 0 < bytes) (hhi : hi < 2 ^ 64) (hs : lo ≤ alignDown (hi - bytes) align) :
    ∃ r, fit .high lo hi bytes align = .range r ∧
      r.start.toNat = alignDown (hi - bytes) align ∧ r.len.toNat = bytes := by
  have := alignDown_le_self (hi - bytes) align
  obtain ⟨r, hr, h1, h2⟩ := rangeOf?_exists (s := alignDown (hi - bytes) align) hb (by omega)
  refine ⟨r, ?_, h1, by unfold PhysRange.endNat at h2; omega⟩
  simp only [fit, Nat.not_le.mpr h, ↓reduceIte, Nat.not_lt.mpr hbh, hr, hs]

/-! ## The scan -/

/-- The extents in the order of the scan of a direction. -/
def placeOrder (d : Direction) (l : List Extent) : List Extent :=
  match d with
  | .low => l
  | .high => l.reverse

theorem placeOrder_length (d : Direction) (l : List Extent) :
    (placeOrder d l).length = l.length := by
  cases d <;> simp [placeOrder]

theorem getElem_placeOrder_low (l : List Extent) {i : Nat} (h : i < l.length) :
    (placeOrder .low l)[i]'(by rwa [placeOrder_length]) = l[i] := rfl

theorem getElem_placeOrder_high (l : List Extent) {i : Nat} (h : i < l.length) :
    (placeOrder .high l)[i]'(by rwa [placeOrder_length]) = l[l.length - 1 - i]'(by omega) := by
  simp only [placeOrder, List.getElem_reverse]

theorem getElem?_placeOrder_low (l : List Extent) (i : Nat) :
    (placeOrder .low l)[i]? = l[i]? := rfl

theorem getElem?_placeOrder_high (l : List Extent) {i : Nat} (h : i < l.length) :
    (placeOrder .high l)[i]? = l[l.length - 1 - i]? := by
  simp only [placeOrder, List.getElem?_reverse h]

/-- A list from an index at which it has an element. -/
theorem drop_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.drop_eq_getElem_cons hi, hx]

section Scan

variable {room bytes align : Nat} {p : Placement}

theorem scan_nil_eq (limited : Bool) :
    scan room bytes align p [] limited =
      .error (if limited then .metadataExhausted else .outOfMemory) := rfl

theorem scan_held {e : Extent} {rest : List Extent} {limited : Bool}
    (h : (e.holding == .free) = false) :
    scan room bytes align p (e :: rest) limited = scan room bytes align p rest limited := by
  rw [scan.eq_2]
  cases hh : e.holding with
  | free => rw [hh] at h; cases h
  | held => rfl

theorem scan_free_none {e : Extent} {rest : List Extent} {limited : Bool}
    (h : (e.holding == .free) = true)
    (hf : fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .none) :
    scan room bytes align p (e :: rest) limited = scan room bytes align p rest limited := by
  have h' : e.holding = .free := by simpa using h
  rw [scan.eq_2]
  simp only [h', hf]

theorem scan_free_overflow {e : Extent} {rest : List Extent} {limited : Bool}
    (h : (e.holding == .free) = true)
    (hf : fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .overflow) :
    scan room bytes align p (e :: rest) limited = .error .addressOverflow := by
  have h' : e.holding = .free := by simpa using h
  rw [scan.eq_2]
  simp only [h', hf]

theorem scan_free_more {e : Extent} {rest : List Extent} {limited : Bool} {r : PhysRange}
    (h : (e.holding == .free) = true)
    (hf : fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .range r)
    (hr : room < e.extra r) :
    scan room bytes align p (e :: rest) limited = scan room bytes align p rest true := by
  have h' : e.holding = .free := by simpa using h
  rw [scan.eq_2]
  simp only [h', hf, hr, ↓reduceIte]

theorem scan_free_ok {e : Extent} {rest : List Extent} {limited : Bool} {r : PhysRange}
    (h : (e.holding == .free) = true)
    (hf : fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .range r)
    (hr : ¬ room < e.extra r) :
    scan room bytes align p (e :: rest) limited = .ok r := by
  have h' : e.holding = .free := by simpa using h
  rw [scan.eq_2]
  simp only [h', hf, hr, ↓reduceIte]

end Scan

/-! ## The entries -/

/-- `Extent.extra` on the numbers of the ranges. -/
theorem extra_eq (e : Extent) (r : PhysRange) :
    e.extra r = (if e.range.start.toNat < r.start.toNat then 1 else 0) +
      (if r.endNat < e.range.endNat then 1 else 0) := rfl

/-- `Ownership.choose` as the nested checks of the code: the pages, then the
alignment, of `2 ^ 52` pages or more, the pages 0, the alignment 0, an
alignment that shares a bit with its predecessor, the counter exhausted,
then the scan. -/
theorem choose_eq {E X : Nat} (t : Ownership E X) (owner pages alignment : UInt64)
    (p : Placement) :
    t.choose owner pages alignment p =
      if 2 ^ 52 ≤ pages.toNat then .error .addressOverflow
      else if 2 ^ 52 ≤ alignment.toNat then .error .addressOverflow
      else if pages.toNat = 0 then .error .invalidSize
      else if alignment.toNat = 0 then .error .invalidAlignment
      else if alignment.toNat &&& (alignment.toNat - 1) ≠ 0 then .error .invalidAlignment
      else if t.counter = .exhausted then .error .generationExhausted
      else (scan (E - t.extents.length) (pages.toNat * PAGE_SIZE) (alignment.toNat * PAGE_SIZE) p
        (placeOrder p.direction t.extents) false).map (⟨owner, ·⟩) := by
  have hp : pages = 0 ↔ pages.toNat = 0 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_zero]
  unfold Ownership.choose
  simp only [PAGE_SIZE]
  by_cases h1 : 2 ^ 52 ≤ pages.toNat
  · simp only [show 2 ^ 64 ≤ pages.toNat * 4096 by omega, decide_true, Bool.true_or, h1,
      ↓reduceIte]; rfl
  by_cases h2 : 2 ^ 52 ≤ alignment.toNat
  · simp only [show 2 ^ 64 ≤ alignment.toNat * 4096 by omega, decide_true, Bool.or_true, h1, h2,
      ↓reduceIte]; rfl
  simp only [show ¬ 2 ^ 64 ≤ pages.toNat * 4096 by omega,
    show ¬ 2 ^ 64 ≤ alignment.toNat * 4096 by omega, decide_false, Bool.or_false, h1, h2,
    Bool.false_eq_true, ↓reduceIte, hp]
  by_cases h3 : pages.toNat = 0
  · simp only [h3, ↓reduceIte]; rfl
  simp only [h3, ↓reduceIte]
  have h4 : (!isPowerOfTwo alignment.toNat) = true ↔
      (alignment.toNat = 0 ∨ alignment.toNat &&& (alignment.toNat - 1) ≠ 0) := by
    rw [Bool.not_eq_true', ← Bool.not_eq_true, isPowerOfTwo_iff_and]; omega
  by_cases h5 : alignment.toNat = 0
  · simp only [h5, ↓reduceIte]; rfl
  by_cases h6 : alignment.toNat &&& (alignment.toNat - 1) = 0
  · simp only [show ¬ (!isPowerOfTwo alignment.toNat) = true from fun h => (h4.1 h).elim h5
      (fun h' => h' h6), h5, h6, ne_eq, not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
    by_cases h7 : t.counter = .exhausted
    · simp only [h7, ↓reduceIte]; rfl
    simp only [h7, ↓reduceIte]
    obtain ⟨d, w⟩ := p
    cases d <;> exact bind_pure_comp _ _
  · simp only [show (!isPowerOfTwo alignment.toNat) = true from h4.2 (Or.inr h6), h5, h6,
      ne_eq, not_false_eq_true, ↓reduceIte]; rfl

section Take

variable {E X : Nat} {t : Ownership E X} {c : Choice} {s : HoldState}

theorem take_exhausted (h : t.counter = .exhausted) :
    t.take c s = .error .generationExhausted := by
  unfold Ownership.take
  simp only [h]; rfl

theorem take_none {g : UInt64} (hg : t.counter = .next g)
    (h : splitFirst (fun e => e.holding == .free && e.range.contains c.range) t.extents [] =
      none) :
    t.take c s = .error .outOfMemory := by
  unfold Ownership.take
  simp only [hg, h]; rfl

theorem take_more {g : UInt64} {before after : List Extent} {e : Extent}
    (hg : t.counter = .next g)
    (h : splitFirst (fun e => e.holding == .free && e.range.contains c.range) t.extents [] =
      some (before, e, after))
    (hm : E - t.extents.length < e.extra c.range) :
    t.take c s = .error .metadataExhausted := by
  unfold Ownership.take
  simp only [hg, h, hm]; rfl

theorem take_some {g : UInt64} {before after : List Extent} {e : Extent}
    (hg : t.counter = .next g)
    (h : splitFirst (fun e => e.holding == .free && e.range.contains c.range) t.extents [] =
      some (before, e, after))
    (hm : ¬ E - t.extents.length < e.extra c.range) :
    t.take c s = .ok ({ t with
      extents := before.reverseAux (e.take c.range (.held c.owner g s) ++ after)
      counter := Counter.after g }, ⟨t.arena, c.owner, g, c.range⟩) := by
  unfold Ownership.take
  simp only [hg, h, hm]; rfl

/-- `Ownership.reserve` after a choice: the take of the choice, reserved,
with a reservation not attempted and with no failure. -/
theorem reserve_ok_eq {owner pages alignment : UInt64} {p : Placement}
    (h : t.choose owner pages alignment p = .ok c) :
    t.reserve owner pages alignment p =
      (t.take c .reserved).map (fun x => (x.1, (⟨x.2, false, 0⟩ : Reservation))) := by
  unfold Ownership.reserve
  rw [h]
  cases h' : t.take c .reserved <;> simp [h', Bind.bind, Except.bind, Except.map, pure,
    Except.pure]

/-- `Ownership.reserve` after a refused request: its error. -/
theorem reserve_error_eq {owner pages alignment : UInt64} {p : Placement} {e : OwnershipError}
    (h : t.choose owner pages alignment p = .error e) :
    t.reserve owner pages alignment p = .error e := by
  unfold Ownership.reserve
  rw [h]
  rfl

/-- No part of a free extent before a range that starts with it. -/
theorem before_none {e : Extent} {r : PhysRange} (h : r.start.toNat ≤ e.range.start.toNat) :
    rangeOf? e.range.start.toNat (r.start.toNat - e.range.start.toNat) = none := by
  unfold rangeOf?
  split
  · rename_i h'; exact absurd h'.1 (by omega)
  · rfl

/-- No part of a free extent after a range that ends with it. -/
theorem after_none {e : Extent} {r : PhysRange} (h : e.range.endNat ≤ r.endNat) :
    rangeOf? r.endNat (e.range.endNat - r.endNat) = none := by
  unfold rangeOf?
  split
  · rename_i h'; exact absurd h'.1 (by omega)
  · rfl

/-- The part of a free extent before a range inside it. -/
theorem before_some {e : Extent} {r : PhysRange} (h : e.range.start.toNat < r.start.toNat) :
    ∃ B, rangeOf? e.range.start.toNat (r.start.toNat - e.range.start.toNat) = some B ∧
      B.start.toNat = e.range.start.toNat ∧ B.len.toNat = r.start.toNat - e.range.start.toNat := by
  have := r.fits
  obtain ⟨B, hB, h1, h2⟩ := rangeOf?_exists (s := e.range.start.toNat)
    (l := r.start.toNat - e.range.start.toNat) (by omega) (by omega)
  exact ⟨B, hB, h1, by unfold PhysRange.endNat at h2; omega⟩

/-- The part of a free extent after a range inside it. -/
theorem after_some {e : Extent} {r : PhysRange} (h : r.endNat < e.range.endNat) :
    ∃ B, rangeOf? r.endNat (e.range.endNat - r.endNat) = some B ∧
      B.start.toNat = r.endNat ∧ B.len.toNat = e.range.endNat - r.endNat := by
  have := e.range.fits
  obtain ⟨B, hB, h1, h2⟩ := rangeOf?_exists (s := r.endNat)
    (l := e.range.endNat - r.endNat) (by omega) (by unfold PhysRange.endNat at *; omega)
  exact ⟨B, hB, h1, by unfold PhysRange.endNat at h1 h2 ⊢; omega⟩

end Take

end Krepi.Proofs.PageTables.Refinement
