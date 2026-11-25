module

public import Krepi.Statements.Fdt.Representation
public import Krepi.Proofs.Fdt.Refinement.BasicLemmas
public import Krepi.Spec.Fdt.Discovery

/-!
# Device tree: refinement of the word reads, the spans and the cells

The triples of the generated functions that read words of a byte slice, that
build and check spans, and that read a number in cells, each a `@[step]`
lemma, so that the proof of a caller steps over the call with the triple of
the callee and a mutant of a callee fails the proof of the callee alone:

- the word reads of `fdt::format`: `fits_spec` (whether `count` bytes from
  `at` lie in the slice), `u32_at_spec` and `u64_at_spec` (the big-endian
  word of `u32At` and `u64At` of the bytes, or `Truncated`);
- the spans: `span_new_spec`, `span_end_spec` and `span_contains_spec`, the
  statements `SpanNew`, `SpanEnd` and `SpanContains` without their premise;
- the cells: `cells_u64_spec`, the statement `CellsU64` without its premise;
- the helpers of `fdt::span` that the entries share: `below_end_spec`,
  `overlaps_spec`, `touches_spec`, `ends_within_spec`, `holds_spec`,
  `valid_spec`, the loops `touches_any_spec` and `in_one_range_spec`, and
  `prefix_spec` and `part_spec`, the prefixes and parts of a slice.

With them, the spans of the specification of a span of the code:
`spanOf_start`, `spanOf_size`, `spanOf_endNat`, `spanOf_valid_iff`, `spanOf_endAddr`,
`agrees_endAddr_ok` (a success of `Span::end` is the exact end, within 64
bits), `endAddr_eq_error` (a failure is `Overflow` of a span whose end leaves
64 bits) and `spanOf_contains`.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Word reads -/

/-- `fits(bytes, at, count)`: whether `count` bytes from `at` lie in the slice.
-/
@[step] theorem fits_spec (bytes : Slice U8) (i count : Usize) :
    fdt.format.fits bytes i count ⦃ b => b = decide (i.val + count.val ≤ bytes.length) ⦄ := by
  unfold fdt.format.fits
  step*

/-- `u32_at(bytes, at)`: the big-endian 32-bit word of `u32At`, or
`Truncated`. -/
@[step] theorem u32_at_spec (bytes : Slice U8) (off : Usize) :
    fdt.format.u32_at bytes off ⦃ r =>
      Agrees (fun n N => word32 n = N) errorOf r (u32At (bytesOf bytes) off.val) ⦄ := by
  unfold fdt.format.u32_at
  step*
  · have hb : off.val + 4 ≤ bytes.length := of_decide_post b_post ‹_›
    simp only [u32At_bytesOf, hb, ↓reduceIte, agrees_ok_ok]
    rw [word32_ofNat_iff, beNat_bytesOf_four bytes _ hb]
    have g0 : i = bytes.val[off.val]! := by rw [i_post]; exact getElem_eq_getElem! rfl _
    have g1 : i4 = bytes.val[off.val + 1]! := by rw [i4_post]; exact getElem_eq_getElem! i3_post _
    have g2 : i9 = bytes.val[off.val + 2]! := by rw [i9_post]; exact getElem_eq_getElem! i8_post _
    have g3 : i14 = bytes.val[off.val + 3]! := by
      rw [i14_post]; exact getElem_eq_getElem! i13_post _
    rw [← g0, ← g1, ← g2, ← g3]
    have b0 : i.val < 2 ^ 8 := i.hmax
    have b1 : i4.val < 2 ^ 8 := i4.hmax
    have b2 : i9.val < 2 ^ 8 := i9.hmax
    have b3 : i14.val < 2 ^ 8 := i14.hmax
    have e2 : i2.val = i.val * 2 ^ (8 + 16) := by
      rw [i2_post, i1_post, U8.cast_U32_val_eq, Nat.shiftLeft_eq, u32_size]
      exact Nat.mod_eq_of_lt (by omega)
    have e6 : i6.val = i4.val * 2 ^ 16 := by
      rw [i6_post, i5_post, U8.cast_U32_val_eq, Nat.shiftLeft_eq, u32_size]
      exact Nat.mod_eq_of_lt (by omega)
    have e7 : i7.val = (i.val * 2 ^ 8 + i4.val) * 2 ^ (8 + 8) := by
      rw [i7_post, UScalar.val_or, e2, e6, or_shift 16 8 b1]
    have e11 : i11.val = i9.val * 2 ^ 8 := by
      rw [i11_post, i10_post, U8.cast_U32_val_eq, Nat.shiftLeft_eq, u32_size]
      exact Nat.mod_eq_of_lt (by omega)
    have e12 : i12.val = ((i.val * 2 ^ 8 + i4.val) * 2 ^ 8 + i9.val) * 2 ^ 8 := by
      rw [i12_post, UScalar.val_or, e7, e11, or_shift 8 8 b2]
    have e16 : i16.val = ((i.val * 2 ^ 8 + i4.val) * 2 ^ 8 + i9.val) * 2 ^ 8 + i14.val := by
      rw [i16_post, UScalar.val_or, e12, i15_post, U8.cast_U32_val_eq, or_add 8 b3]
    rw [e16]
    omega
  · have hb : ¬ off.val + 4 ≤ bytes.length := of_decide_post_not b_post ‹_›
    simp only [u32At_bytesOf, hb, ↓reduceIte, agrees_err_error]
    rfl

/-- `u64_at(bytes, at)`: the big-endian 64-bit word of `u64At`, or
`Truncated`. -/
@[step] theorem u64_at_spec (bytes : Slice U8) (off : Usize) :
    fdt.format.u64_at bytes off ⦃ r =>
      Agrees (fun n N => word64 n = N) errorOf r (u64At (bytesOf bytes) off.val) ⦄ := by
  unfold fdt.format.u64_at
  step*
  · have hb : off.val + 8 ≤ bytes.length := of_decide_post b_post ‹_›
    have hv := agrees_ok_of_eq (agrees_of_branch_ok cf_post ‹_› r_post)
      (u32At_bytesOf_ok (by omega))
    have hv1 := agrees_ok_of_eq (agrees_of_branch_ok cf1_post ‹_› r1_post)
      (u32At_bytesOf_ok (by omega))
    rw [word32_beNat_iff] at hv hv1
    simp only [u64At_bytesOf, hb, ↓reduceIte, agrees_ok_ok, word64_beNat_iff]
    have b0 : val.val < 2 ^ 32 := val.hmax
    have b1 : val1.val < 2 ^ 32 := val1.hmax
    rw [beNat_bytesOf_eight bytes _ hb, i4_post, UScalar.val_or, i2_post, i1_post, i3_post,
      U32.cast_U64_val_eq, U32.cast_U64_val_eq, Nat.shiftLeft_eq, u64_size,
      Nat.mod_eq_of_lt (by omega), or_add 32 b1, hv, hv1, i_post]
  · exfalso
    have hb : off.val + 8 ≤ bytes.length := of_decide_post b_post ‹_›
    have := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
    rw [u32At_bytesOf_ok (by omega)] at this
    cases this
  · exfalso
    have hb : off.val + 8 ≤ bytes.length := of_decide_post b_post ‹_›
    have := agrees_err_of_branch cf_post ‹_› residual_post ‹_›
    rw [u32At_bytesOf_ok (by omega)] at this
    cases this
  · have hb : ¬ off.val + 8 ≤ bytes.length := of_decide_post_not b_post ‹_›
    simp only [u64At_bytesOf, hb, ↓reduceIte, agrees_err_error]
    rfl

/-! ## Spans of the specification -/

@[simp] theorem spanOf_start (s : fdt.Span) : (spanOf s).start = word64 s.start := rfl

@[simp] theorem spanOf_size (s : fdt.Span) : (spanOf s).size = word64 s.size := rfl

theorem spanOf_endNat (s : fdt.Span) : (spanOf s).endNat = s.start.val + s.size.val := by
  simp only [Span.endNat, spanOf_start, spanOf_size, word64_toNat]

theorem spanOf_valid_iff (s : fdt.Span) :
    (spanOf s).Valid ↔ s.start.val + s.size.val < 2 ^ 64 := by
  simp only [Span.Valid, Span.endNat, spanOf, word64_toNat]

theorem spanOf_endAddr (s : fdt.Span) :
    (spanOf s).endAddr =
      if s.start.val + s.size.val < 2 ^ 64 then .ok (word64 s.start + word64 s.size)
      else .error .overflow := by
  simp only [Span.endAddr, spanOf_valid_iff]; rfl

/-- A success of `Span::end` is the exact end of the span, within 64 bits. -/
theorem agrees_endAddr_ok {s : fdt.Span} {v : U64} :
    Agrees (fun n N => word64 n = N) errorOf (.Ok v) (spanOf s).endAddr ↔
      s.start.val + s.size.val < 2 ^ 64 ∧ v.val = s.start.val + s.size.val := by
  rw [spanOf_endAddr]
  split
  · rw [agrees_ok_ok, word64_eq_iff, UInt64.toNat_add, word64_toNat, word64_toNat,
      Nat.mod_eq_of_lt ‹_›]
    simp only [true_and, *]
  · simp only [agrees_ok_error, false_iff, not_and]; intro h; exact absurd h ‹_›

/-- A failure of `Span.endAddr` is `Overflow` of a span whose end leaves 64
bits. -/
theorem endAddr_eq_error {s : fdt.Span} {x : Krepi.Spec.Fdt.Error}
    (h : (spanOf s).endAddr = .error x) :
    ¬ s.start.val + s.size.val < 2 ^ 64 ∧ x = .overflow := by
  rw [spanOf_endAddr] at h
  split at h
  · cases h
  · cases h; exact ⟨‹_›, rfl⟩

theorem spanOf_contains (s o : fdt.Span) :
    (spanOf s).contains (spanOf o) =
      if o.start.val + o.size.val < 2 ^ 64 then
        if s.start.val + s.size.val < 2 ^ 64 then
          .ok (decide (s.start.val ≤ o.start.val ∧
            o.start.val + o.size.val ≤ s.start.val + s.size.val))
        else .error .overflow
      else .error .overflow := by
  simp only [Span.contains, spanOf_valid_iff, ite_not, Span.holds, Span.endNat, spanOf_start,
    spanOf_size, word64_toNat, Bool.decide_and]

/-! ## Spans -/

/-- `Span::new(start, size)`: the span of `Span.new`, or its error. -/
@[step] theorem span_new_spec (start size : U64) :
    fdt.span.Span.new start size ⦃ r =>
      Agrees SpanRepr errorOf r (Span.new (word64 start) (word64 size)) ⦄ := by
  unfold fdt.span.Span.new
  step*
  · have hc : ¬ start.val + size.val < 2 ^ 64 := by scalar_tac
    simp only [Span.new, word64_toNat, hc, ↓reduceIte, agrees_err_error]; rfl
  · have hc : start.val + size.val < 2 ^ 64 := by scalar_tac
    simp only [Span.new, word64_toNat, hc, ↓reduceIte, agrees_ok_ok]; rfl

/-- `Span::end()`: the end of `Span.endAddr`, or its error. -/
@[step] theorem span_end_spec (s : fdt.Span) :
    fdt.span.Span.end s ⦃ r =>
      Agrees (fun n N => word64 n = N) errorOf r (spanOf s).endAddr ⦄ := by
  unfold fdt.span.Span.end
  step*
  · have hc : ¬ s.start.val + s.size.val < 2 ^ 64 := by scalar_tac
    simp only [spanOf_endAddr, hc, ↓reduceIte, agrees_err_error]; rfl
  · rw [agrees_endAddr_ok]; scalar_tac

/-- `Span::contains(other)`: whether the span holds the other, or the error, of
`Span.contains`. -/
@[step] theorem span_contains_spec (s other : fdt.Span) :
    fdt.span.Span.contains s other ⦃ r =>
      Agrees (· = ·) errorOf r ((spanOf s).contains (spanOf other)) ⦄ := by
  unfold fdt.span.Span.contains
  step*
  · obtain ⟨hv, hval⟩ := agrees_endAddr_ok.mp (agrees_of_branch_ok cf_post ‹_› r_post)
    obtain ⟨hv1, hval1⟩ := agrees_endAddr_ok.mp (agrees_of_branch_ok cf1_post ‹_› r1_post)
    simp only [spanOf_contains, hv, hv1, ↓reduceIte, agrees_ok_ok, decide_eq_decide]
    constructor
    · intro h; constructor <;> scalar_tac
    · intro h; scalar_tac
  · obtain ⟨hv, hval⟩ := agrees_endAddr_ok.mp (agrees_of_branch_ok cf_post ‹_› r_post)
    obtain ⟨hv1, hval1⟩ := agrees_endAddr_ok.mp (agrees_of_branch_ok cf1_post ‹_› r1_post)
    simp only [spanOf_contains, hv, hv1, ↓reduceIte, agrees_ok_ok]
    symm; rw [decide_eq_false_iff_not]; intro h; scalar_tac
  · obtain ⟨hv, -⟩ := agrees_endAddr_ok.mp (agrees_of_branch_ok cf_post ‹_› ‹_›)
    obtain ⟨hv1, he⟩ := endAddr_eq_error (agrees_err_of_branch cf1_post ‹_› residual_post r1_post)
    simp only [spanOf_contains, hv, hv1, ↓reduceIte, r_post, agrees_err_error, ← he, e_post]
  · obtain ⟨hv, he⟩ := endAddr_eq_error (agrees_err_of_branch cf_post ‹_› residual_post ‹_›)
    simp only [spanOf_contains, hv, ↓reduceIte, r_post, agrees_err_error, ← he, e_post]

/-! ## Cells -/

/-- `cells_u64(bytes, cells)`: the number of `cellsU64`, or its error. -/
@[step] theorem cells_u64_spec (bytes : Slice U8) (cells : U32) :
    fdt.cells_u64 bytes cells ⦃ r =>
      Agrees (fun n N => word64 n = N) errorOf r (cellsU64 (bytesOf bytes) (word32 cells)) ⦄ := by
  unfold fdt.cells_u64
  step*
  · have hc : 2 < cells.val := by scalar_tac
    simp only [cellsU64_bytesOf, hc, ↓reduceIte, agrees_err_error]; rfl
  · have hc : ¬ 2 < cells.val := by scalar_tac
    have hl : bytes.length ≠ cells.val * 4 := by
      have := ‹(bytes.len != i2) = true›
      simp only [bne_iff_ne, ne_eq] at this
      intro h; apply this; apply UScalar.eq_of_val_eq
      rw [Slice.len_val, i2_post, i1_post, U32.cast_Usize_val_eq, h]
    simp only [cellsU64_bytesOf, hc, ne_eq, hl, not_false_eq_true, ↓reduceIte, agrees_err_error]
    rfl
  · have hl : bytes.length = 0 := by
      have := ‹¬(bytes.len != i2) = true›
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
      have h' : bytes.len.val = i2.val := by rw [this]
      scalar_tac
    rw [cellsU64_ok_of (by scalar_tac) (by scalar_tac), hl, beNat_zero]
    rfl
  · have hl : bytes.length = 4 := by
      have := ‹¬(bytes.len != i2) = true›
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
      have h' : bytes.len.val = i2.val := by rw [this]
      scalar_tac
    have hv := agrees_ok_of_eq (agrees_of_branch_ok cf_post ‹_› r_post)
      (u32At_bytesOf_ok (by omega))
    rw [word32_beNat_iff] at hv
    rw [cellsU64_ok_of (by scalar_tac) (by scalar_tac), hl, agrees_ok_ok, word64_ofNat_iff,
      Nat.mod_eq_of_lt (by have := beNat_lt bytes 0 4; omega), i3_post, U32.cast_U64_val_eq, hv]
  · exfalso
    have hl : bytes.length = 4 := by
      have := ‹¬(bytes.len != i2) = true›
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
      have h' : bytes.len.val = i2.val := by rw [this]
      scalar_tac
    have := agrees_err_of_branch cf_post ‹_› residual_post ‹_›
    rw [u32At_bytesOf_ok (by omega)] at this
    cases this
  · have hl : bytes.length = 8 := by
      have := ‹¬(bytes.len != i2) = true›
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
      have h' : bytes.len.val = i2.val := by rw [this]
      scalar_tac
    refine agrees_of_eq ?_ r_post
    rw [cellsU64_ok_of (by scalar_tac) (by scalar_tac), u64At_bytesOf_ok (by omega), hl]

/-! ## Helpers of the spans

The functions of `fdt::span` that the entries share: comparisons at the
exact ends, the checks of `touches` and `holds` against a slice of spans,
and the prefixes and parts of a slice. -/

/-- `below_end(address, span)`: whether the address lies before the exact end.
-/
@[step] theorem below_end_spec (a : U64) (s : fdt.Span) :
    fdt.span.below_end a s ⦃ b => b = decide (a.val < s.start.val + s.size.val) ⦄ := by
  unfold fdt.span.below_end
  step*

/-- `overlaps(a, b)`: `Span.overlaps`. -/
@[step] theorem overlaps_spec (a b : fdt.Span) :
    fdt.span.overlaps a b ⦃ r => r = (spanOf a).overlaps (spanOf b) ⦄ := by
  unfold fdt.span.overlaps
  step*
  all_goals simp only [Span.overlaps, spanOf_endNat, spanOf_start, word64_toNat] at *
  all_goals simp_all

/-- `touches(a, b)`: `Span.touches`. -/
@[step] theorem touches_spec (a b : fdt.Span) :
    fdt.span.touches a b ⦃ r => r = (spanOf a).touches (spanOf b) ⦄ := by
  unfold fdt.span.touches
  step*
  all_goals simp only [Span.touches, spanOf_size, word64_bne_zero] at *
  all_goals simp_all

/-- `ends_within(inner, outer)`: whether `inner` ends at or before `outer`, at
the exact ends. -/
@[step] theorem ends_within_spec (inner outer : fdt.Span) :
    fdt.span.ends_within inner outer ⦃ b =>
      b = decide ((spanOf inner).endNat ≤ (spanOf outer).endNat) ⦄ := by
  unfold fdt.span.ends_within
  simp only [spanOf_endNat]
  step*
  all_goals (subst_vars; simp only [u64_max_eq, u64_MAX_val, U64.rMax] at *)
  all_goals
    have := u64_lt inner.start
    have := u64_lt inner.size
    have := u64_lt outer.start
    have := u64_lt outer.size
    omega

/-- `holds(outer, inner)`: `Span.holds`. -/
@[step] theorem holds_spec (outer inner : fdt.Span) :
    fdt.span.holds outer inner ⦃ r => r = (spanOf outer).holds (spanOf inner) ⦄ := by
  unfold fdt.span.holds
  step*
  · simp only [Span.holds, spanOf_start, word64_toNat]
    rw [decide_eq_true (by scalar_tac), Bool.true_and]; exact r_post
  · simp only [Span.holds, spanOf_start, word64_toNat]
    rw [decide_eq_false (by scalar_tac), Bool.false_and]

/-- `valid(span)`: `Span.Valid`. -/
@[step] theorem valid_spec (s : fdt.Span) :
    fdt.span.valid s ⦃ r => r = decide (spanOf s).Valid ⦄ := by
  unfold fdt.span.valid
  step*
  all_goals simp only [spanOf_valid_iff]
  all_goals scalar_tac

/-- `touches_any(spans, span)`: whether a span of the slice touches `span`. -/
@[step] theorem touches_any_spec (spans : Slice fdt.Span) (span : fdt.Span) :
    fdt.span.touches_any spans span ⦃ b =>
      b = (spansOf spans).any (·.touches (spanOf span)) ⦄ := by
  unfold fdt.span.touches_any fdt.span.touches_any_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => spans.length - i.val)
    (inv := fun (i : Usize) => ((spansOf spans).drop i.val).any (·.touches (spanOf span)) =
      (spansOf spans).any (·.touches (spanOf span)))
  · intro i hinv
    unfold fdt.span.touches_any_loop.body
    step*
    · have hi : i.val < (spansOf spans).length := by simp [spansOf]; scalar_tac
      have e : (spansOf spans)[i.val] = spanOf s := by
        simp only [spansOf, List.getElem_map, s_post]
      rw [← hinv, any_drop_cons hi, e, ← b_post, ‹b = true›, Bool.true_or]
    · have hi : i.val < (spansOf spans).length := by simp [spansOf]; scalar_tac
      refine ⟨?_, by scalar_tac⟩
      have e : (spansOf spans)[i.val] = spanOf s := by
        simp only [spansOf, List.getElem_map, s_post]
      rw [← hinv, any_drop_cons hi, index1_post, e, ← b_post,
        (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_or]
    · rw [← hinv, List.drop_eq_nil_of_le (by simp [spansOf]; scalar_tac)]; rfl
  · rfl

/-- `in_one_range(ranges, span)`: `inOneRange`, whether a span of the slice
holds `span`. -/
@[step] theorem in_one_range_spec (ranges : Slice fdt.Span) (span : fdt.Span) :
    fdt.span.in_one_range ranges span ⦃ b => b = inOneRange (spansOf ranges) (spanOf span) ⦄ := by
  unfold fdt.span.in_one_range fdt.span.in_one_range_loop inOneRange
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => ranges.length - i.val)
    (inv := fun (i : Usize) => ((spansOf ranges).drop i.val).any (·.holds (spanOf span)) =
      (spansOf ranges).any (·.holds (spanOf span)))
  · intro i hinv
    unfold fdt.span.in_one_range_loop.body
    step*
    · have hi : i.val < (spansOf ranges).length := by simp [spansOf]; scalar_tac
      have e : (spansOf ranges)[i.val] = spanOf s := by
        simp only [spansOf, List.getElem_map, s_post]
      rw [← hinv, any_drop_cons hi, e, ← b_post, ‹b = true›, Bool.true_or]
    · have hi : i.val < (spansOf ranges).length := by simp [spansOf]; scalar_tac
      refine ⟨?_, by scalar_tac⟩
      have e : (spansOf ranges)[i.val] = spanOf s := by
        simp only [spansOf, List.getElem_map, s_post]
      rw [← hinv, any_drop_cons hi, index1_post, e, ← b_post,
        (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_or]
    · rw [← hinv, List.drop_eq_nil_of_le (by simp [spansOf]; scalar_tac)]; rfl
  · rfl

/-- `prefix(items, count)`: the first `count` items. -/
@[step] theorem prefix_spec {T : Type} (items : Slice T) (count : Usize)
    (h : count.val ≤ items.length) :
    fdt.span.prefix items count ⦃ s => s.val = items.val.take count.val ⦄ := by
  unfold fdt.span.prefix
  step*
  simp [s_post, List.slice]

/-- `part(items, start, end)`: the items `[start, end)`. -/
@[step] theorem part_spec {T : Type} (items : Slice T) (start stop : Usize)
    (h0 : start.val ≤ stop.val) (h1 : stop.val ≤ items.length) :
    fdt.span.part items start stop ⦃ s =>
      s.val = (items.val.drop start.val).take (stop.val - start.val) ⦄ := by
  unfold fdt.span.part
  step*
  simp [s_post, List.slice]

end Krepi.Proofs.Fdt.Refinement
