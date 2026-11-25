module

public import Krepi.Proofs.Fdt.Refinement.SpanLemmas
public import Krepi.Proofs.Fdt.Refinement.Utf8Lemmas

/-!
# Device tree: refinement of the byte reads of the format

The triples of the generated functions of `fdt::format` and of
`fdt::nodes::piece_at`, each a `@[step]` lemma stated against the function of
the specification that it implements, so that the proof of a caller steps
over the call with the triple of the callee and a mutant of a callee fails the
proof of the callee alone. The lemmas that need no generated code are in
`Krepi.Proofs.Fdt.Refinement.Utf8Lemmas`.

- Constants: `tokens_spec` and `depth_spec`, `MAX_TOKENS` and `MAX_DEPTH` as a
  `usize`.
- Padding and strings: `align4_spec` (`align4`), `find_nul_spec` (`findNul`),
  `zeros_spec` and `padded_end_spec` (`paddedEnd`, or its error), and
  `c_string_spec` (the NUL of the string of `cString`, or its error).
- UTF-8: `continues_spec`, the rests `scalar_tail2_spec`, `scalar_tail3_spec`
  and `scalar_tail4_spec` of `scalar_end` by the length of the sequence,
  `scalar_end_eq_spec` (`scalarEnd`), `scalar_end_spec` (the index after the
  character that `ByteArray.utf8DecodeChar?` decodes) and `is_utf8_spec`
  (`ByteArray.IsValidUTF8` of the bytes of a range, the condition of
  `String.fromUTF8?`). The table of `scalar_end` is 1,075 generated lines of
  branches that repeat the tests of its first byte; `scalar_end_eq_spec`
  follows the branches that the first byte takes and steps over each rest with
  the triple of its length, so that no theorem walks the whole table.
- Names: `alphanumeric_spec` and `alphanumeric_isAlphanum`
  (`Char.isAlphanum`), `name_byte_spec` (`nameChar`, the characters of
  `isNodeNameChar` and `isPropertyNameChar`) and `name_bytes_spec`.
- Comparisons: `same_bytes_loop_spec`, `same_bytes_spec`, `starts_with_spec`,
  `name_at_loop_spec` and `name_at_spec`, stated on the bytes of the slices.
- Tokens: `pieceOf`, a token of the code as the `Piece` of the specification,
  and `piece_at_spec` (`pieceAt`), with `agrees_word32_ok` and
  `agrees_word32_err`, the word reads that agree with `u32At`.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Constants -/

/-- `TOKENS`: `MAX_TOKENS` as a `usize`. -/
@[step] theorem tokens_spec : fdt.TOKENS ⦃ n => n.val = MAX_TOKENS.toNat ⦄ := by
  unfold fdt.TOKENS
  refine spec_of_eq rfl ?_
  rw [UScalar.cast_val_eq, fdt.MAX_TOKENS]
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits :=
    Nat.pow_le_pow_right (by omega) usize_numBits_ge
  exact Nat.mod_eq_of_lt (by show 65536 < _; omega)

/-- `DEPTH`: `MAX_DEPTH` as a `usize`. -/
@[step] theorem depth_spec : fdt.DEPTH ⦃ n => n.val = MAX_DEPTH.toNat ⦄ := by
  unfold fdt.DEPTH
  refine spec_of_eq rfl ?_
  rw [UScalar.cast_val_eq, fdt.MAX_DEPTH]
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits :=
    Nat.pow_le_pow_right (by omega) usize_numBits_ge
  exact Nat.mod_eq_of_lt (by show 32 < _; omega)

/-! ## Padding and strings -/

/-- `align4(offset)`: `align4`, for an offset 3 below the largest `usize`. -/
@[step] theorem align4_spec (offset : Usize) (h : offset.val + 3 ≤ Usize.max) :
    fdt.format.align4 offset ⦃ r => r.val = Krepi.Spec.Fdt.align4 offset.val ⦄ := by
  unfold fdt.format.align4
  step*
  rw [UScalar.val_and, i1_post]
  have hn : (~~~3#usize).val = 2 ^ UScalarTy.Usize.numBits - 1 - 3 := by
    show (~~~(3#usize).bv).toNat = _
    rw [BitVec.toNat_not]; rfl
  have hl : i.val < 2 ^ UScalarTy.Usize.numBits := i.hmax
  rw [hn, land_mask4 (by have := usize_numBits_ge; omega) hl, i_post, Krepi.Spec.Fdt.align4]

/-- `find_nul(bytes, start)`: `findNul`, the first NUL at or after `start`. -/
@[step] theorem find_nul_spec (bytes : Slice U8) (start : Usize) :
    fdt.format.find_nul bytes start ⦃ o => o.map (·.val) = findNul (bytesOf bytes) start.val ⦄ := by
  unfold fdt.format.find_nul fdt.format.find_nul_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => bytes.length - i.val)
    (inv := fun (i : Usize) => findNul (bytesOf bytes) i.val = findNul (bytesOf bytes) start.val)
  · intro i hinv
    unfold fdt.format.find_nul_loop.body
    step*
    · have hi : i.val < bytes.val.length := by scalar_tac
      rw [← hinv, findNul_zero (by simpa using hi)
        (by rw [bytesOf_getElem?_of_lt hi, ← i1_post, ‹i1 = 0#u8›]; rfl)]
      rfl
    · have hi : i.val < bytes.val.length := by scalar_tac
      refine ⟨?_, by scalar_tac⟩
      rw [← hinv, at1_post]
      refine (findNul_step (by simpa using hi) ?_).symm
      rw [bytesOf_getElem?_of_lt hi, ne_eq, Option.some.injEq, byte_eq_zero_iff, ← i1_post]
      intro h0; exact ‹¬i1 = 0#u8› (UScalar.eq_of_val_eq h0)
    · rw [← hinv, findNul_end (by simpa using ‹¬i < bytes.len›)]; rfl
  · rfl

/-! ## UTF-8 -/

/-- `continues(byte)`: `continuesByte`. -/
@[step] theorem continues_spec (x : U8) :
    fdt.format.continues x ⦃ b => b = continuesByte x.val ⦄ := by
  unfold fdt.format.continues continuesByte
  step*

/-- The two-byte rest of `scalar_end`: `scalarTail` of length 2. -/
theorem scalar_tail2_spec (bytes : Slice U8) («at» «end» : Usize) (lo hi : U8)
    (h1 : «at».val < «end».val) (h2 : «end».val ≤ bytes.length) :
    (do
      let i ← «end» - «at»
      if i < 2#usize
      then ok none
      else
        let i1 ← «at» + 1#usize
        let second ← Slice.index_usize bytes i1
        if second < lo
        then ok none
        else
          if second > hi
          then ok none
          else
            if 2#usize >= 3#usize
            then
              let i2 ← «at» + 2#usize
              let i3 ← Slice.index_usize bytes i2
              let b ← fdt.format.continues i3
              if b
              then
                if 2#usize = 4#usize
                then
                  let i4 ← «at» + 3#usize
                  let i5 ← Slice.index_usize bytes i4
                  let b1 ← fdt.format.continues i5
                  if b1
                  then ok (some i2)
                  else ok none
                else ok (some i2)
              else ok none
            else
              if 2#usize = 4#usize
              then
                let i2 ← «at» + 3#usize
                let i3 ← Slice.index_usize bytes i2
                let b ← fdt.format.continues i3
                if b
                then let i4 ← «at» + 2#usize
                     ok (some i4)
                else ok none
              else let i2 ← «at» + 2#usize
                   ok (some i2)
      : Result (Option Usize)) ⦃ o =>
      o.map (·.val) = scalarTail (bytesOf bytes) «at».val «end».val 2 lo.val hi.val ⦄ := by
  step*
  · have : i.val < 2 := ‹i < 2#usize›
    rw [scalarTail_short (by omega)]; rfl
  all_goals have : ¬ i.val < 2 := ‹¬ i < 2#usize›
  all_goals have e := byte_at second_post i1_post
  · have : second.val < lo.val := ‹second < lo›
    rw [scalarTail_two (by omega), e, ite_eq_right]
    exacts [rfl, by omega]
  · have : hi.val < second.val := ‹second > hi›
    rw [scalarTail_two (by omega), e, ite_eq_right]
    exacts [rfl, by omega]
  · have : ¬ second.val < lo.val := ‹¬ second < lo›
    have : ¬ hi.val < second.val := ‹¬ second > hi›
    rw [scalarTail_two (by omega), e, ite_eq_left]
    · rw [Option.map_some, i4_post]
    · omega

/-- The three-byte rest of `scalar_end`: `scalarTail` of length 3. -/
theorem scalar_tail3_spec (bytes : Slice U8) («at» «end» : Usize) (lo hi : U8)
    (h1 : «at».val < «end».val) (h2 : «end».val ≤ bytes.length) :
    (do
      let i ← «end» - «at»
      if i < 3#usize
      then ok none
      else
        let i1 ← «at» + 1#usize
        let second ← Slice.index_usize bytes i1
        if second < lo
        then ok none
        else
          if second > hi
          then ok none
          else
            if 3#usize >= 3#usize
            then
              let i2 ← «at» + 2#usize
              let i3 ← Slice.index_usize bytes i2
              let b ← fdt.format.continues i3
              if b
              then
                if 3#usize = 4#usize
                then
                  let i4 ← «at» + 3#usize
                  let i5 ← Slice.index_usize bytes i4
                  let b1 ← fdt.format.continues i5
                  if b1
                  then ok (some i4)
                  else ok none
                else let i4 ← «at» + 3#usize
                     ok (some i4)
              else ok none
            else
              if 3#usize = 4#usize
              then
                let i2 ← «at» + 3#usize
                let i3 ← Slice.index_usize bytes i2
                let b ← fdt.format.continues i3
                if b
                then ok (some i2)
                else ok none
              else let i2 ← «at» + 3#usize
                   ok (some i2)
      : Result (Option Usize)) ⦃ o =>
      o.map (·.val) = scalarTail (bytesOf bytes) «at».val «end».val 3 lo.val hi.val ⦄ := by
  step*
  · have : i.val < 3 := ‹i < 3#usize›
    rw [scalarTail_short (by omega)]; rfl
  all_goals have : ¬ i.val < 3 := ‹¬ i < 3#usize›
  all_goals have e := byte_at second_post i1_post
  · have : second.val < lo.val := ‹second < lo›
    rw [scalarTail_three (by omega), e, ite_eq_right]
    exacts [rfl, by omega]
  · have : hi.val < second.val := ‹second > hi›
    rw [scalarTail_three (by omega), e, ite_eq_right]
    exacts [rfl, by omega]
  · have : ¬ second.val < lo.val := ‹¬ second < lo›
    have : ¬ hi.val < second.val := ‹¬ second > hi›
    have e2 := byte_at i3_post i2_post
    have hc := ‹b = true›
    rw [b_post, continuesByte, decide_eq_true_eq] at hc
    rw [scalarTail_three (by omega), e, e2, ite_eq_left]
    · rw [Option.map_some, i4_post]
    · omega
  · have : ¬ second.val < lo.val := ‹¬ second < lo›
    have : ¬ hi.val < second.val := ‹¬ second > hi›
    have e2 := byte_at i3_post i2_post
    have hc := ‹¬ b = true›
    rw [b_post, continuesByte, decide_eq_true_eq] at hc
    rw [scalarTail_three (by omega), e, e2, ite_eq_right]
    exacts [rfl, by omega]

/-- The four-byte rest of `scalar_end`: `scalarTail` of length 4. -/
theorem scalar_tail4_spec (bytes : Slice U8) («at» «end» : Usize) (lo hi : U8)
    (h1 : «at».val < «end».val) (h2 : «end».val ≤ bytes.length) :
    (do
      let i ← «end» - «at»
      if i < 4#usize
      then ok none
      else
        let i1 ← «at» + 1#usize
        let second ← Slice.index_usize bytes i1
        if second < lo
        then ok none
        else
          if second > hi
          then ok none
          else
            if 4#usize >= 3#usize
            then
              let i2 ← «at» + 2#usize
              let i3 ← Slice.index_usize bytes i2
              let b ← fdt.format.continues i3
              if b
              then
                if 4#usize = 4#usize
                then
                  let i4 ← «at» + 3#usize
                  let i5 ← Slice.index_usize bytes i4
                  let b1 ← fdt.format.continues i5
                  if b1
                  then let i6 ← «at» + 4#usize
                       ok (some i6)
                  else ok none
                else let i4 ← «at» + 4#usize
                     ok (some i4)
              else ok none
            else
              if 4#usize = 4#usize
              then
                let i2 ← «at» + 3#usize
                let i3 ← Slice.index_usize bytes i2
                let b ← fdt.format.continues i3
                if b
                then let i4 ← «at» + 4#usize
                     ok (some i4)
                else ok none
              else let i2 ← «at» + 4#usize
                   ok (some i2)
      : Result (Option Usize)) ⦃ o =>
      o.map (·.val) = scalarTail (bytesOf bytes) «at».val «end».val 4 lo.val hi.val ⦄ := by
  step*
  · have : i.val < 4 := ‹i < 4#usize›
    rw [scalarTail_short (by omega)]; rfl
  all_goals have : ¬ i.val < 4 := ‹¬ i < 4#usize›
  all_goals have e := byte_at second_post i1_post
  · have : second.val < lo.val := ‹second < lo›
    rw [scalarTail_four (by omega), e, ite_eq_right]
    exacts [rfl, by omega]
  · have : hi.val < second.val := ‹second > hi›
    rw [scalarTail_four (by omega), e, ite_eq_right]
    exacts [rfl, by omega]
  all_goals have : ¬ second.val < lo.val := ‹¬ second < lo›
  all_goals have : ¬ hi.val < second.val := ‹¬ second > hi›
  all_goals have e2 := byte_at i3_post i2_post
  · have e3 := byte_at i5_post i4_post
    have hc := ‹b = true›
    have hc1 := ‹b1 = true›
    rw [b_post, continuesByte, decide_eq_true_eq] at hc
    rw [b1_post, continuesByte, decide_eq_true_eq] at hc1
    rw [scalarTail_four (by omega), e, e2, e3, ite_eq_left]
    · rw [Option.map_some, i6_post]
    · omega
  · have e3 := byte_at i5_post i4_post
    have hc1 := ‹¬ b1 = true›
    rw [b1_post, continuesByte, decide_eq_true_eq] at hc1
    rw [scalarTail_four (by omega), e, e2, e3, ite_eq_right]
    exacts [rfl, by omega]
  · have hc := ‹¬ b = true›
    rw [b_post, continuesByte, decide_eq_true_eq] at hc
    rw [scalarTail_four (by omega), e, e2, ite_eq_right]
    exacts [rfl, by omega]

/-- `scalar_end(bytes, at, end)`: `scalarEnd`, for an index before `end`
within the slice. The generated code repeats the tests of the first byte in
each branch of its table; the proof follows the branches that the first byte
takes, closes the others by its value, and steps over each rest with the
triple of its length. -/
theorem scalar_end_eq_spec (bytes : Slice U8) («at» «end» : Usize)
    (h1 : «at».val < «end».val) (h2 : «end».val ≤ bytes.length) :
    fdt.format.scalar_end bytes «at» «end» ⦃ o =>
      o.map (·.val) = scalarEnd (bytesOf bytes) «at».val «end».val ⦄ := by
  unfold fdt.format.scalar_end
  step
  have hf : ((bytesOf bytes)[«at».val]!).toNat = first.val := byte_at first_post rfl
  have hw : first.val < 256 := first.hmax
  by_cases c0 : first.val < 128
  · refine ite_spec_pos (show first < 128#u8 from c0) ?_
    step*
    rw [scalarEnd_ascii (by omega), Option.map_some, i_post]
  refine ite_spec_neg (show ¬ first < 128#u8 from c0) ?_
  by_cases c1 : 194 ≤ first.val
  · refine ite_spec_pos (show first >= 194#u8 from c1) ?_
    by_cases c2 : first.val ≤ 223
    · refine ite_spec_pos (show first <= 223#u8 from c2) ?_
      exact spec_mono (scalar_tail2_spec bytes «at» «end» 128#u8 191#u8 h1 h2)
        (fun o h => h.trans (scalarEnd_two (by omega)).symm)
    refine ite_spec_neg (show ¬ first <= 223#u8 from c2) ?_
    by_cases c3 : first.val = 224
    · refine ite_spec_pos (show first = 224#u8 from UScalar.eq_of_val_eq c3) ?_
      exact spec_mono (scalar_tail3_spec bytes «at» «end» 160#u8 191#u8 h1 h2)
        (fun o h => h.trans (scalarEnd_e0 (by omega)).symm)
    refine ite_spec_neg (show ¬ first = 224#u8 from fun h => c3 (congrArg UScalar.val h)) ?_
    by_cases c4 : first.val = 237
    · refine ite_spec_pos (show first = 237#u8 from UScalar.eq_of_val_eq c4) ?_
      exact spec_mono (scalar_tail3_spec bytes «at» «end» 128#u8 159#u8 h1 h2)
        (fun o h => h.trans (scalarEnd_ed (by omega)).symm)
    refine ite_spec_neg (show ¬ first = 237#u8 from fun h => c4 (congrArg UScalar.val h)) ?_
    refine ite_spec_pos (show first >= 225#u8 from (by omega : 225 ≤ first.val)) ?_
    by_cases c5 : first.val ≤ 239
    · refine ite_spec_pos (show first <= 239#u8 from c5) ?_
      exact spec_mono (scalar_tail3_spec bytes «at» «end» 128#u8 191#u8 h1 h2)
        (fun o h => h.trans (scalarEnd_three (by omega) (by omega)).symm)
    refine ite_spec_neg (show ¬ first <= 239#u8 from c5) ?_
    by_cases c6 : first.val = 240
    · refine ite_spec_pos (show first = 240#u8 from UScalar.eq_of_val_eq c6) ?_
      exact spec_mono (scalar_tail4_spec bytes «at» «end» 144#u8 191#u8 h1 h2)
        (fun o h => h.trans (scalarEnd_f0 (by omega)).symm)
    refine ite_spec_neg (show ¬ first = 240#u8 from fun h => c6 (congrArg UScalar.val h)) ?_
    refine ite_spec_pos (show first >= 241#u8 from (by omega : 241 ≤ first.val)) ?_
    by_cases c7 : first.val ≤ 243
    · refine ite_spec_pos (show first <= 243#u8 from c7) ?_
      exact spec_mono (scalar_tail4_spec bytes «at» «end» 128#u8 191#u8 h1 h2)
        (fun o h => h.trans (scalarEnd_four (by omega)).symm)
    refine ite_spec_neg (show ¬ first <= 243#u8 from c7) ?_
    by_cases c8 : first.val = 244
    · refine ite_spec_pos (show first = 244#u8 from UScalar.eq_of_val_eq c8) ?_
      exact spec_mono (scalar_tail4_spec bytes «at» «end» 128#u8 143#u8 h1 h2)
        (fun o h => h.trans (scalarEnd_f4 (by omega)).symm)
    refine ite_spec_neg (show ¬ first = 244#u8 from fun h => c8 (congrArg UScalar.val h)) ?_
    exact spec_of_eq rfl (scalarEnd_bad (by omega)).symm
  refine ite_spec_neg (show ¬ first >= 194#u8 from c1) ?_
  refine ite_spec_neg (show ¬ first = 224#u8 from fun h =>
    (by omega : first.val ≠ 224) (congrArg UScalar.val h)) ?_
  refine ite_spec_neg (show ¬ first = 237#u8 from fun h =>
    (by omega : first.val ≠ 237) (congrArg UScalar.val h)) ?_
  refine ite_spec_neg (show ¬ first >= 225#u8 from (by omega : ¬ 225 ≤ first.val)) ?_
  refine ite_spec_neg (show ¬ first = 240#u8 from fun h =>
    (by omega : first.val ≠ 240) (congrArg UScalar.val h)) ?_
  refine ite_spec_neg (show ¬ first >= 241#u8 from (by omega : ¬ 241 ≤ first.val)) ?_
  refine ite_spec_neg (show ¬ first = 244#u8 from fun h =>
    (by omega : first.val ≠ 244) (congrArg UScalar.val h)) ?_
  exact spec_of_eq rfl (scalarEnd_bad (by omega)).symm

/-- `scalar_end(bytes, at, end)`: the index after the character that
`ByteArray.utf8DecodeChar?` of Lean core decodes at the start of the bytes
`[at, end)`, none when they encode none. -/
@[step] theorem scalar_end_spec (bytes : Slice U8) («at» «end» : Usize)
    (h1 : «at».val < «end».val) (h2 : «end».val ≤ bytes.length) :
    fdt.format.scalar_end bytes «at» «end» ⦃ o =>
      o.map (·.val) = (((bytesOf bytes).extract «at».val «end».val).utf8DecodeChar? 0).map
        («at».val + ·.utf8Size) ⦄ :=
  spec_mono (scalar_end_eq_spec bytes «at» «end» h1 h2)
    (fun _ h => h.trans (scalarEnd_eq h1 (by rw [bytesOf_size]; exact h2)))

/-- `is_utf8(bytes, start, end)`: whether the bytes `[start, end)` are UTF-8,
`ByteArray.IsValidUTF8`, the condition of `String.fromUTF8?`. -/
@[step] theorem is_utf8_spec (bytes : Slice U8) (start «end» : Usize)
    (h : «end».val ≤ bytes.length) :
    fdt.format.is_utf8 bytes start «end» ⦃ b =>
      b = decide ((bytesOf bytes).extract start.val «end».val).IsValidUTF8 ⦄ := by
  unfold fdt.format.is_utf8 fdt.format.is_utf8_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => «end».val - i.val)
    (inv := fun (i : Usize) => (((bytesOf bytes).extract i.val «end».val).IsValidUTF8 ↔
      ((bytesOf bytes).extract start.val «end».val).IsValidUTF8))
  · intro i hinv
    unfold fdt.format.is_utf8_loop.body
    step*
    · have hi : i.val < «end».val := ‹i < «end»›
      rw [← scalarEnd_eq hi (by rw [bytesOf_size]; exact h), ‹o = none›, Option.map_none] at o_post
      rw [decide_eq_false (fun hv => scalarEnd_none hi (by rw [bytesOf_size]; exact h)
        o_post.symm (hinv.mpr hv))]
    · have hi : i.val < «end».val := ‹i < «end»›
      rw [← scalarEnd_eq hi (by rw [bytesOf_size]; exact h), ‹o = some next›, Option.map_some]
        at o_post
      obtain ⟨hn1, -, hn⟩ := scalarEnd_some hi (by rw [bytesOf_size]; exact h) o_post.symm
      exact ⟨hn.symm.trans hinv, by omega⟩
    · have hi : ¬ i.val < «end».val := ‹¬ i < «end»›
      rw [decide_eq_true (hinv.mp (isValidUTF8_extract_of_le (by omega)))]
  · exact Iff.rfl

/-- `c_string(bytes, start)`: the NUL of the string of `cString`, or its
error. On a success, the NUL is the one that `findNul` finds, the
specification's index after the string is the one after the NUL, and its
string is that of the bytes from `start` to the NUL. -/
@[step] theorem c_string_spec (bytes : Slice U8) (start : Usize) :
    fdt.format.c_string bytes start ⦃ r =>
      Agrees (fun nul p => findNul (bytesOf bytes) start.val = some nul.val ∧
          p.2 = nul.val + 1 ∧
          String.fromUTF8? ((bytesOf bytes).extract start.val nul.val) = some p.1)
        errorOf r (cString (bytesOf bytes) start.val) ⦄ := by
  unfold fdt.format.c_string
  step
  split
  · rw [Option.map_none] at o_post
    refine spec_of_eq rfl ?_
    simp only [cString, ← o_post, agrees_err_error]
    rfl
  · rename_i nul
    rw [Option.map_some] at o_post
    obtain ⟨-, hlt, -, -⟩ := findNul_some o_post.symm
    step
    · rw [bytesOf_size] at hlt; omega
    by_cases hv : ((bytesOf bytes).extract start.val nul.val).IsValidUTF8
    · have hs : String.fromUTF8? ((bytesOf bytes).extract start.val nul.val) =
          some (String.fromUTF8 _ hv) := by
        simp only [String.fromUTF8?, hv, ↓reduceDIte]
      simp only [b_post, hv, decide_true, ↓reduceIte]
      refine spec_of_eq rfl ?_
      simp only [cString, ← o_post, hs]
      exact ⟨rfl, rfl, hs⟩
    · have hs : String.fromUTF8? ((bytesOf bytes).extract start.val nul.val) = none := by
        simp only [String.fromUTF8?, hv, ↓reduceDIte]
      simp only [b_post, hv, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine spec_of_eq rfl ?_
      simp only [cString, ← o_post, hs, agrees_err_error]
      rfl

/-! ## Zeros and padding -/

/-- `zeros(bytes, start, end)`: whether the bytes `[start, end)`, which lie in
the slice, are all zero, in the form of `paddedEnd`. -/
@[step] theorem zeros_spec (bytes : Slice U8) (start «end» : Usize) (h : «end».val ≤ bytes.length) :
    fdt.format.zeros bytes start «end» ⦃ b =>
      b = !((bytesOf bytes).extract start.val «end».val).toList.any (· ≠ 0) ⦄ := by
  unfold fdt.format.zeros fdt.format.zeros_loop
  rw [bytesOf_extract_any]
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => «end».val - i.val)
    (inv := fun (i : Usize) =>
      ((bytes.val.drop i.val).take («end».val - i.val)).any (fun x => x.val ≠ 0) =
        ((bytes.val.drop start.val).take («end».val - start.val)).any (fun x => x.val ≠ 0))
  · intro pos hinv
    unfold fdt.format.zeros_loop.body
    step*
    · have hp : pos.val < «end».val := ‹pos < «end»›
      have hx : i.val ≠ 0 := fun h0 => (bne_iff_ne.mp ‹_›) (UScalar.eq_of_val_eq h0)
      rw [← hinv, drop_take_cons hp (by have : «end».val ≤ bytes.val.length := h; omega),
        List.any_cons, ← i_post, decide_eq_true hx, Bool.true_or, Bool.not_true]
    · have hp : pos.val < «end».val := ‹pos < «end»›
      have hx : ¬ i.val ≠ 0 := fun h0 =>
        ‹¬(i != 0#u8) = true› (bne_iff_ne.mpr (fun h1 => h0 (by rw [h1]; rfl)))
      refine ⟨?_, by omega⟩
      rw [← hinv, drop_take_cons hp (by have : «end».val ≤ bytes.val.length := h; omega),
        List.any_cons, ← i_post, decide_eq_false hx, Bool.false_or, at1_post]
    · have hp : ¬ pos.val < «end».val := ‹¬ pos < «end»›
      rw [← hinv, show «end».val - pos.val = 0 by omega, List.take_zero, List.any_nil]
      rfl
  · rfl

/-! ## Names -/

/-- `alphanumeric(byte)`: an ASCII letter or digit, as numbers. -/
@[step] theorem alphanumeric_spec (x : U8) :
    fdt.format.alphanumeric x ⦃ b => b = decide ((48 ≤ x.val ∧ x.val ≤ 57) ∨
      (97 ≤ x.val ∧ x.val ≤ 122) ∨ (65 ≤ x.val ∧ x.val ≤ 90)) ⦄ := by
  unfold fdt.format.alphanumeric
  step*

/-- `alphanumeric(byte)`: `Char.isAlphanum` of the byte. -/
theorem alphanumeric_isAlphanum (x : U8) :
    fdt.format.alphanumeric x ⦃ b => b = (Char.ofNat x.val).isAlphanum ⦄ :=
  spec_mono (alphanumeric_spec x) (fun _ h => h.trans (isAlphanum_ofNat x.hmax).symm)

/-- `name_byte(byte, property)`: whether the byte is a character of a
property name, `isPropertyNameChar`, or with `property` false of a node name,
`isNodeNameChar`. -/
@[step] theorem name_byte_spec (x : U8) (property : Bool) :
    fdt.format.name_byte x property ⦃ b => b = nameChar property (Char.ofNat x.val) ⦄ := by
  rw [nameChar_ofNat property x.hmax]
  unfold fdt.format.name_byte
  step*
  exact (decide_eq_true (Or.inl (of_decide_post b_post ‹_›))).symm

/-- `padded_end(bytes, end, zero)`: the end of the padding of `paddedEnd`, or its
error, for an end 3 below the largest `usize`. -/
@[step] theorem padded_end_spec (bytes : Slice U8) («end» : Usize) (zero : Bool)
    (h : «end».val + 3 ≤ Usize.max) :
    fdt.format.padded_end bytes «end» zero ⦃ r =>
      Agrees (fun a n => a.val = n) errorOf r (paddedEnd (bytesOf bytes) «end».val zero) ⦄ := by
  unfold fdt.format.padded_end
  step*
  · have hl : bytes.length < aligned.val := by scalar_tac
    simp only [paddedEnd, bytesOf_size, ← aligned_post, hl, ↓reduceIte, agrees_err_error]
    rfl
  · have hl : ¬ bytes.length < aligned.val := by scalar_tac
    have hz : ((bytesOf bytes).extract «end».val aligned.val).toList.any (· ≠ 0) = false := by
      rw [← Bool.not_eq_true', ← b_post]; exact ‹b = true›
    simp only [paddedEnd, bytesOf_size, ← aligned_post, hl, ↓reduceIte, hz, Bool.and_false,
      Bool.false_eq_true, agrees_ok_ok]
  · have hl : ¬ bytes.length < aligned.val := by scalar_tac
    have hz : ((bytesOf bytes).extract «end».val aligned.val).toList.any (· ≠ 0) = true := by
      rw [← Bool.not_eq_false', ← b_post]; exact (Bool.not_eq_true _).mp ‹¬b = true›
    simp only [paddedEnd, bytesOf_size, ← aligned_post, hl, ↓reduceIte, hz, Bool.and_true,
      agrees_err_error]
    rfl
  · have hl : ¬ bytes.length < aligned.val := by scalar_tac
    simp only [paddedEnd, bytesOf_size, ← aligned_post, hl, ↓reduceIte, Bool.false_and,
      Bool.false_eq_true, agrees_ok_ok]

/-- `name_bytes(bytes, start, end, property)`: whether every byte of
`[start, end)`, which lies in the slice, is a character of a property name,
or with `property` false of a node name. -/
@[step] theorem name_bytes_spec (bytes : Slice U8) (start «end» : Usize) (property : Bool)
    (h : «end».val ≤ bytes.length) :
    fdt.format.name_bytes bytes start «end» property ⦃ b =>
      b = ((bytesOf bytes).extract start.val «end».val).toList.all
        (fun x => nameChar property (Char.ofNat x.toNat)) ⦄ := by
  unfold fdt.format.name_bytes fdt.format.name_bytes_loop
  rw [bytesOf_extract_all _ _ _ (fun n => nameChar property (Char.ofNat n))]
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => «end».val - i.val)
    (inv := fun (i : Usize) =>
      ((bytes.val.drop i.val).take («end».val - i.val)).all
          (fun x => nameChar property (Char.ofNat x.val)) =
        ((bytes.val.drop start.val).take («end».val - start.val)).all
          (fun x => nameChar property (Char.ofNat x.val)))
  · intro pos hinv
    unfold fdt.format.name_bytes_loop.body
    step*
    · have hp : pos.val < «end».val := ‹pos < «end»›
      refine ⟨?_, by omega⟩
      rw [← hinv, drop_take_cons hp (by have : «end».val ≤ bytes.val.length := h; omega),
        List.all_cons, ← i_post, ← b_post, ‹b = true›, Bool.true_and, at1_post]
    · have hp : pos.val < «end».val := ‹pos < «end»›
      rw [← hinv, drop_take_cons hp (by have : «end».val ≤ bytes.val.length := h; omega),
        List.all_cons, ← i_post, ← b_post, (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_and]
    · have hp : ¬ pos.val < «end».val := ‹¬ pos < «end»›
      rw [← hinv, show «end».val - pos.val = 0 by omega, List.take_zero, List.all_nil]
  · rfl

/-! ## Comparisons -/

/-- The loop of `same_bytes`: whether the bytes from `start` agree with those of
`other`, one by one. -/
@[step] theorem same_bytes_loop_spec (bytes : Slice U8) (start : Usize) (other : Slice U8)
    (h : start.val + other.length ≤ bytes.length) :
    fdt.format.same_bytes_loop bytes start other 0#usize ⦃ b =>
      b = decide (∀ k < other.length, bytes.val[start.val + k]! = other.val[k]!) ⦄ := by
  unfold fdt.format.same_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => other.length - i.val)
    (inv := fun (i : Usize) => i.val ≤ other.length ∧
      ∀ k < i.val, bytes.val[start.val + k]! = other.val[k]!)
  · intro index hinv
    unfold fdt.format.same_bytes_loop.body
    step*
    · have hi : index.val < other.length := by scalar_tac
      have e2 : i2 = bytes.val[start.val + index.val]! := by
        rw [i2_post]; exact getElem_eq_getElem! i1_post _
      have e3 : i3 = other.val[index.val]! := by rw [i3_post]; exact getElem_eq_getElem! rfl _
      refine (decide_eq_false fun hall => ?_).symm
      exact (bne_iff_ne.mp ‹(i2 != i3) = true›) (by rw [e2, e3]; exact hall _ hi)
    · have hi : index.val < other.length := by scalar_tac
      have e2 : i2 = bytes.val[start.val + index.val]! := by
        rw [i2_post]; exact getElem_eq_getElem! i1_post _
      have e3 : i3 = other.val[index.val]! := by rw [i3_post]; exact getElem_eq_getElem! rfl _
      have heq : i2 = i3 := by
        have := ‹¬(i2 != i3) = true›
        rwa [bne_iff_ne, ne_eq, Decidable.not_not] at this
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [index1_post] at hk
      by_cases hk' : k < index.val
      · exact hinv.2 k hk'
      · rw [show k = index.val by omega, ← e2, ← e3, heq]
  · exact ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩

/-- `same_bytes(bytes, start, end, other)`: whether the bytes `[start, end)`,
which lie in the slice, are those of `other`. -/
@[step] theorem same_bytes_spec (bytes : Slice U8) (start «end» : Usize) (other : Slice U8) :
    fdt.format.same_bytes bytes start «end» other ⦃ b =>
      b = decide (start.val ≤ «end».val ∧ «end».val ≤ bytes.length ∧
        (bytesOf bytes).extract start.val «end».val = bytesOf other) ⦄ := by
  unfold fdt.format.same_bytes
  step*
  · have hle : «end».val ≤ bytes.length := by scalar_tac
    have hne : «end».val - start.val ≠ other.length := by
      have := bne_iff_ne.mp ‹(i1 != other.len) = true›; scalar_tac
    refine (decide_eq_false ?_).symm
    rintro ⟨-, -, heq⟩
    have := congrArg ByteArray.size heq
    rw [ByteArray.size_extract, bytesOf_size, bytesOf_size] at this
    omega
  · have hle : «end».val ≤ bytes.length := by scalar_tac
    have hlen : «end».val - start.val = other.length := by
      have := ‹¬(i1 != other.len) = true›
      rw [bne_iff_ne, ne_eq, Decidable.not_not] at this
      scalar_tac
    rw [b_post, decide_eq_decide, bytesOf_extract_eq_iff i1_post1 hle]
    exact ⟨fun h => ⟨i1_post1, hle, hlen, h⟩, fun h => h.2.2.2⟩

/-- `starts_with(bytes, start, end, prefix)`: whether the bytes `[start, end)`,
which lie in the slice, start with those of `prefix`. -/
@[step] theorem starts_with_spec (bytes : Slice U8) (start «end» : Usize) («prefix» : Slice U8) :
    fdt.format.starts_with bytes start «end» «prefix» ⦃ b =>
      b = decide (start.val ≤ «end».val ∧ «end».val ≤ bytes.length ∧
        «prefix».length ≤ «end».val - start.val ∧
        (bytesOf bytes).extract start.val (start.val + «prefix».length) = bytesOf «prefix») ⦄ := by
  unfold fdt.format.starts_with
  step*
  have hle : «end».val ≤ bytes.length := by scalar_tac
  have hp : «prefix».length ≤ «end».val - start.val := by scalar_tac
  have h4 : i4.val = start.val + «prefix».length := by scalar_tac
  rw [b_post, decide_eq_decide, h4]
  exact ⟨fun h => ⟨i1_post1, hle, hp, h.2.2⟩, fun h => ⟨by omega, by omega, h.2.2.2⟩⟩

/-- The loop of `name_at`: whether the bytes of `name` are nonzero and agree
with those of the strings block from `offset`. -/
@[step] theorem name_at_loop_spec (strings : Slice U8) (offset : Usize) («name» : Slice U8)
    (h : offset.val + «name».length ≤ strings.length) :
    fdt.format.name_at_loop strings offset «name» 0#usize ⦃ b =>
      b = decide (∀ k < «name».length, («name».val[k]!).val ≠ 0 ∧
        strings.val[offset.val + k]! = «name».val[k]!) ⦄ := by
  unfold fdt.format.name_at_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => «name».length - i.val)
    (inv := fun (i : Usize) => i.val ≤ «name».length ∧
      ∀ k < i.val, («name».val[k]!).val ≠ 0 ∧ strings.val[offset.val + k]! = «name».val[k]!)
  · intro index hinv
    unfold fdt.format.name_at_loop.body
    step*
    · have hi : index.val < «name».length := by scalar_tac
      have e1 : i1 = «name».val[index.val]! := by rw [i1_post]; exact getElem_eq_getElem! rfl _
      refine (decide_eq_false fun hall => (hall index.val hi).1 ?_).symm
      rw [← e1, ‹i1 = 0#u8›]; rfl
    · have hi : index.val < «name».length := by scalar_tac
      have e1 : i1 = «name».val[index.val]! := by rw [i1_post]; exact getElem_eq_getElem! rfl _
      have e3 : i3 = strings.val[offset.val + index.val]! := by
        rw [i3_post]; exact getElem_eq_getElem! i2_post _
      refine (decide_eq_false fun hall => ?_).symm
      exact (bne_iff_ne.mp ‹(i3 != i1) = true›) (by rw [e1, e3]; exact (hall index.val hi).2)
    · have hi : index.val < «name».length := by scalar_tac
      have e1 : i1 = «name».val[index.val]! := by rw [i1_post]; exact getElem_eq_getElem! rfl _
      have e3 : i3 = strings.val[offset.val + index.val]! := by
        rw [i3_post]; exact getElem_eq_getElem! i2_post _
      have hnz : i1.val ≠ 0 := fun h0 => ‹¬i1 = 0#u8› (UScalar.eq_of_val_eq h0)
      have heq : i3 = i1 := by
        have := ‹¬(i3 != i1) = true›
        rwa [bne_iff_ne, ne_eq, Decidable.not_not] at this
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [index1_post] at hk
      by_cases hk' : k < index.val
      · exact hinv.2 k hk'
      · rw [show k = index.val by omega, ← e1, ← e3, heq]
        exact ⟨hnz, rfl⟩
  · exact ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩

/-- `name_at(strings, offset, name)`: whether the string at `offset` of the
strings block, up to its NUL, is `name`: the NUL that `findNul` finds lies
after as many bytes as `name` has, and they are those of `name`. -/
@[step] theorem name_at_spec (strings : Slice U8) (offset : Usize) («name» : Slice U8) :
    fdt.format.name_at strings offset «name» ⦃ b =>
      b = decide (findNul (bytesOf strings) offset.val = some (offset.val + «name».length) ∧
        (bytesOf strings).extract offset.val (offset.val + «name».length) = bytesOf «name») ⦄ := by
  unfold fdt.format.name_at
  step*
  · have hl : offset.val + «name».length + 1 ≤ strings.length := by
      have := of_decide_post b1_post ‹_›; scalar_tac
    have e5 : i5 = strings.val[offset.val + «name».length]! := by
      rw [i5_post]; exact getElem_eq_getElem! (by scalar_tac) _
    refine (decide_eq_false fun hp => ?_).symm
    obtain ⟨-, -, h0, -⟩ := findNul_some hp.1
    have hl' : offset.val + «name».length < strings.length := by omega
    rw [bytesOf_getElem?_of_lt' hl', ← e5, Option.some.injEq, byte_eq_zero_iff] at h0
    exact (bne_iff_ne.mp ‹(i5 != 0#u8) = true›) (UScalar.eq_of_val_eq h0)
  · have hl : offset.val + «name».length + 1 ≤ strings.length := by
      have := of_decide_post b1_post ‹_›; scalar_tac
    have e5 : i5 = strings.val[offset.val + «name».length]! := by
      rw [i5_post]; exact getElem_eq_getElem! (by scalar_tac) _
    have h0 : (strings.val[offset.val + «name».length]!).val = 0 := by
      have := ‹¬(i5 != 0#u8) = true›
      rw [bne_iff_ne, ne_eq, Decidable.not_not] at this
      rw [← e5, this]; rfl
    rw [b_post, decide_eq_decide, nameAt_bytesOf_iff (by omega) h0]
  · have hl : ¬ offset.val + «name».length + 1 ≤ strings.length := by
      have := of_decide_post_not b1_post ‹_›; scalar_tac
    refine (decide_eq_false fun hp => ?_).symm
    obtain ⟨-, h2, -, -⟩ := findNul_some hp.1
    rw [bytesOf_size] at h2
    omega
  · have hl : ¬ offset.val + «name».length ≤ strings.length := by
      have := of_decide_post_not b_post ‹_›; scalar_tac
    refine (decide_eq_false fun hp => ?_).symm
    obtain ⟨-, h2, -, -⟩ := findNul_some hp.1
    rw [bytesOf_size] at h2
    omega

/-! ## Tokens -/

/-- A word of the code that agrees with a read of the specification is the
word that it reads. -/
theorem agrees_word32_ok {v : U32} {E : Except Krepi.Spec.Fdt.Error UInt32}
    (h : Agrees (fun n N => word32 n = N) errorOf (.Ok v) E) : E = .ok (word32 v) := by
  obtain ⟨w, hw, he⟩ := agrees_ok_iff.mp h
  rw [hw, he]

/-- A failure of the code that agrees with a read of the specification is a
failure of the read. -/
theorem agrees_word32_err {x : fdt.Error} {E : Except Krepi.Spec.Fdt.Error UInt32}
    (h : Agrees (fun n N => word32 n = N) errorOf (.Err x) E) : ∃ e, E = .error e :=
  ⟨_, agrees_err_iff.mp h⟩

/-- A token of the code as the `Piece` of the specification. -/
def pieceOf : fdt.nodes.Piece → Piece
  | .Begin nameEnd => .beginNode nameEnd.val
  | .EndNode => .endNode
  | .Property off valueStart valueEnd => .property off.val valueStart.val valueEnd.val
  | .Nop => .nop
  | .End => .endToken

/-- `nodes::piece_at(structure, cursor)`: `pieceAt`, the token at `cursor` and
the offset of the next, for a block whose size leaves room for a value of
`2 ^ 32` bytes below the largest `usize`. -/
@[step] theorem piece_at_spec («structure» : Slice U8) (cursor : Usize)
    (h : «structure».length + 2 ^ 32 ≤ Usize.max) :
    fdt.nodes.piece_at «structure» cursor ⦃ o =>
      o.map (fun p => (pieceOf p.1, p.2.val)) = pieceAt (bytesOf «structure») cursor.val ⦄ := by
  unfold fdt.nodes.piece_at
  step
  split
  · rename_i tag
    have hu := agrees_word32_ok r_post
    have hb := u32At_ok_le hu
    rw [bytesOf_size] at hb
    step
    by_cases t1 : tag.val = 1
    · refine ite_spec_pos (show tag = 1#u32 from UScalar.eq_of_val_eq t1) ?_
      step
      split
      · refine spec_of_eq rfl ?_
        simp only [pieceAt, hu, word32_toNat, t1, ↓reduceIte, ← next_post, ← o_post]
        rfl
      · rename_i nul
        obtain ⟨-, hlt, -, -⟩ := findNul_some o_post.symm
        rw [bytesOf_size] at hlt
        step*
        simp only [pieceAt, hu, word32_toNat, t1, ↓reduceIte, ← next_post, ← o_post,
          Option.map_some, pieceOf, i1_post, i_post]
    refine ite_spec_neg (show ¬ tag = 1#u32 from fun h => t1 (congrArg UScalar.val h)) ?_
    by_cases t3 : tag.val = 3
    · refine ite_spec_pos (show tag = 3#u32 from UScalar.eq_of_val_eq t3) ?_
      step
      split
      · rename_i length
        have hu1 := agrees_word32_ok r1_post
        have hb1 := u32At_ok_le hu1
        rw [bytesOf_size] at hb1
        step
        have hl1 : length1.val = length.val := by rw [length1_post, U32.cast_Usize_val_eq]
        step
        step
        split
        · rename_i off
          have hu2 := agrees_word32_ok r2_post
          have hb2 := u32At_ok_le hu2
          rw [bytesOf_size] at hb2
          have hl := u32_lt length
          have hu1' : u32At (bytesOf «structure») (cursor.val + 4) = .ok (word32 length) := by
            rw [← next_post]; exact hu1
          have hu2' : u32At (bytesOf «structure») (cursor.val + 8) = .ok (word32 off) := by
            rw [show cursor.val + 8 = i.val by omega]; exact hu2
          step*
          · have hv : «structure».length < cursor.val + 12 + length.val := by scalar_tac
            simp only [pieceAt, hu, word32_toNat, t3, ↓reduceIte, hu1', hu2', bytesOf_size, hv]
            rfl
          · have hv : ¬ «structure».length < cursor.val + (12 + length.val) := by scalar_tac
            simp only [pieceAt, hu, word32_toNat, t3, ↓reduceIte, hu1', hu2', bytesOf_size, hv,
              Option.map_some, pieceOf, name1_post, U32.cast_Usize_val_eq, value_start_post,
              value_end_post, i2_post, hl1, next_post, Nat.add_assoc, Nat.reduceAdd,
              Nat.reduceEqDiff]
        · obtain ⟨e, he⟩ := agrees_word32_err r2_post
          refine spec_of_eq rfl ?_
          have hu1' : u32At (bytesOf «structure») (cursor.val + 4) = .ok (word32 length) := by
            rw [← next_post]; exact hu1
          have he' : u32At (bytesOf «structure») (cursor.val + 8) = .error e := by
            rw [show cursor.val + 8 = i.val by omega]; exact he
          simp only [pieceAt, hu, word32_toNat, t3, ↓reduceIte, hu1', he']
          rfl
      · obtain ⟨e, he⟩ := agrees_word32_err r1_post
        refine spec_of_eq rfl ?_
        have he' : u32At (bytesOf «structure») (cursor.val + 4) = .error e := by
          rw [← next_post]; exact he
        simp only [pieceAt, hu, word32_toNat, t3, ↓reduceIte, he']
        rfl
    refine ite_spec_neg (show ¬ tag = 3#u32 from fun h => t3 (congrArg UScalar.val h)) ?_
    step*
    · have t2 : tag.val = 2 := congrArg UScalar.val ‹tag = 2#u32›
      simp only [pieceAt, hu, word32_toNat, t2, ↓reduceIte, Option.map_some, pieceOf, next_post,
        Nat.reduceEqDiff]
    · have t2 : tag.val ≠ 2 := fun h => ‹¬tag = 2#u32› (UScalar.eq_of_val_eq h)
      have t4 : tag.val = 4 := congrArg UScalar.val ‹tag = 4#u32›
      simp only [pieceAt, hu, word32_toNat, t4, ↓reduceIte, Option.map_some, pieceOf, next_post,
        Nat.reduceEqDiff]
    · have t2 : tag.val ≠ 2 := fun h => ‹¬tag = 2#u32› (UScalar.eq_of_val_eq h)
      have t4 : tag.val ≠ 4 := fun h => ‹¬tag = 4#u32› (UScalar.eq_of_val_eq h)
      simp only [pieceAt, hu, word32_toNat, t1, t3, t2, t4, ↓reduceIte, Option.map_some, pieceOf,
        next_post]
  · obtain ⟨e, he⟩ := agrees_word32_err r_post
    refine spec_of_eq rfl ?_
    simp only [pieceAt, he]
    rfl

end Krepi.Proofs.Fdt.Refinement
