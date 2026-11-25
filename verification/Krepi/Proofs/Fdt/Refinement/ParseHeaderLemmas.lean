module

public import Krepi.Proofs.Fdt.Refinement.SpanLemmas
public import Krepi.Proofs.Fdt.Refinement.TranslateSpecLemmas
public import Krepi.Proofs.Fdt.Refinement.ParseHeaderSpecLemmas

/-!
# Device tree: refinement of the header, the reservation map and its iterator

The triples of the generated functions of `fdt::parser` that check the header
and the reservation map, and of the iterator over the entries of the map,
each a `@[step]` lemma, so that the proof of a caller steps over the call with
the triple of the callee and a mutant of a callee fails the proof of the
callee alone:

- the layout: `LayoutRepr` (a layout of the code stands for the layout of a
  header of the specification: the same offsets, with the ends of the blocks);
- the header: `intersects_spec` (`intersects`), `block_spec` (`block`: the
  end of the block, and the bytes of the block of the specification) and
  `header_spec` (`header`: the layout of the header, or its error), with the
  numbers of its checks `header_size_val`, `magic_iff`, `max_blob_val`,
  `version_iff` and `rem_ne_iff`;
- the reservation map: `overlaps_earlier_spec` (whether a span overlaps one of
  the entries read before it), `reservation_entry_spec` (`entryStep`: whether
  the entry is the terminator, or its error) with `zero_pair_iff` and
  `max_res_val`, and `reservation_map_spec` (`reservationMap`: the end of the
  entries before the terminator, or the error);
- the tree: `fdtRepr_of_header` (the representation of a tree whose views
  are the parts of the header of its input), `total_size_spec` and
  `fdt_total_size_spec` (the statement `FdtTotalSize`);
- the iterator: `reservation_step_spec`, `reservations_next_end` and
  `reservations_next_ok` (the two outcomes of `Reservations::next`),
  `reservations_stands` (an iterator stands for the entries that its bytes
  give from its cursor) and `fdt_reservations_spec` (the statement
  `FdtReservations` without its premise).

`header_spec` walks the 373 generated lines of `header` once: `ite_merge`
merges the two copies of the checks after the versions that the code repeats,
and each check is one step of `check_spec`, `check_or_spec` or `try_spec`
against the join point or the step of the specification at the same place.
`reservation_map_spec` is proved with `loop.spec_decr_nat`: the entries read
so far and the map from the cursor on give the map from the start.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The layout -/

/-- A layout of the code stands for the layout of a header of the
specification: the same `totalsize` and offsets, with the end of each block
in place of its size. -/
def LayoutRepr (l : fdt.parser.Layout) (L : Layout) : Prop :=
  l.total.val = L.total ∧ l.structure.val = L.structStart ∧
    l.structure_end.val = L.structEnd ∧ l.strings.val = L.stringsStart ∧
    l.strings_end.val = L.stringsEnd ∧ l.reservations.val = L.reserveStart

/-! ## The header -/

theorem header_size_val : fdt.format.HEADER_SIZE.val = 40 := by
  rw [fdt.format.HEADER_SIZE]; rfl

theorem magic_iff (v : U32) : (v != fdt.format.MAGIC) = true ↔ word32 v ≠ FDT_MAGIC := by
  rw [bne_iff_ne, ne_eq, ne_eq, word32_eq_iff, fdt.format.MAGIC]
  constructor
  · intro h h'; exact h (UScalar.eq_of_val_eq (by rw [h']; rfl))
  · intro h h'; exact h (by rw [h']; rfl)

theorem max_blob_val : fdt.MAX_BLOB_SIZE.val = 2097152 := by
  rw [fdt.MAX_BLOB_SIZE]; rfl

/-- The test of the versions of the code, as that of the specification. -/
theorem version_iff (v c : U32) :
    (v < 17#u32 ∨ (c != 16#u32) = true ∧ (c != 17#u32) = true ∨ v < c) ↔
      (decide (v.val < 17) || !(c.val == 16 || c.val == 17) || decide (v.val < c.val)) = true := by
  simp only [UScalar.lt_equiv, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  have e16 : c = 16#u32 ↔ c.val = 16 :=
    ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩
  have e17 : c = 17#u32 ↔ c.val = 17 :=
    ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩
  rw [e16, e17]
  have h17 : (17#u32).val = 17 := rfl
  constructor <;> intro h <;> omega

/-- A test of a remainder of the code, as that of the specification. -/
theorem rem_ne_iff {x i : Usize} {n : Nat} (h : i.val = x.val % n) :
    (i != 0#usize) = true ↔ (x.val % n != 0) = true := by
  rw [bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, ← h]
  exact ⟨fun h' h0 => h' (UScalar.eq_of_val_eq h0), fun h' h0 => h' (by rw [h0]; rfl)⟩

/-- `intersects(a, a_end, b, b_end)`: `intersects`. -/
@[step] theorem intersects_spec (a ae b be : Usize) :
    fdt.format.intersects a ae b be ⦃ r => r = intersects a.val ae.val b.val be.val ⦄ := by
  unfold fdt.format.intersects intersects
  by_cases h1 : a < ae <;> by_cases h2 : b < be <;> by_cases h3 : a < be <;>
    simp only [h1, h2, h3, ↓reduceIte, spec_ok] <;>
    simp only [UScalar.lt_equiv] at h1 h2 h3 <;> simp [h1, h2, h3, UScalar.lt_equiv]

/-- `block(blob, start, size)`: the end of the block of `block`, whose bytes
are those of the block of the specification, or its error. -/
@[step] theorem block_spec (hU : Usize64) (blob : Slice U8) (start size : Usize) :
    fdt.parser.block blob start size ⦃ r =>
      Agrees (fun e B => e.val = start.val + size.val ∧
          B = (bytesOf blob).extract start.val e.val)
        errorOf r (block (bytesOf blob) start.val size.val) ⦄ := by
  unfold fdt.parser.block block
  refine check_spec (by rw [UScalar.lt_equiv, header_size_val]; rfl) rfl fun _ _ => ?_
  step as ⟨o, o_post⟩
  have hm := usize_max hU
  cases o with
  | none =>
    rw [checkedAdd_of_not_lt (by omega)]; exact (spec_ok _).mpr rfl
  | some e =>
    obtain ⟨hle, he, -⟩ := o_post
    rw [checkedAdd_of_lt (by omega), except_ok_bind]
    refine check_spec (by rw [UScalar.lt_equiv, Slice.len_val, bytesOf_size, he]) rfl
      fun _ _ => ?_
    rw [spec_ok]
    exact ⟨he, by rw [he]⟩

/-- `header(input)`: the layout of the header of `header`, or its error. -/
@[step] theorem header_spec (hU : Usize64) (input : Slice U8) :
    fdt.parser.header input ⦃ r =>
      Agrees (fun l h => LayoutRepr l h.layout) errorOf r (header (bytesOf input)) ⦄ := by
  unfold fdt.parser.header
  simp only [ite_merge]
  unfold header
  refine check_spec (by rw [UScalar.lt_equiv, Slice.len_val, header_size_val, bytesOf_size]; rfl)
    rfl fun _ _ => ?_
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun v b hv _ => ?_
  subst hv
  refine check_spec (magic_iff v) rfl fun _ _ => ?_
  step as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun v1 b1 hv1 _ => ?_
  subst hv1
  step as ⟨total, total_post⟩
  have htv : total.val = v1.val := by rw [total_post, U32.cast_Usize_val_eq]
  rw [word32_toNat, ← htv]
  refine check_spec (by rw [UScalar.lt_equiv, header_size_val]; rfl) rfl fun _ _ => ?_
  step as ⟨i1, i1_post⟩
  have hi1 : i1.val = total.val := by
    rw [i1_post, UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (usize_lt hU total)
  refine check_spec (by rw [gt_iff_lt, UScalar.lt_equiv, max_blob_val, hi1]; rfl)
    rfl fun _ _ => ?_
  refine check_spec (by rw [UScalar.lt_equiv, Slice.len_val, bytesOf_size]) rfl fun _ _ => ?_
  step as ⟨blob, blob_post, _⟩
  rw [← bytesOf_slice blob_post]
  step as ⟨r2, r2_post⟩
  refine try_spec r2_post (fun e => from_residual_spec e) fun v2 b2 hv2 _ => ?_
  subst hv2
  step as ⟨r3, r3_post⟩
  refine try_spec r3_post (fun e => from_residual_spec e) fun v3 b3 hv3 _ => ?_
  subst hv3
  rw [word32_toNat, word32_toNat]
  refine check_spec (version_iff v2 v3) rfl fun _ _ => ?_
  step as ⟨r4, r4_post⟩
  refine try_spec r4_post (fun e => from_residual_spec e) fun v4 b4 hv4 _ => ?_
  subst hv4
  step as ⟨st, st_post⟩
  step as ⟨r5, r5_post⟩
  refine try_spec r5_post (fun e => from_residual_spec e) fun v5 b5 hv5 _ => ?_
  subst hv5
  step as ⟨sg, sg_post⟩
  step as ⟨r6, r6_post⟩
  refine try_spec r6_post (fun e => from_residual_spec e) fun v6 b6 hv6 _ => ?_
  subst hv6
  step as ⟨rs, rs_post⟩
  step as ⟨r7, r7_post⟩
  refine try_spec r7_post (fun e => from_residual_spec e) fun v7 b7 hv7 _ => ?_
  subst hv7
  step as ⟨sgz, sgz_post⟩
  step as ⟨r8, r8_post⟩
  refine try_spec r8_post (fun e => from_residual_spec e) fun v8 b8 hv8 _ => ?_
  subst hv8
  step as ⟨stz, stz_post⟩
  have hst : st.val = v4.val := by rw [st_post, U32.cast_Usize_val_eq]
  have hsg : sg.val = v5.val := by rw [sg_post, U32.cast_Usize_val_eq]
  have hrs : rs.val = v6.val := by rw [rs_post, U32.cast_Usize_val_eq]
  have hsgz : sgz.val = v7.val := by rw [sgz_post, U32.cast_Usize_val_eq]
  have hstz : stz.val = v8.val := by rw [stz_post, U32.cast_Usize_val_eq]
  rw [word32_toNat, word32_toNat, word32_toNat, word32_toNat, word32_toNat, ← hst, ← hsg,
    ← hrs, ← hsgz, ← hstz, Bool.or_assoc]
  step as ⟨i3, i3_post⟩
  refine check_or_spec (rem_ne_iff i3_post) rfl fun _ => ?_
  step as ⟨i4, i4_post⟩
  refine check_or_spec (rem_ne_iff i4_post) rfl fun _ => ?_
  step as ⟨i5, i5_post⟩
  refine check_spec (rem_ne_iff i5_post) rfl fun _ _ => ?_
  step as ⟨r9, r9_post⟩
  refine try_spec r9_post (fun e => from_residual_spec e) fun v9 b9 hv9 _ => ?_
  step as ⟨r10, r10_post⟩
  refine try_spec r10_post (fun e => from_residual_spec e) fun v10 b10 hv10 _ => ?_
  refine check_or_spec (by rw [UScalar.lt_equiv, decide_eq_true_iff]; rfl) rfl fun _ => ?_
  refine check_spec (by rw [UScalar.lt_equiv, header_size_val, decide_eq_true_iff]; rfl) rfl
    fun _ _ => ?_
  step as ⟨bi, bi_post⟩
  refine check_spec (by rw [bi_post, hv9.1, hv10.1]; rfl) rfl fun _ _ => ?_
  rw [spec_ok]
  exact ⟨rfl, rfl, hv9.1, rfl, hv10.1, rfl⟩

/-! ## The reservation map -/

theorem spanOf_mk (a b : U64) : spanOf { start := a, size := b } = ⟨word64 a, word64 b⟩ := rfl

/-- `overlaps_earlier(blob, first, cursor, span)`: whether the span overlaps
one of the entries read from `first` up to `cursor`, for entries that the
bytes give. -/
@[step] theorem overlaps_earlier_spec (blob : Slice U8) (first cursor : Usize) (span : fdt.Span)
    (earlier : List Span) (hr : ReadsAt (bytesOf blob) first.val earlier)
    (hc : cursor.val = first.val + 16 * earlier.length) :
    fdt.parser.overlaps_earlier blob first cursor span ⦃ r =>
      r = .Ok (earlier.any (·.overlaps (spanOf span))) ⦄ := by
  unfold fdt.parser.overlaps_earlier fdt.parser.overlaps_earlier_loop
  apply loop.spec_decr_nat
    (measure := fun (e : Usize) => cursor.val - e.val)
    (inv := fun (e : Usize) => ∃ k, e.val = first.val + 16 * k ∧ k ≤ earlier.length ∧
      (earlier.drop k).any (·.overlaps (spanOf span)) = earlier.any (·.overlaps (spanOf span)))
  · rintro e ⟨k, hk, hkn, hany⟩
    unfold fdt.parser.overlaps_earlier_loop.body
    by_cases hlt : e < cursor
    · have hkl : k < earlier.length := by rw [UScalar.lt_equiv] at hlt; omega
      obtain ⟨h1, h2⟩ := hr k hkl
      simp only [hlt, ↓reduceIte]
      step as ⟨r, r_post⟩
      rw [hk, h1] at r_post
      obtain ⟨v, rfl, hv⟩ := eq_ok_of_agrees r_post
      refine branch_ok_spec ?_
      step as ⟨i, i_post⟩
      step as ⟨r1, r1_post⟩
      rw [i_post, hk, h2] at r1_post
      obtain ⟨v1, rfl, hv1⟩ := eq_ok_of_agrees r1_post
      refine branch_ok_spec ?_
      step as ⟨b, b_post⟩
      rw [spanOf_mk, hv, hv1] at b_post
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte, spec_ok]
        rw [← hany, any_drop_cons hkl, ← b_post, hb, Bool.true_or]
      · simp only [hb, ↓reduceIte, Bool.false_eq_true]
        step as ⟨e1, e1_post⟩
        refine ⟨⟨k + 1, by omega, hkl, ?_⟩, by rw [UScalar.lt_equiv] at hlt; omega⟩
        rw [← hany, any_drop_cons hkl, ← b_post, Bool.not_eq_true _ |>.mp hb, Bool.false_or]
    · have hkn' : k = earlier.length := by rw [UScalar.lt_equiv] at hlt; omega
      simp only [hlt, ↓reduceIte, spec_ok]
      rw [← hany, hkn', List.drop_length, List.any_nil]
  · exact ⟨0, by omega, Nat.zero_le _, rfl⟩

/-- The test of the terminator of the code, as that of the specification. -/
theorem zero_pair_iff (a b : U64) :
    (a = 0#u64 ∧ b = 0#u64) ↔ (word64 a == 0 && word64 b == 0) = true := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, word64_eq_iff, word64_eq_iff, u64_eq_zero_iff,
    u64_eq_zero_iff]; rfl

theorem max_res_val : fdt.MAX_RESERVATIONS.val = 128 := by
  rw [fdt.MAX_RESERVATIONS]; rfl

/-- `reservation_entry(blob, layout, cursor, count)`: whether the entry at the
cursor is the terminator, or the error of `entryStep`, after `count` entries
that the bytes give. -/
@[step] theorem reservation_entry_spec (hU : Usize64) (blob : Slice U8) (layout : fdt.parser.Layout)
    (cursor : Usize) (count : U64) (h : Header) (earlier : List Span)
    (hl : LayoutRepr layout h.layout) (hb : bytesOf blob = h.blob)
    (hr : ReadsAt h.blob layout.reservations.val earlier)
    (hc : cursor.val = layout.reservations.val + 16 * earlier.length)
    (hn : count.val = earlier.length) (hcount : count.val ≤ 128) :
    fdt.parser.reservation_entry blob layout cursor count ⦃ r =>
      Agrees (fun b o => b = o.isNone) errorOf r (entryStep h cursor.val earlier) ⦄ := by
  unfold fdt.parser.reservation_entry entryStep
  simp only [ite_merge2]
  step as ⟨o, o_post⟩
  have hm := usize_max hU
  cases o with
  | none =>
    rw [checkedAdd_of_not_lt (by omega)]; exact (spec_ok _).mpr rfl
  | some e =>
    obtain ⟨hle, he, -⟩ := o_post
    rw [checkedAdd_of_lt (by omega), except_ok_bind]
    refine check_spec (by rw [UScalar.lt_equiv, hl.1, he]) rfl fun _ _ => ?_
    step as ⟨b, b_post⟩
    refine check_or_spec (by rw [b_post, he, hl.2.1, hl.2.2.1]) rfl fun _ => ?_
    step as ⟨b1, b1_post⟩
    refine check_spec (by rw [b1_post, he, hl.2.2.2.1, hl.2.2.2.2.1]) rfl fun _ _ => ?_
    step as ⟨r, r_post⟩
    rw [hb] at r_post
    refine try_spec r_post (fun e => from_residual_spec e) fun v w hv _ => ?_
    subst hv
    step as ⟨i, i_post⟩
    step as ⟨r1, r1_post⟩
    rw [hb, i_post] at r1_post
    refine try_spec r1_post (fun e => from_residual_spec e) fun v1 w1 hv1 _ => ?_
    subst hv1
    refine ite_agrees_spec (zero_pair_iff v v1) (fun _ => (spec_ok _).mpr rfl) fun _ => ?_
    step as ⟨i1, i1_post⟩
    refine check_spec (by rw [gt_iff_lt, UScalar.lt_equiv, max_res_val, i1_post, hn]; rfl) rfl
      fun _ _ => ?_
    step as ⟨r2, r2_post⟩
    refine try_spec r2_post (fun e => from_residual_spec e) fun v2 sp hv2 _ => ?_
    subst hv2
    refine check_spec (by rw [word64_eq_iff, u64_eq_zero_iff]; rfl) rfl fun _ _ => ?_
    step with overlaps_earlier_spec blob layout.reservations cursor v2 earlier
      (by rw [hb]; exact hr) hc as ⟨r3, r3_post⟩
    subst r3_post
    refine branch_ok_spec (check_spec Iff.rfl rfl fun _ _ => ?_)
    exact (spec_ok _).mpr rfl

/-- `reservation_map(blob, layout)`: the end of the entries of
`reservationMap` before the terminator, or its error. -/
@[step] theorem reservation_map_spec (hU : Usize64) (blob : Slice U8) (layout : fdt.parser.Layout)
    (h : Header) (hl : LayoutRepr layout h.layout) (hb : bytesOf blob = h.blob) :
    fdt.parser.reservation_map blob layout ⦃ r =>
      Agrees (fun e l => e.val = h.layout.reserveStart + 16 * l.length) errorOf r
        (reservationMap h) ⦄ := by
  unfold fdt.parser.reservation_map fdt.parser.reservation_map_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Usize × U64) => 129 - p.2.val)
    (inv := fun (p : Usize × U64) => ∃ earlier : List Span, p.2.val = earlier.length ∧
      p.2.val ≤ 129 ∧ p.1.val = layout.reservations.val + 16 * earlier.length ∧
      ReadsAt h.blob layout.reservations.val earlier ∧
      reservationsFrom h (129 - p.2.val) p.1.val earlier = reservationMap h)
  · rintro ⟨c, n⟩ ⟨earlier, hn, h129, hc, hr, hE⟩
    unfold fdt.parser.reservation_map_loop.body
    dsimp only at hn h129 hc hE ⊢
    by_cases hle : n ≤ fdt.MAX_RESERVATIONS
    · simp only [hle, ↓reduceIte]
      have hn128 : n.val ≤ 128 := by rw [UScalar.le_equiv, max_res_val] at hle; exact hle
      step with reservation_entry_spec hU blob _ c n h earlier hl hb hr hc hn hn128
        as ⟨r, r_post⟩
      rw [show 129 - n.val = (128 - n.val) + 1 by omega, reservationsFrom_succ] at hE
      cases hes : entryStep h c.val earlier with
      | error e =>
        rw [hes] at r_post
        obtain ⟨x, rfl, hx⟩ := eq_err_of_agrees r_post
        refine branch_err_spec ?_
        step with from_residual_spec x as ⟨r1, r1_post⟩
        rw [r1_post, ← hE, hes, ← hx]
        rfl
      | ok o =>
        rw [hes] at r_post
        obtain ⟨b, rfl, hb⟩ := eq_ok_of_agrees r_post
        refine branch_ok_spec ?_
        obtain ⟨h16, hs⟩ := entryStep_ok hes
        cases o with
        | none =>
          simp only [hb, Option.isNone_none, ↓reduceIte, spec_ok]
          have hE' : reservationMap h = .ok earlier := by rw [← hE, hes]; rfl
          rw [hE', agrees_ok_ok, hc, hl.2.2.2.2.2]
        | some s =>
          simp only [hb, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
          have := hl.1
          step as ⟨c2, c2_post⟩
          step as ⟨n1, n1_post⟩
          obtain ⟨h1, h2⟩ := hs s rfl
          rw [hc] at h1 h2
          refine ⟨⟨earlier ++ [s], by simp; omega, by omega, by simp; omega,
            readsAt_append hr h1 h2, ?_⟩, by omega⟩
          rw [← hE, hes, n1_post, c2_post, show 129 - (n.val + 1) = 128 - n.val by omega]
          rfl
    · have h129' : n.val = 129 := by rw [UScalar.le_equiv, max_res_val] at hle; omega
      simp only [hle, ↓reduceIte, spec_ok]
      rw [← hE, h129']; rfl
  · exact ⟨[], rfl, by simp, by simp, readsAt_nil _ _, by rw [hl.2.2.2.2.2]; rfl⟩


/-! ## The tree -/

/-- A tree of the code whose views are the tree's bytes, the blocks and the
entries of the map of the header `h` of an input stands for the parse of that
input: the form in which the proof of `Fdt::parse` concludes `FdtRepr`. -/
theorem fdtRepr_of_header {input : ByteArray} {h : Header} {T : Fdt} (t : fdt.Fdt)
    (hh : header input = .ok h) (hp : Fdt.parse input = .ok T) (hblob : bytesOf t.blob = h.blob)
    (hst : bytesOf t.structure = h.structure_) (hsg : bytesOf t.strings = h.strings)
    (hres : bytesOf t.reservations = h.blob.extract h.layout.reserveStart
      (h.layout.reserveStart + 16 * T.reservations.length)) :
    FdtRepr t T :=
  ⟨by rw [hblob, parse_blob hh, hp], h, by rw [hblob, header_blob hh], hblob.symm, hst, hsg,
    hres⟩

/-- `Fdt::total_size()`: the length of the tree's bytes. -/
@[step] theorem total_size_spec (hU : Usize64) (t : fdt.Fdt) :
    fdt.parser.Fdt.total_size t ⦃ n => n.val = t.blob.length ⦄ := by
  unfold fdt.parser.Fdt.total_size
  rw [spec_ok, UScalar.cast_val_eq, Slice.len_val]
  exact Nat.mod_eq_of_lt (slice_length_lt hU t.blob)

/-- The statement `FdtTotalSize` without its premise on the platform's
`usize`, which `total_size_spec` takes. -/
theorem fdt_total_size_spec (hU : Usize64) (t : fdt.Fdt) (T : Fdt) (hR : FdtRepr t T) :
    fdt.parser.Fdt.total_size t ⦃ n => word64 n = T.totalSize ⦄ := by
  obtain ⟨hp, h, hh, hblob, -, -, -⟩ := hR
  have F := header_facts hh
  refine spec_mono (total_size_spec hU t) fun n hn => ?_
  rw [(parse_ok hp hh).2.1, word64, hn, ← bytesOf_size, ← hblob, F.blob_size]

/-! ## The iterator over the reservation map -/

/-- `reservation_step(entries, cursor)`: the entry at the cursor and the
cursor after it when the entry lies within the bytes, none and the same
cursor otherwise. -/
@[step] theorem reservation_step_spec (entries : Slice U8) (cursor : Usize) :
    fdt.nodes.reservation_step entries cursor ⦃ c o =>
      if cursor.val + 16 ≤ entries.length then
        c.val = cursor.val + 16 ∧ ∃ s, o = some s ∧
          u64At (bytesOf entries) cursor.val = .ok (word64 s.start) ∧
          u64At (bytesOf entries) (cursor.val + 8) = .ok (word64 s.size)
      else c = cursor ∧ o = none ⦄ := by
  unfold fdt.nodes.reservation_step
  step as ⟨r, r_post⟩
  cases r with
  | Err e =>
    have hlt := u64At_error_lt (agrees_err_iff.mp r_post)
    rw [bytesOf_size] at hlt
    rw [spec_ok, uncurry'_pair]
    simp only [show ¬ cursor.val + 16 ≤ entries.length by omega, ↓reduceIte, and_self]
  | Ok start =>
    obtain ⟨w, hw, hsw⟩ := agrees_ok_iff.mp r_post
    have h8 := u64At_ok_le hw
    rw [bytesOf_size] at h8
    dsimp only
    step as ⟨i, i_post⟩
    step as ⟨r1, r1_post⟩
    rw [i_post] at r1_post
    cases r1 with
    | Err e =>
      have hlt := u64At_error_lt (agrees_err_iff.mp r1_post)
      rw [bytesOf_size] at hlt
      rw [spec_ok, uncurry'_pair]
      simp only [show ¬ cursor.val + 16 ≤ entries.length by omega, ↓reduceIte, and_self]
    | Ok size =>
      obtain ⟨w1, hw1, hsw1⟩ := agrees_ok_iff.mp r1_post
      have h16 := u64At_ok_le hw1
      rw [bytesOf_size] at h16
      dsimp only
      step as ⟨i1, i1_post⟩
      simp only [show cursor.val + 16 ≤ entries.length by omega, ↓reduceIte]
      exact ⟨i1_post, _, rfl, by rw [hw, hsw], by rw [hw1, hsw1]⟩

/-- `Reservations::next()` at the end of the bytes: none, and the same
iterator. -/
theorem reservations_next_end (it : fdt.Reservations)
    (h : it.entries.length < it.cursor.val + 16) :
    fdt.nodes.Reservations.next it ⦃ o it' => o = none ∧ it' = it ⦄ := by
  unfold fdt.nodes.Reservations.next
  step as ⟨c, o, hco⟩
  simp only [show ¬ it.cursor.val + 16 ≤ it.entries.length by omega, ↓reduceIte] at hco
  obtain ⟨rfl, rfl⟩ := hco
  exact ⟨rfl, rfl⟩

/-- `Reservations::next()` on an entry within the bytes: the entry that the
two words at the cursor give, and the cursor after it. -/
theorem reservations_next_ok (it : fdt.Reservations)
    (h : it.cursor.val + 16 ≤ it.entries.length) :
    fdt.nodes.Reservations.next it ⦃ o it' => it'.entries = it.entries ∧
      it'.cursor.val = it.cursor.val + 16 ∧ ∃ s, o = some s ∧
        u64At (bytesOf it.entries) it.cursor.val = .ok (word64 s.start) ∧
        u64At (bytesOf it.entries) (it.cursor.val + 8) = .ok (word64 s.size) ⦄ := by
  unfold fdt.nodes.Reservations.next
  step as ⟨c, o, hco⟩
  simp only [h, ↓reduceIte] at hco
  obtain ⟨hc, s, rfl, h1, h2⟩ := hco
  exact ⟨hc, s, rfl, h1, h2⟩

/-- An iterator over the reservation map stands for the entries that the
words of its bytes give from its cursor on, when they fill its bytes. -/
theorem reservations_stands (l : List Span) (it : fdt.Reservations)
    (hl : it.entries.length = it.cursor.val + 16 * l.length)
    (hr : ReadsAt (bytesOf it.entries) it.cursor.val l) :
    Stands fdt.nodes.Reservations.next SpanRepr it l := by
  refine stands_of_sim (fun it l => it.entries.length = it.cursor.val + 16 * l.length ∧
    ReadsAt (bytesOf it.entries) it.cursor.val l) ?_ ?_ l it ⟨hl, hr⟩
  · rintro s ⟨hs, -⟩
    rw [List.length_nil, Nat.mul_zero, Nat.add_zero] at hs
    have hlt : s.entries.length < s.cursor.val + 16 := by omega
    refine spec_mono (reservations_next_end s hlt) ?_
    rintro ⟨o, s'⟩ ⟨ho, hs'⟩
    rw [hs']
    exact ⟨ho, (fixed_iff s).mpr (reservations_next_end s hlt)⟩
  · rintro s b l ⟨hs, hr⟩
    obtain ⟨⟨hb1, hb2⟩, hr'⟩ := readsAt_cons.mp hr
    rw [List.length_cons] at hs
    have hle : s.cursor.val + 16 ≤ s.entries.length := by omega
    refine spec_mono (reservations_next_ok s hle) ?_
    rintro ⟨o, s'⟩ ⟨he, hc, a, rfl, ha1, ha2⟩
    rw [hb1] at ha1
    rw [hb2] at ha2
    injection ha1 with e1
    injection ha2 with e2
    refine ⟨a, rfl, ?_, ?_, ?_⟩
    · show spanOf a = b
      rw [spanOf, ← e1, ← e2]
    · rw [he, hc]; omega
    · rw [he, hc]; exact hr'

/-- The statement `FdtReservations` without its premise: the iterator of a
tree stands for the entries of its reservation map. -/
theorem fdt_reservations_spec (t : fdt.Fdt) (T : Fdt) (hR : FdtRepr t T) :
    fdt.parser.Fdt.reservations t ⦃ it =>
      Stands fdt.nodes.Reservations.next SpanRepr it T.reservations ⦄ := by
  obtain ⟨hp, h, hh, -, -, -, hres⟩ := hR
  have F := header_facts hh
  obtain ⟨hread, hlen⟩ := reservationMap_ok (parse_ok hp hh).1
  unfold fdt.parser.Fdt.reservations
  rw [spec_ok]
  have hle : h.layout.reserveStart + 16 * T.reservations.length ≤ h.blob.size := by
    rw [F.blob_size]; omega
  have hsz : (bytesOf t.reservations).size = 16 * T.reservations.length := by
    rw [hres, ByteArray.size_extract]; omega
  refine reservations_stands T.reservations _ ?_ ?_
  · rw [bytesOf_size] at hsz
    show t.reservations.length = (0#usize).val + 16 * T.reservations.length
    rw [hsz, show (0#usize).val = 0 from rfl, Nat.zero_add]
  · show ReadsAt (bytesOf t.reservations) (0#usize).val T.reservations
    rw [hres]
    exact readsAt_extract hread (Nat.le_refl _) hle

end Krepi.Proofs.Fdt.Refinement
