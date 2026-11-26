module

public import Krepi.Proofs.Fdt.Refinement.MemoryLemmas
public import Krepi.Proofs.Fdt.Refinement.AccessorLemmas
public import Krepi.Proofs.Fdt.Refinement.BootSpecLemmas

/-!
# Device tree: refinement of the boot memory

The triples of the generated functions of `fdt::hand_over` and
`fdt::hand_over::selection`, stated against `Krepi.Spec.Fdt.BootMemory`, so
that the proof of a caller steps over the call with the triple of the callee
and a mutant of a callee fails the proof of the callee alone. The lemmas that
need no generated code are in `Krepi.Proofs.Fdt.Refinement.BootSpecLemmas`.

- Numbers: `is_aligned_spec` (whether the address is a multiple of
  `2 ^ alignment_log2`), `align_up_spec` (`alignUp` to a power of two) and
  `ram_bytes_spec` (the fold of `checkedAdd` over the RAM ranges).
- Availability: `touches_region_spec` and `boot_memory_is_available_spec`, the
  statement `BootMemoryIsAvailable` without its premises.
- The checks on the memory map: `check_storage_spec` (`checkStorage`).
- The selection: `furthest_touched_loop_spec` and `furthest_touched_spec`
  (`furthestOf` of the exclusions), `exclusions_repr`,
  `search_range_loop_spec` and `search_range_spec`
  (`BootMemory.searchRange`), `search_ranges_loop_spec` and
  `search_ranges_spec` (`BootMemory.searchRanges`), and
  `boot_memory_find_available_spec`, the statement `BootMemoryFindAvailable`
  without its premise `Usize64`. The code adds the ends of the RAM ranges and
  of the exclusions without a check; the invariants `MemoryMap.WellFormed` and
  `BootMemory.Consistent` keep them within 64 bits.
- The root `compatible`: `compatible_entries_loop_spec` and
  `compatible_entries_spec` (`compatibleEntries` of the pieces before the final
  NUL), `has_entry_loop_spec` and `has_entry_spec`,
  `holds_required_loop_spec` and `holds_required_spec`, and
  `check_compatible_spec` (`checkCompatible`).
- The discovery: `check_hand_over_spec` (`handOverCheck`) and
  `fdt_discover_boot_memory_spec`, the statement `FdtDiscoverBootMemory`.

The loops are proved with `loop.spec_decr_nat`, with the invariant that the
answer of the specification from the cursor on is the answer from the start.
The proofs over `if`s of the specification walk its join points in lockstep
with the code (`check_spec`, `check_neg_spec`, `try_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Numbers -/

/-- `is_aligned(address, alignment_log2)`: whether the address is a multiple
of `2 ^ alignment_log2`. -/
@[step] theorem is_aligned_spec (address : U64) (log2 : U8) :
    fdt.hand_over.is_aligned address log2 ⦃ b =>
      b = decide (address.val % 2 ^ log2.val = 0) ⦄ := by
  unfold fdt.hand_over.is_aligned
  step* -grind
  · have hs : shift.val = log2.val := by rw [shift_post, U8.cast_U64_val_eq]
    have h64 : 64 ≤ log2.val := by
      have := ‹shift ≥ 64#u64›
      rw [ge_iff_le, UScalar.le_equiv] at this
      rw [← hs]; exact this
    have hlt : address.val < 2 ^ log2.val :=
      Nat.lt_of_lt_of_le (u64_lt address) (Nat.pow_le_pow_right (by decide) h64)
    rw [Nat.mod_eq_of_lt hlt, decide_eq_decide]
    exact u64_eq_zero_iff
  · have hs : shift.val < 64 := by
      have := ‹¬shift ≥ 64#u64›
      rw [ge_iff_le, UScalar.le_equiv] at this
      exact Nat.lt_of_not_le this
    have hi : i.val = 2 ^ shift.val := by
      rw [i_post, Nat.shiftLeft_eq, Nat.one_mul, u64_size]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)
    rw [hi]; exact Nat.one_le_two_pow
  · have hsv : shift.val = log2.val := by rw [shift_post, U8.cast_U64_val_eq]
    have hs : shift.val < 64 := by
      have := ‹¬shift ≥ 64#u64›
      rw [ge_iff_le, UScalar.le_equiv] at this
      exact Nat.lt_of_not_le this
    have hi : i.val = 2 ^ shift.val := by
      rw [i_post, Nat.shiftLeft_eq, Nat.one_mul, u64_size]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)
    have h2 : i2.val = address.val % 2 ^ log2.val := by
      rw [i2_post, UScalar.val_and, i1_post, hi, Nat.and_two_pow_sub_one_eq_mod, hsv]
    rw [decide_eq_decide, u64_eq_zero_iff, h2]

/-- `align_up(address, alignment)`: `alignUp` to a power of two. -/
@[step] theorem align_up_spec (address alignment : U64) {k : Nat} (hk : k < 64)
    (ha : alignment.val = 2 ^ k) :
    fdt.hand_over.selection.align_up address alignment ⦃ r =>
      Agrees (fun v n => v.val = n) errorOf r (alignUp address.val alignment.val) ⦄ := by
  unfold fdt.hand_over.selection.align_up
  step* -grind
  · rw [ha]; exact Nat.one_le_two_pow
  · subst_vars
    simp only [u64_max_eq] at o_post
    rw [ha, alignUp_pow_error hk (by rw [ha] at i_post; omega)]
    rfl
  · subst_vars
    obtain ⟨-, hz, -⟩ := o_post
    have hn : (~~~i).val = 2 ^ 64 - 2 ^ k := by
      rw [u64_not_val, i_post, ha]
      have := Nat.one_le_two_pow (n := k)
      have := Nat.pow_lt_pow_right (a := 2) (by decide) hk
      omega
    have hlt : address.val + 2 ^ k - 1 < 2 ^ 64 := by
      have := u64_lt sum
      rw [i_post, ha] at hz
      have := Nat.one_le_two_pow (n := k)
      omega
    rw [ha, alignUp_pow_ok hk hlt, agrees_ok_ok, i2_post, UScalar.val_and, hn, hz, i_post, ha]
    have := Nat.one_le_two_pow (n := k)
    congr 1
    omega

/-! ## The sum of the RAM ranges -/

/-- `ram_bytes(ranges)`: the sum of the sizes, or `Overflow`, as the fold of
`checkedAdd` of `Fdt.discoverBootMemory`. -/
@[step] theorem ram_bytes_spec (ranges : Slice fdt.Span) :
    fdt.hand_over.ram_bytes ranges ⦃ r => Agrees (fun n N => n.val = N) errorOf r
      ((spansOf ranges).foldlM (fun sum s => checkedAdd sum s.size.toNat) 0) ⦄ := by
  unfold fdt.hand_over.ram_bytes fdt.hand_over.ram_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × Usize) => ranges.length - x.2.val)
    (inv := fun (x : U64 × Usize) => x.2.val ≤ ranges.length ∧
      ((spansOf ranges).drop x.2.val).foldlM (fun sum s => checkedAdd sum s.size.toNat) x.1.val =
        (spansOf ranges).foldlM (fun sum s => checkedAdd sum s.size.toNat) 0)
  · rintro ⟨sum, i⟩ ⟨hle, hinv⟩
    simp only at hle hinv
    unfold fdt.hand_over.ram_bytes_loop.body
    have hl : (spansOf ranges).length = ranges.length := List.length_map _
    step* -grind
    · have hi : i.val < (spansOf ranges).length := by rw [hl]; scalar_tac
      have e : (spansOf ranges)[i.val] = spanOf s := by
        simp only [spansOf, List.getElem_map, s_post]
      obtain rfl : o = none := ‹_›
      simp only [u64_max_eq] at o_post
      have hc : ¬ sum.val + s.size.val < 2 ^ 64 := by omega
      rw [← hinv, List.drop_eq_getElem_cons hi, e, List.foldlM_cons]
      simp only [checkedAdd, spanOf_size, word64_toNat, hc, ↓reduceIte]
      rfl
    · have hi : i.val < (spansOf ranges).length := by rw [hl]; scalar_tac
      have e : (spansOf ranges)[i.val] = spanOf s := by
        simp only [spansOf, List.getElem_map, s_post]
      obtain rfl : o = some sum1 := ‹_›
      obtain ⟨h1, h2, -⟩ := o_post
      rw [u64_max_eq] at h1
      have hc : sum.val + s.size.val < 2 ^ 64 := by omega
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, List.drop_eq_getElem_cons hi, e, List.foldlM_cons, index1_post, h2]
      simp only [checkedAdd, spanOf_size, word64_toNat, hc, ↓reduceIte]
      rfl
    · rw [← hinv, List.drop_eq_nil_of_le (by rw [hl]; scalar_tac)]
      rfl
  · exact ⟨Nat.zero_le _, rfl⟩

/-! ## Availability -/

/-- `touches_region(regions, span)`: whether the span of a region of the slice
touches `span`. -/
@[step] theorem touches_region_spec (regions : Slice fdt.ReservedRegion) (span : fdt.Span) :
    fdt.hand_over.touches_region regions span ⦃ b =>
      b = ((regionsOf regions).map (·.span)).any (·.touches (spanOf span)) ⦄ := by
  unfold fdt.hand_over.touches_region fdt.hand_over.touches_region_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => regions.length - i.val)
    (inv := fun (i : Usize) =>
      (((regionsOf regions).map (·.span)).drop i.val).any (·.touches (spanOf span)) =
        ((regionsOf regions).map (·.span)).any (·.touches (spanOf span)))
  · intro i hinv
    unfold fdt.hand_over.touches_region_loop.body
    have hl : ((regionsOf regions).map (·.span)).length = regions.length := by
      simp [regionsOf]
    step* -grind
    · have hi : i.val < ((regionsOf regions).map (·.span)).length := by rw [hl]; scalar_tac
      have e : ((regionsOf regions).map (·.span))[i.val] = spanOf rr.span := by
        simp only [regionsOf, List.map_map, List.getElem_map, rr_post, Function.comp_apply,
          regionOf]
      rw [← hinv, any_drop_cons hi, e, ← b_post, ‹b = true›, Bool.true_or]
    · have hi : i.val < ((regionsOf regions).map (·.span)).length := by rw [hl]; scalar_tac
      refine ⟨?_, by scalar_tac⟩
      have e : ((regionsOf regions).map (·.span))[i.val] = spanOf rr.span := by
        simp only [regionsOf, List.map_map, List.getElem_map, rr_post, Function.comp_apply,
          regionOf]
      rw [← hinv, any_drop_cons hi, index1_post, e, ← b_post,
        (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_or]
    · rw [← hinv, List.drop_eq_nil_of_le (by rw [hl]; scalar_tac)]; rfl
  · rfl

/-- `BootMemory::is_available(span)`: the statement `BootMemoryIsAvailable`,
which holds without the invariants of the boot memory. -/
@[step] theorem boot_memory_is_available_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M) (span : fdt.Span) :
    fdt.hand_over.BootMemory.is_available m span ⦃ r =>
      Agrees (· = ·) errorOf r (M.isAvailable (spanOf span)) ⦄ := by
  obtain ⟨hm, hdtb, himg, -, -, -⟩ := h
  have hsz : (spanOf span).size = 0 ↔ span.size = 0#u64 := by
    rw [spanOf_size, word64_eq_zero_iff]
  unfold fdt.hand_over.BootMemory.is_available
  step* -grind
  · simp only [BootMemory.isAvailable, hsz.mpr ‹_›, ↓reduceIte]; rfl
  · have hne : ¬ (spanOf span).size = 0 := fun h => ‹¬span.size = 0#u64› (hsz.mp h)
    simp only [BootMemory.isAvailable, hne, of_decide_post b_post ‹_›, not_true_eq_false,
      ↓reduceIte, agrees_ok_ok, BootMemory.exclusions, List.any_cons, himg, ← b2_post,
      ‹b2 = true›, Bool.true_or, Bool.not_true, Bool.and_false]
  · have hne : ¬ (spanOf span).size = 0 := fun h => ‹¬span.size = 0#u64› (hsz.mp h)
    have h2 : b2 = false := by simpa using ‹¬b2 = true›
    simp only [BootMemory.isAvailable, hne, of_decide_post b_post ‹_›, not_true_eq_false,
      ↓reduceIte, agrees_ok_ok, BootMemory.exclusions, List.any_cons, himg, hdtb, ← b2_post,
      ← b3_post, h2, ‹b3 = true›, Bool.true_or, Bool.false_or, Bool.not_true, Bool.and_false]
  · have hne : ¬ (spanOf span).size = 0 := fun h => ‹¬span.size = 0#u64› (hsz.mp h)
    have h2 : b2 = false := by simpa using ‹¬b2 = true›
    have h3 : b3 = false := by simpa using ‹¬b3 = true›
    simp only [BootMemory.isAvailable, hne, of_decide_post b_post ‹_›, not_true_eq_false,
      ↓reduceIte, agrees_ok_ok, BootMemory.exclusions, List.any_cons, himg, hdtb, ← b2_post,
      ← b3_post, h2, h3, Bool.false_or, BootMemory.ram, BootMemory.reserved, ← s_post,
      ← b1_post, ‹b1 = true›, Bool.true_and, ← s1_post, ← b4_post]
    cases b4 <;> rfl
  · have hne : ¬ (spanOf span).size = 0 := fun h => ‹¬span.size = 0#u64› (hsz.mp h)
    have h1 : b1 = false := by simpa using ‹¬b1 = true›
    simp only [BootMemory.isAvailable, hne, of_decide_post b_post ‹_›, not_true_eq_false,
      ↓reduceIte, agrees_ok_ok, BootMemory.ram, ← s_post, ← b1_post, h1, Bool.false_and]
  · have hne : ¬ (spanOf span).size = 0 := fun h => ‹¬span.size = 0#u64› (hsz.mp h)
    have hv : ¬ (spanOf span).Valid := of_decide_post_not b_post ‹_›
    simp only [BootMemory.isAvailable, hne, hv, not_false_eq_true, ↓reduceIte]; rfl

/-! ## The checks on the memory map -/

/-- `check_storage(memory, dtb, image)`: `checkStorage`, the tree and then the
image inside one RAM range. -/
@[step] theorem check_storage_spec {m : fdt.MemoryMap} {M : MemoryMap} (h : MemoryMapRepr m M)
    (dtb image : fdt.Span) :
    fdt.hand_over.check_storage m dtb image ⦃ r =>
      Agrees (fun _ _ => True) errorOf r (checkStorage M (spanOf dtb) (spanOf image)) ⦄ := by
  unfold fdt.hand_over.check_storage
  step* -grind
  all_goals unfold checkStorage
  · simp only [← s_post, ← b_post, ← b1_post, ‹b = true›, ‹b1 = true›, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]; exact trivial
  · have h1 : b1 = false := by simpa using ‹¬b1 = true›
    simp only [← s_post, ← b_post, ← b1_post, ‹b = true›, h1, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte]; rfl
  · have h0 : b = false := by simpa using ‹¬b = true›
    simp only [← s_post, ← b_post, h0, Bool.not_false, ↓reduceIte]; rfl

/-! ## The selection -/

/-- The loop of `furthest_touched(image, dtb, regions, candidate)` over the
regions from `index` on: the search of the furthest end from the state
`(touched, end)`. -/
@[step] theorem furthest_touched_loop_spec (regions : Slice fdt.ReservedRegion)
    (candidate : fdt.Span) (touched : Bool) (e : U64) (index : Usize)
    (hv : ∀ x ∈ (regionsOf regions).map (·.span), x.Valid) (hi : index.val ≤ regions.length) :
    fdt.hand_over.selection.furthest_touched_loop regions candidate touched e index ⦃ t e' =>
      (t, e'.val) = (((regionsOf regions).map (·.span)).drop index.val).foldl
        (furthestStep (spanOf candidate)) (touched, e.val) ⦄ := by
  generalize hW : (((regionsOf regions).map (·.span)).drop index.val).foldl
    (furthestStep (spanOf candidate)) (touched, e.val) = W
  have hl : ((regionsOf regions).map (·.span)).length = regions.length := by simp [regionsOf]
  unfold fdt.hand_over.selection.furthest_touched_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Bool × U64 × Usize) => regions.length - x.2.2.val)
    (inv := fun (x : Bool × U64 × Usize) => x.2.2.val ≤ regions.length ∧
      (((regionsOf regions).map (·.span)).drop x.2.2.val).foldl
        (furthestStep (spanOf candidate)) (x.1, x.2.1.val) = W)
  · rintro ⟨t, en, i⟩ ⟨hle, hinv⟩
    simp only at hle hinv
    unfold fdt.hand_over.selection.furthest_touched_loop.body
    step* -grind
    · have hi0 : i.val < regions.length := by
        have h0 := ‹i < regions.len›; rw [UScalar.lt_equiv, Slice.len_val] at h0; exact h0
      have hmax : i.val + 1 ≤ Usize.max := by
        have := regions.property; have h' : i.val < regions.val.length := hi0; omega
      have hil : i.val < ((regionsOf regions).map (·.span)).length := by rw [hl]; exact hi0
      have ex : ((regionsOf regions).map (·.span))[i.val] = spanOf rr.span := by
        simp only [regionsOf, List.map_map, List.getElem_map, rr_post, Function.comp_apply,
          regionOf]
      have hvx : rr.span.start.val + rr.span.size.val ≤ U64.max := by
        have := hv _ (ex ▸ List.getElem_mem hil)
        rw [Span.Valid, spanOf_endNat] at this
        rw [u64_max_eq]; omega
      rw [List.drop_eq_getElem_cons hil, ex, List.foldl_cons] at hinv
      by_cases hb : b = true <;> by_cases ht : t = true <;>
        simp only [hb, ht, ↓reduceIte, Bool.false_eq_true]
      · step* -grind
        by_cases hx : x > en <;> simp only [hx, ↓reduceIte] <;> step* -grind <;>
          refine ⟨by omega, ?_, by omega⟩ <;> rw [index1_post, ← hinv] <;> congr 1 <;>
          simp only [furthestStep, ← b_post, hb, ht, ↓reduceIte, spanOf_endNat, ← x_post]
        · rw [gt_iff_lt, UScalar.lt_equiv] at hx
          rw [Nat.max_eq_right (Nat.le_of_lt hx)]
        · rw [gt_iff_lt, UScalar.lt_equiv] at hx
          rw [Nat.max_eq_left (Nat.le_of_not_lt hx)]
      · step* -grind
        refine ⟨by omega, ?_, by omega⟩
        rw [index1_post, ← hinv]
        simp only [furthestStep, ← b_post, hb, ht, ↓reduceIte, spanOf_endNat, ← x_post,
          Bool.false_eq_true]
      · step* -grind
        refine ⟨by omega, ?_, by omega⟩
        have hb' : b = false := by simpa using hb
        rw [index1_post, ← hinv]
        simp only [furthestStep, ← b_post, hb', ht, Bool.false_eq_true, ↓reduceIte]
      · step* -grind
        refine ⟨by omega, ?_, by omega⟩
        have hb' : b = false := by simpa using hb
        have ht' : t = false := by simpa using ht
        rw [index1_post, ← hinv]
        simp only [furthestStep, ← b_post, hb', ht', Bool.false_eq_true, ↓reduceIte]
    · have h0 := ‹¬i < regions.len›
      rw [UScalar.lt_equiv, Slice.len_val] at h0
      rw [← hinv, List.drop_eq_nil_of_le (by rw [hl]; omega)]; rfl
  · exact ⟨hi, hW⟩

/-- `furthest_touched(image, dtb, regions, candidate)`: the furthest end of the
image, the tree and the regions that the candidate touches, none when it
touches none, for exclusions within 64 bits. -/
@[step] theorem furthest_touched_spec (image dtb : fdt.Span) (regions : Slice fdt.ReservedRegion)
    (candidate : fdt.Span) (hi : (spanOf image).Valid) (hd : (spanOf dtb).Valid)
    (hv : ∀ x ∈ (regionsOf regions).map (·.span), x.Valid) :
    fdt.hand_over.selection.furthest_touched image dtb regions candidate ⦃ o =>
      o.map (·.val) = furthestOf (spanOf image :: spanOf dtb :: (regionsOf regions).map (·.span))
        (spanOf candidate) ⦄ := by
  have hiv : image.start.val + image.size.val < 2 ^ 64 := by
    rw [Span.Valid, spanOf_endNat] at hi; exact hi
  have hdv : dtb.start.val + dtb.size.val < 2 ^ 64 := by
    rw [Span.Valid, spanOf_endNat] at hd; exact hd
  unfold fdt.hand_over.selection.furthest_touched
  have key : ∀ (t : Bool) (en : U64), (t, en.val) = furthestStep (spanOf candidate)
      (furthestStep (spanOf candidate) (false, 0) (spanOf image)) (spanOf dtb) →
      (do
        let (touched1, end2) ←
          fdt.hand_over.selection.furthest_touched_loop regions candidate t en 0#usize
        if touched1 = true then ok (some end2) else ok none) ⦃ o =>
        o.map (·.val) = furthestOf (spanOf image :: spanOf dtb :: (regionsOf regions).map (·.span))
          (spanOf candidate) ⦄ := by
    intro t en h
    step* -grind
    all_goals
      have hf := furthestOf_of_foldl (xs := spanOf image :: spanOf dtb ::
        (regionsOf regions).map (·.span)) (c := spanOf candidate) (t := touched1) (e := end2.val)
        (by rw [touched1_post, List.drop_zero, h, List.foldl_cons, List.foldl_cons])
    · rw [← hf]; simp [‹touched1 = true›]
    · rw [← hf]; simp [‹¬touched1 = true›]
  step as ⟨b, b_post⟩
  have hc1 : furthestStep (spanOf candidate) (false, 0) (spanOf image) =
      if b = true then (true, image.start.val + image.size.val) else (false, 0) := by
    simp only [furthestStep, ← b_post, spanOf_endNat, Bool.false_eq_true, ↓reduceIte]
  by_cases hb : b = true
  · simp only [hb, ↓reduceIte] at hc1 ⊢
    step as ⟨x, x_post⟩
    step as ⟨b1, b1_post⟩
    by_cases hb1 : b1 = true
    · simp only [hb1, ↓reduceIte]
      step as ⟨i, i_post⟩
      by_cases hx : i > x
      · simp only [hx, ↓reduceIte, bind_ok]
        refine key true i ?_
        rw [hc1]
        rw [gt_iff_lt, UScalar.lt_equiv] at hx
        simp only [furthestStep, ← b1_post, hb1, spanOf_endNat, ↓reduceIte, ← x_post, ← i_post,
          Nat.max_eq_right (Nat.le_of_lt hx)]
      · simp only [hx, ↓reduceIte, bind_ok]
        refine key true x ?_
        rw [hc1]
        rw [gt_iff_lt, UScalar.lt_equiv] at hx
        simp only [furthestStep, ← b1_post, hb1, spanOf_endNat, ↓reduceIte, ← x_post, ← i_post,
          Nat.max_eq_left (Nat.le_of_not_lt hx)]
    · simp only [hb1, Bool.false_eq_true, ↓reduceIte, bind_ok]
      refine key true x ?_
      have hb1' : b1 = false := by simpa using hb1
      rw [hc1]
      simp only [furthestStep, ← b1_post, hb1', Bool.false_eq_true, ↓reduceIte, x_post]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
    step as ⟨b1, b1_post⟩
    by_cases hb1 : b1 = true
    · simp only [hb1, ↓reduceIte]
      step as ⟨end2, end2_post⟩
      refine key true end2 ?_
      rw [hc1]
      simp only [furthestStep, ← b1_post, hb1, spanOf_endNat, ↓reduceIte, Bool.false_eq_true,
        ← end2_post]
    · simp only [hb1, Bool.false_eq_true, ↓reduceIte, bind_ok]
      refine key false 0#u64 ?_
      have hb1' : b1 = false := by simpa using hb1
      rw [hc1]
      simp only [furthestStep, ← b1_post, hb1', Bool.false_eq_true, ↓reduceIte]
      rfl

/-- The exclusions of a boot memory of the code, with the reserved regions of
a slice that stands for its reserved regions. -/
theorem exclusions_repr {m : fdt.BootMemory} {M : BootMemory} (h : BootMemoryRepr m M)
    {regions : Slice fdt.ReservedRegion} (hr : regionsOf regions = M.reserved) :
    M.exclusions = spanOf m.image :: spanOf m.dtb :: (regionsOf regions).map (·.span) := by
  rw [BootMemory.exclusions, h.2.2.1, h.2.1, hr]

/-- The loop of `search_range(memory, size, alignment, bound, start, fuel)`
from the candidate at `start` after `tried` candidates: `BootMemory.searchRange`
with the fuel left. -/
theorem search_range_loop_spec {m : fdt.BootMemory} {M : BootMemory} (h : BootMemoryRepr m M)
    (hv : ∀ x ∈ M.exclusions, x.Valid) (regions : Slice fdt.ReservedRegion)
    (hr : regionsOf regions = M.reserved) (size alignment bound : U64) {k : Nat} (hk : k < 64)
    (ha : alignment.val = 2 ^ k) (fuel : Usize) (start : U64) (tried : Usize)
    (ht : tried.val ≤ fuel.val) :
    fdt.hand_over.selection.search_range_loop m.dtb m.image size alignment bound fuel regions
      start tried ⦃ r =>
      Agrees (OptionRel SpanRepr) errorOf r
        (M.searchRange size.val alignment.val bound.val (fuel.val - tried.val) start.val) ⦄ := by
  have hex := exclusions_repr h hr
  have hvi : (spanOf m.image).Valid := hv _ (by rw [hex]; simp)
  have hvd : (spanOf m.dtb).Valid := hv _ (by rw [hex]; simp)
  have hvr : ∀ x ∈ (regionsOf regions).map (·.span), x.Valid :=
    fun x hx => hv x (by rw [hex]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  generalize hW : M.searchRange size.val alignment.val bound.val (fuel.val - tried.val)
    start.val = W
  unfold fdt.hand_over.selection.search_range_loop
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × Usize) => fuel.val - x.2.val)
    (inv := fun (x : U64 × Usize) => x.2.val ≤ fuel.val ∧
      M.searchRange size.val alignment.val bound.val (fuel.val - x.2.val) x.1.val = W)
  · rintro ⟨st, tr⟩ ⟨hle, hinv⟩
    simp only at hle hinv
    unfold fdt.hand_over.selection.search_range_loop.body
    dsimp only
    have hcand : spanOf { start := st, size := size } =
        ⟨UInt64.ofNat st.val, UInt64.ofNat size.val⟩ := rfl
    by_cases htf : tr < fuel
    · have hlt : tr.val < fuel.val := htf
      rw [show fuel.val - tr.val = (fuel.val - tr.val - 1) + 1 by omega, searchRange_succ,
        ← hcand] at hinv
      simp only [htf, ↓reduceIte]
      step* -grind
      · obtain rfl : o = none := ‹_›
        simp only [u64_max_eq] at o_post
        have hc : (2 ^ 64 ≤ st.val + size.val || bound.val < st.val + size.val) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
        rw [← hinv]
        simp only [hc, ↓reduceIte]
        exact trivial
      · obtain rfl : o = some «end» := ‹_›
        obtain ⟨-, hz, -⟩ := o_post
        have hb : bound.val < «end».val := ‹«end» > bound›
        have hc : (2 ^ 64 ≤ st.val + size.val || bound.val < st.val + size.val) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
        rw [← hinv]
        simp only [hc, ↓reduceIte]
        exact trivial
      all_goals
        obtain rfl : o = some «end» := ‹_›
        obtain ⟨h1, hz, -⟩ := o_post
        have hb : ¬ bound.val < «end».val := ‹¬«end» > bound›
        rw [u64_max_eq] at h1
        have hc : (2 ^ 64 ≤ st.val + size.val || bound.val < st.val + size.val) = false := by
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hinv
      · obtain rfl : o1 = none := ‹_›
        rw [Option.map_none, ← hex] at o1_post
        rw [← o1_post] at hinv
        rw [← hinv]
        exact hcand
      · obtain rfl : o1 = some furthest := ‹_›
        rw [Option.map_some, ← hex] at o1_post
        obtain ⟨n, hn, hvn⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
        simp only [← o1_post, hn, except_ok_bind, ← hvn] at hinv
        refine ⟨by omega, ?_, by omega⟩
        rw [← hinv, tried1_post]
        congr 1
      · obtain rfl : o1 = some furthest := ‹_›
        rw [Option.map_some, ← hex] at o1_post
        have hE := agrees_err_of_branch cf_post ‹_› residual_post r_post
        simp only [← o1_post, hE, except_error_bind] at hinv
        rw [← hinv, r1_post, ← e_post]
        rfl
    · have hge : ¬ tr.val < fuel.val := htf
      simp only [htf, ↓reduceIte, spec_ok]
      rw [show fuel.val - tr.val = 0 by omega] at hinv
      rw [← hinv]
      rfl
  · exact ⟨ht, hW⟩

/-- `search_range(memory, size, alignment, bound, start, fuel)`:
`BootMemory.searchRange` of the reserved regions of the boot memory, for
exclusions within 64 bits and an alignment that is a power of two. -/
@[step] theorem search_range_spec {m : fdt.BootMemory} {M : BootMemory} (h : BootMemoryRepr m M)
    (hv : ∀ x ∈ M.exclusions, x.Valid) (size alignment bound start : U64) {k : Nat}
    (hk : k < 64) (ha : alignment.val = 2 ^ k) (fuel : Usize) :
    fdt.hand_over.selection.search_range m size alignment bound start fuel ⦃ r =>
      Agrees (OptionRel SpanRepr) errorOf r
        (M.searchRange size.val alignment.val bound.val fuel.val start.val) ⦄ := by
  unfold fdt.hand_over.selection.search_range
  step with memory_map_reserved_spec h.1 as ⟨regions, hr⟩
  have := search_range_loop_spec h hv regions hr size alignment bound hk ha fuel start 0#usize
    (Nat.zero_le _)
  simpa using this

/-- The loop of `search_ranges(memory, size, alignment, minimum, limit)` over the
RAM ranges from `index` on: `BootMemory.searchRanges` of those ranges. -/
theorem search_ranges_loop_spec {m : fdt.BootMemory} {M : BootMemory} (h : BootMemoryRepr m M)
    (hv : ∀ x ∈ M.exclusions, x.Valid) (size alignment minimum limit : U64) {k : Nat}
    (hk : k < 64) (ha : alignment.val = 2 ^ k) (ranges : Slice fdt.Span)
    (hrv : ∀ x ∈ spansOf ranges, x.Valid) (fuel : Usize) (hf : fuel.val = M.reserved.length + 3)
    (index : Usize) (hi : index.val ≤ ranges.length) :
    fdt.hand_over.selection.search_ranges_loop m.memory m.dtb m.image m.ram_bytes
      m.max_blob_size m.alignment_log2 size alignment minimum limit ranges fuel index ⦃ r =>
      Agrees (OptionRel SpanRepr) errorOf r (M.searchRanges size.val alignment.val minimum.val
        limit.val ((spansOf ranges).drop index.val)) ⦄ := by
  have h' : BootMemoryRepr (fdt.BootMemory.mk m.memory m.dtb m.image m.ram_bytes
      m.max_blob_size m.alignment_log2) M := h
  have hl : (spansOf ranges).length = ranges.length := List.length_map _
  generalize hW : M.searchRanges size.val alignment.val minimum.val limit.val
    ((spansOf ranges).drop index.val) = W
  unfold fdt.hand_over.selection.search_ranges_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => ranges.length - i.val)
    (inv := fun (i : Usize) => i.val ≤ ranges.length ∧
      M.searchRanges size.val alignment.val minimum.val limit.val
        ((spansOf ranges).drop i.val) = W)
  · rintro i ⟨hle, hinv⟩
    unfold fdt.hand_over.selection.search_ranges_loop.body
    simp only [bind_ite_ok_prop]
    by_cases hi1 : i < ranges.len
    · have hi0 : i.val < ranges.length := by
        have h0 := hi1; rw [UScalar.lt_equiv, Slice.len_val] at h0; exact h0
      have hmax : i.val + 1 ≤ Usize.max := by
        have := ranges.property; have h' : i.val < ranges.val.length := hi0; omega
      have hil : i.val < (spansOf ranges).length := by rw [hl]; exact hi0
      simp only [hi1, ↓reduceIte]
      step as ⟨range, range_post⟩
      have e : (spansOf ranges)[i.val] = spanOf range := by
        simp only [spansOf, List.getElem_map, range_post]
      have hvr : range.start.val + range.size.val ≤ U64.max := by
        have := hrv _ (e ▸ List.getElem_mem hil)
        rw [Span.Valid, spanOf_endNat] at this
        rw [u64_max_eq]; omega
      rw [List.drop_eq_getElem_cons hil, e, BootMemory.searchRanges, spanOf_start, word64_toNat,
        ← u64_ite_gt_val] at hinv
      step* -grind
      · obtain ⟨n, hn, hvn⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
        rw [hn, except_ok_bind, ← hvn] at hinv
        have hb : (min (spanOf range).endNat limit.val) =
            (if range_end < limit then range_end else limit).val := by
          rw [u64_ite_lt_val, range_end_post, spanOf_endNat]
        obtain ⟨b, hb1, hrel⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf1_post ‹_› r1_post)
        rw [‹val1 = none›] at hrel
        rcases b with _ | b
        · rw [hb, ← hf, hb1, except_ok_bind] at hinv
          refine ⟨by omega, ?_, by omega⟩
          rw [index1_post, ← hinv]
        · exact hrel.elim
      · obtain ⟨n, hn, hvn⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
        rw [hn, except_ok_bind, ← hvn] at hinv
        have hb : (min (spanOf range).endNat limit.val) =
            (if range_end < limit then range_end else limit).val := by
          rw [u64_ite_lt_val, range_end_post, spanOf_endNat]
        obtain ⟨b, hb1, hrel⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf1_post ‹_› r1_post)
        rw [‹val1 = some _›] at hrel
        rcases b with _ | b
        · exact hrel.elim
        · rw [hb, ← hf, hb1, except_ok_bind] at hinv
          rw [← hinv]
          exact hrel
      · obtain ⟨n, hn, hvn⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
        rw [hn, except_ok_bind, ← hvn] at hinv
        have hb : (min (spanOf range).endNat limit.val) =
            (if range_end < limit then range_end else limit).val := by
          rw [u64_ite_lt_val, range_end_post, spanOf_endNat]
        have hE := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
        rw [hb, ← hf, hE, except_error_bind] at hinv
        rw [← hinv, r2_post, ← e_post]
        rfl
      · have hE := agrees_err_of_branch cf_post ‹_› residual_post r_post
        rw [hE, except_error_bind] at hinv
        rw [← hinv, r2_post, ← e_post]
        rfl
    · simp only [hi1, ↓reduceIte, spec_ok]
      have h0 := hi1
      rw [UScalar.lt_equiv, Slice.len_val] at h0
      rw [← hinv, List.drop_eq_nil_of_le (by rw [hl]; omega)]
      exact trivial
  · exact ⟨hi, hW⟩

/-- `search_ranges(memory, size, alignment, minimum, limit)`:
`BootMemory.searchRanges` through the RAM ranges, with `Q + 3` candidates
in each, for RAM ranges and exclusions within 64 bits and an alignment that
is a power of two. -/
@[step] theorem search_ranges_spec {m : fdt.BootMemory} {M : BootMemory} (h : BootMemoryRepr m M)
    (hv : ∀ x ∈ M.exclusions, x.Valid) (hrv : ∀ x ∈ M.ram, x.Valid)
    (size alignment minimum limit : U64) {k : Nat} (hk : k < 64) (ha : alignment.val = 2 ^ k) :
    fdt.hand_over.selection.search_ranges m size alignment minimum limit ⦃ r =>
      Agrees (OptionRel SpanRepr) errorOf r
        (M.searchRanges size.val alignment.val minimum.val limit.val M.ram) ⦄ := by
  unfold fdt.hand_over.selection.search_ranges
  step with memory_map_ram_spec h.1 as ⟨ranges, hra⟩
  step with memory_map_reserved_spec h.1 as ⟨s, hs⟩
  have hsl : s.length = M.reserved.length := by
    rw [BootMemory.reserved, ← hs]; simp [regionsOf]
  have hmax : M.reserved.length ≤ 128 := by
    obtain ⟨-, h2, h3⟩ := h.1
    rw [BootMemory.reserved, h3]
    simp only [List.length_map, List.length_take]
    have : MAX_RESERVED_REGIONS.toNat = 128 := rfl
    omega
  step as ⟨fuel, hfuel⟩
  have := search_ranges_loop_spec h hv size alignment minimum limit hk ha ranges
    (by rw [hra]; exact hrv) fuel (by rw [hfuel, Slice.len_val, hsl]) 0#usize (Nat.zero_le _)
  simpa [hra, BootMemory.ram] using this

/-- `BootMemory::find_available(size, alignment, minimum, limit)`: the statement
`BootMemoryFindAvailable` without its premise `Usize64`. -/
@[step] theorem boot_memory_find_available_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M)
    (hw : M.memory.WellFormed) (hc : M.Consistent) (size alignment minimum limit : U64) :
    fdt.hand_over.selection.BootMemory.find_available m size alignment minimum limit ⦃ r =>
      Agrees (OptionRel SpanRepr) errorOf r (M.findAvailable (word64 size) (word64 alignment)
        (word64 minimum) (word64 limit)) ⦄ := by
  have hv : ∀ x ∈ M.exclusions, x.Valid := by
    intro x hx
    simp only [BootMemory.exclusions, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | rfl | ⟨r, hr, rfl⟩
    · exact consistent_image_valid hc
    · exact consistent_dtb_valid hc
    · exact wellFormed_reserved_valid hw r hr
  have hrv : ∀ x ∈ M.ram, x.Valid := wellFormed_ram_valid hw
  unfold fdt.hand_over.selection.BootMemory.find_available BootMemory.findAvailable
  by_cases h1 : size = 0#u64
  · have : (decide (word64 size = 0) || decide (word64 limit ≤ word64 minimum)) = true := by
      simp [word64_eq_zero_iff, h1]
    rw [this]
    simp only [h1, ↓reduceIte, spec_ok]
    rfl
  simp only [h1, ↓reduceIte]
  by_cases h2 : minimum >= limit
  · have : (decide (word64 size = 0) || decide (word64 limit ≤ word64 minimum)) = true := by
      rw [ge_iff_le, UScalar.le_equiv] at h2
      simp only [Bool.or_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, word64_toNat]
      exact Or.inr h2
    rw [this]
    simp only [h2, ↓reduceIte, spec_ok]
    rfl
  have h12 : (decide (word64 size = 0) || decide (word64 limit ≤ word64 minimum)) = false := by
    rw [ge_iff_le, UScalar.le_equiv] at h2
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, word64_eq_zero_iff,
      UInt64.le_iff_toNat_le, word64_toNat]
    exact ⟨h1, h2⟩
  simp only [h2, ↓reduceIte, h12, Bool.false_eq_true]
  by_cases h3 : alignment = 0#u64
  · have : isPowerOfTwo (word64 alignment) = false := by
      rw [Bool.eq_false_iff, ne_eq, isPowerOfTwo_iff, word64_toNat, h3]
      simp
    rw [this]
    simp only [h3, ↓reduceIte, spec_ok, Bool.not_false]
    rfl
  simp only [h3, ↓reduceIte]
  step as ⟨i, i_post, _⟩
  step as ⟨i1, i1_post, _⟩
  have hp : isPowerOfTwo (word64 alignment) = true ↔ i1.val = 0 := by
    rw [isPowerOfTwo_iff, word64_toNat, i1_post, UScalar.val_and, i_post]
    exact ⟨fun h => h.2, fun h => ⟨fun h0 => h3 (UScalar.eq_of_val_eq h0), h⟩⟩
  by_cases h4 : (i1 != 0#u64) = true
  · have : isPowerOfTwo (word64 alignment) = false := by
      rw [Bool.eq_false_iff, ne_eq, hp]
      intro h0; rw [bne_iff_ne, ne_eq] at h4; exact h4 (UScalar.eq_of_val_eq h0)
    rw [this]
    simp only [h4, ↓reduceIte, spec_ok, Bool.not_false]
    rfl
  · have hpw : isPowerOfTwo (word64 alignment) = true := by
      rw [hp]; simpa using h4
    obtain ⟨k, hk, ha⟩ := isPowerOfTwo_exists hpw
    rw [word64_toNat] at ha
    rw [hpw]
    simp only [h4, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    step with search_ranges_spec h hv hrv size alignment minimum limit hk ha as ⟨r, r_post⟩
    simpa only [word64_toNat] using r_post

/-! ## The root `compatible` -/

/-- The loop of `compatible_entries(bytes, end)` from the piece at `start`: the
entries of the pieces of the bytes before `end`, whose byte at `end` is the
final NUL, as `compatibleEntries` reads them; the entries before `start`
succeeded. -/
theorem compatible_entries_loop_spec (bytes : Slice U8) (e : Usize) (he : e.val < bytes.length)
    (hz : (bytesOf bytes)[e.val]? = some 0) (start entries : Usize) (hs : start.val ≤ e.val)
    (hen : entries.val ≤ start.val) (pre : List String)
    (hW : compatibleEntries (splitAtNul ((bytesOf bytes).toList.take e.val)) =
      compatibleEntries (splitAtNul (((bytesOf bytes).toList.take e.val).drop start.val)) >>=
        fun more => pure (pre ++ more)) :
    fdt.hand_over.compatible_entries_loop bytes e start entries ⦃ r =>
      Agrees (fun _ _ => True) errorOf r
        (compatibleEntries (splitAtNul ((bytesOf bytes).toList.take e.val))) ⦄ := by
  unfold fdt.hand_over.compatible_entries_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Usize × Usize) => e.val + 1 - x.1.val)
    (inv := fun (x : Usize × Usize) => x.1.val ≤ e.val ∧ x.2.val ≤ x.1.val ∧
      ∃ pre : List String, compatibleEntries (splitAtNul ((bytesOf bytes).toList.take e.val)) =
        compatibleEntries (splitAtNul (((bytesOf bytes).toList.take e.val).drop x.1.val)) >>=
          fun more => pure (pre ++ more))
  · rintro ⟨st, en⟩ ⟨hst, hens, pre', hinv⟩
    simp only at hst hens hinv
    unfold fdt.hand_over.compatible_entries_loop.body
    have hfe : ∀ n, findNul (bytesOf bytes) st.val = some n → n ≤ e.val :=
      fun n hn => findNul_le_of_zero hz hst hn
    obtain ⟨c1, c2, c3⟩ := cut_bytes bytes (Nat.le_of_lt he) hst hfe
    step* -grind
    rcases o with _ | nul
    · exfalso
      exact findNul_none o_post.symm e.val hst hz
    simp only [bind_ok]
    have hstop : (findNul (bytesOf bytes) st.val).getD e.val = nul.val := by
      rw [← o_post]; rfl
    rw [hstop] at c1 c2 c3
    have hsize : ((bytesOf bytes).extract st.val nul.val).size = nul.val - st.val := by
      rw [ByteArray.size_extract, bytesOf_size]; omega
    have hm0 : nul.val ≤ bytes.length := by omega
    have hm1 : nul.val + 1 ≤ Usize.max := by
      have := bytes.property; have h' : e.val < bytes.val.length := he; omega
    have hm2 : en.val + 1 ≤ Usize.max := by
      have := bytes.property; have h' : e.val < bytes.val.length := he; omega
    step* -grind
    · have hn : nul.val = st.val := by rw [‹nul = st›]
      rw [hinv, c3, compatibleEntries_empty (by omega)]
      rfl
    · have hn : nul.val ≠ st.val := fun h => ‹¬nul = st› (UScalar.eq_of_val_eq h)
      have hge : ¬ nul.val < e.val := by
        have := ‹nul ≥ e›; rw [ge_iff_le, UScalar.le_equiv] at this; omega
      obtain ⟨str, hstr⟩ := compatibleEntries_valid (of_decide_post b_post ‹_›) (by omega)
        ([] : List (List UInt8))
      rw [hinv, agrees_true_bind_pure, c3]
      simp only [hge, ↓reduceIte]
      rw [hstr, agrees_true_bind_pure]
      exact trivial
    · have hn : nul.val ≠ st.val := fun h => ‹¬nul = st› (UScalar.eq_of_val_eq h)
      have hlt : nul.val < e.val := by
        have := ‹¬nul ≥ e›; rw [ge_iff_le, UScalar.le_equiv] at this; omega
      obtain ⟨str, hstr⟩ := compatibleEntries_valid (of_decide_post b_post ‹_›) (by omega)
        (splitAtNul (((bytesOf bytes).toList.take e.val).drop (nul.val + 1)))
      refine ⟨by omega, by omega, ⟨pre' ++ [str], ?_⟩, by omega⟩
      rw [hinv, c3]
      simp only [hlt, ↓reduceIte]
      rw [hstr, entries_bind_assoc, start1_post]
      rfl
    · rw [hinv, c3, compatibleEntries_invalid (of_decide_post_not b_post ‹_›)]
      rfl
  · exact ⟨hs, hen, pre, hW⟩

/-- `compatible_entries(bytes, end)`: the entries of the pieces of the bytes
before the final NUL at `end`, `compatibleEntries`. -/
@[step] theorem compatible_entries_spec (bytes : Slice U8) (e : Usize) (he : e.val < bytes.length)
    (hz : (bytesOf bytes)[e.val]? = some 0) :
    fdt.hand_over.compatible_entries bytes e ⦃ r =>
      Agrees (fun _ _ => True) errorOf r
        (compatibleEntries (splitAtNul ((bytesOf bytes).toList.take e.val))) ⦄ := by
  unfold fdt.hand_over.compatible_entries
  refine compatible_entries_loop_spec bytes e he hz 0#usize 0#usize (Nat.zero_le _)
    (Nat.le_refl _) [] ?_
  simp only [UScalar.ofNatCore_val_eq, List.drop_zero, List.nil_append]
  cases compatibleEntries (splitAtNul ((bytesOf bytes).toList.take e.val)) <;> rfl

/-- The loop of `has_entry(bytes, end, entry)` from the piece at `start`:
whether a piece of the bytes before the final NUL at `end`, from `start` on,
is the bytes of `entry`. -/
theorem has_entry_loop_spec (bytes : Slice U8) (e : Usize) (entry : Slice U8)
    (he : e.val < bytes.length) (hz : (bytesOf bytes)[e.val]? = some 0) (start entries : Usize)
    (hs : start.val ≤ e.val) (hen : entries.val ≤ start.val) :
    fdt.hand_over.has_entry_loop bytes e entry start entries ⦃ b =>
      b = (splitAtNul (((bytesOf bytes).toList.take e.val).drop start.val)).any
        (· == (bytesOf entry).toList) ⦄ := by
  generalize hW : (splitAtNul (((bytesOf bytes).toList.take e.val).drop start.val)).any
    (· == (bytesOf entry).toList) = W
  unfold fdt.hand_over.has_entry_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Usize × Usize) => e.val + 1 - x.1.val)
    (inv := fun (x : Usize × Usize) => x.1.val ≤ e.val ∧ x.2.val ≤ x.1.val ∧
      (splitAtNul (((bytesOf bytes).toList.take e.val).drop x.1.val)).any
        (· == (bytesOf entry).toList) = W)
  · rintro ⟨st, en⟩ ⟨hst, hens, hinv⟩
    simp only at hst hens hinv
    unfold fdt.hand_over.has_entry_loop.body
    have hfe : ∀ n, findNul (bytesOf bytes) st.val = some n → n ≤ e.val :=
      fun n hn => findNul_le_of_zero hz hst hn
    obtain ⟨c1, c2, c3⟩ := cut_bytes bytes (Nat.le_of_lt he) hst hfe
    step* -grind
    rcases o with _ | nul
    · exfalso
      exact findNul_none o_post.symm e.val hst hz
    simp only [bind_ok]
    have hstop : (findNul (bytesOf bytes) st.val).getD e.val = nul.val := by
      rw [← o_post]; rfl
    rw [hstop] at c1 c2 c3
    rw [c3] at hinv
    have hm1 : nul.val + 1 ≤ Usize.max := by
      have := bytes.property; have h' : e.val < bytes.val.length := he; omega
    have hm2 : en.val + 1 ≤ Usize.max := by
      have := bytes.property; have h' : e.val < bytes.val.length := he; omega
    step* -grind
    · have hb := of_decide_post b_post ‹_›
      rw [← hinv, List.any_cons, ← hb.2.2, beq_self_eq_true, Bool.true_or]
    · have hb := of_decide_post_not b_post ‹_›
      have hne : ((bytesOf bytes).extract st.val nul.val).toList ≠ (bytesOf entry).toList := by
        intro h; exact hb ⟨c1, by have := c2; omega, byteArray_eq_iff.mpr h⟩
      have hge : ¬ nul.val < e.val := by
        have := ‹nul ≥ e›; rw [ge_iff_le, UScalar.le_equiv] at this; omega
      simp only [hge, ↓reduceIte, List.any_cons, List.any_nil, Bool.or_false] at hinv
      rw [← hinv, beq_eq_false_iff_ne.mpr hne]
    · have hb := of_decide_post_not b_post ‹_›
      have hne : ((bytesOf bytes).extract st.val nul.val).toList ≠ (bytesOf entry).toList := by
        intro h; exact hb ⟨c1, by have := c2; omega, byteArray_eq_iff.mpr h⟩
      have hlt : nul.val < e.val := by
        have := ‹¬nul ≥ e›; rw [ge_iff_le, UScalar.le_equiv] at this; omega
      simp only [hlt, ↓reduceIte, List.any_cons, beq_eq_false_iff_ne.mpr hne,
        Bool.false_or] at hinv
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [start1_post]; exact hinv
  · exact ⟨hs, hen, hW⟩

/-- `has_entry(bytes, end, entry)`: whether a piece of the bytes before the
final NUL at `end` is the bytes of `entry`. -/
@[step] theorem has_entry_spec (bytes : Slice U8) (e : Usize) (entry : Slice U8)
    (he : e.val < bytes.length) (hz : (bytesOf bytes)[e.val]? = some 0) :
    fdt.hand_over.has_entry bytes e entry ⦃ b =>
      b = (splitAtNul ((bytesOf bytes).toList.take e.val)).any (· == (bytesOf entry).toList) ⦄ := by
  unfold fdt.hand_over.has_entry
  simpa using has_entry_loop_spec bytes e entry he hz 0#usize 0#usize (Nat.zero_le _)
    (Nat.le_refl _)

/-- The loop of `holds_required(bytes, end, required)` from the piece of
`required` at `start`: whether every nonempty piece of `required` from `start`
on is a piece of the bytes before the final NUL at `end`. -/
theorem holds_required_loop_spec (bytes : Slice U8) (e : Usize) (required : Slice U8)
    (he : e.val < bytes.length) (hz : (bytesOf bytes)[e.val]? = some 0) (start pieces : Usize)
    (hs : start.val ≤ required.length) (hp : pieces.val ≤ start.val) :
    fdt.hand_over.holds_required_loop bytes e required start pieces ⦃ b =>
      b = ((splitAtNul (((bytesOf required).toList.take required.length).drop start.val)).filter
        (· != [])).all fun q =>
          (splitAtNul ((bytesOf bytes).toList.take e.val)).any (· == q) ⦄ := by
  generalize hW : ((splitAtNul (((bytesOf required).toList.take required.length).drop
    start.val)).filter (· != [])).all
      (fun q => (splitAtNul ((bytesOf bytes).toList.take e.val)).any (· == q)) = W
  unfold fdt.hand_over.holds_required_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Usize × Usize) => required.length + 1 - x.1.val)
    (inv := fun (x : Usize × Usize) => x.1.val ≤ required.length ∧ x.2.val ≤ x.1.val ∧
      ((splitAtNul (((bytesOf required).toList.take required.length).drop x.1.val)).filter
        (· != [])).all (fun q => (splitAtNul ((bytesOf bytes).toList.take e.val)).any (· == q)) =
          W)
  · rintro ⟨st, pc⟩ ⟨hst, hpc, hinv⟩
    simp only at hst hpc hinv
    unfold fdt.hand_over.holds_required_loop.body
    have hfe : ∀ n, findNul (bytesOf required) st.val = some n → n ≤ required.length := by
      intro n hn
      have := (findNul_some hn).2.1
      rw [bytesOf_size] at this; omega
    obtain ⟨c1, c2, c3⟩ := cut_bytes required (Nat.le_refl _) hst hfe
    rw [c3] at hinv
    step* -grind
    rcases o with _ | nul
    · simp only [bind_ok]
      have hstop : (findNul (bytesOf required) st.val).getD required.length =
          required.len.val := by
        rw [← o_post, Option.map_none, Option.getD_none, Slice.len_val]
      rw [hstop] at c1 c2 hinv
      step* -grind
      · have hgt : st.val < required.len.val := by
          have := ‹required.len > st›; rw [gt_iff_lt, UScalar.lt_equiv] at this; exact this
        have hne : ¬ ((bytesOf required).extract st.val required.len.val).toList = [] := by
          rw [extract_toList_eq_nil required (by rw [Slice.len_val])]; omega
        have hge : ¬ required.len.val < required.length := by rw [Slice.len_val]; omega
        rw [← hinv, all_filter_cons_piece]
        simp only [hge, ↓reduceIte, hne, List.filter_nil, List.all_nil, Bool.and_true]
        rw [← bytesOf_slice s_post, ← b_post, ‹b = true›]
      · have hgt : st.val < required.len.val := by
          have := ‹required.len > st›; rw [gt_iff_lt, UScalar.lt_equiv] at this; exact this
        have hne : ¬ ((bytesOf required).extract st.val required.len.val).toList = [] := by
          rw [extract_toList_eq_nil required (by rw [Slice.len_val])]; omega
        have hb : b = false := by simpa using ‹¬b = true›
        rw [← hinv, all_filter_cons_piece]
        simp only [hne, ↓reduceIte]
        rw [← bytesOf_slice s_post, ← b_post, hb, Bool.false_and]
      · have hle : required.len.val ≤ st.val := by
          have := ‹¬required.len > st›; rw [gt_iff_lt, UScalar.lt_equiv] at this; omega
        have he0 : ((bytesOf required).extract st.val required.len.val).toList = [] := by
          rw [extract_toList_eq_nil required (by rw [Slice.len_val])]; omega
        have hge : ¬ required.len.val < required.length := by rw [Slice.len_val]; omega
        rw [← hinv, all_filter_cons_piece]
        simp only [hge, ↓reduceIte, he0, List.filter_nil, List.all_nil]
    simp only [bind_ok]
    have hstop : (findNul (bytesOf required) st.val).getD required.length = nul.val := by
      rw [← o_post]; rfl
    rw [hstop] at c1 c2 hinv
    have hnl : nul.val < required.length := by
      have := (findNul_some o_post.symm).2.1
      rwa [bytesOf_size] at this
    have hm1 : nul.val + 1 ≤ Usize.max := by
      have := required.property; have h' : nul.val < required.val.length := hnl; omega
    have hm2 : pc.val + 1 ≤ Usize.max := by
      have := required.property; have h' : nul.val < required.val.length := hnl; omega
    step* -grind
    · have hgt : st.val < nul.val := by
        have := ‹nul > st›; rw [gt_iff_lt, UScalar.lt_equiv] at this; exact this
      have hlt : nul.val < required.length := by
        have := ‹¬nul ≥ required.len›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val] at this
        omega
      have hne : ¬ ((bytesOf required).extract st.val nul.val).toList = [] := by
        rw [extract_toList_eq_nil required (by omega)]; omega
      rw [all_filter_cons_piece] at hinv
      simp only [hlt, ↓reduceIte, hne] at hinv
      rw [← bytesOf_slice s_post, ← b_post, ‹b = true›, Bool.true_and] at hinv
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [start1_post]; exact hinv
    · have hgt : st.val < nul.val := by
        have := ‹nul > st›; rw [gt_iff_lt, UScalar.lt_equiv] at this; exact this
      have hne : ¬ ((bytesOf required).extract st.val nul.val).toList = [] := by
        rw [extract_toList_eq_nil required (by omega)]; omega
      have hb : b = false := by simpa using ‹¬b = true›
      rw [← hinv, all_filter_cons_piece]
      simp only [hne, ↓reduceIte]
      rw [← bytesOf_slice s_post, ← b_post, hb, Bool.false_and]
    · have hle : nul.val ≤ st.val := by
        have := ‹¬nul > st›; rw [gt_iff_lt, UScalar.lt_equiv] at this; omega
      have hlt : nul.val < required.length := by
        have := ‹¬nul ≥ required.len›; rw [ge_iff_le, UScalar.le_equiv, Slice.len_val] at this
        omega
      have he0 : ((bytesOf required).extract st.val nul.val).toList = [] := by
        rw [extract_toList_eq_nil required (by omega)]; omega
      rw [all_filter_cons_piece] at hinv
      simp only [hlt, ↓reduceIte, he0] at hinv
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [start1_post]; exact hinv
  · exact ⟨hs, hp, hW⟩

/-- `holds_required(bytes, end, required)`: whether every nonempty piece of
`required` is a piece of the bytes before the final NUL at `end`. -/
@[step] theorem holds_required_spec (bytes : Slice U8) (e : Usize) (required : Slice U8)
    (he : e.val < bytes.length) (hz : (bytesOf bytes)[e.val]? = some 0) :
    fdt.hand_over.holds_required bytes e required ⦃ b =>
      b = ((splitAtNul (bytesOf required).toList).filter (· != [])).all fun q =>
        (splitAtNul ((bytesOf bytes).toList.take e.val)).any (· == q) ⦄ := by
  unfold fdt.hand_over.holds_required
  have := holds_required_loop_spec bytes e required he hz 0#usize 0#usize (Nat.zero_le _)
    (Nat.le_refl _)
  rw [List.take_of_length_le (by rw [bytesOf_toList, List.length_map])] at this
  simpa using this

/-- `check_compatible(bytes, required)`: `checkCompatible`, the root
`compatible` against the entries that the profile requires. -/
@[step] theorem check_compatible_spec (bytes required : Slice U8) :
    fdt.hand_over.check_compatible bytes required ⦃ r =>
      Agrees (fun _ _ => True) errorOf r
        (checkCompatible (bytesOf required) (bytesOf bytes)) ⦄ := by
  unfold fdt.hand_over.check_compatible checkCompatible
  step as ⟨b, b_post⟩
  by_cases hb : b = true
  · have hl : bytes.val = [] := by
      have : bytes.length = 0 := b_post ▸ hb
      exact List.eq_nil_of_length_eq_zero this
    have : (bytesOf bytes).toList = [] := by rw [bytesOf_toList, hl]; rfl
    simp only [hb, ↓reduceIte, spec_ok, this, List.getLast?_nil]
    rfl
  have hl : bytes.length ≠ 0 := fun h => hb (b_post ▸ h)
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  step as ⟨i1, i1_post⟩
  step as ⟨i2, i2_post⟩
  have hi1 : i1.val = bytes.length - 1 := by rw [i1_post, Slice.len_val]
  have hlast : (bytesOf bytes).toList.getLast? = some (byte i2) := by
    rw [bytesOf_toList, List.getLast?_map, List.getLast?_eq_getElem?, i2_post]
    rw [List.getElem?_eq_getElem (by have h' : bytes.val.length ≠ 0 := hl; omega)]
    simp only [Option.map_some, Option.some.injEq]
    congr 2
    rw [hi1]
  rw [hlast]
  by_cases h2 : (i2 != 0#u8) = true
  · have : (some (byte i2) != some (0 : UInt8)) = true := by
      rw [bne_iff_ne, ne_eq, Option.some.injEq, byte_eq_zero_iff]
      rw [bne_iff_ne, ne_eq] at h2
      exact fun h => h2 (UScalar.eq_of_val_eq h)
    simp only [h2, ↓reduceIte, this, spec_ok]
    rfl
  have h0 : i2.val = 0 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h2; rw [h2]; rfl
  have : (some (byte i2) != some (0 : UInt8)) = false := by
    rw [bne_eq_false_iff_eq, Option.some.injEq, byte_eq_zero_iff]; exact h0
  simp only [h2, Bool.false_eq_true, ↓reduceIte, this]
  step as ⟨i4, i4_post⟩
  have hi4 : i4.val = bytes.length - 1 := by rw [i4_post, Slice.len_val]
  have he : i4.val < bytes.length := by omega
  have hz : (bytesOf bytes)[i4.val]? = some 0 := by
    rw [bytesOf_getElem?, List.getElem?_eq_getElem (by omega)]
    simp only [Option.map_some, Option.some.injEq]
    have : bytes.val[i4.val] = i2 := by rw [i2_post]; congr 1; rw [hi4, hi1]
    rw [this, byte_eq_zero_iff]; exact h0
  have hdrop : (bytesOf bytes).toList.dropLast = (bytesOf bytes).toList.take i4.val := by
    rw [List.dropLast_eq_take, bytesOf_toList, List.length_map, hi4]
  rw [hdrop]
  step with compatible_entries_spec bytes i4 he hz as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun _ entries _ hE => ?_
  step as ⟨i6, i6_post⟩
  have hi6 : i6 = i4 := UScalar.eq_of_val_eq (by rw [i6_post, Slice.len_val, hi4])
  rw [hi6]
  step with holds_required_spec bytes i4 required he hz as ⟨b1, b1_post⟩
  have hq : ((requiredEntries (bytesOf required)).all fun r =>
      entries.any fun e => String.fromUTF8? ⟨r.toArray⟩ == some e) = b1 := by
    rw [b1_post, requiredEntries]
    congr 1
    funext q
    exact compatibleEntries_any hE q
  rw [hq]
  by_cases hb1 : b1 = true
  · simp only [hb1, ↓reduceIte, Bool.not_true, Bool.false_eq_true, spec_ok]
    exact trivial
  · simp only [hb1, Bool.false_eq_true, ↓reduceIte, Bool.not_false, spec_ok]
    rfl

/-! ## The discovery of the boot memory -/

/-- `check_hand_over(tree, hand_over, dtb_address, image)`: the span of the tree
of `handOverCheck`, the checks of `Fdt.discoverBootMemory` before the memory
map, or its error. -/
@[step] theorem check_hand_over_spec (hu : Usize64) (t : fdt.Fdt) (T : Fdt) (h : FdtRepr t T)
    (handOver : fdt.HandOverProfile) (dtbAddress : U64) (image : fdt.Span) :
    fdt.hand_over.check_hand_over t handOver dtbAddress image ⦃ r =>
      Agrees SpanRepr errorOf r
        (handOverCheck T (handOverOf handOver) (word64 dtbAddress) (spanOf image)) ⦄ := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h
  unfold fdt.hand_over.check_hand_over handOverCheck
  step with fdt_total_size_spec hu t T h as ⟨i, hi⟩
  refine check_spec (by
    rw [← hi]
    simp only [handOverOf, gt_iff_lt, UScalar.lt_equiv, UInt64.lt_iff_toNat_lt, word64_toNat])
    rfl fun _ _ => ?_
  step as ⟨b, b_post⟩
  refine check_neg_spec (by
    rw [b_post, decide_eq_true_iff, bne_iff_ne, ne_eq]
    simp only [handOverOf, word64_toNat, byte_toNat]) rfl fun _ _ => ?_
  rw [findNode_slash_eq_root, except_ok_bind]
  step with first_node_spec ht as ⟨o, ho⟩
  rcases hroot : T.root with _ | R <;> rw [hroot] at ho <;> rcases o with _ | root
  · simp only [spec_ok]; rfl
  · exact ho.elim
  · exact ho.elim
  dsimp only
  step with address_cells_at_spec hu ho as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun c C hc _ => ?_
  refine check_spec (by rw [← hc]; exact (word32_bne_two c).symm) rfl fun _ _ => ?_
  step with size_cells_at_spec hu ho as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun c1 C1 hc1 _ => ?_
  refine check_spec (by rw [← hc1]; exact (word32_bne_two c1).symm) rfl fun _ _ => ?_
  step as ⟨s, s_post⟩
  have hk : bytesOf s = "compatible".toUTF8 := by rw [s_post]; exact bytes_compatible
  step with value_at_spec hu ho s "compatible" hk as ⟨o1, ho1⟩
  rcases hv : R.property "compatible" with _ | v <;> rw [hv] at ho1 <;>
    rcases o1 with _ | ⟨st, en⟩
  · simp only [spec_ok]; rfl
  · exact ho1.elim
  · exact ho1.elim
  obtain ⟨h1, h2, h3⟩ := ho1
  dsimp only at h1 h2 h3 ⊢
  step as ⟨s1, s1_post, _⟩
  have hb1 : bytesOf s1 = v := by rw [bytesOf_slice s1_post, h3]
  step with check_compatible_spec s1 handOver.compatible as ⟨r2, r2_post⟩
  rw [hb1] at r2_post
  refine try_spec r2_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
  step with span_new_spec dtbAddress i as ⟨r3, r3_post⟩
  rw [hi] at r3_post
  refine try_spec r3_post (fun e => from_residual_spec e) fun val2 D hD _ => ?_
  refine check_spec (by rw [spanOf_size, word64_eq_zero_iff]) rfl fun _ _ => ?_
  step with span_end_spec image as ⟨r4, r4_post⟩
  refine try_spec r4_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
  step with touches_spec image val2 as ⟨b1, b1_post⟩
  rw [hD] at b1_post
  refine check_spec (by rw [b1_post]) rfl fun _ _ => ?_
  simp only [spec_ok]
  exact hD

/-- `Fdt::discover_boot_memory(hand_over, dtb_address, image)`: the statement
`FdtDiscoverBootMemory`. -/
@[step] theorem fdt_discover_boot_memory_spec (hu : Usize64) (t : fdt.Fdt) (T : Fdt)
    (handOver : fdt.HandOverProfile) (dtbAddress : U64) (image : fdt.Span) (h : FdtRepr t T) :
    fdt.hand_over.Fdt.discover_boot_memory t handOver dtbAddress image ⦃ r =>
      Agrees BootMemoryRepr errorOf r
        (T.discoverBootMemory (handOverOf handOver) (word64 dtbAddress) (spanOf image)) ⦄ := by
  unfold fdt.hand_over.Fdt.discover_boot_memory
  rw [discoverBootMemory_eq]
  step with check_hand_over_spec hu t T h handOver dtbAddress image as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun val D hD _ => ?_
  step with fdt_discover_memory_spec hu t T h as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun mm M hM _ => ?_
  step with check_storage_spec hM val image as ⟨r2, r2_post⟩
  rw [show spanOf val = D from hD] at r2_post
  refine try_spec r2_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
  step with memory_map_ram_spec hM as ⟨s, s_post⟩
  step with ram_bytes_spec s as ⟨r3, r3_post⟩
  rw [s_post] at r3_post
  refine try_spec r3_post (fun e => from_residual_spec e) fun n N hn _ => ?_
  simp only [spec_ok]
  refine ⟨hM, (show spanOf val = D from hD).symm, rfl, ?_, rfl, rfl⟩
  rw [word64, hn]

end Krepi.Proofs.Fdt.Refinement
