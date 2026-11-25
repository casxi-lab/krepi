module

public import Krepi.Proofs.Fdt.Refinement.SpanLemmas
public import Krepi.Proofs.Fdt.Refinement.TranslateSpecLemmas

/-!
# Device tree: refinement of the regions and address maps

The triples of the generated functions of `fdt::translation`, each a
`@[step]` lemma, so that the proof of a caller steps over the call with the
triple of the callee and a mutant of a callee fails the proof of the callee
alone:

- the width of an address: `check_width_spec` (`checkWidth`, read with
  `checkWidth_spanOf`);
- the regions: `reg_stride_spec`, `reg_entry_spec` (`regEntry` of the entry
  at an offset), `check_reg_entries_spec` and `check_reg_spec` (the checks of
  `Reg.new`), and `reg_step_spec`; `reg_next_end` and `reg_next_entry`, the
  two outcomes of `Reg::next`; `reg_stands` (a `Reg` stands for the entries
  from its cursor) and `reg_new_spec`, the statement `RegNew` without its
  premise;
- the address maps: `windowOf` (a window of the code as one of the
  specification), `stride_spec`, `window_spec`, `check_windows_loop_spec`,
  `check_windows_spec`, `check_map_spec` (the checks of `AddressMap.new`),
  and `address_map_new_spec` and `address_map_kind_spec`, the statements
  `AddressMapNew` and `AddressMapKind` without their premise;
- the translation: `through_windows_loop_spec`, `through_windows_spec`
  (`throughWindows` of the windows of a checked value), `translate_map_spec`
  (`AddressMap.translate` of the map of a checked value), and
  `address_map_to_parent_spec` and `address_map_to_child_spec`, the
  statements `AddressMapToParent` and `AddressMapToChild` without their
  premise.

The loops are proved with `loop.spec_decr_nat`: the entries or windows from
the offset of an iteration on, the `chunks` of the bytes from that offset,
give the answer from the start.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The width of an address -/

/-- `checkWidth` of a span of the code, at the exact end. -/
theorem checkWidth_spanOf (s : fdt.Span) (c : U32) :
    checkWidth (spanOf s) (word32 c) =
      if s.start.val + s.size.val < 2 ^ 64 then
        if c.val = 1 ∧ (2 ^ 32 ≤ s.start.val ∨ 2 ^ 32 < s.start.val + s.size.val) then
          .error .overflow
        else .ok ()
      else .error .overflow := by
  simp only [checkWidth, spanOf_valid_iff, spanOf_endNat, spanOf_start, word64_toNat, ite_not,
    word32_beq_iff, UInt32.reduceToNat, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]

/-- `check_width(span, cells)`: `checkWidth`. -/
@[step] theorem check_width_spec (span : fdt.Span) (cells : U32) :
    fdt.translation.check_width span cells ⦃ r =>
      Agrees (· = ·) errorOf r (checkWidth (spanOf span) (word32 cells)) ⦄ := by
  unfold fdt.translation.check_width
  step as ⟨o, o_post⟩
  cases o with
  | none =>
    have hv : ¬ span.start.val + span.size.val < 2 ^ 64 := by
      have := u64_max_eq; simp only at o_post; omega
    simp only [checkWidth_spanOf, hv, ↓reduceIte]
    exact spec_of_eq rfl rfl
  | some e =>
    simp only at o_post
    have hv : span.start.val + span.size.val < 2 ^ 64 := by
      have := o_post.1; have := u64_max_eq; omega
    simp only [checkWidth_spanOf, hv, ↓reduceIte]
    by_cases h1 : cells.val = 1
    · have h1' : cells = 1#u32 := UScalar.eq_of_val_eq h1
      by_cases h2 : 2 ^ 32 ≤ span.start.val
      · have h2' : span.start > 4294967295#u64 := by rw [gt_iff_lt, UScalar.lt_equiv]; exact h2
        simp only [eq_true h1', eq_true h2', ↓reduceIte, h1, h2, true_or, and_self]
        exact spec_of_eq rfl rfl
      · have h2' : ¬ span.start > 4294967295#u64 := by rw [gt_iff_lt, UScalar.lt_equiv]; exact h2
        by_cases h3 : 2 ^ 32 < span.start.val + span.size.val
        · have h3' : e > 4294967296#u64 := by
            rw [gt_iff_lt, UScalar.lt_equiv, o_post.2.1]; exact h3
          simp only [eq_true h1', eq_false h2', eq_true h3', ↓reduceIte, h1, h3, or_true,
            and_self]
          exact spec_of_eq rfl rfl
        · have h3' : ¬ e > 4294967296#u64 := by
            rw [gt_iff_lt, UScalar.lt_equiv, o_post.2.1]; exact h3
          simp only [eq_true h1', eq_false h2', eq_false h3', ↓reduceIte, h2, h3, or_self,
            and_false]
          exact spec_of_eq rfl trivial
    · have h1' : ¬ cells = 1#u32 := fun h => h1 (by rw [h]; rfl)
      simp only [eq_false h1', ↓reduceIte, h1, false_and]
      exact spec_of_eq rfl trivial

/-! ## Regions -/

/-- `reg_stride(address_cells, size_cells)`: the bytes of one entry. -/
@[step] theorem reg_stride_spec (ac sc : U32) (h : ac.val + sc.val ≤ 4) :
    fdt.translation.reg_stride ac sc ⦃ s => s.val = (ac.val + sc.val) * 4 ⦄ := by
  unfold fdt.translation.reg_stride
  step*

/-- `reg_entry(bytes, at, address_cells, size_cells)`: `regEntry` of the
entry at `at`. -/
@[step] theorem reg_entry_spec (bytes : Slice U8) (pos : Usize) (ac sc : U32)
    (h : pos.val + (ac.val + sc.val) * 4 ≤ bytes.length) :
    fdt.translation.reg_entry bytes pos ac sc ⦃ r =>
      Agrees SpanRepr errorOf r
        (regEntry (word32 ac) (word32 sc)
          ((bytesOf bytes).extract pos.val (pos.val + (ac.val + sc.val) * 4))) ⦄ := by
  unfold fdt.translation.reg_entry
  step as ⟨i, i_post⟩
  step as ⟨i1, i1_post⟩
  step as ⟨split, split_post⟩
  step as ⟨i2, i2_post⟩
  step as ⟨i3, i3_post⟩
  step as ⟨stop, stop_post⟩
  step as ⟨s, s_post, _⟩
  have hi : i.val = ac.val := by rw [i_post, U32.cast_Usize_val_eq]
  have hi2 : i2.val = sc.val := by rw [i2_post, U32.cast_Usize_val_eq]
  rw [show pos.val + (ac.val + sc.val) * 4 = stop.val by omega,
    regEntry_extract (q := split.val) (by simp only [word32_toNat]; omega)
      (by simp only [word32_toNat]; omega) (by simp only [bytesOf_size]; omega),
    ← bytesOf_slice s_post]
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun val _ hv _ => ?_
  subst hv
  dsimp only
  step as ⟨s1, s1_post, _⟩
  rw [← bytesOf_slice s1_post]
  step as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun val1 _ hv1 _ => ?_
  subst hv1
  dsimp only
  step as ⟨r2, r2_post⟩
  refine try_spec r2_post (fun e => from_residual_spec e) fun val2 _ hv2 _ => ?_
  subst hv2
  dsimp only
  step as ⟨r3, r3_post⟩
  refine try_spec r3_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
  dsimp only
  exact spec_of_eq rfl rfl

/-- `check_reg_entries(bytes, address_cells, size_cells, stride)`: the
failure of the first entry that fails, as `mapM` of `regEntry` over the
entries. -/
@[step] theorem check_reg_entries_spec (bytes : Slice U8) (ac sc : U32) (stride : Usize)
    (hs : stride.val = (ac.val + sc.val) * 4) (h0 : 0 < stride.val)
    (hd : bytes.length % stride.val = 0) :
    fdt.translation.check_reg_entries bytes ac sc stride ⦃ r =>
      Agrees (fun _ _ => True) errorOf r
        ((chunks (bytesOf bytes) stride.val (bytes.length / stride.val) 0).mapM
          (regEntry (word32 ac) (word32 sc))) ⦄ := by
  unfold fdt.translation.check_reg_entries fdt.translation.check_reg_entries_loop
  rw [← Nat.sub_zero bytes.length]
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => bytes.length - i.val)
    (inv := fun (i : Usize) => i.val % stride.val = 0 ∧
      ∀ r : core.result.Result Unit fdt.Error,
        Agrees (fun _ _ => True) errorOf r ((chunks (bytesOf bytes) stride.val
          ((bytes.length - i.val) / stride.val) i.val).mapM (regEntry (word32 ac) (word32 sc))) →
        Agrees (fun _ _ => True) errorOf r ((chunks (bytesOf bytes) stride.val
          ((bytes.length - 0) / stride.val) 0).mapM (regEntry (word32 ac) (word32 sc))))
  · rintro i ⟨hi, hinv⟩
    unfold fdt.translation.check_reg_entries_loop.body
    step*
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have := add_stride_le hi hd hlt
      omega
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have := add_stride_le hi hd hlt
      have := bytes.property
      simp only [Slice.length] at *
      omega
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have hle := add_stride_le hi hd hlt
      have hok := agrees_ok_eq (agrees_of_branch_ok cf_post ‹_› r_post)
      rw [← hs] at hok
      refine ⟨by rw [at1_post, Nat.add_mod_right, hi], fun r hr => hinv r ?_, by omega⟩
      rw [chunks_cons h0 hle, agrees_true_mapM_cons hok, ← at1_post]
      exact hr
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have hle := add_stride_le hi hd hlt
      have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
      rw [← hs] at he
      apply hinv
      rw [chunks_cons h0 hle, mapM_cons_error he, r1_post, ← e_post]
      rfl
    · apply hinv
      rw [chunks_nil h0 (by have := slice_len_le ‹_›; omega)]
      exact trivial
  · exact ⟨Nat.zero_mod _, fun r h => h⟩

theorem u32_bne_iff {x y : U32} : (x != y) = true ↔ x.val ≠ y.val := by
  rw [bne_iff_ne, ne_eq, UScalar.eq_equiv]

theorem usize_bne_iff {x y : Usize} : (x != y) = true ↔ x.val ≠ y.val := by
  rw [bne_iff_ne, ne_eq, UScalar.eq_equiv]

theorem u32_zero_val : (0#u32 : U32).val = 0 := rfl
theorem u32_one_val : (1#u32 : U32).val = 1 := rfl
theorem u32_two_val : (2#u32 : U32).val = 2 := rfl
theorem usize_zero_val : (0#usize : Usize).val = 0 := rfl

/-- `check_reg(bytes, address_cells, size_cells)`: the checks of `Reg.new`. -/
@[step] theorem check_reg_spec (bytes : Slice U8) (ac sc : U32) :
    fdt.translation.check_reg bytes ac sc ⦃ r =>
      Agrees (fun _ _ => True) errorOf r (Reg.new (bytesOf bytes) (word32 ac) (word32 sc)) ⦄ := by
  unfold fdt.translation.check_reg
  step*
  all_goals simp only [u32_bne_iff, usize_bne_iff, ne_eq, Decidable.not_not, gt_iff_lt,
    UScalar.lt_equiv, not_lt, u32_one_val, u32_two_val, usize_zero_val] at *
  · rw [regNew_unsupported _ (by omega)]; rfl
  · rw [regNew_unsupported _ (by omega)]; rfl
  · rw [regNew_badProperty (by omega) (Or.inl (by rwa [← b_post]))]; rfl
  · rw [regNew_badProperty (by omega)
      (Or.inr (by rw [← stride_post, ← Slice.len_val, ← i1_post]; omega))]; rfl
  · have hl : ¬ bytes.length = 0 := by rwa [← b_post]
    have hm : bytes.length % ((ac.val + sc.val) * 4) = 0 := by
      rw [← stride_post, ← Slice.len_val, ← i1_post]; omega
    rw [regNew_entries (by omega) (by rintro (h | h); exact hl h; exact h hm), agrees_true_map,
      ← stride_post]
    exact r_post
  · rw [regNew_unsupported _ (by omega)]; rfl
  · rw [regNew_badProperty (by omega) (Or.inl (by rwa [← b_post]))]; rfl
  · rw [regNew_badProperty (by omega)
      (Or.inr (by rw [← stride_post, ← Slice.len_val, ← i1_post]; omega))]; rfl
  · have hl : ¬ bytes.length = 0 := by rwa [← b_post]
    have hm : bytes.length % ((ac.val + sc.val) * 4) = 0 := by
      rw [← stride_post, ← Slice.len_val, ← i1_post]; omega
    rw [regNew_entries (by omega) (by rintro (h | h); exact hl h; exact h hm), agrees_true_map,
      ← stride_post]
    exact r_post

/-- `reg_step(bytes, address_cells, size_cells, cursor)`: the entry at the
cursor and the cursor after it, when a whole entry is left and it is read;
otherwise none and the same cursor. -/
@[step] theorem reg_step_spec (bytes : Slice U8) (ac sc : U32) (cursor : Usize)
    (h1 : 0 < ac.val) (h2 : ac.val + sc.val ≤ 4) :
    fdt.translation.reg_step bytes ac sc cursor ⦃ c o =>
      if cursor.val + (ac.val + sc.val) * 4 ≤ bytes.length then
        match regEntry (word32 ac) (word32 sc)
            ((bytesOf bytes).extract cursor.val (cursor.val + (ac.val + sc.val) * 4)) with
        | .ok sp => c.val = cursor.val + (ac.val + sc.val) * 4 ∧ o.map spanOf = some sp
        | .error _ => c = cursor ∧ o = none
      else c = cursor ∧ o = none ⦄ := by
  unfold fdt.translation.reg_step
  step*
  all_goals simp only [ge_iff_le, UScalar.le_equiv, UScalar.lt_equiv, not_le, not_lt,
    Slice.len_val] at *
  · have hc : ¬ cursor.val + (ac.val + sc.val) * 4 ≤ bytes.length := by omega
    simp only [hc, ↓reduceIte]
  · have hc : ¬ cursor.val + (ac.val + sc.val) * 4 ≤ bytes.length := by omega
    simp only [hc, ↓reduceIte]
  · have hc : cursor.val + (ac.val + sc.val) * 4 ≤ bytes.length := by omega
    subst_vars
    simp only [hc, ↓reduceIte, agrees_ok_eq r_post, Option.map_some, and_true]
    omega
  · have hc : cursor.val + (ac.val + sc.val) * 4 ≤ bytes.length := by omega
    subst_vars
    simp only [hc, ↓reduceIte, agrees_err_iff.mp r_post]

/-- At a cursor where no whole entry is left, `Reg::next` gives none and stays. -/
theorem reg_next_end (g : fdt.Reg) (h1 : 0 < g.address_cells.val)
    (h2 : g.address_cells.val + g.size_cells.val ≤ 4)
    (h : ¬ g.cursor.val + (g.address_cells.val + g.size_cells.val) * 4 ≤ g.bytes.length) :
    fdt.translation.Reg.next g = .ok (none, g) := by
  unfold fdt.translation.Reg.next
  obtain ⟨⟨c, o⟩, heq, hp⟩ :=
    spec_iff.mp (reg_step_spec g.bytes g.address_cells g.size_cells g.cursor h1 h2)
  simp only [uncurry'_pair, h, ↓reduceIte] at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp only [heq, bind_ok]; rfl

/-- At a cursor where a whole entry is left and is read, `Reg::next` gives
its span and moves the cursor past it. -/
theorem reg_next_entry (g : fdt.Reg) (h1 : 0 < g.address_cells.val)
    (h2 : g.address_cells.val + g.size_cells.val ≤ 4) {sp : Span}
    (h : g.cursor.val + (g.address_cells.val + g.size_cells.val) * 4 ≤ g.bytes.length)
    (he : regEntry (word32 g.address_cells) (word32 g.size_cells)
      ((bytesOf g.bytes).extract g.cursor.val
        (g.cursor.val + (g.address_cells.val + g.size_cells.val) * 4)) = .ok sp) :
    fdt.translation.Reg.next g ⦃ o g' => ∃ a, o = some a ∧ SpanRepr a sp ∧
      g'.bytes = g.bytes ∧ g'.address_cells = g.address_cells ∧ g'.size_cells = g.size_cells ∧
      g'.cursor.val = g.cursor.val + (g.address_cells.val + g.size_cells.val) * 4 ⦄ := by
  unfold fdt.translation.Reg.next
  step as ⟨c, o, hp⟩
  simp only [h, ↓reduceIte, he] at hp
  obtain ⟨hc, ho⟩ := hp
  obtain ⟨a, rfl, ha⟩ := Option.map_eq_some_iff.mp ho
  exact ⟨a, rfl, ha, hc⟩

/-- A `Reg` whose cells are those of a checked value stands for the entries
that `regEntry` gives for the entries from its cursor. -/
theorem reg_stands (g : fdt.Reg) (l : List Span) (h1 : 0 < g.address_cells.val)
    (h2 : g.address_cells.val + g.size_cells.val ≤ 4)
    (h : (chunks (bytesOf g.bytes) ((g.address_cells.val + g.size_cells.val) * 4)
      ((g.bytes.length - g.cursor.val) / ((g.address_cells.val + g.size_cells.val) * 4))
        g.cursor.val).mapM (regEntry (word32 g.address_cells) (word32 g.size_cells)) = .ok l) :
    RegRepr g l := by
  refine stands_of_sim (fun (s : fdt.Reg) (l : List Span) => 0 < s.address_cells.val ∧
      s.address_cells.val + s.size_cells.val ≤ 4 ∧
      (chunks (bytesOf s.bytes) ((s.address_cells.val + s.size_cells.val) * 4)
        ((s.bytes.length - s.cursor.val) / ((s.address_cells.val + s.size_cells.val) * 4))
          s.cursor.val).mapM (regEntry (word32 s.address_cells) (word32 s.size_cells)) = .ok l)
    ?_ ?_ l g ⟨h1, h2, h⟩
  · rintro s ⟨h1, h2, hm⟩
    have hc : ¬ s.cursor.val + (s.address_cells.val + s.size_cells.val) * 4 ≤ s.bytes.length :=
      fun hle => by
        rw [chunks_cons (by omega) hle] at hm
        have := mapM_ok_length hm
        simp only [List.length_nil, List.length_cons] at this
        omega
    rw [reg_next_end s h1 h2 hc]
    exact spec_of_eq rfl ⟨rfl, reg_next_end s h1 h2 hc⟩
  · rintro s b l ⟨h1, h2, hm⟩
    have hle : s.cursor.val + (s.address_cells.val + s.size_cells.val) * 4 ≤ s.bytes.length := by
      apply Classical.byContradiction; intro hc
      rw [chunks_nil (by omega) (by omega)] at hm
      cases hm
    rw [chunks_cons (by omega) hle, mapM_cons_ok] at hm
    refine spec_mono (reg_next_entry s h1 h2 hle hm.1) ?_
    rintro ⟨o, s'⟩ ⟨a, ho, ha, hb, hac, hsc, hcur⟩
    refine ⟨a, ho, ha, by rw [hac]; exact h1, by rw [hac, hsc]; exact h2, ?_⟩
    rw [hb, hac, hsc, hcur]
    exact hm.2

/-- `Reg::new(bytes, address_cells, size_cells)`: a `Reg` that stands for the
entries of `Reg.new`, or its error. -/
@[step] theorem reg_new_spec (bytes : Slice U8) (ac sc : U32) :
    fdt.translation.Reg.new bytes ac sc ⦃ r =>
      Agrees (fun g R => RegRepr g R.entries) errorOf r
        (Reg.new (bytesOf bytes) (word32 ac) (word32 sc)) ⦄ := by
  unfold fdt.translation.Reg.new
  step as ⟨r, r_post⟩
  rw [← bind_pure (Reg.new (bytesOf bytes) (word32 ac) (word32 sc))]
  refine try_spec r_post (fun e => from_residual_spec e) fun _ R _ hR => ?_
  obtain ⟨hac, hsc, -, -, hm⟩ := regNew_ok hR
  refine spec_of_eq rfl (reg_stands _ _ (by dsimp only; omega) (by dsimp only; omega) ?_)
  rw [bytesOf_size] at hm
  exact hm

/-! ## Address maps -/

/-- A window of the code, a pair of child and parent spans, as a window of the
specification. -/
def windowOf (p : fdt.Span × fdt.Span) : Window := ⟨spanOf p.1, spanOf p.2⟩

/-- `stride(child_cells, parent_cells, size_cells)`: the bytes of one window. -/
@[step] theorem stride_spec (cc pc sc : U32) (h : cc.val + pc.val + sc.val ≤ 6) :
    fdt.translation.stride cc pc sc ⦃ s => s.val = (cc.val + pc.val + sc.val) * 4 ⦄ := by
  unfold fdt.translation.stride
  step*

/-- `window(bytes, at, child_cells, parent_cells, size_cells)`: `window` of the
window at `at`. -/
@[step] theorem window_spec (bytes : Slice U8) (pos : Usize) (cc pc sc : U32)
    (h : pos.val + (cc.val + pc.val + sc.val) * 4 ≤ bytes.length) :
    fdt.translation.window bytes pos cc pc sc ⦃ r =>
      Agrees (fun p w => windowOf p = w) errorOf r
        (window (word32 cc) (word32 pc) (word32 sc)
          ((bytesOf bytes).extract pos.val (pos.val + (cc.val + pc.val + sc.val) * 4))) ⦄ := by
  unfold fdt.translation.window
  step as ⟨i, i_post⟩
  step as ⟨i1, i1_post⟩
  step as ⟨child_end, child_end_post⟩
  step as ⟨i2, i2_post⟩
  step as ⟨i3, i3_post⟩
  step as ⟨parent_end, parent_end_post⟩
  step as ⟨i4, i4_post⟩
  step as ⟨i5, i5_post⟩
  step as ⟨stop, stop_post⟩
  step as ⟨s, s_post, _⟩
  have hi : i.val = cc.val := by rw [i_post, U32.cast_Usize_val_eq]
  have hi2 : i2.val = pc.val := by rw [i2_post, U32.cast_Usize_val_eq]
  have hi4 : i4.val = sc.val := by rw [i4_post, U32.cast_Usize_val_eq]
  rw [show pos.val + (cc.val + pc.val + sc.val) * 4 = stop.val by omega,
    window_extract (q := child_end.val) (r := parent_end.val)
      (by simp only [word32_toNat]; omega) (by simp only [word32_toNat]; omega)
      (by simp only [word32_toNat]; omega) (by simp only [bytesOf_size]; omega),
    ← bytesOf_slice s_post]
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun val _ hv _ => ?_
  subst hv
  dsimp only
  step as ⟨s1, s1_post, _⟩
  rw [← bytesOf_slice s1_post]
  step as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun val1 _ hv1 _ => ?_
  subst hv1
  dsimp only
  step as ⟨s2, s2_post, _⟩
  rw [← bytesOf_slice s2_post]
  step as ⟨r2, r2_post⟩
  refine try_spec r2_post (fun e => from_residual_spec e) fun val2 _ hv2 _ => ?_
  subst hv2
  dsimp only
  by_cases hz : val2 = 0#u64
  · have hz' : word64 val2 = 0 := by rw [word64_eq_iff, u64_eq_zero_iff.mp hz]; rfl
    simp only [eq_true hz, eq_true hz', ↓reduceIte]
    exact spec_of_eq rfl rfl
  · have hz' : ¬ word64 val2 = 0 := by
      rw [word64_eq_iff]; exact fun h => hz (u64_eq_zero_iff.mpr h)
    simp only [eq_false hz, eq_false hz', ↓reduceIte]
    step as ⟨r3, r3_post⟩
    refine try_spec r3_post (fun e => from_residual_spec e) fun val3 _ hv3 _ => ?_
    subst hv3
    dsimp only
    step as ⟨r4, r4_post⟩
    refine try_spec r4_post (fun e => from_residual_spec e) fun val4 _ hv4 _ => ?_
    subst hv4
    dsimp only
    step as ⟨r5, r5_post⟩
    refine try_spec r5_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
    dsimp only
    step as ⟨r6, r6_post⟩
    refine try_spec r6_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
    dsimp only
    exact spec_of_eq rfl rfl

/-- The loop of `check_windows`: the failure of the first window that fails,
as `mapM` of `window` over the windows. -/
@[step] theorem check_windows_loop_spec (bytes : Slice U8) (cc pc sc : U32) (stride : Usize)
    (hs : stride.val = (cc.val + pc.val + sc.val) * 4) (h0 : 0 < stride.val)
    (hd : bytes.length % stride.val = 0) :
    fdt.translation.check_windows_loop bytes cc pc sc stride 0#usize ⦃ r =>
      Agrees (fun _ _ => True) errorOf r
        ((chunks (bytesOf bytes) stride.val (bytes.length / stride.val) 0).mapM
          (window (word32 cc) (word32 pc) (word32 sc))) ⦄ := by
  unfold fdt.translation.check_windows_loop
  rw [← Nat.sub_zero bytes.length]
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => bytes.length - i.val)
    (inv := fun (i : Usize) => i.val % stride.val = 0 ∧
      ∀ r : core.result.Result Unit fdt.Error,
        Agrees (fun _ _ => True) errorOf r ((chunks (bytesOf bytes) stride.val
          ((bytes.length - i.val) / stride.val) i.val).mapM
            (window (word32 cc) (word32 pc) (word32 sc))) →
        Agrees (fun _ _ => True) errorOf r ((chunks (bytesOf bytes) stride.val
          ((bytes.length - 0) / stride.val) 0).mapM (window (word32 cc) (word32 pc) (word32 sc))))
  · rintro i ⟨hi, hinv⟩
    unfold fdt.translation.check_windows_loop.body
    step*
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have := add_stride_le hi hd hlt
      omega
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have := add_stride_le hi hd hlt
      have := bytes.property
      simp only [Slice.length] at *
      omega
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have hle := add_stride_le hi hd hlt
      have hok := agrees_ok_eq (agrees_of_branch_ok cf_post ‹_› r_post)
      rw [← hs] at hok
      refine ⟨by rw [at1_post, Nat.add_mod_right, hi], fun r hr => hinv r ?_, by omega⟩
      rw [chunks_cons h0 hle, agrees_true_mapM_cons hok, ← at1_post]
      exact hr
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have hle := add_stride_le hi hd hlt
      have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
      rw [← hs] at he
      apply hinv
      rw [chunks_cons h0 hle, mapM_cons_error he, r1_post, ← e_post]
      rfl
    · apply hinv
      rw [chunks_nil h0 (by have := slice_len_le ‹_›; omega)]
      exact trivial
  · exact ⟨Nat.zero_mod _, fun r h => h⟩

/-- `check_windows(bytes, child_cells, parent_cells, size_cells)`: the
failure of the first window that fails. -/
@[step] theorem check_windows_spec (bytes : Slice U8) (cc pc sc : U32)
    (h1 : 0 < cc.val) (h2 : cc.val + pc.val + sc.val ≤ 6)
    (hd : bytes.length % ((cc.val + pc.val + sc.val) * 4) = 0) :
    fdt.translation.check_windows bytes cc pc sc ⦃ r =>
      Agrees (fun _ _ => True) errorOf r
        ((chunks (bytesOf bytes) ((cc.val + pc.val + sc.val) * 4)
          (bytes.length / ((cc.val + pc.val + sc.val) * 4)) 0).mapM
            (window (word32 cc) (word32 pc) (word32 sc))) ⦄ := by
  unfold fdt.translation.check_windows
  step as ⟨stride, stride_post⟩
  rw [← stride_post]
  exact check_windows_loop_spec bytes cc pc sc stride stride_post (by omega) (by rwa [stride_post])

/-- `check_map(bytes, present, child_cells, parent_cells, size_cells)`: the
checks of `AddressMap.new`. -/
@[step] theorem check_map_spec (bytes : Slice U8) (present : Bool) (cc pc sc : U32) :
    fdt.translation.check_map bytes present cc pc sc ⦃ r =>
      Agrees (fun _ _ => True) errorOf r
        (AddressMap.new (if present then some (bytesOf bytes) else none) (word32 cc) (word32 pc)
          (word32 sc)) ⦄ := by
  unfold fdt.translation.check_map
  step*
  all_goals simp only [u32_bne_iff, usize_bne_iff, ne_eq, Decidable.not_not, gt_iff_lt,
    UScalar.lt_equiv, UScalar.eq_equiv, not_lt, u32_one_val, u32_two_val, u32_zero_val,
    usize_zero_val] at *
  · rw [addressMapNew_unsupported _ (by omega)]; rfl
  · rw [addressMapNew_unsupported _ (by omega)]; rfl
  · rw [addressMapNew_unsupported _ (by omega)]; rfl
  · rw [addressMapNew_empty (by omega) (by rw [bytesOf_size]; rwa [← b_post])]; trivial
  · rw [addressMapNew_badProperty (by rw [u32_zero_val]; omega)
      (by rwa [bytesOf_size, ne_eq, ← b_post]) (Or.inl rfl)]; rfl
  · rw [addressMapNew_badProperty (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (Or.inr (by rwa [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]))]; rfl
  · rw [addressMapNew_windows (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (by rw [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]; omega), agrees_true_map,
      agrees_true_map, bytesOf_size]
    exact r_post
  · rw [addressMapNew_none (by omega)]; trivial
  · rw [addressMapNew_unsupported _ (by omega)]; rfl
  · rw [addressMapNew_empty (by omega) (by rw [bytesOf_size]; rwa [← b_post])]; trivial
  · rw [addressMapNew_badProperty (by rw [u32_zero_val]; omega)
      (by rwa [bytesOf_size, ne_eq, ← b_post]) (Or.inl rfl)]; rfl
  · rw [addressMapNew_badProperty (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (Or.inr (by rwa [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]))]; rfl
  · rw [addressMapNew_windows (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (by rw [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]; omega), agrees_true_map,
      agrees_true_map, bytesOf_size]
    exact r_post
  · rw [addressMapNew_none (by omega)]; trivial
  · rw [addressMapNew_unsupported _ (by omega)]; rfl
  · rw [addressMapNew_unsupported _ (by omega)]; rfl
  · rw [addressMapNew_empty (by omega) (by rw [bytesOf_size]; rwa [← b_post])]; trivial
  · rw [addressMapNew_badProperty (by rw [u32_zero_val]; omega)
      (by rwa [bytesOf_size, ne_eq, ← b_post]) (Or.inl rfl)]; rfl
  · rw [addressMapNew_badProperty (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (Or.inr (by rwa [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]))]; rfl
  · rw [addressMapNew_windows (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (by rw [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]; omega), agrees_true_map,
      agrees_true_map, bytesOf_size]
    exact r_post
  · rw [addressMapNew_none (by omega)]; trivial
  · rw [addressMapNew_unsupported _ (by omega)]; rfl
  · rw [addressMapNew_empty (by omega) (by rw [bytesOf_size]; rwa [← b_post])]; trivial
  · rw [addressMapNew_badProperty (by rw [u32_zero_val]; omega)
      (by rwa [bytesOf_size, ne_eq, ← b_post]) (Or.inl rfl)]; rfl
  · rw [addressMapNew_badProperty (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (Or.inr (by rwa [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]))]; rfl
  · rw [addressMapNew_windows (by omega) (by rwa [bytesOf_size, ne_eq, ← b_post])
      (by rw [bytesOf_size, ← i1_post, ← Slice.len_val, ← i2_post]; omega), agrees_true_map,
      agrees_true_map, bytesOf_size]
    exact r_post
  · rw [addressMapNew_none (by omega)]; trivial

/-- `AddressMap::new(bytes, child_cells, parent_cells, size_cells)`: an
address map that stands for that of `AddressMap.new`, or its error. -/
@[step] theorem address_map_new_spec (bytes : Option (Slice U8)) (cc pc sc : U32) :
    fdt.translation.AddressMap.new bytes cc pc sc ⦃ r =>
      Agrees AddressMapRepr errorOf r
        (AddressMap.new (bytes.map bytesOf) (word32 cc) (word32 pc) (word32 sc)) ⦄ := by
  unfold fdt.translation.AddressMap.new
  cases bytes with
  | none =>
    step as ⟨r, r_post⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at r_post
    rw [Option.map_none, ← bind_pure (AddressMap.new none (word32 cc) (word32 pc) (word32 sc))]
    refine try_spec r_post (fun e => from_residual_spec e) fun _ M _ hM => ?_
    exact spec_of_eq rfl hM
  | some value =>
    step as ⟨r, r_post⟩
    simp only [↓reduceIte] at r_post
    rw [Option.map_some,
      ← bind_pure (AddressMap.new (some (bytesOf value)) (word32 cc) (word32 pc) (word32 sc))]
    refine try_spec r_post (fun e => from_residual_spec e) fun _ M _ hM => ?_
    exact spec_of_eq rfl hM

/-- `AddressMap::kind()`: the kind of `AddressMap.kind`. -/
@[step] theorem address_map_kind_spec (m : fdt.AddressMap) (M : AddressMap)
    (h : AddressMapRepr m M) :
    fdt.translation.AddressMap.kind m ⦃ k => kindOf k = M.kind ⦄ := by
  rw [addressMapNew_kind h]
  unfold fdt.translation.AddressMap.kind
  step*
  · have hl : m.bytes.length = 0 := by rwa [← b_post]
    simp only [bytesOf_size, hl, ↓reduceIte]; rfl
  · have hl : ¬ m.bytes.length = 0 := by rwa [← b_post]
    simp only [bytesOf_size, hl, ↓reduceIte]; rfl
  · rfl

/-- The loop of `through_windows`: from the window at `at` on, with the span
`found` that the windows before it gave and `seen` whether there was one,
the translation of `throughWindows` through the windows that are left. -/
theorem through_windows_loop_spec (bytes : Slice U8) (cc pc sc : U32) (request : fdt.Span)
    (reverse : Bool) (stride : Usize) (found : Option fdt.Span) (seen : Bool) (pos : Usize)
    (hs : stride.val = (cc.val + pc.val + sc.val) * 4) (h0 : 0 < stride.val)
    (hd : bytes.length % stride.val = 0) (hp : pos.val % stride.val = 0)
    (hseen : seen = found.isSome) {rest : List Window}
    (hw : (chunks (bytesOf bytes) stride.val ((bytes.length - pos.val) / stride.val)
      pos.val).mapM (window (word32 cc) (word32 pc) (word32 sc)) = .ok rest) :
    fdt.translation.through_windows_loop bytes cc pc sc request reverse stride found seen pos ⦃ r =>
      Agrees SpanRepr errorOf r (throughWindows (spanOf request)
        (fun w => if reverse then w.parent else w.child)
        (fun w => if reverse then w.child else w.parent) rest (found.map spanOf)) ⦄ := by
  unfold fdt.translation.through_windows_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Option fdt.Span × Bool × Usize) => bytes.length - x.2.2.val)
    (inv := fun (x : Option fdt.Span × Bool × Usize) => x.2.2.val % stride.val = 0 ∧
      x.2.1 = x.1.isSome ∧ ∃ rest', (chunks (bytesOf bytes) stride.val
        ((bytes.length - x.2.2.val) / stride.val) x.2.2.val).mapM
          (window (word32 cc) (word32 pc) (word32 sc)) = .ok rest' ∧
        throughWindows (spanOf request) (fun w => if reverse then w.parent else w.child)
          (fun w => if reverse then w.child else w.parent) rest' (x.1.map spanOf) =
        throughWindows (spanOf request) (fun w => if reverse then w.parent else w.child)
          (fun w => if reverse then w.child else w.parent) rest (found.map spanOf))
  · rintro ⟨found', seen', i⟩ ⟨hi, hseen', rest', hw', heq⟩
    dsimp only at hi hseen' hw' heq
    unfold fdt.translation.through_windows_loop.body
    step*
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have := add_stride_le hi hd hlt
      omega
    · have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have hle := add_stride_le hi hd hlt
      rw [chunks_cons h0 hle] at hw'
      obtain ⟨w, rest'', rfl, hw1, hw2⟩ := mapM_cons_eq_ok hw'
      have hok := agrees_ok_eq (agrees_of_branch_ok cf_post ‹_› r_post)
      rw [← hs, hw1] at hok
      cases hok
      obtain ⟨child, parent⟩ := val
      simp only [uncurry_apply_pair, bind_ite_ok]
      rcases hft : (if reverse = true then (parent, child) else (child, parent)) with ⟨src, dst⟩
      simp only [uncurry_apply_pair]
      have hsrc : (if reverse = true then (windowOf (child, parent)).parent
          else (windowOf (child, parent)).child) = spanOf src := by
        cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hft <;>
          obtain ⟨rfl, rfl⟩ := hft <;> rfl
      have hdst : (if reverse = true then (windowOf (child, parent)).child
          else (windowOf (child, parent)).parent) = spanOf dst := by
        cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hft <;>
          obtain ⟨rfl, rfl⟩ := hft <;> rfl
      rw [← heq, throughWindows, hsrc, hdst]
      step*
      · have hh : (spanOf src).holds (spanOf request) = true := by rwa [← b_post]
        have hf : (Option.map spanOf found').isSome = true := by
          rwa [Option.isSome_map, ← hseen']
        simp only [hh, hf, ↓reduceIte]
        rfl
      · have hh : (spanOf src).holds (spanOf request) = true := by rwa [← b_post]
        simp only [Span.holds, spanOf_start, spanOf_endNat, word64_toNat, Bool.and_eq_true,
          decide_eq_true_eq] at hh
        exact hh.1
      · have hh : (spanOf src).holds (spanOf request) = true := by rwa [← b_post]
        have hf : ¬ (Option.map spanOf found').isSome = true := by
          rwa [Option.isSome_map, ← hseen']
        subst ‹o = none›
        simp only [] at o_post
        have hov : ¬ dst.start.val + (request.start.val - src.start.val) < 2 ^ 64 := by
          have := u64_max_eq; omega
        simp only [hh, hf, ↓reduceIte, checkedAdd, spanOf_start, word64_toNat, hov]
        rfl
      · have hh : (spanOf src).holds (spanOf request) = true := by rwa [← b_post]
        have hf : ¬ (Option.map spanOf found').isSome = true := by
          rwa [Option.isSome_map, ← hseen']
        subst ‹o = some start›
        simp only [] at o_post
        have hstart : start.val = dst.start.val + (request.start.val - src.start.val) := by
          rw [o_post.2.1, i1_post]
        have hsn := agrees_ok_eq (agrees_of_branch_ok cf1_post ‹_› r1_post)
        refine ⟨by rw [at1_post, Nat.add_mod_right, hi], rfl,
          ⟨rest'', by rw [at1_post]; exact hw2, ?_⟩, by omega⟩
        simp only [hh, hf, ↓reduceIte, checkedAdd, spanOf_start, spanOf_size, word64_toNat,
          ← hstart, u64_lt start, except_ok_bind]
        rw [show UInt64.ofNat start.val = word64 start from rfl, hsn]
        rfl
      · have hh : (spanOf src).holds (spanOf request) = true := by rwa [← b_post]
        have hf : ¬ (Option.map spanOf found').isSome = true := by
          rwa [Option.isSome_map, ← hseen']
        subst ‹o = some start›
        simp only [] at o_post
        have hstart : start.val = dst.start.val + (request.start.val - src.start.val) := by
          rw [o_post.2.1, i1_post]
        have he := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
        simp only [hh, hf, ↓reduceIte, checkedAdd, spanOf_start, spanOf_size, word64_toNat,
          ← hstart, u64_lt start, except_ok_bind]
        rw [show UInt64.ofNat start.val = word64 start from rfl, he, r2_post, ← e_post]
        rfl
      · have hh : ¬ (spanOf src).holds (spanOf request) = true := by rwa [← b_post]
        have ho : (spanOf src).overlaps (spanOf request) = true := by rwa [← b1_post]
        simp only [hh, ho, ↓reduceIte, Bool.false_eq_true]
        rfl
      · have hh : ¬ (spanOf src).holds (spanOf request) = true := by rwa [← b_post]
        have ho : ¬ (spanOf src).overlaps (spanOf request) = true := by rwa [← b1_post]
        refine ⟨by rw [at1_post, Nat.add_mod_right, hi], hseen',
          ⟨rest'', by rw [at1_post]; exact hw2, ?_⟩, by omega⟩
        simp only [hh, ho, ↓reduceIte, Bool.false_eq_true]
    · exfalso
      have hlt : i.val < bytes.length := slice_lt_len ‹_›
      have hle := add_stride_le hi hd hlt
      rw [chunks_cons h0 hle] at hw'
      obtain ⟨w, rest'', -, hw1, -⟩ := mapM_cons_eq_ok hw'
      have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
      rw [← hs, hw1] at he
      cases he
    · rw [chunks_nil h0 (by have := slice_len_le ‹_›; omega)] at hw'
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hw'
      subst hw' ‹found' = none›
      rw [← heq]
      rfl
    · rw [chunks_nil h0 (by have := slice_len_le ‹_›; omega)] at hw'
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hw'
      subst hw' ‹found' = some span›
      rw [← heq]
      rfl
  · exact ⟨hp, hseen, rest, hw, rfl⟩

/-- `through_windows(bytes, child_cells, parent_cells, size_cells, request,
reverse)`: `throughWindows` of the windows of a value that `check_map`
accepted, from the child's side to the parent's or, reversed, back. -/
@[step] theorem through_windows_spec (bytes : Slice U8) (cc pc sc : U32) (request : fdt.Span)
    (reverse : Bool) (h1 : 0 < cc.val) (h2 : cc.val + pc.val + sc.val ≤ 6)
    (hd : bytes.length % ((cc.val + pc.val + sc.val) * 4) = 0) {ws : List Window}
    (hw : (chunks (bytesOf bytes) ((cc.val + pc.val + sc.val) * 4)
      (bytes.length / ((cc.val + pc.val + sc.val) * 4)) 0).mapM
        (window (word32 cc) (word32 pc) (word32 sc)) = .ok ws) :
    fdt.translation.through_windows bytes cc pc sc request reverse ⦃ r =>
      Agrees SpanRepr errorOf r (throughWindows (spanOf request)
        (fun w => if reverse then w.parent else w.child)
        (fun w => if reverse then w.child else w.parent) ws none) ⦄ := by
  unfold fdt.translation.through_windows
  step as ⟨stride, stride_post⟩
  exact through_windows_loop_spec bytes cc pc sc request reverse stride none false 0#usize
    stride_post (by omega) (by rwa [stride_post]) (Nat.zero_mod _) rfl
    (by rw [stride_post]; exact hw)

/-- `translate_map(bytes, present, child_cells, parent_cells, size_cells,
request, reverse)`: `AddressMap.translate` of the map that `AddressMap.new`
gives for the value and the cells. -/
@[step] theorem translate_map_spec (bytes : Slice U8) (present : Bool) (cc pc sc : U32)
    (request : fdt.Span) (reverse : Bool) {M : AddressMap}
    (hM : AddressMap.new (if present then some (bytesOf bytes) else none) (word32 cc)
      (word32 pc) (word32 sc) = .ok M) :
    fdt.translation.translate_map bytes present cc pc sc request reverse ⦃ r =>
      Agrees SpanRepr errorOf r (M.translate (spanOf request) reverse) ⦄ := by
  obtain ⟨hc, hp, hsc, hmc, hmp, -, hw⟩ := addressMapNew_ok hM
  rw [translate_eq, hmc, hmp]
  unfold fdt.translation.translate_map
  by_cases hz : request.size = 0#u64
  · have hz' : (spanOf request).size = 0 := by
      rw [spanOf_size, word64_eq_iff, u64_eq_zero_iff.mp hz]; rfl
    simp only [eq_true hz, eq_true hz', ↓reduceIte]
    exact spec_of_eq rfl rfl
  · have hz' : ¬ (spanOf request).size = 0 := by
      rw [spanOf_size, word64_eq_iff]; exact fun h => hz (u64_eq_zero_iff.mpr h)
    simp only [eq_false hz, eq_false hz', ↓reduceIte, bind_ite_ok]
    rcases hcells : (if reverse = true then (pc, cc) else (cc, pc)) with ⟨scells, tcells⟩
    simp only [uncurry_apply_pair]
    have hs' : (if reverse = true then word32 pc else word32 cc) = word32 scells := by
      cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hcells <;>
        obtain ⟨rfl, rfl⟩ := hcells <;> rfl
    have ht' : (if reverse = true then word32 cc else word32 pc) = word32 tcells := by
      cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hcells <;>
        obtain ⟨rfl, rfl⟩ := hcells <;> rfl
    rw [hs', ht']
    step as ⟨r, r_post⟩
    refine try_spec r_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
    dsimp only
    cases present with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
      rw [hw]
      exact spec_of_eq rfl rfl
    | true =>
      simp only [↓reduceIte] at hw ⊢
      step as ⟨b, b_post⟩
      by_cases hb : b = true
      · have hl : (bytesOf bytes).size = 0 := by rw [bytesOf_size, ← b_post]; exact hb
        simp only [hl, ↓reduceIte] at hw
        rw [hw]
        simp only [hb, ↓reduceIte]
        step as ⟨r1, r1_post⟩
        refine try_spec r1_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
        exact spec_of_eq rfl rfl
      · have hl : ¬ (bytesOf bytes).size = 0 := by rw [bytesOf_size, ← b_post]; exact hb
        simp only [hl, ↓reduceIte] at hw
        obtain ⟨-, hd, ws, hm, hws⟩ := hw
        have hne := mapM_chunks_ne_nil (by omega) hl hd hm
        rw [bytesOf_size] at hm hd
        rw [hws]
        obtain ⟨w, ws', rfl⟩ := List.exists_cons_of_ne_nil hne
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact through_windows_spec bytes cc pc sc request reverse (by omega) (by omega) hd hm

/-- `AddressMap::to_parent(span)`: the span of `AddressMap.toParent`, or its
error. -/
@[step] theorem address_map_to_parent_spec (m : fdt.AddressMap) (M : AddressMap)
    (span : fdt.Span) (h : AddressMapRepr m M) :
    fdt.translation.AddressMap.to_parent m span ⦃ r =>
      Agrees SpanRepr errorOf r (M.toParent (spanOf span)) ⦄ := by
  unfold fdt.translation.AddressMap.to_parent AddressMap.toParent
  exact translate_map_spec _ _ _ _ _ _ _ h

/-- `AddressMap::to_child(span)`: the span of `AddressMap.toChild`, or its
error. -/
@[step] theorem address_map_to_child_spec (m : fdt.AddressMap) (M : AddressMap)
    (span : fdt.Span) (h : AddressMapRepr m M) :
    fdt.translation.AddressMap.to_child m span ⦃ r =>
      Agrees SpanRepr errorOf r (M.toChild (spanOf span)) ⦄ := by
  unfold fdt.translation.AddressMap.to_child AddressMap.toChild
  exact translate_map_spec _ _ _ _ _ _ _ h

end Krepi.Proofs.Fdt.Refinement
