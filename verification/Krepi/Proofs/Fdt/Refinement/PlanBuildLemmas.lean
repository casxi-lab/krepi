module

public import Krepi.Proofs.Fdt.Refinement.PlanQueryLemmas
public import Krepi.Proofs.Fdt.Refinement.PlanBuildSpecLemmas
public import Krepi.Proofs.Fdt.Refinement.TranslateSpecLemmas

/-!
# Device tree: refinement of the construction of a boot memory map

The triples of the generated functions that build a boot memory map, each a
`@[step]` lemma where a caller steps over it, so that the proof of a caller
uses the triple of the callee and a mutant of a callee fails the proof of the
callee alone:

- spans and pages: `check_span_spec` (`checkPlanSpan`) and `pages_of_spec`
  (`pagesOf`, the `&&&` with the page mask read by `and_page_mask`);
- the banks: `add_banks_spec` (the fold of `addBank`), the insertion sort
  `insert_bank_loop_spec`, `insert_bank_spec` and `sort_banks_spec` (the
  first banks sorted by their start, which `map_eq_sortByStart` of
  `Krepi.Proofs.Fdt.Refinement.PlanBuildSpecLemmas` turns into
  `sortByStart`), and `admit_banks_loop_spec` and `admit_banks_spec` (the
  fold of `admitBank`);
- boot storage and firmware: `add_boot_spec` and `add_firmware_spec` (the
  folds of `addBoot` and `addFirmware`);
- the entries: `build_spec` (`MemoryPlan.allRam` of the first `count` spans
  of boot storage), `check_window_spec` (`windowCheck`),
  `manage_window_spec`, `all_ram_spec` and `new_spec`, the statements
  `MemoryPlanAllRam` and `MemoryPlanNew` without their premise `Usize64`,
  and `from_boot_memory_loop_spec` and `from_boot_memory_spec`, the
  statement `MemoryPlanFromBootMemory` without its premises.

Each loop is `loop.spec_decr_nat` with the invariant that the fold of the
specification from the position of the loop, after what the code has filled
in so far, is the fold of the whole list.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Spans and pages -/

/-- `check_span(span)`: `checkPlanSpan`. -/
@[step] theorem check_span_spec (s : fdt.Span) :
    fdt.plan.check_span s ⦃ r =>
      Agrees (fun _ _ => True) planErrorOf r (checkPlanSpan (spanOf s)) ⦄ := by
  unfold fdt.plan.check_span
  by_cases h0 : s.size = 0#u64
  · have : (spanOf s).size = 0 := by simp only [spanOf_size, word64_eq_iff, h0]; rfl
    simp only [h0, ↓reduceIte, spec_ok, checkPlanSpan, this]
    rfl
  · have : ¬ (spanOf s).size = 0 := by
      simp only [spanOf_size, word64_eq_iff]
      intro h; exact h0 (u64_eq_zero_iff.2 (by simpa using h))
    simp only [h0, ↓reduceIte, checkPlanSpan, this]
    step as ⟨b, hb⟩
    subst hb
    by_cases hv : (spanOf s).Valid
    · simp [hv]
    · simp [hv]; rfl

/-- The mask of a page applied to a word: its rounding down to a page. -/
theorem and_page_mask (x m : U64) (hm : m.val = 4095) : (x &&& ~~~m).val = x.val / 4096 * 4096 := by
  rw [UScalar.val_and]
  have hn : (~~~m).val = 2 ^ 64 - 1 - (2 ^ 12 - 1) := by
    show (~~~m.bv).toNat = _
    rw [BitVec.toNat_not]; show 2 ^ 64 - 1 - m.val = _; omega
  rw [hn]
  exact land_mask (by omega) (u64_lt x)

/-- `pages_of(span)`: `pagesOf`, the pages of the span or its error. -/
@[step] theorem pages_of_spec (s : fdt.Span) :
    fdt.plan.pages_of s ⦃ r => Agrees SpanRepr planErrorOf r (pagesOf (spanOf s)) ⦄ := by
  unfold fdt.plan.pages_of pagesOf
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun _ _ _ hc => ?_
  dsimp only
  have hn := checkPlanSpan_ok hc
  have hv : s.start.val + s.size.val < 2 ^ 64 := (spanOf_valid_iff s).1 hn.2
  have hp : fdt.plan.PAGE_SIZE = 4096#u64 := by unfold fdt.plan.PAGE_SIZE; rfl
  simp only [hp, MemoryPlan.PAGE_SIZE, spanOf_endNat, spanOf_start, word64_toNat]
  step as ⟨i, i_post, i_post1⟩
  step as ⟨i1, i1_post⟩
  step as ⟨start, start_post, start_post1⟩
  step as ⟨i2, i2_post⟩
  step as ⟨o, o_post⟩
  have h1 : start.val = s.start.val / 4096 * 4096 := by
    rw [start_post, i1_post, and_page_mask _ _ (by omega)]
  rcases o with _ | stop'
  · simp only at o_post ⊢
    rw [u64_max_eq] at o_post
    simp only [show 2 ^ 64 ≤ (s.start.val + s.size.val + 4096 - 1) / 4096 * 4096 by omega,
      ↓reduceIte, spec_ok]
    rfl
  simp only at o_post ⊢
  obtain ⟨ho, ho2, -⟩ := o_post
  rw [u64_max_eq] at ho
  step as ⟨i3, i3_post⟩
  step as ⟨stop, stop_post, stop_post1⟩
  have h2 : stop.val = stop'.val / 4096 * 4096 := by
    rw [stop_post, i3_post, and_page_mask _ _ (by omega)]
  have hle : start.val ≤ stop.val := by rw [h1, h2]; omega
  step as ⟨i4, i4_post, i4_post1⟩
  simp only [show ¬ 2 ^ 64 ≤ (s.start.val + s.size.val + 4096 - 1) / 4096 * 4096 by omega,
    ↓reduceIte, agrees_ok_iff]
  refine ⟨_, rfl, ?_⟩
  simp only [SpanRepr, spanOf, spanBetween, Span.mk.injEq, word64_ofNat_iff]
  constructor
  · rw [h1]; omega
  · rw [i4_post, h1, h2]; omega

/-! ## The banks -/

/-- `add_banks(plan, ram)`: the fold of `addBank` over the banks; on a success the
first banks of the map are those given, and the managed banks and the boot
storage are untouched. -/
@[step] theorem add_banks_spec (plan : fdt.MemoryPlan) (ram : Slice fdt.Span)
    (hl : ram.length ≤ 32) (hc : plan.ram_count.val = 0) :
    fdt.plan.add_banks plan ram ⦃ x =>
      Agrees (fun _ b => b = spansOf ram ∧ x.2.ram_count.val = ram.length ∧
        x.2.ram.val.take ram.length = ram.val ∧ x.2.managed_count = plan.managed_count ∧
        x.2.boot_count = plan.boot_count)
        planErrorOf x.1 ((spansOf ram).foldlM addBank []) ⦄ := by
  unfold fdt.plan.add_banks fdt.plan.add_banks_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryPlan × Usize) => ram.length - x.2.val)
    (inv := fun (x : fdt.MemoryPlan × Usize) => x.2.val ≤ ram.length ∧
      x.1.ram_count.val = x.2.val ∧ x.1.ram.val.take x.2.val = ram.val.take x.2.val ∧
      x.1.managed_count = plan.managed_count ∧ x.1.boot_count = plan.boot_count ∧
      ((spansOf ram).drop x.2.val).foldlM addBank ((spansOf ram).take x.2.val) =
        (spansOf ram).foldlM addBank [])
  · rintro ⟨p, i⟩ ⟨hi, hpc, hpt, hpm, hpb, hf⟩
    simp only at hi hpc hpt hpm hpb hf
    unfold fdt.plan.add_banks_loop.body
    step*
    · have hi' := slice_lt_len ‹i < ram.len›
      obtain ⟨u, hu, -⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
      have hL : i.val < (spansOf ram).length := by simp only [spansOf, List.length_map]; exact hi'
      have hb : (spansOf ram)[i.val] = spanOf bank := by
        simp only [spansOf, List.getElem_map, bank_post]
      have hacc : spansOf s1 = (spansOf ram).take i.val := by
        simp only [spansOf, s1_post, s_post, Array.val_to_slice, hpc, hpt, List.map_take]
      rw [← hf, foldlM_drop_step hL, hb, addBank_of_check hu, ← hacc, ← b_post,
        ‹b = true›]
      rfl
    · have hi' := slice_lt_len ‹i < ram.len›
      obtain ⟨u, hu, -⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
      have hL : i.val < (spansOf ram).length := by simp only [spansOf, List.length_map]; exact hi'
      have hb : (spansOf ram)[i.val] = spanOf bank := by
        simp only [spansOf, List.getElem_map, bank_post]
      have hacc : spansOf s1 = (spansOf ram).take i.val := by
        simp only [spansOf, s1_post, s_post, Array.val_to_slice, hpc, hpt, List.map_take]
      have h32 : p.ram_count.val < p.ram.val.length := by
        have : p.ram.val.length = 32 := p.ram.property
        omega
      refine ⟨by omega, by omega, ?_, hpm, hpb, ?_, by omega⟩
      · rw [index1_post, a_post, Array.set_val_eq, hpc, take_succ_set (hpc ▸ h32), hpt,
          List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some, bank_post]
      · rw [← hf, foldlM_drop_step hL, hb, addBank_of_check hu,
          ← hacc, ← b_post, (Bool.not_eq_true _).mp ‹¬b = true›]
        simp only [Bool.false_eq_true, ↓reduceIte, except_ok_bind]
        rw [index1_post, hacc, List.take_add_one, List.getElem?_eq_getElem hL,
          Option.toList_some, hb]
    · have hi' := slice_lt_len ‹i < ram.len›
      have hL : i.val < (spansOf ram).length := by simp only [spansOf, List.length_map]; exact hi'
      have hb : (spansOf ram)[i.val] = spanOf bank := by
        simp only [spansOf, List.getElem_map, bank_post]
      have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
      rw [← hf, foldlM_drop_step hL, hb, addBank_of_error he, except_error_bind, r1_post,
        ← e_post]
      rfl
    · have hi' := slice_len_le ‹¬i < ram.len›
      have hL : (spansOf ram).length ≤ i.val := by simp only [spansOf, List.length_map]; exact hi'
      have hie : i.val = ram.length := by omega
      rw [← hf, foldlM_drop_end hL, agrees_ok_ok]
      refine ⟨?_, by omega, ?_, hpm, hpb⟩
      · rw [hie]; exact List.take_of_length_le (by simp [spansOf])
      · rw [← hie, hpt, hie]; exact List.take_length
  · simp [hc]
/-- The loop of `insert_bank`: the item `x` moves down past the items of the
sorted list `L` above it. -/
theorem insert_bank_loop_spec (banks : Array fdt.Span 32#usize) (pos : Usize) (L C : List fdt.Span)
    (x : fdt.Span) (hb : banks.val = L.take pos.val ++ x :: (L.drop pos.val ++ C))
    (hpos : pos.val ≤ L.length) (hL : L.Pairwise (fun a b => a.start.val ≤ b.start.val))
    (hx : ∀ y ∈ L.drop pos.val, x.start.val < y.start.val) :
    fdt.plan.insert_bank_loop banks pos ⦃ r => ∃ j ≤ L.length,
      r.val = L.take j ++ x :: (L.drop j ++ C) ∧
      (∀ a ∈ L.take j, a.start.val ≤ x.start.val) ∧
      ∀ y ∈ L.drop j, x.start.val < y.start.val ⦄ := by
  unfold fdt.plan.insert_bank_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array fdt.Span 32#usize × Usize) => s.2.val)
    (inv := fun (s : Array fdt.Span 32#usize × Usize) =>
      s.1.val = L.take s.2.val ++ x :: (L.drop s.2.val ++ C) ∧ s.2.val ≤ L.length ∧
        ∀ y ∈ L.drop s.2.val, x.start.val < y.start.val)
  · rintro ⟨b, p⟩ ⟨hb, hp, hx⟩
    simp only at hb hp hx
    have htl : (L.take p.val).length = p.val := List.length_take_of_le hp
    have hlen : p.val < b.length := by
      simp only [Array.length, hb, List.length_append, List.length_cons, htl]; omega
    unfold fdt.plan.insert_bank_loop.body
    step*
    · have hp0 : 0 < p.val := (UScalar.lt_equiv _ _).1 ‹p > 0#usize›
      obtain ⟨q, hq⟩ : ∃ q, p.val = q + 1 := ⟨p.val - 1, by omega⟩
      have hj : q < L.length := by omega
      have e1 : L.take (q + 1) = L.take q ++ [L[q]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      have e2 : L.drop q = L[q] :: L.drop (q + 1) := List.drop_eq_getElem_cons hj
      rw [hq] at hb hx
      have hl1 : (L.take q).length = q := List.length_take_of_le (by omega)
      have hb' : b.val = L.take q ++ L[q] :: x :: (L.drop (q + 1) ++ C) := by
        rw [hb, e1, List.append_assoc, List.singleton_append]
      have hs : s = L[q] := by
        rw [s_post]; exact getElem_of_append_cons hb' (by omega) _
      have hs1 : s1 = x := by
        rw [s1_post]
        exact getElem_of_append_cons hb (by rw [List.length_take_of_le (by omega), hq]) _
      have hs2 : s2 = L[q] := by
        rw [s2_post]; exact getElem_of_append_cons hb' (by omega) _
      refine ⟨?_, by omega, ?_, by omega⟩
      · rw [a_post, banks1_post, Array.set_val_eq, Array.set_val_eq, hb', hq, i_post, hq, hs2, hs1,
          show q + 1 - 1 = q by omega]
        have hsw := set_swap (L.take q) (L.drop (q + 1) ++ C) x L[q]
        rw [hl1] at hsw
        rw [hsw, e2]
        rfl
      · rw [i_post, hq, show q + 1 - 1 = q by omega, e2]
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · have := ‹s.start > s1.start›
          rw [hs, hs1] at this
          simp only [gt_iff_lt, UScalar.lt_equiv] at this
          exact this
        · exact hx y hy
    · have hp0 : 0 < p.val := (UScalar.lt_equiv _ _).1 ‹p > 0#usize›
      obtain ⟨q, hq⟩ : ∃ q, p.val = q + 1 := ⟨p.val - 1, by omega⟩
      have hj : q < L.length := by omega
      have e1 : L.take (q + 1) = L.take q ++ [L[q]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      rw [hq] at hb hx
      have hb' : b.val = L.take q ++ L[q] :: x :: (L.drop (q + 1) ++ C) := by
        rw [hb, e1, List.append_assoc, List.singleton_append]
      have hl1 : (L.take q).length = q := List.length_take_of_le (by omega)
      have hs : s = L[q] := by
        rw [s_post]; exact getElem_of_append_cons hb' (by omega) _
      have hs1 : s1 = x := by
        rw [s1_post]
        exact getElem_of_append_cons hb (by rw [List.length_take_of_le (by omega), hq]) _
      refine ⟨q + 1, by omega, hb, ?_, hx⟩
      have hle : L[q].start.val ≤ x.start.val := by
        have := ‹¬s.start > s1.start›
        rw [hs, hs1] at this
        simp only [gt_iff_lt, UScalar.lt_equiv, Nat.not_lt] at this
        exact this
      intro a ha
      exact Nat.le_trans (le_of_take (fun s : fdt.Span => s.start.val) hL hj a ha) hle
    · have hp0 : p.val = 0 := by
        have := mt (UScalar.lt_equiv 0#usize p).2 ‹¬p > 0#usize›
        have h0 : (0#usize).val = 0 := rfl
        omega
      refine ⟨0, Nat.zero_le _, ?_, by simp, ?_⟩
      · rw [← hp0]; exact hb
      · rw [← hp0]; exact hx
  · exact ⟨hb, hpos, hx⟩

/-- `insert_bank(banks, index)`: the first `index + 1` banks are those before
and sorted by their start when the first `index` were. -/
@[step] theorem insert_bank_spec (banks : Array fdt.Span 32#usize) (index : Usize)
    (hi : index.val < 32)
    (hs : (banks.val.take index.val).Pairwise (fun a b => a.start.val ≤ b.start.val)) :
    fdt.plan.insert_bank banks index ⦃ r =>
      (r.val.take (index.val + 1)).Perm (banks.val.take (index.val + 1)) ∧
      (r.val.take (index.val + 1)).Pairwise (fun a b => a.start.val ≤ b.start.val) ∧
      r.val.drop (index.val + 1) = banks.val.drop (index.val + 1) ⦄ := by
  have hlen : banks.val.length = 32 := banks.property
  have hil : index.val < banks.val.length := by omega
  have hLl : (banks.val.take index.val).length = index.val := List.length_take_of_le (by omega)
  have hb : banks.val = (banks.val.take index.val).take index.val ++ banks.val[index.val] ::
      ((banks.val.take index.val).drop index.val ++ banks.val.drop (index.val + 1)) := by
    rw [List.take_take, Nat.min_self, List.drop_eq_nil_of_le (by omega), List.nil_append,
      ← List.drop_eq_getElem_cons hil, List.take_append_drop]
  have h1 : (banks.val.take (index.val + 1)) =
      banks.val.take index.val ++ [banks.val[index.val]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hil, Option.toList_some]
  unfold fdt.plan.insert_bank
  obtain ⟨r, hr, j, hj, hrv, hA, hB⟩ := spec_iff.1
    (insert_bank_loop_spec banks index _ _ _ hb (by omega) hs (by simp))
  refine spec_iff.2 ⟨r, hr, ?_⟩
  rw [hLl] at hj
  have hm : (List.take j (List.take index.val banks.val) ++
      banks.val[index.val] :: List.drop j (List.take index.val banks.val)).length =
        index.val + 1 := by
    simp only [List.length_append, List.length_cons, List.length_take, List.length_drop, hLl]
    omega
  have e : ∀ (A B C : List fdt.Span) (y : fdt.Span), A ++ y :: (B ++ C) = (A ++ y :: B) ++ C := by
    intros; simp
  rw [hrv, e, List.take_left' hm, List.drop_left' hm, h1]
  refine ⟨List.perm_middle.trans ?_, ?_, rfl⟩
  · rw [List.take_append_drop]; exact (List.perm_append_singleton _ _).symm
  · exact pairwise_insert_between (fun s : fdt.Span => s.start.val)
      (by rw [List.take_append_drop]; exact hs) hA hB

/-- `sort_banks(banks, count)`: the first `count` banks, sorted by their start. -/
@[step] theorem sort_banks_spec (banks : Array fdt.Span 32#usize) (count : Usize)
    (h0 : 0 < count.val) (h32 : count.val ≤ 32) :
    fdt.plan.sort_banks banks count ⦃ r =>
      (r.val.take count.val).Perm (banks.val.take count.val) ∧
      (r.val.take count.val).Pairwise (fun a b => a.start.val ≤ b.start.val) ⦄ := by
  unfold fdt.plan.sort_banks fdt.plan.sort_banks_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array fdt.Span 32#usize × Usize) => count.val - s.2.val)
    (inv := fun (s : Array fdt.Span 32#usize × Usize) =>
      1 ≤ s.2.val ∧ s.2.val ≤ count.val ∧
      (s.1.val.take s.2.val).Pairwise (fun a b => a.start.val ≤ b.start.val) ∧
      (s.1.val.take count.val).Perm (banks.val.take count.val))
  · rintro ⟨b, i⟩ ⟨h1, h2, hs, hp⟩
    simp only at h1 h2 hs hp
    unfold fdt.plan.sort_banks_loop.body
    step*
    · have hic : i.val < count.val := (UScalar.lt_equiv _ _).1 ‹i < count›
      refine ⟨by omega, by omega, ?_, ?_, by omega⟩
      · rw [index1_post]; exact banks1_post1
      · have e : count.val = (i.val + 1) + (count.val - (i.val + 1)) := by omega
        have t1 := List.take_add (l := banks1.val) (i := i.val + 1) (j := count.val - (i.val + 1))
        have t2 := List.take_add (l := b.val) (i := i.val + 1) (j := count.val - (i.val + 1))
        rw [← e] at t1 t2
        rw [t1, banks1_post2]
        exact (banks1_post.append_right _).trans (by rw [← t2]; exact hp)
  · refine ⟨Nat.le_refl 1, h0, ?_, List.Perm.refl _⟩
    simp only
    cases banks.val with
    | nil => exact List.Pairwise.nil
    | cons a l => simp

/-- The value of `MAX_RAM_BYTES`. -/
theorem max_ram_bytes_eq : fdt.plan.MAX_RAM_BYTES = 17179869184#u64 := by
  unfold fdt.plan.MAX_RAM_BYTES; rfl

/-- The loop of `admit_banks`: the fold of `admitBank` over the banks from
`index` on, after the sum `sum` and the managed banks of the map. -/
theorem admit_banks_loop_spec (plan : fdt.MemoryPlan) (sum : U64) (index : Usize)
    (h32 : plan.ram_count.val ≤ 32) (hi : index.val ≤ plan.ram_count.val)
    (hm : plan.managed_count.val ≤ index.val)
    (hv : ∀ b ∈ (plan.ram.val.take plan.ram_count.val).map spanOf, b.Valid) :
    fdt.plan.admit_banks_loop plan sum index ⦃ x =>
      Agrees (fun _ (acc : Nat × List Span) =>
          acc.2 = (x.2.2.2.1.val.take x.2.2.2.2.1.val).map spanOf ∧
          x.2.2.2.2.1.val ≤ plan.ram_count.val ∧ x.2.1 = plan.ram ∧
          x.2.2.1 = plan.ram_count ∧
          x.2.2.2.2.2.2.1 = plan.boot_count)
        planErrorOf x.1
        ((((plan.ram.val.take plan.ram_count.val).map spanOf).drop index.val).foldlM admitBank
          (sum.val, (plan.managed.val.take plan.managed_count.val).map spanOf)) ⦄ := by
  unfold fdt.plan.admit_banks_loop
  apply loop.spec_decr_nat
    (measure := fun (s : fdt.MemoryPlan × U64 × Usize) => plan.ram_count.val - s.2.2.val)
    (inv := fun (s : fdt.MemoryPlan × U64 × Usize) => s.1.ram = plan.ram ∧
      s.1.ram_count = plan.ram_count ∧ s.1.boot_count = plan.boot_count ∧
      s.2.2.val ≤ plan.ram_count.val ∧ s.1.managed_count.val ≤ s.2.2.val ∧
      (((plan.ram.val.take plan.ram_count.val).map spanOf).drop s.2.2.val).foldlM admitBank
          (s.2.1.val, (s.1.managed.val.take s.1.managed_count.val).map spanOf) =
        (((plan.ram.val.take plan.ram_count.val).map spanOf).drop index.val).foldlM admitBank
          (sum.val, (plan.managed.val.take plan.managed_count.val).map spanOf))
  · rintro ⟨p, s, k⟩ ⟨hr, hc, hb, hk, hm, hf⟩
    simp only at hr hc hb hk hm hf
    unfold fdt.plan.admit_banks_loop.body
    have hp : fdt.plan.PAGE_SIZE = 4096#u64 := by unfold fdt.plan.PAGE_SIZE; rfl
    simp only [hp, max_ram_bytes_eq]
    have hlen : p.ram.val.length = 32 := p.ram.property
    by_cases hkc : k < p.ram_count
    · simp only [hkc, ↓reduceIte]
      have hk' : k.val < plan.ram_count.val := by rw [← hc]; exact (UScalar.lt_equiv _ _).1 hkc
      have hB : k.val < ((plan.ram.val.take plan.ram_count.val).map spanOf).length := by
        simp only [List.length_map, List.length_take, hr ▸ hlen]; omega
      have hBk : ((plan.ram.val.take plan.ram_count.val).map spanOf)[k.val] =
          spanOf (p.ram.val[k.val]'(by omega)) := by
        simp only [List.getElem_map, List.getElem_take, hr]
      have hbv := hv _ (List.getElem_mem hB)
      rw [hBk, spanOf_valid_iff] at hbv
      step as ⟨bank, bank_post⟩
      rw [← bank_post] at hbv hBk
      rw [← hf, foldlM_drop_step hB, hBk, admitBank_eq]
      simp only [spanOf_size, spanOf_start, word64_toNat, spanOf_endNat]
      have hmx : MemoryPlan.MAX_RAM_BYTES = 17179869184 := rfl
      step as ⟨o, o_post⟩
      rcases o with _ | sum1
      · simp only at o_post ⊢
        rw [u64_max_eq] at o_post
        simp only [show 2 ^ 64 ≤ s.val + bank.size.val by omega, ↓reduceIte, spec_ok]
        rfl
      simp only at o_post ⊢
      obtain ⟨ho, ho2, -⟩ := o_post
      rw [u64_max_eq] at ho
      have h3 : (17179869184#u64).val = 17179869184 := rfl
      by_cases hgt : sum1 > 17179869184#u64
      · have h2 := hgt
        rw [gt_iff_lt, UScalar.lt_equiv] at h2
        simp only [hgt, ↓reduceIte, spec_ok, show ¬ 2 ^ 64 ≤ s.val + bank.size.val by omega,
          show MemoryPlan.MAX_RAM_BYTES < s.val + bank.size.val by omega]
        rfl
      have h2 := hgt
      rw [gt_iff_lt, UScalar.lt_equiv, Nat.not_lt] at h2
      simp only [hgt, ↓reduceIte, show ¬ 2 ^ 64 ≤ s.val + bank.size.val by omega,
        show ¬ MemoryPlan.MAX_RAM_BYTES < s.val + bank.size.val by omega]
      step as ⟨i, i_post, i_post1⟩
      step as ⟨o1, o1_post⟩
      rcases o1 with _ | start
      · simp only at o1_post ⊢
        rw [u64_max_eq] at o1_post
        simp only [show 2 ^ 64 ≤ (bank.start.val + 4096 - 1) / 4096 * 4096 by omega, ↓reduceIte,
          spec_ok]
        rfl
      simp only at o1_post ⊢
      obtain ⟨ho1, ho12, -⟩ := o1_post
      rw [u64_max_eq] at ho1
      step as ⟨i1, i1_post⟩
      step as ⟨start1, start1_post, start1_post1⟩
      step as ⟨i2, i2_post⟩
      step as ⟨i3, i3_post⟩
      step as ⟨stop, stop_post, stop_post1⟩
      have e1 : start1.val = (bank.start.val + 4096 - 1) / 4096 * 4096 := by
        rw [start1_post, i1_post, and_page_mask _ _ (by omega), ho12, i_post]; omega
      have e2 : stop.val = (bank.start.val + bank.size.val) / 4096 * 4096 := by
        rw [stop_post, i3_post, and_page_mask _ _ (by omega), i2_post]
      simp only [show ¬ 2 ^ 64 ≤ (bank.start.val + 4096 - 1) / 4096 * 4096 by omega,
        ↓reduceIte,
        except_ok_bind]
      by_cases hlt : start1 < stop
      · have hlt' : (bank.start.val + 4096 - 1) / 4096 * 4096 <
            (bank.start.val + bank.size.val) / 4096 * 4096 := by
          rw [← e1, ← e2]; exact (UScalar.lt_equiv _ _).1 hlt
        have hmc : p.managed_count.val < p.managed.val.length := by
          have : p.managed.val.length = 32 := p.managed.property
          omega
        simp only [hlt, hlt', ↓reduceIte]
        step as ⟨i5, i5_post, i5_post1⟩
        step as ⟨a1, a1_post⟩
        step as ⟨i6, i6_post⟩
        step as ⟨index1, index1_post⟩
        refine ⟨hr, hc, hb, by omega, by omega, ?_, by omega⟩
        rw [index1_post, ho2, a1_post, i6_post, Array.set_val_eq, take_succ_set hmc,
          List.map_append, List.map_singleton]
        congr 4
        simp only [spanOf, spanBetween, Span.mk.injEq, word64_ofNat_iff]
        constructor
        · omega
        · rw [i5_post]; omega
      · have hlt' : ¬ (bank.start.val + 4096 - 1) / 4096 * 4096 <
            (bank.start.val + bank.size.val) / 4096 * 4096 := by
          rw [← e1, ← e2]; intro h; exact hlt ((UScalar.lt_equiv _ _).2 h)
        simp only [hlt, hlt', ↓reduceIte, bind_ok]
        step as ⟨index1, index1_post⟩
        exact ⟨hr, hc, hb, by omega, by omega, by rw [index1_post, ho2], by omega⟩
    · simp only [hkc, ↓reduceIte, spec_ok]
      have hk' : plan.ram_count.val ≤ k.val := by
        rw [← hc]; exact Nat.not_lt.1 (mt (UScalar.lt_equiv _ _).2 hkc)
      have hB : ((plan.ram.val.take plan.ram_count.val).map spanOf).length ≤ k.val := by
        simp only [List.length_map, List.length_take]; omega
      rw [← hf, foldlM_drop_end hB, agrees_ok_ok]
      exact ⟨rfl, by omega, hr, hc, hb⟩
  · exact ⟨rfl, rfl, rfl, hi, hm, rfl⟩

/-- `admit_banks(plan)`: the fold of `admitBank` over the banks; on a success the
managed banks of the map are those of the fold. -/
@[step] theorem admit_banks_spec (plan : fdt.MemoryPlan) (h32 : plan.ram_count.val ≤ 32)
    (hm : plan.managed_count.val = 0)
    (hv : ∀ b ∈ (plan.ram.val.take plan.ram_count.val).map spanOf, b.Valid) :
    fdt.plan.admit_banks plan ⦃ x =>
      Agrees (fun _ (acc : Nat × List Span) =>
          acc.2 = (x.2.managed.val.take x.2.managed_count.val).map spanOf ∧
          x.2.managed_count.val ≤ plan.ram_count.val ∧ x.2.ram = plan.ram ∧
          x.2.ram_count = plan.ram_count ∧ x.2.boot_count = plan.boot_count)
        planErrorOf x.1
        (((plan.ram.val.take plan.ram_count.val).map spanOf).foldlM admitBank (0, [])) ⦄ := by
  unfold fdt.plan.admit_banks
  have h := admit_banks_loop_spec plan 0#u64 0#usize h32 (Nat.zero_le _) (by rw [hm]; rfl) hv
  obtain ⟨⟨r, a, i, a1, i1, a2, i2, i3⟩, hx, hp⟩ := spec_iff.1 h
  rw [hx]
  simp only [bind_ok]
  simpa [hm] using hp

/-! ## Boot storage and firmware -/

/-- `add_boot(plan, boot, count)`: the fold of `addBoot` over the first `count`
spans of boot storage; on a success the boot storage of the map is that of the
fold. -/
@[step] theorem add_boot_spec (plan : fdt.MemoryPlan) (boot : Slice fdt.Span) (count : Usize)
    (hc : count.val ≤ boot.length) (h4 : count.val ≤ 4) (hb0 : plan.boot_count.val = 0)
    (hr : plan.ram_count.val ≤ 32) :
    fdt.plan.add_boot plan boot count ⦃ x =>
      Agrees (fun _ (bp : List Span) =>
          bp = (x.2.reserved.val.take x.2.boot_count.val).map spanOf ∧
          x.2.boot_count.val = count.val ∧ x.2.reserved_count = x.2.boot_count ∧
          x.2.ram = plan.ram ∧ x.2.ram_count = plan.ram_count ∧ x.2.managed = plan.managed ∧
          x.2.managed_count = plan.managed_count)
        planErrorOf x.1 (((spansOf boot).take count.val).foldlM
          (addBoot ((plan.ram.val.take plan.ram_count.val).map spanOf)) []) ⦄ := by
  unfold fdt.plan.add_boot fdt.plan.add_boot_loop
  have hBl : ((spansOf boot).take count.val).length = count.val := by
    have : count.val ≤ boot.val.length := hc
    simp only [List.length_take, spansOf, List.length_map]; omega
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryPlan × Usize) => count.val - x.2.val)
    (inv := fun (x : fdt.MemoryPlan × Usize) => x.2.val ≤ count.val ∧
      x.1.boot_count.val = x.2.val ∧ x.1.ram = plan.ram ∧ x.1.ram_count = plan.ram_count ∧
      x.1.managed = plan.managed ∧ x.1.managed_count = plan.managed_count ∧
      (((spansOf boot).take count.val).drop x.2.val).foldlM
          (addBoot ((plan.ram.val.take plan.ram_count.val).map spanOf))
          ((x.1.reserved.val.take x.2.val).map spanOf) =
        ((spansOf boot).take count.val).foldlM
          (addBoot ((plan.ram.val.take plan.ram_count.val).map spanOf)) [])
  · rintro ⟨p, k⟩ ⟨hk, hpb, hpr, hpc, hpm, hpmc, hf⟩
    simp only at hk hpb hpr hpc hpm hpmc hf
    unfold fdt.plan.add_boot_loop.body
    have hrl : p.reserved.val.length = 132 := p.reserved.property
    step*
    · have hkB : k.val < ((spansOf boot).take count.val).length := by
        rw [hBl]; exact (UScalar.lt_equiv _ _).1 ‹k < count›
      have hBk : ((spansOf boot).take count.val)[k.val] = spanOf s := by
        simp only [List.getElem_take, spansOf, List.getElem_map, s_post]
      obtain ⟨pg, hpg, hv⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
      have hv' : spanOf val = pg := hv
      subst hv'
      have hbanks : spansOf s2 = (plan.ram.val.take plan.ram_count.val).map spanOf := by
        simp only [spansOf, s2_post, s1_post, Array.val_to_slice, hpr, hpc]
      have hacc : spansOf s4 = (p.reserved.val.take k.val).map spanOf := by
        simp only [spansOf, s4_post, s3_post, Array.val_to_slice, hpb]
      rw [← hf, foldlM_drop_step hkB, hBk, addBoot_of_pages hpg, ← hbanks, ← b_post,
        ‹b = true›,
        ← hacc, ← b1_post, ‹b1 = true›]
      rfl
    · have hkB : k.val < ((spansOf boot).take count.val).length := by
        rw [hBl]; exact (UScalar.lt_equiv _ _).1 ‹k < count›
      have hBk : ((spansOf boot).take count.val)[k.val] = spanOf s := by
        simp only [List.getElem_take, spansOf, List.getElem_map, s_post]
      obtain ⟨pg, hpg, hv⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
      have hv' : spanOf val = pg := hv
      subst hv'
      have hbanks : spansOf s2 = (plan.ram.val.take plan.ram_count.val).map spanOf := by
        simp only [spansOf, s2_post, s1_post, Array.val_to_slice, hpr, hpc]
      have hacc : spansOf s4 = (p.reserved.val.take k.val).map spanOf := by
        simp only [spansOf, s4_post, s3_post, Array.val_to_slice, hpb]
      have hkc : k.val < count.val := (UScalar.lt_equiv _ _).1 ‹k < count›
      have hbc : p.boot_count.val < p.reserved.val.length := by omega
      refine ⟨by omega, by omega, hpr, hpc, hpm, hpmc, ?_, by omega⟩
      rw [← hf, foldlM_drop_step hkB, hBk, addBoot_of_pages hpg, ← hbanks, ← b_post,
        ‹b = true›,
        ← hacc, ← b1_post, (Bool.not_eq_true _).mp ‹¬b1 = true›]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, except_ok_bind]
      rw [index1_post, a_post, Array.set_val_eq, ← hpb, take_succ_set hbc, List.map_append,
        List.map_singleton, hacc, hpb]
    · have hkB : k.val < ((spansOf boot).take count.val).length := by
        rw [hBl]; exact (UScalar.lt_equiv _ _).1 ‹k < count›
      have hBk : ((spansOf boot).take count.val)[k.val] = spanOf s := by
        simp only [List.getElem_take, spansOf, List.getElem_map, s_post]
      obtain ⟨pg, hpg, hv⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
      have hv' : spanOf val = pg := hv
      subst hv'
      have hbanks : spansOf s2 = (plan.ram.val.take plan.ram_count.val).map spanOf := by
        simp only [spansOf, s2_post, s1_post, Array.val_to_slice, hpr, hpc]
      rw [← hf, foldlM_drop_step hkB, hBk, addBoot_of_pages hpg, ← hbanks, ← b_post,
        (Bool.not_eq_true _).mp ‹¬b = true›]
      rfl
    · have hkB : k.val < ((spansOf boot).take count.val).length := by
        rw [hBl]; exact (UScalar.lt_equiv _ _).1 ‹k < count›
      have hBk : ((spansOf boot).take count.val)[k.val] = spanOf s := by
        simp only [List.getElem_take, spansOf, List.getElem_map, s_post]
      have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
      rw [← hf, foldlM_drop_step hkB, hBk, addBoot_of_error he, except_error_bind, r1_post,
        ← e_post]
      rfl
    · have hkc : count.val ≤ k.val :=
        Nat.not_lt.1 (mt (UScalar.lt_equiv _ _).2 ‹¬k < count›)
      rw [← hf, foldlM_drop_end (by omega), agrees_ok_ok]
      exact ⟨by rw [hpb], by omega, hpr, hpc, hpm, hpmc⟩
  · simp [hb0]

/-- `add_firmware(plan, firmware)`: the fold of `addFirmware` over the
reservations; on a success the firmware reservations of the map are those of
the fold, after its boot storage, which stays as it was. -/
@[step] theorem add_firmware_spec (plan : fdt.MemoryPlan) (firmware : Slice fdt.ReservedRegion)
    (hl : firmware.length ≤ 128) (hb : plan.boot_count.val ≤ 4)
    (hrc : plan.reserved_count = plan.boot_count) :
    fdt.plan.add_firmware plan firmware ⦃ x =>
      Agrees (fun _ (fp : List Span) =>
          fp = ((x.2.reserved.val.take x.2.reserved_count.val).drop
            x.2.boot_count.val).map spanOf ∧
          x.2.reserved_count.val = plan.boot_count.val + firmware.length ∧
          x.2.reserved.val.take plan.boot_count.val = plan.reserved.val.take plan.boot_count.val ∧
          x.2.ram = plan.ram ∧ x.2.ram_count = plan.ram_count ∧ x.2.managed = plan.managed ∧
          x.2.managed_count = plan.managed_count ∧ x.2.boot_count = plan.boot_count)
        planErrorOf x.1 ((regionsOf firmware).foldlM
          (addFirmware ((plan.reserved.val.take plan.boot_count.val).map spanOf)) []) ⦄ := by
  unfold fdt.plan.add_firmware fdt.plan.add_firmware_loop
  have hFl : (regionsOf firmware).length = firmware.length := List.length_map _
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.MemoryPlan × Usize) => firmware.length - x.2.val)
    (inv := fun (x : fdt.MemoryPlan × Usize) => x.2.val ≤ firmware.length ∧
      x.1.reserved_count.val = plan.boot_count.val + x.2.val ∧
      x.1.boot_count = plan.boot_count ∧
      x.1.reserved.val.take plan.boot_count.val = plan.reserved.val.take plan.boot_count.val ∧
      x.1.ram = plan.ram ∧ x.1.ram_count = plan.ram_count ∧
      x.1.managed = plan.managed ∧ x.1.managed_count = plan.managed_count ∧
      ((regionsOf firmware).drop x.2.val).foldlM
          (addFirmware ((plan.reserved.val.take plan.boot_count.val).map spanOf))
          (((x.1.reserved.val.take x.1.reserved_count.val).drop plan.boot_count.val).map spanOf) =
        (regionsOf firmware).foldlM
          (addFirmware ((plan.reserved.val.take plan.boot_count.val).map spanOf)) [])
  · rintro ⟨p, k⟩ ⟨hk, hpr, hpb, hpt, hpram, hpc, hpm, hpmc, hf⟩
    simp only at hk hpr hpb hpt hpram hpc hpm hpmc hf
    unfold fdt.plan.add_firmware_loop.body
    have hrl : p.reserved.val.length = 132 := p.reserved.property
    step*
    · have hkF : k.val < (regionsOf firmware).length := by
        rw [hFl]; exact slice_lt_len ‹k < Slice.len firmware›
      have hFk : (regionsOf firmware)[k.val] = regionOf rr := by
        simp only [regionsOf, List.getElem_map, rr_post]
      obtain ⟨pg, hpg, hv⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
      have hv' : spanOf val = pg := hv
      subst hv'
      have hacc : spansOf s1 = (plan.reserved.val.take plan.boot_count.val).map spanOf := by
        simp only [spansOf, s1_post, s_post, Array.val_to_slice, hpb, hpt]
      rw [← hf, foldlM_drop_step hkF, hFk, addFirmware_of_pages hpg, ← hacc, ← b_post,
        ‹b = true›]
      rfl
    · have hkF : k.val < (regionsOf firmware).length := by
        rw [hFl]; exact slice_lt_len ‹k < Slice.len firmware›
      have hFk : (regionsOf firmware)[k.val] = regionOf rr := by
        simp only [regionsOf, List.getElem_map, rr_post]
      obtain ⟨pg, hpg, hv⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› r_post)
      have hv' : spanOf val = pg := hv
      subst hv'
      have hacc : spansOf s1 = (plan.reserved.val.take plan.boot_count.val).map spanOf := by
        simp only [spansOf, s1_post, s_post, Array.val_to_slice, hpb, hpt]
      have hkf : k.val < firmware.length := slice_lt_len ‹k < Slice.len firmware›
      have hrc : p.reserved_count.val < p.reserved.val.length := by omega
      have hbr : plan.boot_count.val ≤ p.reserved_count.val := by omega
      refine ⟨by omega, by omega, hpb, ?_, hpram, hpc, hpm, hpmc, ?_, by omega⟩
      · rw [a_post, Array.set_val_eq, List.take_set_of_le hbr, hpt]
      · rw [← hf, foldlM_drop_step hkF, hFk, addFirmware_of_pages hpg, ← hacc, ← b_post,
          (Bool.not_eq_true _).mp ‹¬b = true›]
        simp only [Bool.false_eq_true, ↓reduceIte, except_ok_bind]
        rw [index1_post, i1_post, a_post, Array.set_val_eq, take_succ_set hrc,
          List.drop_append_of_le_length (by rw [List.length_take_of_le (by omega)]; exact hbr),
          List.map_append, List.map_singleton]
    · have hkF : k.val < (regionsOf firmware).length := by
        rw [hFl]; exact slice_lt_len ‹k < Slice.len firmware›
      have hFk : (regionsOf firmware)[k.val] = regionOf rr := by
        simp only [regionsOf, List.getElem_map, rr_post]
      have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
      rw [← hf, foldlM_drop_step hkF, hFk, addFirmware_of_error he, except_error_bind, r1_post,
        ← e_post]
      rfl
    · have hkc : firmware.length ≤ k.val := slice_len_le ‹¬k < Slice.len firmware›
      rw [← hf, foldlM_drop_end (by omega), agrees_ok_ok]
      exact ⟨by rw [hpb], by omega, hpt, hpram, hpc, hpm, hpmc, hpb⟩
  · simp [hrc]

/-! ## The entries -/

/-- The counts of `NO_PLAN`. -/
theorem no_plan_managed_count : fdt.plan.NO_PLAN.managed_count = 0#usize := by
  unfold fdt.plan.NO_PLAN; rfl

theorem no_plan_ram_count : fdt.plan.NO_PLAN.ram_count = 0#usize := by
  unfold fdt.plan.NO_PLAN; rfl

theorem no_plan_boot_count : fdt.plan.NO_PLAN.boot_count = 0#usize := by
  unfold fdt.plan.NO_PLAN; rfl

/-- `build(ram, boot, count, firmware)`: `MemoryPlan.allRam` with the boot
storage `B`, the first `count` spans of `boot` when `count` is at most 4 and
any list of `count` spans otherwise. -/
@[step] theorem build_spec (ram boot : Slice fdt.Span) (count : Usize)
    (firmware : Slice fdt.ReservedRegion) (B : List Span)
    (hB : count.val ≤ 4 → count.val ≤ boot.length ∧ (spansOf boot).take count.val = B)
    (hBl : B.length = count.val) :
    fdt.plan.build ram boot count firmware ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (MemoryPlan.allRam (spansOf ram) B (regionsOf firmware)) ⦄ := by
  unfold fdt.plan.build
  rw [allRam_eq]
  have hbk : fdt.BANKS = 32#usize := by unfold fdt.BANKS; rfl
  have hbs : fdt.BOOT_SPANS = 4#usize := by unfold fdt.BOOT_SPANS; rfl
  have hfw : fdt.FIRMWARE = 128#usize := by unfold fdt.FIRMWARE; rfl
  have hcap := capacity_iff (spansOf ram) B (regionsOf firmware)
  have hrl : (spansOf ram).length = ram.length := List.length_map _
  have hfl : (regionsOf firmware).length = firmware.length := List.length_map _
  simp only [core.slice.Slice.is_empty, bind_ok, hbk, hbs, hfw]
  by_cases h1 : ram.length = 0
  · simp only [h1, decide_true, ↓reduceIte, hcap.2 (by rw [hrl, hfl, hBl]; omega), spec_ok]; rfl
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : Slice.len ram > 32#usize
  · have : 32 < ram.length := by rw [gt_iff_lt, UScalar.lt_equiv, Slice.len_val] at h2; exact h2
    simp only [h2, ↓reduceIte, hcap.2 (by rw [hrl, hfl, hBl]; omega), spec_ok]; rfl
  simp only [h2, ↓reduceIte]
  by_cases h3 : count = 0#usize
  · have : count.val = 0 := by rw [h3]; rfl
    simp only [h3, ↓reduceIte, hcap.2 (by rw [hrl, hfl, hBl]; omega), spec_ok]; rfl
  simp only [h3, ↓reduceIte]
  by_cases h4 : count > 4#usize
  · have : 4 < count.val := by rw [gt_iff_lt, UScalar.lt_equiv] at h4; exact h4
    simp only [h4, ↓reduceIte, hcap.2 (by rw [hrl, hfl, hBl]; omega), spec_ok]; rfl
  simp only [h4, ↓reduceIte]
  by_cases h5 : Slice.len firmware > 128#usize
  · have : 128 < firmware.length := by
      rw [gt_iff_lt, UScalar.lt_equiv, Slice.len_val] at h5; exact h5
    simp only [h5, ↓reduceIte, hcap.2 (by rw [hrl, hfl, hBl]; omega), spec_ok]; rfl
  simp only [h5, ↓reduceIte]
  have e32 : (32#usize).val = 32 := rfl
  have e4 : (4#usize).val = 4 := rfl
  have e128 : (128#usize).val = 128 := rfl
  have h2' : ram.length ≤ 32 := by
    rw [gt_iff_lt, UScalar.lt_equiv, Slice.len_val] at h2; omega
  have h3' : count.val ≠ 0 := fun h => h3 (UScalar.eq_of_val_eq (by rw [h]; rfl))
  have h4' : count.val ≤ 4 := by rw [gt_iff_lt, UScalar.lt_equiv] at h4; omega
  have h5' : firmware.length ≤ 128 := by
    rw [gt_iff_lt, UScalar.lt_equiv, Slice.len_val] at h5; omega
  have hc : ¬ ((spansOf ram).length = 0 ∨ 32 < (spansOf ram).length ∨ B.length = 0 ∨
      4 < B.length ∨ 128 < (regionsOf firmware).length) := by rw [hrl, hfl, hBl]; omega
  simp only [(Bool.not_eq_true _).mp (mt hcap.1 hc), Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hcb, hBeq⟩ := hB h4'
  -- the banks in input order
  obtain ⟨⟨r, plan⟩, hxe, hx⟩ := spec_iff.1
    (add_banks_spec fdt.plan.NO_PLAN ram h2' (by rw [no_plan_ram_count]; rfl))
  rw [hxe, bind_ok]
  refine try_spec hx (fun e => from_residual_spec e) fun _ b0 hb0 hE => ?_
  obtain ⟨rfl, hpc, hpt, hpm, hpb⟩ := hb0
  dsimp only at hpc hpt hpm hpb
  obtain ⟨-, hb0p, hb0n⟩ := addBank_fold (spansOf ram) [] _ hE List.Pairwise.nil
  dsimp only
  -- the banks in address order
  obtain ⟨a, hae, hap, has⟩ := spec_iff.1
    (sort_banks_spec plan.ram plan.ram_count (by omega) (by omega))
  rw [hae, bind_ok]
  rw [hpc, hpt] at hap
  rw [hpc] at has
  have hsort : (a.val.take ram.length).map spanOf = sortByStart (spansOf ram) :=
    map_eq_sortByStart spanOf hap
      (by simpa only [spanOf_start, word64_toNat] using has) hb0n hb0p
  rw [← hsort]
  have hval : ∀ b ∈ (a.val.take ram.length).map spanOf, b.Valid := by
    intro b hb
    rw [hsort] at hb
    exact (hb0n b ((sortByStart_perm _).mem_iff.1 hb)).2
  -- the managed banks
  obtain ⟨⟨r1, plan1⟩, hx1e, hx1⟩ := spec_iff.1
    (admit_banks_spec { plan with ram := a } (by dsimp only; omega)
      (by dsimp only; rw [hpm, no_plan_managed_count]; rfl) (by dsimp only; rw [hpc]; exact hval))
  rw [hx1e, bind_ok]
  dsimp only at hx1
  rw [hpc] at hx1
  refine try_spec hx1 (fun e => from_residual_spec e) fun _ acc hacc hE1 => ?_
  obtain ⟨hacc, hmc, hr1, hrc1, hb1⟩ := hacc
  dsimp only
  have hml : plan1.managed.val.length = 32 := plan1.managed.property
  by_cases hm0 : plan1.managed_count = 0#usize
  · have : acc.2.isEmpty = true := by
      rw [hacc, hm0]; rfl
    simp only [hm0, ↓reduceIte, this, spec_ok]; rfl
  have hm0' : plan1.managed_count.val ≠ 0 := fun h => hm0 (UScalar.eq_of_val_eq (by rw [h]; rfl))
  have hne : acc.2.isEmpty = false := by
    rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff_length_eq_zero, hacc, List.length_map,
      List.length_take]
    omega
  simp only [hm0, ↓reduceIte, hne, Bool.false_eq_true]
  -- the boot storage
  obtain ⟨⟨r2, plan2⟩, hx2e, hx2⟩ := spec_iff.1
    (add_boot_spec plan1 boot count hcb h4' (by rw [hb1, hpb, no_plan_boot_count]; rfl)
      (by rw [hrc1]; omega))
  rw [hx2e, bind_ok]
  dsimp only at hx2
  rw [hr1, hrc1, hpc, hBeq] at hx2
  refine try_spec hx2 (fun e => from_residual_spec e) fun _ bp hbp hE2 => ?_
  obtain ⟨rfl, hbc2, hrc2, hr2, hrcount2, hm2, hmc2⟩ := hbp
  dsimp only
  -- the firmware reservations
  obtain ⟨⟨r3, plan3⟩, hx3e, hx3⟩ := spec_iff.1
    (add_firmware_spec plan2 firmware h5' (by omega) hrc2)
  rw [hx3e, bind_ok]
  dsimp only at hx3
  refine try_spec hx3 (fun e => from_residual_spec e) fun _ fp hfp hE3 => ?_
  obtain ⟨rfl, hrc3, ht3, hr3, hrcount3, hm3, hmc3, hb3⟩ := hfp
  simp only [spec_ok, agrees_ok_ok]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show plan3.ram_count.val ≤ 32
    rw [hrcount3, hrcount2]; omega
  · show plan3.managed_count.val ≤ 32
    rw [hmc3, hmc2]; omega
  · rw [hrc3, hb3]; omega
  · show plan3.reserved_count.val ≤ 4 + 128
    rw [hrc3]; omega
  · rw [hr3, hr2, hrcount3, hrcount2, hpc, hm3, hm2, hmc3, hmc2, ← hacc, hb3, ht3]

/-- A word that is not zero, as a number. -/
theorem u64_bne_zero_iff (x : U64) : (x != 0#u64) = true ↔ x.val ≠ 0 := by
  rw [bne_iff_ne, ne_eq, ne_eq, u64_eq_zero_iff]

/-- The value of `MAX_WINDOW_BYTES`. -/
theorem max_window_bytes_eq : fdt.plan.MAX_WINDOW_BYTES = 134217728#u64 := by
  unfold fdt.plan.MAX_WINDOW_BYTES; rfl

/-- `check_window(window)`: `windowCheck`. -/
@[step] theorem check_window_spec (window : fdt.Span) :
    fdt.plan.check_window window ⦃ r =>
      Agrees (fun _ _ => True) planErrorOf r (windowCheck (spanOf window)) ⦄ := by
  unfold fdt.plan.check_window windowCheck
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun _ _ _ hc => ?_
  have hv : window.start.val + window.size.val < 2 ^ 64 :=
    (spanOf_valid_iff _).1 (checkPlanSpan_ok hc).2
  have hp : fdt.plan.PAGE_SIZE = 4096#u64 := by unfold fdt.plan.PAGE_SIZE; rfl
  simp only [hp, max_window_bytes_eq, spanOf_start, spanOf_size, word64_toNat, spanOf_endNat,
    MemoryPlan.PAGE_SIZE, MemoryPlan.MAX_WINDOW_BYTES]
  step*
  · have h1 : window.start.val % 4096 ≠ 0 := by
      rw [← i_post]; exact (u64_bne_zero_iff i).1 ‹_›
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, h1, not_false_eq_true, true_or, ↓reduceIte]
    rfl
  · have h1 : window.start.val % 4096 = 0 := by
      rw [← i_post]; exact Decidable.not_not.1 (mt (u64_bne_zero_iff i).2 ‹_›)
    have h2 : (window.start.val + window.size.val) % 4096 ≠ 0 := by
      rw [← i1_post, ← i2_post]; exact (u64_bne_zero_iff i2).1 ‹_›
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, h1, h2, not_false_eq_true, or_true,
      ↓reduceIte]
    rfl
  · have h1 : window.start.val % 4096 = 0 := by
      rw [← i_post]; exact Decidable.not_not.1 (mt (u64_bne_zero_iff i).2 ‹_›)
    have h2 : (window.start.val + window.size.val) % 4096 = 0 := by
      rw [← i1_post, ← i2_post]; exact Decidable.not_not.1 (mt (u64_bne_zero_iff i2).2 ‹_›)
    have h3 : 134217728 < window.size.val := by
      have := ‹window.size > 134217728#u64›
      rw [gt_iff_lt, UScalar.lt_equiv] at this; exact this
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, h1, h2, not_true_eq_false, or_self,
      ↓reduceIte, h3]
    rfl
  · have h1 : window.start.val % 4096 = 0 := by
      rw [← i_post]; exact Decidable.not_not.1 (mt (u64_bne_zero_iff i).2 ‹_›)
    have h2 : (window.start.val + window.size.val) % 4096 = 0 := by
      rw [← i1_post, ← i2_post]; exact Decidable.not_not.1 (mt (u64_bne_zero_iff i2).2 ‹_›)
    have h3 : ¬ 134217728 < window.size.val := by
      have := ‹¬window.size > 134217728#u64›
      rw [gt_iff_lt, UScalar.lt_equiv] at this; exact this
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, h1, h2, not_true_eq_false, or_self,
      ↓reduceIte, h3]
    exact agrees_ok_ok.2 trivial

/-- `manage_window(plan, window)`: the map with the window as its one managed
bank, or `OutsideRam`. -/
@[step] theorem manage_window_spec {p : fdt.MemoryPlan} {P : MemoryPlan} (h : MemoryPlanRepr p P)
    (window : fdt.Span) :
    fdt.plan.manage_window p window ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (if P.containsRam (spanOf window) = false then .error .outsideRam
        else .ok { P with managed := [spanOf window] }) ⦄ := by
  unfold fdt.plan.manage_window
  have hml : p.managed.val.length = 32 := p.managed.property
  step*
  · simp only [← b_post, ‹b = true›, Bool.true_eq_false, ↓reduceIte, agrees_ok_ok]
    obtain ⟨h1, -, h3, h4, rfl⟩ := h
    refine ⟨h1, by show (1 : Nat) ≤ 32; omega, h3, h4, ?_⟩
    have e : (a.val.take (1#usize).val).map spanOf = [spanOf window] := by
      rw [a_post, Array.set_val_eq]
      show ((p.managed.val.set 0 window).take (0 + 1)).map spanOf = _
      rw [take_succ_set (by omega)]; rfl
    dsimp only
    rw [e]
  · simp only [← b_post, (Bool.not_eq_true _).mp ‹¬b = true›, ↓reduceIte]
    rfl

/-- `MemoryPlan::all_ram(ram, boot, firmware)`: `MemoryPlan.allRam`, the statement
`MemoryPlanAllRam` without its premise `Usize64`. -/
@[step] theorem all_ram_spec (ram boot : Slice fdt.Span) (firmware : Slice fdt.ReservedRegion) :
    fdt.plan.MemoryPlan.all_ram ram boot firmware ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (MemoryPlan.allRam (spansOf ram) (spansOf boot) (regionsOf firmware)) ⦄ := by
  unfold fdt.plan.MemoryPlan.all_ram
  have hl : (spansOf boot).length = boot.length := List.length_map _
  exact build_spec ram boot _ firmware (spansOf boot)
    (fun _ => ⟨by rw [Slice.len_val], by rw [Slice.len_val, ← hl, List.take_length]⟩)
    (by rw [Slice.len_val, hl])

/-- `MemoryPlan::new(window, ram, boot, firmware)`: `MemoryPlan.new`, the statement
`MemoryPlanNew` without its premise `Usize64`. -/
@[step] theorem new_spec (window : fdt.Span) (ram boot : Slice fdt.Span)
    (firmware : Slice fdt.ReservedRegion) :
    fdt.plan.MemoryPlan.new window ram boot firmware ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (MemoryPlan.new (spanOf window) (spansOf ram) (spansOf boot) (regionsOf firmware)) ⦄ := by
  unfold fdt.plan.MemoryPlan.new
  rw [new_eq]
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
  have hl : (spansOf boot).length = boot.length := List.length_map _
  have hb := build_spec ram boot (Slice.len boot) firmware (spansOf boot)
    (fun _ => ⟨by rw [Slice.len_val], by rw [Slice.len_val, ← hl, List.take_length]⟩)
    (by rw [Slice.len_val, hl])
  obtain ⟨r1, hr1e, hr1⟩ := spec_iff.1 hb
  simp only [hr1e, bind_ok]
  refine try_spec hr1 (fun e => from_residual_spec e) fun val P hP _ => ?_
  exact manage_window_spec hP window

/-- The loop of `from_boot_memory`: the further spans after the image and the
tree. -/
theorem from_boot_memory_loop_spec (more : Slice fdt.Span) (boot : Array fdt.Span 4#usize)
    (index : Usize) (hm : more.length ≤ 2) (hi : index.val ≤ more.length) (x y : fdt.Span)
    (hb : boot.val.take (2 + index.val) = x :: y :: more.val.take index.val) :
    fdt.plan.MemoryPlan.from_boot_memory_loop more boot index ⦃ r =>
      r.val.take (2 + more.length) = x :: y :: more.val ⦄ := by
  unfold fdt.plan.MemoryPlan.from_boot_memory_loop
  apply loop.spec_decr_nat
    (measure := fun (s : Array fdt.Span 4#usize × Usize) => more.length - s.2.val)
    (inv := fun (s : Array fdt.Span 4#usize × Usize) => s.2.val ≤ more.length ∧
      s.1.val.take (2 + s.2.val) = x :: y :: more.val.take s.2.val)
  · rintro ⟨b, k⟩ ⟨hk, hb⟩
    simp only at hk hb
    unfold fdt.plan.MemoryPlan.from_boot_memory_loop.body
    have hbl : b.val.length = 4 := b.property
    step*
    · have hk' : k.val < more.length := slice_lt_len ‹k < Slice.len more›
      refine ⟨by omega, ?_, by omega⟩
      rw [a_post, Array.set_val_eq, i1_post, index1_post,
        show 2 + (k.val + 1) = (2 + k.val) + 1 by omega,
        take_succ_set (by omega), hb, List.take_add_one, List.getElem?_eq_getElem hk', s_post]
      simp
    · have : k.val = more.length := by have := slice_len_le ‹¬k < Slice.len more›; omega
      rw [← this, hb, this, List.take_length]
  · exact ⟨hi, hb⟩

/-- `MemoryPlan::from_boot_memory(memory, window, more)`: `MemoryPlan.fromBootMemory`,
the statement `MemoryPlanFromBootMemory` without its premises `Usize64`,
`M.memory.WellFormed` and `M.Consistent`. More than two further spans give
`Capacity` before the count `2 + more.len()` is formed, as `MemoryPlan.allRam`
refuses more than four spans of boot storage (`allRam_of_boot_gt`); the second
test of the code on the number of further spans then always holds. -/
theorem from_boot_memory_spec {m : fdt.BootMemory} {M : BootMemory} (h : BootMemoryRepr m M)
    (window : fdt.Span) (more : Slice fdt.Span) :
    fdt.plan.MemoryPlan.from_boot_memory m window more ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (MemoryPlan.fromBootMemory M (spanOf window) (spansOf more)) ⦄ := by
  unfold fdt.plan.MemoryPlan.from_boot_memory
  rw [MemoryPlan.fromBootMemory, new_eq]
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
  have hl : (spansOf more).length = more.length := List.length_map _
  by_cases hgt : Slice.len more > 2#usize
  · have hgt' : 2 < more.length := by
      rw [gt_iff_lt, UScalar.lt_equiv, Slice.len_val] at hgt; exact hgt
    simp only [hgt, ↓reduceIte, spec_ok]
    rw [allRam_of_boot_gt _ _ _ (by rw [List.length_cons, List.length_cons, hl]; omega),
      except_error_bind, agrees_err_error]
    rfl
  · have hle' : more.length ≤ 2 := by
      rw [gt_iff_lt, UScalar.lt_equiv, Slice.len_val] at hgt; exact Nat.le_of_not_lt hgt
    have hle : Slice.len more ≤ 2#usize := by
      rw [UScalar.le_equiv, Slice.len_val]; exact hle'
    have hdtb : M.dtb = spanOf m.dtb := h.2.1
    have himg : M.image = spanOf m.image := h.2.2.1
    simp only [hgt, hle, ↓reduceIte]
    obtain ⟨boot, hbe, hbp⟩ := spec_iff.1 (from_boot_memory_loop_spec more
      (Array.make 4#usize [m.image, m.dtb, fdt.span.EMPTY, fdt.span.EMPTY]) 0#usize hle'
      (Nat.zero_le _) m.image m.dtb (by simp [Array.make]))
    rw [hbe, bind_ok]
    obtain ⟨s, hse, hs⟩ := spec_iff.1 (boot_memory_ram_spec h)
    rw [hse, bind_ok]
    step as ⟨s1, hs1⟩
    step as ⟨i2, hi2⟩
    obtain ⟨s2, hs2e, hs2⟩ := spec_iff.1 (boot_memory_reserved_spec h)
    rw [hs2e, bind_ok]
    have hb := build_spec s s1 i2 s2 (M.image :: M.dtb :: spansOf more)
      (fun _ => ⟨by rw [hs1, Array.length_to_slice]; scalar_tac, by
        rw [spansOf, hs1, Array.val_to_slice, ← List.map_take, hi2, Slice.len_val, hbp, hdtb,
          himg]
        rfl⟩)
      (by rw [hi2, Slice.len_val, List.length_cons, List.length_cons, hl]; omega)
    rw [hs, hs2] at hb
    obtain ⟨r1, hr1e, hr1⟩ := spec_iff.1 hb
    rw [hr1e, bind_ok]
    exact try_spec hr1 (fun e => from_residual_spec e) fun _ _ hP _ =>
      manage_window_spec hP window

end Krepi.Proofs.Fdt.Refinement
