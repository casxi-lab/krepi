module

public import Krepi.Statements.PageTables.Representation
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.ReceiptSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the receipts of the page ownership table

The triples of the generated functions of `ownership::receipts` of the
`page-tables` component: the checks of a value that names an allocation and
the writes of `publish`, `cancel` and `release`. The triples of the helpers
are `@[step]` lemmas, so that the proof of a caller steps over the call with
the triple of the callee. Each holds without the premise `Usize64` and
without `Ownership.Invariant`.

- The search of an extent: `same_state_spec`, `holds_as_spec`,
  `held_extent_spec` (the loop, as `List.findIdx?` over the extents in use),
  `receipt_held_test_eq` and `receipt_held_findIdx_eq` (its test and search
  are those of `Ownership.findHeld`), `find_held_spec` (`Ownership.findHeld`),
  `receipt_found_repr` (the extent found, in the table of the code).
- The entries: `ownership_validate_spec`, `ownership_publish_spec`,
  `ownership_cancel_spec`, `ownership_release_spec`, the statements
  `OwnershipValidate`, `OwnershipPublish`, `OwnershipCancel` and
  `OwnershipRelease` without their premises `Usize64` and
  `Ownership.Invariant`.
- Freeing an extent: `joins_spec`, `close_gap_spec` (the loop that closes a
  gap), `merge_freed_spec` (`mergeFreed`), with `receipt_freed_repr`,
  `receipt_joins_iff`, `receipt_merged_repr`, `receipt_freed_listRel`,
  `receipt_at_repr`, `receipt_at_fits`, `receipt_merge_order` and
  `receipt_merge_final`, `receipt_merge_tail_spec`, `receipt_merge_last_spec` and
  `receipt_merge_tail_first_spec`, the steps of its proof.
- Tables: `receipt_ownershipRepr_with_extents` (a table whose extents and
  count change).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-- `same_state(a, b)`: whether the two states of a holder are one state. -/
@[step] theorem same_state_spec (a b : page_tables.HoldState) :
    page_tables.ownership.receipts.same_state a b ⦃ r =>
      r = decide (holdStateOf a = holdStateOf b) ⦄ := by
  unfold page_tables.ownership.receipts.same_state
  cases a <;> cases b <;> exact spec_of_eq rfl (by decide)

/-- `holds_as(holding, allocation, state)`: whether the holding is that of the
owner identity and the generation of the allocation in the state. -/
@[step] theorem holds_as_spec (h : page_tables.Holding) (a : page_tables.Allocation)
    (s : page_tables.HoldState) :
    page_tables.ownership.receipts.holds_as h a s ⦃ r =>
      r = (holdingOf h == .held (word64 a.owner) (word64 a.generation) (holdStateOf s)) ⦄ := by
  unfold page_tables.ownership.receipts.holds_as
  cases h with
  | Free => exact spec_of_eq rfl (by simp [holdingOf])
  | Held o g st =>
    simp only
    step*
    · rw [r_post]
      cases st <;> cases s <;> simp [holdingOf, holdStateOf]
    · simp [holdingOf, word64_inj, *]
    · simp [holdingOf, word64_inj, *]

/-- `held_extent(extents, count, allocation, state)`: the index of the first
of the first `count` extents whose range has the start and the length of the
range of the allocation and whose holding `holds_as` accepts, for `count`
within the array. The loop keeps the search from its index, shifted to an
index from the start, equal to the search from the start. -/
@[step] theorem held_extent_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count : Usize) (a : page_tables.Allocation) (s : page_tables.HoldState)
    (hc : count.val ≤ E.val) :
    page_tables.ownership.receipts.held_extent extents count a s ⦃ o =>
      o.map (·.val) = (extents.val.take count.val).findIdx? (fun x =>
        x.range.start == a.range.start && x.range.len == a.range.len &&
          (holdingOf x.holding == .held (word64 a.owner) (word64 a.generation) (holdStateOf s))) ⦄ := by
  unfold page_tables.ownership.receipts.held_extent page_tables.ownership.receipts.held_extent_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => count.val - i.val)
    (inv := fun (i : Usize) => i.val ≤ count.val ∧
      (((extents.val.take count.val).drop i.val).findIdx? (fun x =>
        x.range.start == a.range.start && x.range.len == a.range.len &&
          (holdingOf x.holding == .held (word64 a.owner) (word64 a.generation) (holdStateOf s)))).map
          (· + i.val) =
      (extents.val.take count.val).findIdx? (fun x =>
        x.range.start == a.range.start && x.range.len == a.range.len &&
          (holdingOf x.holding == .held (word64 a.owner) (word64 a.generation) (holdStateOf s))))
  · rintro i ⟨hle, hinv⟩
    generalize hP : (fun x : page_tables.Extent =>
        x.range.start == a.range.start && x.range.len == a.range.len &&
          (holdingOf x.holding == .held (word64 a.owner) (word64 a.generation) (holdStateOf s))) = P
      at hinv ⊢
    unfold page_tables.ownership.receipts.held_extent_loop.body
    step*
    · have hi : i.val < (extents.val.take count.val).length := by simp; scalar_tac
      have hp : P (extents.val.take count.val)[i.val] = true := by
        rw [← hP, List.getElem_take, ← extent_post]
        simp only [‹extent.range.start = a.range.start›, ‹extent.range.len = a.range.len›,
          beq_self_eq_true, Bool.true_and, ← b_post, ‹b = true›]
      rw [← hinv, receipt_findIdx_drop hi]
      simp only [hp, ↓reduceIte, Option.map_some]
    · have hi : i.val < (extents.val.take count.val).length := by simp; scalar_tac
      have hp : P (extents.val.take count.val)[i.val] = false := by
        rw [← hP, List.getElem_take, ← extent_post]
        simp only [‹extent.range.start = a.range.start›, ‹extent.range.len = a.range.len›,
          beq_self_eq_true, Bool.true_and, ← b_post]
        simpa using ‹¬b = true›
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, receipt_findIdx_drop hi, index1_post]
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
    · have hi : i.val < (extents.val.take count.val).length := by simp; scalar_tac
      have hp : P (extents.val.take count.val)[i.val] = false := by
        rw [← hP, List.getElem_take, ← extent_post]
        simp [‹¬extent.range.len = a.range.len›]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, receipt_findIdx_drop hi, index1_post]
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
    · have hi : i.val < (extents.val.take count.val).length := by simp; scalar_tac
      have hp : P (extents.val.take count.val)[i.val] = false := by
        rw [← hP, List.getElem_take, ← extent_post]
        simp [‹¬extent.range.start = a.range.start›]
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, receipt_findIdx_drop hi, index1_post]
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
    · rw [← hinv, receipt_findIdx_drop_end (by simp; scalar_tac)]; rfl
  · simp

/-- The test of the search of the code on an extent is that of `findHeld` on
the extent that it stands for, for a value of the owner identity. -/
theorem receipt_held_test_eq {x : page_tables.Extent} {X : Extent} (hx : ExtentRepr x X)
    {a : page_tables.Allocation} {A : Allocation} (hA : AllocationRepr a A) {owner : U64}
    (ho : a.owner = owner) (s : page_tables.HoldState) :
    (x.range.start == a.range.start && x.range.len == a.range.len &&
      (holdingOf x.holding == .held (word64 a.owner) (word64 a.generation) (holdStateOf s))) =
    (X.range == A.range && X.holding == .held (word64 owner) A.generation (holdStateOf s)) := by
  obtain ⟨⟨hs, hl⟩, -, hh⟩ := hx
  obtain ⟨-, -, hg, ⟨has, hal⟩⟩ := hA
  rw [receipt_range_beq, hs, hl, has, hal, hh, hg, ho, receipt_word64_beq, receipt_word64_beq]

/-- The search of the code on extents that stand for the extents of a table
finds the index that the search of `findHeld` finds, for a value whose owner
identity is that of the call. -/
theorem receipt_held_findIdx_eq {l : List page_tables.Extent} {L : List Extent}
    (h : ListRel ExtentRepr l L) {a : page_tables.Allocation} {A : Allocation}
    (hA : AllocationRepr a A) {owner : U64} (ho : a.owner = owner) (s : page_tables.HoldState) :
    l.findIdx? (fun x => x.range.start == a.range.start && x.range.len == a.range.len &&
      (holdingOf x.holding == .held (word64 a.owner) (word64 a.generation) (holdStateOf s))) =
    L.findIdx? (fun X => X.range == A.range &&
      X.holding == .held (word64 owner) A.generation (holdStateOf s)) :=
  by refine receipt_findIdx_eq ?_ h; intro x X hx; exact receipt_held_test_eq hx hA ho s

/-- `Ownership::find_held(owner, allocation, state)` on a table that stands
for a table and a value that stands for an allocation: the error of
`Ownership.findHeld`, or the index of the extent that it finds, the number
of extents before it. -/
theorem find_held_spec {E X : Usize} (t : page_tables.Ownership E X) (T : Ownership E.val X.val)
    (owner : U64) (a : page_tables.Allocation) (A : Allocation) (s : page_tables.HoldState)
    (hT : OwnershipRepr t T) (hA : AllocationRepr a A) :
    page_tables.ownership.receipts.Ownership.find_held t owner a s ⦃ r =>
      Agrees (fun i f => f.1.length = i.val) ownershipErrorOf r
        (T.findHeld (word64 owner) A (holdStateOf s)) ⦄ := by
  have hT' := hT
  obtain ⟨-, hc, -, harena, -, hext, -, -⟩ := hT'
  have hA' := hA
  obtain ⟨ha1, ha2, -, -⟩ := hA'
  unfold page_tables.ownership.receipts.Ownership.find_held
  step*
  · have h : A.arena ≠ T.arena := by
      rw [ha1, harena, ne_eq, word64_inj, ← ne_eq, ← bne_iff_ne]; exact ‹(a.arena != t.arena) = true›
    rw [receipt_findHeld_arena h]; rfl
  · have h1 : A.arena = T.arena := by
      rw [ha1, harena, word64_inj]; exact receipt_not_bne_iff.1 ‹_›
    have h2 : A.owner ≠ word64 owner := by
      rw [ha2, ne_eq, word64_inj, ← ne_eq, ← bne_iff_ne]; exact ‹(a.owner != owner) = true›
    rw [receipt_findHeld_owner h1 h2]; rfl
  · have h1 : A.arena = T.arena := by
      rw [ha1, harena, word64_inj]; exact receipt_not_bne_iff.1 ‹_›
    have ho : a.owner = owner := by
      exact receipt_not_bne_iff.1 ‹_›
    have h2 : A.owner = word64 owner := by rw [ha2, ho]
    have hf := o_post
    rw [‹o = none›, receipt_held_findIdx_eq hext hA ho s] at hf
    rw [receipt_findHeld_none h1 h2 hf.symm]; rfl
  · have h1 : A.arena = T.arena := by
      rw [ha1, harena, word64_inj]; exact receipt_not_bne_iff.1 ‹_›
    have ho : a.owner = owner := by
      exact receipt_not_bne_iff.1 ‹_›
    have h2 : A.owner = word64 owner := by rw [ha2, ho]
    have hf := o_post
    rw [‹o = some index›, receipt_held_findIdx_eq hext hA ho s] at hf
    obtain ⟨b, e, a', heq, hl⟩ := receipt_findHeld_some h1 h2 hf.symm
    rw [heq]; exact hl

/-- What the extent that `findHeld` finds tells about the table of the code:
its index is below the count, the extents of the table are around it, and
the extent of the code at its index stands for it. -/
theorem receipt_found_repr {E X : Usize} {t : page_tables.Ownership E X} {T : Ownership E.val X.val}
    (hT : OwnershipRepr t T) {o : UInt64} {A : Allocation} {s : HoldState}
    {before after : List Extent} {e : Extent} {k : Nat}
    (hf : T.findHeld o A s = .ok (before, e, after)) (hk : before.length = k) :
    k < t.extent_count.val ∧ T.extents = before.reverse ++ e :: after ∧
      ∀ h : k < t.extents.val.length, ExtentRepr t.extents.val[k] e := by
  obtain ⟨-, -, hx, -⟩ := findHeld_ok hf
  have hl := ownershipRepr_extents_length hT
  have hlt : k < t.extent_count.val := by rw [← hl, hx]; simp; omega
  refine ⟨hlt, hx, fun h => ?_⟩
  obtain ⟨-, -, -, -, -, hext, -, -⟩ := hT
  have := receipt_listRel_getElem? hext k
  rw [hx, ← hk, receipt_getElem?_found, hk, List.getElem?_take_of_lt hlt,
    List.getElem?_eq_getElem h] at this
  exact this

/-- `Ownership::validate(owner, allocation, state)`: the statement
`OwnershipValidate` without its premises `Usize64` and
`Ownership.Invariant`. -/
theorem ownership_validate_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (owner : U64) (allocation : page_tables.Allocation) (A : Allocation)
    (state : page_tables.HoldState) (hT : OwnershipRepr t T) (hA : AllocationRepr allocation A) :
    page_tables.ownership.receipts.Ownership.validate t owner allocation state ⦃ r =>
      Agrees (fun _ _ => True) ownershipErrorOf r (T.validate (word64 owner) A (holdStateOf state)) ⦄ := by
  unfold page_tables.ownership.receipts.Ownership.validate
  step with find_held_spec t T owner allocation A state hT hA as ⟨r, hr⟩
  step*
  · obtain ⟨b, hb, -⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› hr)
    simp only [Ownership.validate, hb, Except.map, agrees_ok_ok]
  · rw [Ownership.validate, agrees_err_of_branch cf_post ‹_› residual_post hr, r_post, ← e_post]
    rfl

/-- `joins(a, b)`: whether both extents are free, of one bank, and `a` ends
where `b` starts, for an `a` whose end fits in 64 bits. -/
@[step] theorem joins_spec (a b : page_tables.Extent)
    (h : a.range.start.val + a.range.len.val < 2 ^ 64) :
    page_tables.ownership.receipts.joins a b ⦃ r =>
      r = decide (holdingOf a.holding = .free ∧ holdingOf b.holding = .free ∧
        a.bank.val = b.bank.val ∧ a.range.start.val + a.range.len.val = b.range.start.val) ⦄ := by
  unfold page_tables.ownership.receipts.joins
  step*

/-- `close_gap(extents, count, index, by)`: for `index + by ≤ count` and
`count` within the array, the first `count - by` extents are those below
`index` and those of `[index + by, count)`. The loop keeps the extents below
`index` and from its cursor `at` as they were, and those of `[index, at)` the
extents `by` later. -/
@[step] theorem close_gap_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count index gap : Usize) (h1 : index.val + gap.val ≤ count.val) (h2 : count.val ≤ E.val) :
    page_tables.ownership.receipts.close_gap extents count index gap ⦃ r =>
      r.val.take (count.val - gap.val) =
        extents.val.take index.val ++ (extents.val.take count.val).drop (index.val + gap.val) ⦄ := by
  unfold page_tables.ownership.receipts.close_gap page_tables.ownership.receipts.close_gap_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Aeneas.Std.Array page_tables.Extent E × Usize) => count.val - p.2.val)
    (inv := fun p => index.val ≤ p.2.val ∧ p.2.val + gap.val ≤ count.val ∧
      ∀ j, p.1.val[j]? = if j < index.val ∨ p.2.val ≤ j then extents.val[j]?
        else extents.val[j + gap.val]?)
  · rintro ⟨arr, at'⟩ ⟨hle, hlt, hinv⟩
    simp only at hle hlt hinv
    unfold page_tables.ownership.receipts.close_gap_loop.body
    step*
    · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have hx : arr.val[at'.val + gap.val]? = some e := by
        rw [e_post, ← i_post]; exact List.getElem?_eq_getElem _
      rw [a_post, Array.set_val_eq, at1_post]
      exact receipt_gap_step (by simp) hle (by simp; scalar_tac) hinv e hx
    · exact receipt_gap_done hle (by scalar_tac) (by simp; scalar_tac) hinv
  · refine ⟨le_refl _, h1, fun j => ?_⟩
    dsimp only
    split <;> first | rfl | omega

/-- The freed extent of the code stands for the freed extent. -/
theorem receipt_freed_repr {x : page_tables.Extent} {X : Extent} (h : ExtentRepr x X) :
    ExtentRepr { range := x.range, bank := x.bank, holding := page_tables.Holding.Free }
      { X with holding := .free } :=
  ⟨h.1, h.2.1, rfl⟩

/-- The test of `joins` on extents that stand for extents is `ExtentsJoin`. -/
theorem receipt_joins_iff {a b : page_tables.Extent} {A B : Extent} (ha : ExtentRepr a A)
    (hb : ExtentRepr b B) :
    (holdingOf a.holding = .free ∧ holdingOf b.holding = .free ∧ a.bank.val = b.bank.val ∧
      a.range.start.val + a.range.len.val = b.range.start.val) ↔ ExtentsJoin A B := by
  obtain ⟨hra, hba, hha⟩ := ha
  obtain ⟨hrb, hbb, hhb⟩ := hb
  rw [ExtentsJoin, hha, hhb, hba, hbb, physRange_endNat hra, physRange_start hrb]

/-- The extent that `merge_freed` writes at `first` stands for the free extent
of `mergeFreed`. -/
theorem receipt_merged_repr {f : page_tables.Extent} {X m : Extent} {len : U64}
    (hf : ExtentRepr f X) (hX : X.holding = .free) (hm : m.holding = .free) (hb : X.bank = m.bank)
    (hs : X.range.start.toNat = m.range.start.toNat)
    (he : m.range.endNat = f.range.start.val + len.val) :
    ExtentRepr (⟨⟨f.range.start, len⟩, f.bank, f.holding⟩ : page_tables.Extent) m := by
  obtain ⟨⟨h1, -⟩, h3, h4⟩ := hf
  have hs' : m.range.start.toNat = f.range.start.val := by rw [← hs, h1, word64_toNat]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply UInt64.toNat_inj.1; rw [word64_toNat, hs']
  · apply UInt64.toNat_inj.1; rw [word64_toNat]; show m.range.len.toNat = len.val
    unfold PhysRange.endNat at he; omega
  · rw [← hb, h3]
  · rw [hm, ← h4, hX]

/-- The extents of the code with the extent at `index` freed stand for the
extents with the extent found freed. -/
theorem receipt_freed_listRel {E : Usize} {extents : Aeneas.Std.Array page_tables.Extent E}
    {count index : Usize} {before after : List Extent} {ex : Extent}
    (hrel : ListRel ExtentRepr (extents.val.take count.val) (before.reverse ++ ex :: after))
    (hb : before.length = index.val) {x : page_tables.Extent} {X : Extent} (hx : ExtentRepr x X) :
    ListRel ExtentRepr ((extents.set index x).val.take count.val) (before.reverse ++ X :: after) := by
  rw [Array.set_val_eq, List.take_set, ← hb, ← receipt_set_found before after ex X]
  exact receipt_listRel_set hrel _ hx

/-- The extent of the code at an index below `count` stands for the extent
at that index of the list that the first `count` extents stand for. -/
theorem receipt_at_repr {E : Usize} {ext1 : Aeneas.Std.Array page_tables.Extent E} {count : Usize}
    {Ls : List Extent} (h : ListRel ExtentRepr (ext1.val.take count.val) Ls) {j : Nat}
    (hj : j < count.val) {X : Extent} (hX : Ls[j]? = some X) :
    ∀ hl : j < ext1.val.length, ExtentRepr ext1.val[j] X := by
  intro hl
  obtain ⟨Y, hY, hr⟩ := receipt_listRel_at h hj hl
  rw [hX, Option.some.injEq] at hY
  subst hY; exact hr

/-- The extents and the count after the gap of `merge_freed` is closed, from
the block `[first, last]` that it replaces (the left and right cases of
`receipt_mergeFreed_shape`), the extent `e5` that it reads at `first` and
the length `i3` that it writes there, which ends where the extent at `last`
ends. -/
theorem receipt_merge_final {E : Usize} {ext1 : Aeneas.Std.Array page_tables.Extent E}
    {count first last i4 i5 n : Usize} {i3 : U64} {before after : List Extent} {ex : Extent}
    {r : Aeneas.Std.Array page_tables.Extent E} {e5 : page_tables.Extent}
    (hrel1 : ListRel ExtentRepr (ext1.val.take count.val)
      (before.reverse ++ { ex with holding := .free } :: after))
    (hL : (∀ x, before.head? = some x → ExtentsJoin x { ex with holding := .free } →
        first.val + 1 = before.length) ∧
      ((∀ x, before.head? = some x → ¬ ExtentsJoin x { ex with holding := .free }) →
        first.val = before.length))
    (hR : (∀ y, after.head? = some y → ExtentsJoin { ex with holding := .free } y →
        last.val = before.length + 1) ∧
      ((∀ y, after.head? = some y → ¬ ExtentsJoin { ex with holding := .free } y) →
        last.val = before.length))
    (hfl : first.val ≤ last.val) (hlc : last.val < count.val) (hc : count.val ≤ E.val)
    (he5 : ∀ h : first.val < ext1.val.length, e5 = ext1.val[first.val])
    (hi3 : ∀ h : last.val < ext1.val.length, i3.val + e5.range.start.val =
      (ext1.val[last.val]).range.start.val + (ext1.val[last.val]).range.len.val)
    (hi4 : i4.val = first.val + 1) (hi5 : i5.val = last.val - first.val)
    (hr : r.val.take (count.val - i5.val) =
      (ext1.set first ⟨⟨e5.range.start, i3⟩, e5.bank, e5.holding⟩).val.take i4.val ++
        ((ext1.set first ⟨⟨e5.range.start, i3⟩, e5.bank, e5.holding⟩).val.take count.val).drop
          (i4.val + i5.val))
    (hn : n.val = count.val - i5.val) :
    n.val ≤ E.val ∧ ListRel ExtentRepr (r.val.take n.val) (mergeFreed before ex after) := by
  have hlen : ext1.val.length = E.val := by simp
  have hc' := hc
  obtain ⟨m, hm, hm1, hX, hY⟩ := receipt_mergeFreed_shape hL.1 hL.2 hR.1 hR.2
  obtain ⟨X, hXs, hXr⟩ := receipt_listRel_at (j := first.val) hrel1 (by omega) (by omega)
  obtain ⟨Y, hYs, hYr⟩ := receipt_listRel_at (j := last.val) hrel1 (by omega) (by omega)
  obtain ⟨hX1, hX2, hX3⟩ := hX X hXs
  have hY1 := hY Y hYs
  have hXr' : ExtentRepr e5 X := by rw [he5 (by omega)]; exact hXr
  have h3 := hi3 (by omega)
  have hmr : ExtentRepr (⟨⟨e5.range.start, i3⟩, e5.bank, e5.holding⟩ : page_tables.Extent) m :=
    receipt_merged_repr hXr' hX1 hm1 hX2 hX3 (by rw [← hY1, physRange_endNat hYr.1]; omega)
  refine ⟨by omega, ?_⟩
  rw [hn, hr, hm, Array.set_val_eq, hi4, show first.val + 1 + i5.val = last.val + 1 by omega]
  exact receipt_listRel_replace hrel1 hfl hlc (by omega) hmr

/-- The end of an extent of the code at an index below `count` fits in 64
bits, for extents that stand for extents. -/
theorem receipt_at_fits {E : Usize} {ext1 : Aeneas.Std.Array page_tables.Extent E} {count : Usize}
    {Ls : List Extent} (h : ListRel ExtentRepr (ext1.val.take count.val) Ls) {j : Nat}
    (hj : j < count.val) (hl : j < ext1.val.length) :
    (ext1.val[j]).range.start.val + (ext1.val[j]).range.len.val < 2 ^ 64 := by
  obtain ⟨X, -, hX⟩ := receipt_listRel_at h hj hl
  exact physRange_fits hX.1

/-- The extent at `first` starts below the end of the extent at `last`, for
the block `[first, last]` of `mergeFreed`. -/
theorem receipt_merge_order {E : Usize} {ext1 : Aeneas.Std.Array page_tables.Extent E} {count : Usize}
    {first last : Nat} {before after : List Extent} {ex : Extent}
    (hrel1 : ListRel ExtentRepr (ext1.val.take count.val)
      (before.reverse ++ { ex with holding := .free } :: after))
    (hL : (∀ x, before.head? = some x → ExtentsJoin x { ex with holding := .free } →
        first + 1 = before.length) ∧
      ((∀ x, before.head? = some x → ¬ ExtentsJoin x { ex with holding := .free }) →
        first = before.length))
    (hR : (∀ y, after.head? = some y → ExtentsJoin { ex with holding := .free } y →
        last = before.length + 1) ∧
      ((∀ y, after.head? = some y → ¬ ExtentsJoin { ex with holding := .free } y) →
        last = before.length))
    (hfc : first < count.val) (hlc : last < count.val) (h1 : first < ext1.val.length)
    (h2 : last < ext1.val.length) :
    (ext1.val[first]).range.start.val <
      (ext1.val[last]).range.start.val + (ext1.val[last]).range.len.val := by
  obtain ⟨m, -, -, hX, hY⟩ := receipt_mergeFreed_shape hL.1 hL.2 hR.1 hR.2
  obtain ⟨X, hXs, hXr⟩ := receipt_listRel_at hrel1 hfc h1
  obtain ⟨Y, hYs, hYr⟩ := receipt_listRel_at hrel1 hlc h2
  rw [← physRange_start hXr.1, ← physRange_endNat hYr.1, (hX X hXs).2.2, hY Y hYs]
  exact range_lt m.range

/-- The end of `merge_freed` after an extent before the freed one: from the
block `[first, last]` of `mergeFreed` (the left and right cases of
`receipt_mergeFreed_shape`), with `first ≤ last < count` and `count` within
the array, the extent at `first` is written to end where the one at `last`
ends and the gap after it is closed. -/
theorem receipt_merge_tail_spec {E : Usize} (ext1 : Aeneas.Std.Array page_tables.Extent E)
    (count first last : Usize) (before after : List Extent) (ex : Extent)
    (hc : count.val ≤ E.val)
    (hrel1 : ListRel ExtentRepr (ext1.val.take count.val)
      (before.reverse ++ { ex with holding := .free } :: after))
    (hL : (∀ x, before.head? = some x → ExtentsJoin x { ex with holding := .free } →
        first.val + 1 = before.length) ∧
      ((∀ x, before.head? = some x → ¬ ExtentsJoin x { ex with holding := .free }) →
        first.val = before.length))
    (hR : (∀ y, after.head? = some y → ExtentsJoin { ex with holding := .free } y →
        last.val = before.length + 1) ∧
      ((∀ y, after.head? = some y → ¬ ExtentsJoin { ex with holding := .free } y) →
        last.val = before.length))
    (hfl : first.val ≤ last.val) (hl2 : last.val < count.val) :
    (do
      let e3 ← Array.index_usize ext1 last
      let i2 ← page_tables.range.PhysRange.end e3.range
      let e4 ← Array.index_usize ext1 first
      let i3 ← i2 - e4.range.start
      let (e5, index_mut_back1) ← Array.index_mut_usize ext1 first
      let i4 ← first + 1#usize
      let i5 ← last - first
      let extents3 ←
        page_tables.ownership.receipts.close_gap
          (index_mut_back1
            { range := { start := e5.range.start, len := i3 }, bank := e5.bank, holding := e5.holding })
          count i4 i5
      let i6 ← count - i5
      ok (i6, extents3)) ⦃ n a =>
      n.val ≤ E.val ∧ ListRel ExtentRepr (a.val.take n.val) (mergeFreed before ex after) ⦄ := by
  step*
  · rw [e3_post]; exact receipt_at_fits hrel1 hl2 _
  · rw [i2_post, e4_post, e3_post]
    exact Nat.le_of_lt (receipt_merge_order hrel1 hL hR (by omega) hl2 _ _)
  · subst index_mut_back1_post
    have h45 : e4 = e5 := by rw [e4_post, e5_post]
    exact receipt_merge_final hrel1 hL hR i5_post1 hl2 hc (fun _ => e5_post)
      (fun _ => by rw [← h45, i3_post, ← e3_post]; omega) i4_post i5_post extents3_post i6_post

/-- The index `last` that `merge_freed` computes after an extent before the
freed one, at `index` below `count`: `index + 1` when an extent follows the
freed one, which stands for its freed extent, and joins it, `index`
otherwise, as the right cases of `receipt_mergeFreed_shape` ask. -/
theorem receipt_merge_last_spec {E : Usize} (ext1 : Aeneas.Std.Array page_tables.Extent E)
    (count index i1 : Usize) (e2 : page_tables.Extent) (before after : List Extent) (ex : Extent)
    (hrel1 : ListRel ExtentRepr (ext1.val.take count.val)
      (before.reverse ++ { ex with holding := .free } :: after))
    (hb : before.length = index.val) (hi : index.val < count.val) (hc : count.val ≤ E.val)
    (hLs : count.val = before.length + (after.length + 1))
    (hi1 : i1.val = index.val + 1) (he2 : ExtentRepr e2 { ex with holding := .free }) :
    (if i1 < count then do
        let e3 ← Array.index_usize ext1 i1
        let b1 ← page_tables.ownership.receipts.joins e2 e3
        if b1 = true then ok i1 else ok index
      else ok index) ⦃ last =>
      (∀ y, after.head? = some y → ExtentsJoin { ex with holding := .free } y →
          last.val = before.length + 1) ∧
        ((∀ y, after.head? = some y → ¬ ExtentsJoin { ex with holding := .free } y) →
          last.val = before.length) ∧ index.val ≤ last.val ∧ last.val < count.val ⦄ := by
  have hfit2 : e2.range.start.val + e2.range.len.val < 2 ^ 64 := physRange_fits he2.1
  by_cases h1 : i1 < count
  · simp only [h1, ↓reduceIte]
    have h1' : i1.val < count.val := h1
    have ha0 : 0 < after.length := by omega
    obtain ⟨yr, hy⟩ : ∃ yr, after.head? = some yr := by
      cases after with
      | nil => simp at ha0
      | cons z zs => exact ⟨z, rfl⟩
    step as ⟨e3, e3_post⟩
    have he3 : ExtentRepr e3 yr := by
      rw [e3_post]
      exact receipt_at_repr hrel1 (j := i1.val) h1'
        (by rw [hi1, ← hb, receipt_getElem?_after, hy]) _
    have hjr := receipt_joins_iff he2 he3
    step as ⟨b1, b1_post⟩
    by_cases hb1 : b1 = true
    · simp only [hb1, ↓reduceIte]
      have hd := hb1
      rw [b1_post] at hd
      have hR := receipt_right_join (k := before.length) (last := i1.val) hy
        (hjr.1 (of_decide_eq_true hd)) (by omega)
      exact spec_of_eq rfl ⟨hR.1, hR.2, by omega, h1'⟩
    · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
      have hd := hb1
      rw [b1_post] at hd
      have hR := receipt_right_apart (k := before.length) (last := index.val) hy
        (fun h => hd (decide_eq_true (hjr.2 h))) hb.symm
      exact spec_of_eq rfl ⟨hR.1, hR.2, le_refl _, hi⟩
  · simp only [h1, ↓reduceIte]
    have h1' : ¬ i1.val < count.val := h1
    have ha0 : after = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hR := receipt_right_nil (F := { ex with holding := .free }) (k := before.length)
      (last := index.val) ha0 hb.symm
    exact spec_of_eq rfl ⟨hR.1, hR.2, le_refl _, hi⟩

/-- The end of `merge_freed` when the freed extent is the first: the end
of `receipt_merge_tail_spec` with `first = index`, for `e1` the extent at
`index` and `i = index + 1`. -/
theorem receipt_merge_tail_first_spec {E : Usize} (ext1 : Aeneas.Std.Array page_tables.Extent E)
    (count index last i : Usize) (e1 : page_tables.Extent) (before after : List Extent)
    (ex : Extent) (hc : count.val ≤ E.val)
    (hrel1 : ListRel ExtentRepr (ext1.val.take count.val)
      (before.reverse ++ { ex with holding := .free } :: after))
    (hL : (∀ x, before.head? = some x → ExtentsJoin x { ex with holding := .free } →
        index.val + 1 = before.length) ∧
      ((∀ x, before.head? = some x → ¬ ExtentsJoin x { ex with holding := .free }) →
        index.val = before.length))
    (hR : (∀ y, after.head? = some y → ExtentsJoin { ex with holding := .free } y →
        last.val = before.length + 1) ∧
      ((∀ y, after.head? = some y → ¬ ExtentsJoin { ex with holding := .free } y) →
        last.val = before.length))
    (hl1 : index.val ≤ last.val) (hl2 : last.val < count.val) (hi : i.val = index.val + 1)
    (he1 : ∀ h : index.val < ext1.val.length, e1 = ext1.val[index.val]) :
    (do
      let e3 ← Array.index_usize ext1 last
      let i1 ← page_tables.range.PhysRange.end e3.range
      let i2 ← i1 - e1.range.start
      let (e4, index_mut_back1) ← Array.index_mut_usize ext1 index
      let i3 ← last - index
      let extents3 ←
        page_tables.ownership.receipts.close_gap
          (index_mut_back1
            { range := { start := e4.range.start, len := i2 }, bank := e4.bank, holding := e4.holding })
          count i i3
      let i4 ← count - i3
      ok (i4, extents3)) ⦃ n a =>
      n.val ≤ E.val ∧ ListRel ExtentRepr (a.val.take n.val) (mergeFreed before ex after) ⦄ := by
  have hlen : ext1.val.length = E.val := by simp
  step*
  · rw [e3_post]; exact receipt_at_fits hrel1 hl2 _
  · rw [i1_post, he1 (by omega), e3_post]
    exact Nat.le_of_lt (receipt_merge_order hrel1 hL hR (by omega) hl2 _ _)
  · subst index_mut_back1_post
    have h14 : e1 = e4 := by rw [he1 (by omega), e4_post]
    exact receipt_merge_final (first := index) hrel1 hL hR hl1 hl2 hc (fun _ => e4_post)
      (fun _ => by rw [← h14, i2_post, ← e3_post]; omega) hi i3_post extents3_post i4_post

/-- `merge_freed(extents, count, index)`: for `index < count` within the
array, with the first `count` extents standing for `before.reverse ++ ex ::
after` and `index` the length of `before`, the new count is within the
array and the extents below it stand for `mergeFreed before ex after`. -/
theorem merge_freed_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count index : Usize) (before after : List Extent) (ex : Extent)
    (hc : count.val ≤ E.val) (hi : index.val < count.val)
    (hrel : ListRel ExtentRepr (extents.val.take count.val) (before.reverse ++ ex :: after))
    (hb : before.length = index.val) :
    page_tables.ownership.receipts.merge_freed extents count index ⦃ n a =>
      n.val ≤ E.val ∧ ListRel ExtentRepr (a.val.take n.val) (mergeFreed before ex after) ⦄ := by
  have hlen : extents.val.length = E.val := by simp
  have hLs := listRel_length hrel
  simp only [List.length_take, List.length_append, List.length_reverse, List.length_cons] at hLs
  obtain ⟨X0, hX0, hrX0⟩ := receipt_listRel_at hrel hi (by omega)
  rw [← hb, receipt_getElem?_found, Option.some.injEq] at hX0
  subst hX0
  have hrel1 := receipt_freed_listRel hrel hb (receipt_freed_repr hrX0)
  unfold page_tables.ownership.receipts.merge_freed
  step*
  · subst e_post index_mut_back_post
    rw [e1_post]; exact receipt_at_fits hrel1 (by scalar_tac) _
  · -- an extent before the freed one
    subst e_post index_mut_back_post
    have hk0 : 0 < before.length := by scalar_tac
    obtain ⟨xl, hx⟩ : ∃ xl, before.head? = some xl := by
      cases before with
      | nil => simp at hk0
      | cons z zs => exact ⟨z, rfl⟩
    have he1 : ExtentRepr e1 xl := by
      rw [e1_post]
      exact receipt_at_repr hrel1 (j := i.val) (by scalar_tac)
        (by rw [i_post, ← hb, receipt_getElem?_before after _ hk0, hx]) _
    have he2 : ExtentRepr e2 { ex with holding := .free } := by
      rw [e2_post]
      exact receipt_at_repr hrel1 (j := index.val) (by scalar_tac)
        (receipt_getElem?_freed _ _ _ _ hb.symm) _
    have hjl : b = true ↔ ExtentsJoin xl { ex with holding := .free } := by
      rw [b_post, decide_eq_true_iff]; exact receipt_joins_iff he1 he2
    apply spec_bind (Pₘ := fun first : Usize =>
      (∀ x, before.head? = some x → ExtentsJoin x { ex with holding := .free } →
          first.val + 1 = before.length) ∧
        ((∀ x, before.head? = some x → ¬ ExtentsJoin x { ex with holding := .free }) →
          first.val = before.length) ∧ first.val ≤ index.val)
    · by_cases hbv : b = true
      · simp only [hbv, ↓reduceIte]
        have hL := receipt_left_join (first := i.val) hx (hjl.1 hbv) (by scalar_tac)
        exact spec_of_eq rfl ⟨hL.1, hL.2, by scalar_tac⟩
      · simp only [hbv, Bool.false_eq_true, ↓reduceIte]
        have hL := receipt_left_apart (first := index.val) hx (fun h => hbv (hjl.2 h)) hb.symm
        exact spec_of_eq rfl ⟨hL.1, hL.2, le_refl _⟩
    · rintro first ⟨hL1, hL2, hf1⟩
      step as ⟨i1, i1_post⟩
      apply spec_bind (Pₘ := fun last : Usize =>
        (∀ y, after.head? = some y → ExtentsJoin { ex with holding := .free } y →
            last.val = before.length + 1) ∧
          ((∀ y, after.head? = some y → ¬ ExtentsJoin { ex with holding := .free } y) →
            last.val = before.length) ∧ index.val ≤ last.val ∧ last.val < count.val)
      · exact receipt_merge_last_spec _ count index i1 e2 before after ex hrel1 hb hi hc (by omega)
          (by scalar_tac) he2
      · rintro last ⟨hR1, hR2, hl1, hl2⟩
        exact receipt_merge_tail_spec _ count first last before after ex hc hrel1 ⟨hL1, hL2⟩ ⟨hR1, hR2⟩
          (by omega) hl2
  · subst e_post index_mut_back_post
    rw [e1_post]; exact receipt_at_fits hrel1 hi _
  · -- the first extent, with an extent after it
    subst e_post index_mut_back_post
    have hk0 : before = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    have he1 : ExtentRepr e1 { ex with holding := .free } := by
      rw [e1_post]
      exact receipt_at_repr hrel1 (j := index.val) hi (receipt_getElem?_freed _ _ _ _ hb.symm) _
    have ha0 : 0 < after.length := by scalar_tac
    obtain ⟨yr, hy⟩ : ∃ yr, after.head? = some yr := by
      cases after with
      | nil => simp at ha0
      | cons z zs => exact ⟨z, rfl⟩
    have he2 : ExtentRepr e2 yr := by
      rw [e2_post]
      exact receipt_at_repr hrel1 (j := i.val) (by scalar_tac)
        (by rw [i_post, ← hb, receipt_getElem?_after, hy]) _
    have hjr := receipt_joins_iff he1 he2
    have hL := receipt_left_nil (F := { ex with holding := .free }) (first := index.val) hk0 hb.symm
    apply spec_bind (Pₘ := fun last : Usize =>
      (∀ y, after.head? = some y → ExtentsJoin { ex with holding := .free } y →
          last.val = before.length + 1) ∧
        ((∀ y, after.head? = some y → ¬ ExtentsJoin { ex with holding := .free } y) →
          last.val = before.length) ∧ index.val ≤ last.val ∧ last.val < count.val)
    · by_cases hbv : b = true
      · simp only [hbv, ↓reduceIte]
        have hd := hbv
        rw [b_post] at hd
        have hR := receipt_right_join (k := before.length) (last := i.val) hy
          (hjr.1 (of_decide_eq_true hd)) (by scalar_tac)
        exact spec_of_eq rfl ⟨hR.1, hR.2, by scalar_tac, by scalar_tac⟩
      · simp only [hbv, Bool.false_eq_true, ↓reduceIte]
        have hd := hbv
        rw [b_post] at hd
        have hR := receipt_right_apart (k := before.length) (last := index.val) hy
          (fun h => hd (decide_eq_true (hjr.2 h))) hb.symm
        exact spec_of_eq rfl ⟨hR.1, hR.2, le_refl _, hi⟩
    · rintro last ⟨hR1, hR2, hl1, hl2⟩
      exact receipt_merge_tail_first_spec _ count index last i e1 before after ex hc hrel1 hL ⟨hR1, hR2⟩
        hl1 hl2 i_post (fun _ => e1_post)
  · subst e_post index_mut_back_post
    rw [e1_post]; exact receipt_at_fits hrel1 hi _
  · -- the only extent after the first ones
    subst e_post index_mut_back_post
    have hk0 : before = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    have ha0 : after = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
    have hL := receipt_left_nil (F := { ex with holding := .free }) (first := index.val) hk0 hb.symm
    have hR := receipt_right_nil (F := { ex with holding := .free }) (k := before.length)
      (last := index.val) ha0 hb.symm
    subst index_mut_back1_post
    have h12 : e1 = e2 := by rw [e1_post, e2_post]
    exact receipt_merge_final (first := index) (last := index) hrel1 hL hR (le_refl _) hi hc
      (fun _ => e2_post) (fun _ => by rw [← h12, i2_post, i1_post, ← e1_post]; omega) i_post
      i3_post extents3_post i4_post



/-- A table of the code whose extents and count change stands for the table
with the extents that they stand for. -/
theorem receipt_ownershipRepr_with_extents {E X : Usize} {t : page_tables.Ownership E X}
    {T : Ownership E.val X.val} (hT : OwnershipRepr t T)
    {a : Aeneas.Std.Array page_tables.Extent E} {n : Usize} {L : List Extent}
    (hn : n.val ≤ E.val) (h : ListRel ExtentRepr (a.val.take n.val) L) :
    OwnershipRepr { t with extents := a, extent_count := n } { T with extents := L } := by
  obtain ⟨h1, -, h3, h4, h5, -, h7, h8⟩ := hT
  exact ⟨h1, hn, h3, h4, h5, h, h7, h8⟩

/-- `Ownership::publish(owner, packet)`: the statement `OwnershipPublish`
without its premises `Usize64` and `Ownership.Invariant`. -/
theorem ownership_publish_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (owner : U64) (packet : page_tables.Initialized) (I : Initialized)
    (hT : OwnershipRepr t T) (hI : InitializedRepr packet I) :
    page_tables.ownership.receipts.Ownership.publish t owner packet ⦃ r t' =>
      Writes OwnershipRepr AllocationRepr
        (fun (e, x) (E, Y) => ownershipErrorOf e = E ∧ InitializedRepr x Y) t r t'
        (T.publish (word64 owner) I) ⦄ := by
  unfold page_tables.ownership.receipts.Ownership.publish
  step with find_held_spec t T owner packet.allocation I.allocation .Reserved hT hI.1 as ⟨r, hr⟩
  cases r with
  | Ok index =>
    obtain ⟨⟨before, ex, after⟩, hf, hl⟩ := agrees_ok_iff.mp hr
    have hf' : T.findHeld (word64 owner) I.allocation .reserved = .ok (before, ex, after) := hf
    obtain ⟨hk, hx, he⟩ := receipt_found_repr hT hf hl
    have hext : ListRel ExtentRepr (t.extents.val.take t.extent_count.val)
        (before.reverse ++ ex :: after) := by
      rw [← hx]; exact hT.2.2.2.2.2.1
    simp only
    step*
    simp only [Ownership.publish, hf', Writes]
    refine ⟨hI.1, receipt_ownershipRepr_with_extents hT hT.2.1 ?_⟩
    rw [index_mut_back_post, Array.set_val_eq, List.take_set, List.reverseAux_eq, ← hl,
      ← receipt_set_found before after ex]
    refine receipt_listRel_set hext _ ⟨?_, ?_, ?_⟩
    · rw [e_post]; exact (he _).1
    · rw [e_post]; exact (he _).2.1
    · simp only [holdingOf, holdStateOf, hI.1.2.2.1]
  | Err error =>
    have hf : T.findHeld (word64 owner) I.allocation .reserved = .error (ownershipErrorOf error) :=
      agrees_err_iff.mp hr
    simp only
    refine spec_of_eq rfl ?_
    simp only [Ownership.publish, hf, Writes]
    exact ⟨⟨rfl, hI⟩, rfl⟩

/-- `Ownership::release(owner, receipt)`: the statement `OwnershipRelease`
without its premises `Usize64` and `Ownership.Invariant`. -/
theorem ownership_release_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (owner : U64) (receipt : page_tables.Allocation) (A : Allocation)
    (hT : OwnershipRepr t T) (hA : AllocationRepr receipt A) :
    page_tables.ownership.receipts.Ownership.release t owner receipt ⦃ r t' =>
      Writes OwnershipRepr (fun _ _ => True) (ownershipErrorOf · = ·) t r t'
        ((T.release (word64 owner) A).map (·, ())) ⦄ := by
  unfold page_tables.ownership.receipts.Ownership.release
  step with find_held_spec t T owner receipt A .Published hT hA as ⟨r, hr⟩
  step*
  · obtain ⟨⟨before, ex, after⟩, hf, hl⟩ := agrees_ok_iff.mp (agrees_of_branch_ok cf_post ‹_› hr)
    have hf' : T.findHeld (word64 owner) A .published = .ok (before, ex, after) := hf
    obtain ⟨hk, hx, -⟩ := receipt_found_repr hT hf hl
    have hext : ListRel ExtentRepr (t.extents.val.take t.extent_count.val)
        (before.reverse ++ ex :: after) := by
      rw [← hx]; exact hT.2.2.2.2.2.1
    apply spec_bind (merge_freed_spec t.extents t.extent_count val before after ex hT.2.1 hk hext hl)
    rintro ⟨n, a⟩ ⟨hn, hrel'⟩
    refine spec_of_eq rfl ?_
    simp only [Ownership.release, hf', Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map,
      Writes]
    exact ⟨trivial, receipt_ownershipRepr_with_extents hT hn hrel'⟩
  · have he : T.findHeld (word64 owner) A .published = .error (ownershipErrorOf e) :=
      agrees_err_of_branch cf_post ‹_› residual_post hr
    simp only [Ownership.release, he, Bind.bind, Except.bind, Except.map, Writes, r1_post, ← e_post]
    exact ⟨trivial, trivial⟩

/-- `Ownership::cancel(owner, reservation)`: the statement `OwnershipCancel`
without its premises `Usize64` and `Ownership.Invariant`. -/
theorem ownership_cancel_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (owner : U64) (reservation : page_tables.Reservation)
    (R : Reservation) (hT : OwnershipRepr t T) (hR : ReservationRepr reservation R) :
    page_tables.ownership.receipts.Ownership.cancel t owner reservation ⦃ r t' =>
      Writes OwnershipRepr (fun _ _ => True)
        (fun (e, x) (E, Y) => ownershipErrorOf e = E ∧ ReservationRepr x Y) t r t'
        ((T.cancel (word64 owner) R).map (·, ())) ⦄ := by
  unfold page_tables.ownership.receipts.Ownership.cancel
  by_cases hat : reservation.attempted = true
  · simp only [hat, ↓reduceIte]
    refine spec_of_eq rfl ?_
    have hR' : R.attempted = true := by rw [hR.2.1]; exact hat
    simp only [Ownership.cancel, hR', ↓reduceIte, Except.map, Writes]
    exact ⟨⟨rfl, hR⟩, rfl⟩
  · simp only [hat, Bool.false_eq_true, ↓reduceIte]
    have hR' : R.attempted = false := by rw [hR.2.1]; simpa using hat
    step with find_held_spec t T owner reservation.allocation R.allocation .Reserved hT hR.1
      as ⟨r, hr⟩
    cases r with
    | Ok index =>
      obtain ⟨⟨before, ex, after⟩, hf, hl⟩ := agrees_ok_iff.mp hr
      have hf' : T.findHeld (word64 owner) R.allocation .reserved = .ok (before, ex, after) := hf
      obtain ⟨hk, hx, -⟩ := receipt_found_repr hT hf hl
      have hext : ListRel ExtentRepr (t.extents.val.take t.extent_count.val)
          (before.reverse ++ ex :: after) := by
        rw [← hx]; exact hT.2.2.2.2.2.1
      simp only
      apply spec_bind
        (merge_freed_spec t.extents t.extent_count index before after ex hT.2.1 hk hext hl)
      rintro ⟨n, a⟩ ⟨hn, hrel'⟩
      refine spec_of_eq rfl ?_
      simp only [Ownership.cancel, hR', Bool.false_eq_true, ↓reduceIte, hf', Except.map, Writes]
      exact ⟨trivial, receipt_ownershipRepr_with_extents hT hn hrel'⟩
    | Err error =>
      have hf : T.findHeld (word64 owner) R.allocation .reserved =
          .error (ownershipErrorOf error) := agrees_err_iff.mp hr
      simp only
      refine spec_of_eq rfl ?_
      simp only [Ownership.cancel, hR', Bool.false_eq_true, ↓reduceIte, hf, Except.map, Writes]
      exact ⟨⟨rfl, hR⟩, rfl⟩

end Krepi.Proofs.PageTables.Refinement
