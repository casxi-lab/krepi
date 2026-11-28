module

public import Krepi.Statements.PageTables.Representation
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.WriteSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the lookups and the writes of a set

The triples of the generated functions of the `page-tables` component that
look up a leaf of a set, build its write plans and write its record of the
tables in use, each a `@[step]` lemma, so that the proof of a caller steps
over the call with the triple of the callee and a mutant of a callee fails
the proof of the callee alone. Each holds without the premise `Usize64`.

- Write plans: `plan_spec` (a plan without `Zero` steps), `two_steps_spec`
  (a plan of two steps), with `writePlanRepr_five` and
  `writePlanRepr_seven` (the plans of five and seven steps that the writes
  build).
- The walk to a page leaf: `page_leaf_spec` (`Tables.pageLeaf`, for a pool
  of at least one table).
- The entries that write nothing: `lookup_page_spec` (the statement
  `TablesLookupPage` without its premise) and `lookup_block_spec`
  (`TablesLookupBlock`).
- The writes: `reset_spec` (`TablesReset`), `map_below_spec` (the rest of
  `map_page` below a level 2 entry, `mapBelow`, for a pool whose end fits in
  64 bits), `map_page_spec` (`TablesMapPage`), `map_block_spec`
  (`TablesMapBlock`) and `unmap_page_spec` (`TablesUnmapPage`).
-/
@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Write plans -/

/-- `plan(steps, len)`: the plan of the first `len` steps, with no `Zero`
step. -/
@[step] theorem plan_spec (steps : Aeneas.Std.Array page_tables.Step 7#usize) (len : Usize) :
    page_tables.write.plan steps len ⦃ p => p = { zero_tables := 0#usize, steps, len } ⦄ := by
  unfold page_tables.write.plan
  exact spec_of_eq rfl rfl

/-- A plan of the first five of seven steps stands for the five steps of the
specification that they stand for. -/
theorem writePlanRepr_five {a b c d e f g : page_tables.Step} {A B C D E : Step}
    (ha : stepOf a = A) (hb : stepOf b = B) (hc : stepOf c = C) (hd : stepOf d = D)
    (he : stepOf e = E) :
    WritePlanRepr
      { zero_tables := 0#usize, steps := Array.make 7#usize [a, b, c, d, e, f, g], len := 5#usize }
      [A, B, C, D, E] := by
  refine And.intro
    (by simp only [Array.make_val, List.length_cons, List.length_nil]; decide) ?_
  rw [planOf_steps, Array.make_val]
  show [stepOf a, stepOf b, stepOf c, stepOf d, stepOf e] = _
  rw [ha, hb, hc, hd, he]

/-- A plan of seven steps stands for the seven steps of the specification
that they stand for. -/
theorem writePlanRepr_seven {a b c d e f g : page_tables.Step} {A B C D E F G : Step}
    (ha : stepOf a = A) (hb : stepOf b = B) (hc : stepOf c = C) (hd : stepOf d = D)
    (he : stepOf e = E) (hf : stepOf f = F) (hg : stepOf g = G) :
    WritePlanRepr
      { zero_tables := 0#usize, steps := Array.make 7#usize [a, b, c, d, e, f, g], len := 7#usize }
      [A, B, C, D, E, F, G] := by
  refine And.intro
    (by simp only [Array.make_val, List.length_cons, List.length_nil]; decide) ?_
  rw [planOf_steps, Array.make_val]
  show [stepOf a, stepOf b, stepOf c, stepOf d, stepOf e, stepOf f, stepOf g] = _
  rw [ha, hb, hc, hd, he, hf, hg]

/-- `two_steps(first, last)`: the plan of the two steps. -/
@[step] theorem two_steps_spec (first last : page_tables.Step) :
    page_tables.write.two_steps first last ⦃ p =>
      WritePlanRepr p [stepOf first, stepOf last] ⦄ := by
  unfold page_tables.write.two_steps
  step*
  subst p_post
  refine And.intro
    (by simp only [Array.make_val, List.length_cons, List.length_nil]; decide) ?_
  rw [planOf_steps, Array.make_val]
  rfl

/-! ## The walk to a page leaf -/

/-- `Tables::page_leaf(va, base)` on a pool of at least one table: the page
leaf of `Tables.pageLeaf`, its table and descriptor. -/
@[step] theorem page_leaf_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (va base : U64) (hN : 0 < N.val) :
    page_tables.walk.Tables.page_leaf s va base ⦃ r =>
      Agrees (fun p P => p.1.val = P.1 ∧ word64 p.2 = P.2) tableErrorOf r
        ((tablesOf s).pageLeaf (word64 base) (word64 va)) ⦄ := by
  unfold page_tables.walk.Tables.page_leaf
  step*
  · have hw := eq_of_branch_map cf_post ‹_› r_post
    rw [‹val = none›] at hw
    rw [pageLeaf_root hw]; rfl
  · obtain ⟨t2, entry⟩ := p
    have hw := eq_of_branch_map cf_post ‹_› r_post
    rw [‹val = some (t2, entry)›] at hw
    step*
    · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hb : typeBits (word64 entry) = BLOCK := by
        rw [← i_post, ‹i = page_tables.encoding.BLOCK›, word64_block]
      rw [pageLeaf_block hw hv hb]; rfl
    · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 entry) = none := by
        rw [← o_post, ‹o = none›]; rfl
      rw [pageLeaf_backing hw hv hb hc]; rfl
    · have hc := o_post
      rw [‹o = some leaf›, Option.map_some] at hc
      have h1 : leaf.val < N.val := child?_lt hc.symm
      scalar_tac
    · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 entry) = some leaf.val := by
        rw [← o_post, ‹o = some leaf›]; rfl
      have he : (tablesOf s).entry leaf.val (index3 (word64 va)) = word64 d := by
        subst a_post d_post
        rw [← i1_post]; exact tablesOf_entry s (by scalar_tac) (by scalar_tac)
      have hd : typeBits ((tablesOf s).entry leaf.val (index3 (word64 va))) = TABLE_OR_PAGE := by
        rw [he, ← i2_post, ‹i2 = page_tables.encoding.TABLE_OR_PAGE›, word64_table_or_page]
      rw [pageLeaf_leaf hw hv hb hc hd, he]
      exact ⟨rfl, rfl⟩
    · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 entry) = some leaf.val := by
        rw [← o_post, ‹o = some leaf›]; rfl
      have he : (tablesOf s).entry leaf.val (index3 (word64 va)) = word64 d := by
        subst a_post d_post
        rw [← i1_post]; exact tablesOf_entry s (by scalar_tac) (by scalar_tac)
      have hd : typeBits ((tablesOf s).entry leaf.val (index3 (word64 va))) ≠ TABLE_OR_PAGE := by
        rw [he, ← i2_post, ← word64_table_or_page]
        exact fun h => ‹¬i2 = page_tables.encoding.TABLE_OR_PAGE› (word64_inj.1 h)
      rw [pageLeaf_notLeaf hw hv hb hc hd]; rfl
    · have hv : isValid (word64 entry) = false := by
        rw [← b_post]; simpa using ‹¬b = true›
      rw [pageLeaf_level2 hw hv]; rfl
  · have he := agrees_err_of_branch cf_post ‹_› residual_post ‹_›
    rw [pageLeaf_error he, r_post, ← e_post]; rfl

/-! ## The entries that write nothing -/

/-- `Tables::lookup_page(va, base, bits)`: the page descriptor of
`Tables.lookupPage`, or its error. -/
@[step] theorem lookup_page_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (va base : U64) (bits : U8) :
    page_tables.walk.Tables.lookup_page s va base bits ⦃ r =>
      Agrees (fun d D => word64 d = D) tableErrorOf r
        ((tablesOf s).lookupPage (word64 va) (word64 base) (byte bits)) ⦄ := by
  unfold page_tables.walk.Tables.lookup_page
  simp only [page_size_eq]
  step*
  · exact (checkEntry_fits (ok_of_branch_unit cf_post ‹_› r_post)).1
  · obtain ⟨t3, d⟩ := val
    have hce := ok_of_branch_unit cf_post ‹_› r_post
    obtain ⟨P, hP, -, hd⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› r1_post)
    step*
    rw [lookupPage_leaf hce hP]
    exact hd
  · have hce := ok_of_branch_unit cf_post ‹_› ‹_›
    have he := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
    rw [lookupPage_leaf_error hce he, r_post, ← e_post]; rfl
  · have he := agrees_err_of_branch cf_post ‹_› residual_post ‹_›
    rw [lookupPage_check he, r_post, ← e_post]; rfl

/-- `Tables::lookup_block(va, base, bits)`: the block descriptor of
`Tables.lookupBlock`, or its error. -/
@[step] theorem lookup_block_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (va base : U64) (bits : U8) :
    page_tables.walk.Tables.lookup_block s va base bits ⦃ r =>
      Agrees (fun d D => word64 d = D) tableErrorOf r
        ((tablesOf s).lookupBlock (word64 va) (word64 base) (byte bits)) ⦄ := by
  unfold page_tables.walk.Tables.lookup_block
  simp only [block_size_eq]
  step*
  · exact (checkEntry_fits (ok_of_branch_unit cf_post ‹_› r_post)).1
  · have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hw := eq_of_branch_map cf1_post ‹_› r1_post
    rw [‹val = none›] at hw
    rw [lookupBlock_root hce hw]; rfl
  · obtain ⟨t2, entry⟩ := p
    have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hw := eq_of_branch_map cf1_post ‹_› r1_post
    rw [‹val = some (t2, entry)›] at hw
    rw [lookupBlock_some hce hw]
    step*
    · have hb : typeBits (word64 entry) = BLOCK := by
        rw [← i_post, ‹i = page_tables.encoding.BLOCK›, word64_block]
      simp only [hb, ↓reduceIte, agrees_ok_ok]
    · have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hc : (tablesOf s).child? (word64 base) (word64 entry) = none := by
        rw [← o_post, ‹o = none›]; rfl
      simp only [hb, hv, hc, ↓reduceIte, and_self, agrees_err_error]; rfl
    · have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hc : (tablesOf s).child? (word64 base) (word64 entry) ≠ none := by
        rw [← o_post, ‹o = some _›]; exact fun h => by cases h
      simp only [hb, hc, ↓reduceIte, and_false, agrees_err_error]; rfl
    · have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
      have hv : isValid (word64 entry) = false := by rw [← b_post]; simpa using ‹¬b = true›
      simp only [hb, hv, ↓reduceIte, Bool.false_eq_true, false_and, agrees_err_error]; rfl
  · have hce := ok_of_branch_unit cf_post ‹_› ‹_›
    have he := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
    rw [lookupBlock_walk_error hce he, r_post, ← e_post]; rfl
  · have he := agrees_err_of_branch cf_post ‹_› residual_post ‹_›
    rw [lookupBlock_check he, r_post, ← e_post]; rfl

/-! ## The writes -/

/-- `Tables::reset()`: the set with the root alone in use and the plan of
`Tables.reset`. -/
@[step] theorem reset_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) :
    page_tables.write.Tables.reset s ⦃ plan s' =>
      WritePlanRepr plan (tablesOf s).reset.2 ∧ tablesOf s' = (tablesOf s).reset.1 ⦄ := by
  unfold page_tables.write.Tables.reset
  step*
  have h0 : (0#usize : Usize).val = 0 := rfl
  refine ⟨And.intro (by rw [h0]; exact Nat.zero_le _) ?_, rfl⟩
  simp only [planOf, h0, List.take_zero, List.map_nil, List.append_nil, zero_tables_post,
    Tables.reset, tablesOf_used]

/-- `Tables::map_below(table, entry, va, page, base)` for a pool whose end
fits in 64 bits: the rest of `Tables.mapPage` below the level 2 entry
`entry` of `va` in table `table`, `mapBelow`. -/
@[step] theorem map_below_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (table : Usize) (entry va page base : U64) (hfit : base.val + 4096 * N.val < 2 ^ 64) :
    page_tables.write.Tables.map_below s table entry va page base ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) WritePlanRepr (tableErrorOf · = ·) s r s'
        (mapBelow (tablesOf s) table.val (word64 entry) (word64 va) (word64 page)
          (word64 base)) ⦄ := by
  unfold page_tables.write.Tables.map_below
  step*
  · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
    have hb : typeBits (word64 entry) = BLOCK := by
      rw [← i_post, ‹i = page_tables.encoding.BLOCK›, word64_block]
    rw [mapBelow_block hv hb]
    exact writes_error_of rfl
  · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
    have hb : typeBits (word64 entry) ≠ BLOCK := by
      rw [← i_post, ← word64_block]
      exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
    have hc : (tablesOf s).child? (word64 base) (word64 entry) = none := by
      rw [← o_post, ‹o = none›]; rfl
    rw [mapBelow_backing hv hb hc]
    exact writes_error_of rfl
  · have hc := o_post
    rw [‹o = some level3›, Option.map_some] at hc
    have h1 : level3.val < N.val := child?_lt hc.symm
    scalar_tac
  · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
    have hb : typeBits (word64 entry) ≠ BLOCK := by
      rw [← i_post, ← word64_block]
      exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
    have hc : (tablesOf s).child? (word64 base) (word64 entry) = some level3.val := by
      rw [← o_post, ‹o = some level3›]; rfl
    have he : (tablesOf s).entry level3.val (index3 (word64 va)) = word64 i2 := by
      subst a_post i2_post
      rw [← i1_post]; exact tablesOf_entry s (by scalar_tac) (by scalar_tac)
    have hl : isValid ((tablesOf s).entry level3.val (index3 (word64 va))) = true := by
      rw [he, ← b1_post]; exact ‹b1 = true›
    rw [mapBelow_level3 hv hb hc]
    simp only [hl, ↓reduceIte]
    exact writes_error_of rfl
  · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
    have hb : typeBits (word64 entry) ≠ BLOCK := by
      rw [← i_post, ← word64_block]
      exact fun h => ‹¬i = page_tables.encoding.BLOCK› (word64_inj.1 h)
    have hc : (tablesOf s).child? (word64 base) (word64 entry) = some level3.val := by
      rw [← o_post, ‹o = some level3›]; rfl
    have he : (tablesOf s).entry level3.val (index3 (word64 va)) = word64 i2 := by
      subst a_post i2_post
      rw [← i1_post]; exact tablesOf_entry s (by scalar_tac) (by scalar_tac)
    have hl : isValid ((tablesOf s).entry level3.val (index3 (word64 va))) = false := by
      rw [he, ← b1_post]; simpa using ‹¬b1 = true›
    rw [mapBelow_level3 hv hb hc]
    simp only [hl, Bool.false_eq_true, ↓reduceIte]
    refine writes_ok_of ?_ rfl
    simp only [stepOf, i1_post] at wp_post
    exact wp_post
  · have hv : isValid (word64 entry) = false := by rw [← b_post]; simpa using ‹¬b = true›
    have hn : N.val - (tablesOf s).used < 1 := by rw [tablesOf_used]; scalar_tac
    rw [mapBelow_invalid_full hv hn]
    exact writes_error_of rfl
  · scalar_tac
  · scalar_tac
  · have hv : isValid (word64 entry) = false := by rw [← b_post]; simpa using ‹¬b = true›
    have hn : ¬ N.val - (tablesOf s).used < 1 := by rw [tablesOf_used]; scalar_tac
    rw [mapBelow_invalid hv hn]
    subst wp_post
    refine writes_ok_of (writePlanRepr_five ?_ ?_ ?_ ?_ ?_) ?_
    · rfl
    · simp only [stepOf, i2_post, tablesOf_used]
    · rfl
    · simp only [stepOf, i3_post, i5_post, i4_post1, tablesOf_used]
    · rfl
    · show tablesOf _ = _
      rw [tablesOf_with_used, i1_post]; rfl

/-- `Tables::map_page(va, pa, kind, base, bits)`: the set after the write
phase and the plan of `Tables.mapPage`, or its error with the set
unchanged. -/
@[step] theorem map_page_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (va pa : U64) (kind : page_tables.Kind) (base : U64) (bits : U8) :
    page_tables.write.Tables.map_page s va pa kind base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) WritePlanRepr (tableErrorOf · = ·) s r s'
        ((tablesOf s).mapPage (word64 va) (word64 pa) (kindOf kind) (word64 base)
          (byte bits)) ⦄ := by
  unfold page_tables.write.Tables.map_page
  simp only [page_size_eq]
  step*
  · exact lt_64_of_widthOk (checkEntry_passes (ok_of_branch_unit cf_post ‹_› r_post)).2.2.1
  · exact (checkEntry_fits (ok_of_branch_unit cf_post ‹_› r_post)).1
  · have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hcp := ok_of_branch_unit cf1_post ‹_› r1_post
    have hw := eq_of_branch_map cf2_post ‹_› r2_post
    rw [‹val = none›] at hw
    have hn : N.val - (tablesOf s).used < 2 := by rw [tablesOf_used]; scalar_tac
    rw [mapPage_root_full hce hcp hw hn]
    exact writes_error_of rfl
  · scalar_tac
  · scalar_tac
  · have hf := (checkEntry_fits (ok_of_branch_unit cf_post ‹_› r_post)).2
    simp only [word64_toNat, PAGE_SIZE] at hf
    scalar_tac
  · have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hcp := ok_of_branch_unit cf1_post ‹_› r1_post
    have hw := eq_of_branch_map cf2_post ‹_› r2_post
    rw [‹val = none›] at hw
    have hn : ¬ N.val - (tablesOf s).used < 2 := by rw [tablesOf_used]; scalar_tac
    rw [mapPage_root_new hce hcp hw hn]
    subst wp_post
    have h0 : (0#usize : Usize).val = 0 := rfl
    refine writes_ok_of (writePlanRepr_seven ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · simp only [stepOf, level3_post, tablesOf_used]
    · simp only [stepOf, level3_post, i2_post, page_post, tablesOf_used]
    · rfl
    · simp only [stepOf, i3_post, i5_post, i4_post1, level3_post, tablesOf_used]
    · rfl
    · simp only [stepOf, h0, i6_post, i8_post, i7_post1, tablesOf_used]
    · rfl
    · show tablesOf _ = _
      rw [tablesOf_with_used, i1_post]; rfl
  · obtain ⟨table, entry⟩ := p
    have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hcp := ok_of_branch_unit cf1_post ‹_› r1_post
    have hw := eq_of_branch_map cf2_post ‹_› r2_post
    rw [‹val = some (table, entry)›, Option.map_some] at hw
    have hf := (checkEntry_fits hce).2
    simp only [word64_toNat, PAGE_SIZE] at hf
    rw [mapPage_some hce hcp hw, ← page_post]
    exact map_below_spec s table entry va page base hf
  · have he := agrees_err_of_branch cf2_post ‹_› residual_post r2_post
    rw [mapPage_walk_error (ok_of_branch_unit cf_post ‹_› r_post)
      (ok_of_branch_unit cf1_post ‹_› r1_post) he, r3_post, ← e_post]
    exact writes_error_of rfl
  · have he := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
    rw [mapPage_physical (ok_of_branch_unit cf_post ‹_› r_post) he, r3_post, ← e_post]
    exact writes_error_of rfl
  · have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
    rw [mapPage_check he, r3_post, ← e_post]
    exact writes_error_of rfl

/-- `Tables::map_block(va, pa, base, bits)`: the set after the write phase
and the plan of `Tables.mapBlock`, or its error with the set unchanged. -/
@[step] theorem map_block_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (va pa base : U64) (bits : U8) :
    page_tables.write.Tables.map_block s va pa base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) WritePlanRepr (tableErrorOf · = ·) s r s'
        ((tablesOf s).mapBlock (word64 va) (word64 pa) (word64 base) (byte bits)) ⦄ := by
  unfold page_tables.write.Tables.map_block
  simp only [block_size_eq]
  step*
  · exact lt_64_of_widthOk (checkEntry_passes (ok_of_branch_unit cf_post ‹_› r_post)).2.2.1
  · exact (checkEntry_fits (ok_of_branch_unit cf_post ‹_› r_post)).1
  · have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hcp := ok_of_branch_unit cf1_post ‹_› r1_post
    have hw := eq_of_branch_map cf2_post ‹_› r2_post
    rw [‹val = none›] at hw
    have hn : N.val - (tablesOf s).used < 1 := by rw [tablesOf_used]; scalar_tac
    rw [mapBlock_root_full hce hcp hw hn]
    exact writes_error_of rfl
  · scalar_tac
  · have hf := (checkEntry_fits (ok_of_branch_unit cf_post ‹_› r_post)).2
    simp only [word64_toNat, PAGE_SIZE] at hf
    scalar_tac
  · have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hcp := ok_of_branch_unit cf1_post ‹_› r1_post
    have hw := eq_of_branch_map cf2_post ‹_› r2_post
    rw [‹val = none›] at hw
    have hn : ¬ N.val - (tablesOf s).used < 1 := by rw [tablesOf_used]; scalar_tac
    rw [mapBlock_root_new hce hcp hw hn]
    subst wp_post
    have h0 : (0#usize : Usize).val = 0 := rfl
    refine writes_ok_of (writePlanRepr_five ?_ ?_ ?_ ?_ ?_) ?_
    · rfl
    · simp only [stepOf, i2_post, block_post, tablesOf_used]
    · rfl
    · simp only [stepOf, h0, i3_post, i5_post, i4_post1, tablesOf_used]
    · rfl
    · show tablesOf _ = _
      rw [tablesOf_with_used, i1_post]; rfl
  · obtain ⟨table, entry⟩ := found
    have hce := ok_of_branch_unit cf_post ‹_› r_post
    have hcp := ok_of_branch_unit cf1_post ‹_› r1_post
    have hw := eq_of_branch_map cf2_post ‹_› r2_post
    rw [‹val = some (table, entry)›, Option.map_some] at hw
    step*
    · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => by simp only [word64_inj.1 h, bne_self_eq_false, Bool.false_eq_true] at *
      have hc : (tablesOf s).child? (word64 base) (word64 entry) = none := by
        rw [← o_post, ‹o = none›]; rfl
      rw [mapBlock_backing hce hcp hw hv hb hc]
      exact writes_error_of rfl
    · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hb : typeBits (word64 entry) ≠ BLOCK := by
        rw [← i_post, ← word64_block]
        exact fun h => by simp only [word64_inj.1 h, bne_self_eq_false, Bool.false_eq_true] at *
      obtain ⟨t3, ho⟩ : ∃ t3, o = some t3 := ⟨_, ‹o = some _›⟩
      have hc : (tablesOf s).child? (word64 base) (word64 entry) = some t3.val := by
        rw [← o_post, ho]; rfl
      rw [mapBlock_table hce hcp hw hv hb hc]
      exact writes_error_of rfl
    · have hv : isValid (word64 entry) = true := by rw [← b_post]; exact ‹b = true›
      have hb : typeBits (word64 entry) = BLOCK := by
        have := ‹¬(i != page_tables.encoding.BLOCK) = true›
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
        rw [← i_post, this, word64_block]
      rw [mapBlock_block hce hcp hw hv hb]
      exact writes_error_of rfl
    · have hv : isValid (word64 entry) = false := by rw [← b_post]; simpa using ‹¬b = true›
      rw [mapBlock_invalid hce hcp hw hv]
      refine writes_ok_of ?_ rfl
      simp only [stepOf, i1_post, block_post] at wp_post
      exact wp_post
  · have he := agrees_err_of_branch cf2_post ‹_› residual_post r2_post
    rw [mapBlock_walk_error (ok_of_branch_unit cf_post ‹_› r_post)
      (ok_of_branch_unit cf1_post ‹_› r1_post) he, r3_post, ← e_post]
    exact writes_error_of rfl
  · have he := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
    rw [mapBlock_physical (ok_of_branch_unit cf_post ‹_› r_post) he, r3_post, ← e_post]
    exact writes_error_of rfl
  · have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
    rw [mapBlock_check he, r3_post, ← e_post]
    exact writes_error_of rfl

/-- `Tables::unmap_page(va, base, bits)`: the plan and the physical page of
`Tables.unmapPage`, with the set unchanged, or its error. -/
@[step] theorem unmap_page_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (va base : U64) (bits : U8) :
    page_tables.write.Tables.unmap_page s va base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S)
        (fun (plan, pa) (P, A) => WritePlanRepr plan P ∧ word64 pa = A)
        (tableErrorOf · = ·) s r s'
        (((tablesOf s).unmapPage (word64 va) (word64 base) (byte bits)).map
          (tablesOf s, ·)) ⦄ := by
  unfold page_tables.write.Tables.unmap_page
  simp only [page_size_eq]
  step*
  · exact (checkEntry_fits (ok_of_branch_unit cf_post ‹_› r_post)).1
  · obtain ⟨level3, leaf⟩ := val
    have hce := ok_of_branch_unit cf_post ‹_› r_post
    obtain ⟨P, hP, h1, h2⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› r1_post)
    step*
    rw [unmapPage_leaf hce hP]
    refine writes_ok_of (b := (_, _)) ⟨?_, ?_⟩ rfl
    · simp only [stepOf, i_post, h1] at plan_post
      exact plan_post
    · rw [i1_post, h2]
  · have hce := ok_of_branch_unit cf_post ‹_› r_post
    have he := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
    rw [unmapPage_leaf_error hce he, r2_post, ← e_post]
    exact writes_error_of rfl
  · have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
    rw [unmapPage_check he, r2_post, ← e_post]
    exact writes_error_of rfl

end Krepi.Proofs.PageTables.Refinement
