module

public import Krepi.Statements.PageTables.Tables
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.CopySpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the copy of the kernel tables

The triples of the generated functions of `copy`, each a `@[step]` lemma so
that a caller steps over the call, and the plan iterator of a copy. Each
holds without the premise `Usize64`.

- Constants and small facts of the code: `copy_unreached_eq`,
  `copy_root_eq`, `copy_level2_eq`, `copy_leaves_eq` (the marks of the
  walk), `copy_u8_eq_zero_iff`, `copy_u8_eq_three_iff`, `copy_word64_beq`,
  `copy_entry_lt` and `copy_table_toList` (an entry and a table of the set of
  the code), `copy_lt_length`, `copy_lt_val_length`, `copy_usize_512`,
  `copy_lt_512`, `copy_ge_512`, `copy_usize_ne_zero`, `copy_child?_eq` (the
  `child_index` of the code with the record as the limit is `Tables.child?`)
  and `copy_isPlain_iff` (the test of a table descriptor with no attribute).
- The leaves: `copy_kind_spec` (one of the page descriptors of the kinds that
  a copy takes), `copyable_spec` (`copyableLeaf`, for a width below 64),
  `copy_check_leaves_loop_spec` and `copy_check_leaves_spec` (`checkLeaves`,
  for a width below 64).
- The walk of the source on its marks (`VisitRepr`), for a record of at most
  `N` tables and a width below 64: `copy_reach_spec` (`Tables.reach`),
  `copy_walk_level2_loop_spec` and `copy_walk_level2_spec`
  (`Tables.walkLevel2`, for every visit that the marks stand for:
  `Level2Post`), `copy_walk_root_loop_spec` and `copy_walk_root_spec`
  (`Tables.walkRoot` from the root, for a pool of at least one table),
  `all_reached_loop_spec` and `all_reached_spec` (every table in use is
  marked).
- The plan: `next_valid_loop_spec` and `next_valid_spec` (the next valid
  entry of the source with the stores of the plan from it, `NextValid`);
  `CloneRest`, the simulation relation of the plan iterator (a state stands
  for the `Zero` steps it has left, the stores from its position and `Sync`),
  with `clone_next_done`, `clone_next_cons` and `clone_stands` (an iterator
  in that relation stands for its list).
- The entry: `clone_pool_ok`, `clone_pools`, `clone_writes_err`,
  `clone_ok_writes`, and `clone_kernel_from_spec`, the statement
  `TablesCloneKernelFrom` without its premise.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Constants of the code -/

theorem copy_unreached_eq : page_tables.copy.UNREACHED = 0#u8 := by
  unfold page_tables.copy.UNREACHED; rfl

theorem copy_root_eq : page_tables.copy.ROOT = 1#u8 := by
  unfold page_tables.copy.ROOT; rfl

theorem copy_level2_eq : page_tables.copy.LEVEL2 = 2#u8 := by
  unfold page_tables.copy.LEVEL2; rfl

theorem copy_leaves_eq : page_tables.copy.LEAVES = 3#u8 := by
  unfold page_tables.copy.LEAVES; rfl

theorem copy_u8_eq_zero_iff {x : U8} : x = 0#u8 ↔ x.val = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by rw [h]; rfl)⟩

theorem copy_u8_eq_three_iff {x : U8} : x = 3#u8 ↔ x.val = 3 :=
  ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by rw [h]; rfl)⟩

theorem copy_word64_beq (x y : U64) : (word64 x == word64 y) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, word64_inj]

/-- An entry of the set of the code at a table of the pool and an index below
512: the word of its descriptor. -/
theorem copy_entry_lt {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) {t i : Nat}
    (ht : t < N.val) (hi : i < 512) :
    (tablesOf s).entry t i = word64 ((s.pool.val[t]'(by scalar_tac)).val[i]'(by scalar_tac)) :=
  tablesOf_entry s _ _

theorem copy_lt_length {α : Type _} {n : Usize} (a : Aeneas.Std.Array α n) {i : Nat}
    (h : i < n.val) : i < a.length := by scalar_tac

theorem copy_lt_val_length {α : Type _} {n : Usize} (a : Aeneas.Std.Array α n) {i : Nat}
    (h : i < n.val) : i < a.val.length := by scalar_tac

theorem copy_usize_512 : (512#usize).val = 512 := by scalar_tac

theorem copy_lt_512 {x : Usize} (h : x < 512#usize) : x.val < 512 := by scalar_tac

theorem copy_ge_512 {x : Usize} (h : ¬ x < 512#usize) : 512 ≤ x.val := by scalar_tac

/-- A `usize` that is not the literal 0 is not 0. -/
theorem copy_usize_ne_zero {x : Usize} (h : ¬ x = 0#usize) : x.val ≠ 0 :=
  fun h0 => h (UScalar.eq_of_val_eq (by rw [h0]; simp))

/-- A table of the set of the code, as a list: the words of its descriptors. -/
theorem copy_table_toList {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) {t : Nat}
    (ht : t < s.pool.val.length) :
    ((tablesOf s).table t).toList = (s.pool.val[t]'ht).val.map word64 :=
  clone_table_poolView s.pool s.used.val ht

/-- The table that the code's `child_index` gives with the record as the
limit, for a record of at most `N` tables: `Tables.child?`. -/
theorem copy_child?_eq {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (hu : s.used.val ≤ N.val) (entry base : U64) {o : Option Usize}
    (ho : o.map (fun x => x.val) = childIndex (outputAddress (word64 entry)).toNat base.val s.used.val) :
    (tablesOf s).child? (word64 base) (word64 entry) = o.map (fun x => x.val) := by
  rw [child?_eq, ho, tablesOf_used, word64_toNat, Nat.min_eq_left hu]

/-- The test of a table descriptor with no attribute in the code. -/
theorem copy_isPlain_iff {entry i i1 : U64} (hi : i = ~~~page_tables.encoding.ADDRESS_MASK)
    (h1 : i1.val = (entry &&& i).val) :
    isPlainTableDescriptor (word64 entry) = true ↔
      ¬ (i1 != page_tables.encoding.TABLE_OR_PAGE) = true := by
  rw [isPlainTableDescriptor, beq_iff_eq, bne_iff_ne, not_not, ← word64_inj, word64_table_or_page,
    word64_congr h1, word64_and, hi, word64_not, word64_address_mask]

/-! ## Leaves -/

/-- `copy_kind(d, address)`: whether `d` is the page descriptor at `address`
of one of the kinds that a copy takes. -/
@[step] theorem copy_kind_spec (d address : U64) :
    page_tables.copy.copy_kind d address ⦃ b =>
      b = copyKinds.any (fun k => descriptor k (word64 address) == word64 d) ⦄ := by
  unfold page_tables.copy.copy_kind
  step*
  · have e0 : descriptor .readExecute (word64 address) = word64 i := i_post.symm
    simp only [copyKinds, List.any_cons, e0, beq_self_eq_true, Bool.true_or]
  · have e1 : descriptor .readOnly (word64 address) = word64 i1 := i1_post.symm
    simp only [copyKinds, List.any_cons, e1, beq_self_eq_true, Bool.true_or, Bool.or_true]
  · have e2 : descriptor .readWrite (word64 address) = word64 i2 := i2_post.symm
    simp only [copyKinds, List.any_cons, e2, beq_self_eq_true, Bool.true_or, Bool.or_true]
  · have e0 : descriptor .readExecute (word64 address) = word64 i := i_post.symm
    have e1 : descriptor .readOnly (word64 address) = word64 i1 := i1_post.symm
    have e2 : descriptor .readWrite (word64 address) = word64 i2 := i2_post.symm
    have e3 : descriptor .device (word64 address) = word64 i3 := i3_post.symm
    simp only [copyKinds, List.any_cons, List.any_nil, e0, e1, e2, e3, copy_word64_beq,
        Bool.or_false]
    rw [decide_eq_false (Ne.symm ‹¬d = i›), decide_eq_false (Ne.symm ‹¬d = i1›),
      decide_eq_false (Ne.symm ‹¬d = i2›), Bool.false_or, Bool.false_or, Bool.false_or]
    exact decide_eq_decide.2 eq_comm

/-- `copyable(d, bits)` for a width below 64: `copyableLeaf`. -/
@[step] theorem copyable_spec (d : U64) (bits : U8) (hb : bits.val < 64) :
    page_tables.copy.copyable d bits ⦃ b => b = copyableLeaf (byte bits) (word64 d) ⦄ := by
  unfold page_tables.copy.copyable
  step*
  · have hl : i.val = 2 ^ bits.val := by rw [i_post, u64_size]; exact one_shiftLeft hb
    rw [copyableLeaf, ← address_post, ← b_post, ‹b = true›, Bool.true_and, word64_toNat,
      byte_toNat, ← hl, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    scalar_tac
  · have hb' : b = false := by simpa using ‹¬b = true›
    rw [copyableLeaf, ← address_post, ← b_post, hb', Bool.false_and]

/-! ## The walk of the source -/

/-- `reach(entry, base, used, levels)` on marks that stand for a visit, for a
record of at most `N` tables: `Tables.reach`, the table reached below the
record and not marked yet. -/
@[step] theorem copy_reach_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (entry base : U64) (levels : Aeneas.Std.Array U8 N) (st : Visit) (hu : s.used.val ≤ N.val)
    (hV : VisitRepr levels.val st) :
    page_tables.copy.reach entry base s.used levels ⦃ r =>
      Agrees (fun t p => p = (t.val, { st with reached := st.reached ++ [t.val] }) ∧
          t.val < s.used.val ∧ ∃ h : t.val < levels.val.length, (levels.val[t.val]'h).val = 0)
        tableErrorOf r ((tablesOf s).reach (word64 base) (word64 entry) st) ⦄ := by
  unfold page_tables.copy.reach
  step*
  · have hp : isPlainTableDescriptor (word64 entry) = false := by
      rw [← Bool.not_eq_true, copy_isPlain_iff i_post i1_post, not_not]; exact ‹_›
    rw [reach_invalid _ _ _ hp]; rfl
  · have hp : isPlainTableDescriptor (word64 entry) = true :=
      (copy_isPlain_iff i_post i1_post).2 ‹_›
    have hc : (tablesOf s).child? (word64 base) (word64 entry) = none := by
      rw [copy_child?_eq s hu entry base o_post, ‹o = none›]; rfl
    rw [reach_none _ _ _ hp hc]; rfl
  · have hc := o_post
    rw [‹o = some table›, Option.map_some] at hc
    have h1 : table.val < s.used.val := childIndex_lt hc.symm
    exact copy_lt_length _ (Nat.lt_of_lt_of_le h1 hu)
  · have hp : isPlainTableDescriptor (word64 entry) = true :=
      (copy_isPlain_iff i_post i1_post).2 ‹_›
    have hc : (tablesOf s).child? (word64 base) (word64 entry) = some table.val := by
      rw [copy_child?_eq s hu entry base o_post, ‹o = some table›]; rfl
    have hr : st.reached.contains table.val = true := by
      have h2 := ‹(i2 != page_tables.copy.UNREACHED) = true›
      rw [copy_unreached_eq, bne_iff_ne, ne_eq, copy_u8_eq_zero_iff, i2_post] at h2
      exact (visitRepr_reached hV _).2 h2
    rw [reach_again _ _ _ hp hc hr]; rfl
  · have hp : isPlainTableDescriptor (word64 entry) = true :=
      (copy_isPlain_iff i_post i1_post).2 ‹_›
    have hc : (tablesOf s).child? (word64 base) (word64 entry) = some table.val := by
      rw [copy_child?_eq s hu entry base o_post, ‹o = some table›]; rfl
    have hlt : table.val < s.used.val := by
      have hc' := o_post
      rw [‹o = some table›, Option.map_some] at hc'
      exact childIndex_lt hc'.symm
    have hl : table.val < levels.val.length := copy_lt_val_length _ (Nat.lt_of_lt_of_le hlt hu)
    have h2 := ‹¬(i2 != page_tables.copy.UNREACHED) = true›
    rw [copy_unreached_eq, bne_iff_ne, ne_eq, not_not, copy_u8_eq_zero_iff, i2_post] at h2
    have hr : st.reached.contains table.val = false := by
      rw [← Bool.not_eq_true, visitRepr_reached hV hl, not_not]; exact h2
    rw [reach_new _ _ _ hp hc hr, agrees_ok_ok]
    exact ⟨rfl, hlt, hl, h2⟩

/-- The loop of `check_leaves(table, bits)` from an index, for a width below
64: `checkLeaves` of the entries from that index. -/
theorem copy_check_leaves_loop_spec (table : Aeneas.Std.Array U64 512#usize) (bits : U8)
    (hb : bits.val < 64) (start : Usize) :
    page_tables.copy.check_leaves_loop table bits start ⦃ r =>
      Agrees (fun _ _ => True) tableErrorOf r
        (checkLeaves (byte bits) ((table.val.map word64).drop start.val)) ⦄ := by
  unfold page_tables.copy.check_leaves_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => 512 - i.val)
    (inv := fun (i : Usize) => checkLeaves (byte bits) ((table.val.map word64).drop i.val) =
      checkLeaves (byte bits) ((table.val.map word64).drop start.val))
  · intro index hinv
    unfold page_tables.copy.check_leaves_loop.body
    simp only [entries_eq]
    step*
    · subst i_post
      have hi512 := copy_lt_512 ‹index < 512#usize›
      have hi' : index.val < table.val.length := copy_lt_val_length table ‹index < 512#usize›
      have hi : index.val < (table.val.map word64).length := by rw [List.length_map]; exact hi'
      have hv : (isValid (word64 table.val[index.val]) &&
          !copyableLeaf (byte bits) (word64 table.val[index.val])) = false := by
        rw [← b_post, ← b1_post, ‹b = true›, ‹b1 = true›]; rfl
      refine ⟨?_, by omega⟩
      rw [index1_post, ← hinv, List.drop_eq_getElem_cons hi, checkLeaves_cons, List.getElem_map, hv]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · subst i_post
      have hi512 := copy_lt_512 ‹index < 512#usize›
      have hi' : index.val < table.val.length := copy_lt_val_length table ‹index < 512#usize›
      have hi : index.val < (table.val.map word64).length := by rw [List.length_map]; exact hi'
      have hv : (isValid (word64 table.val[index.val]) &&
          !copyableLeaf (byte bits) (word64 table.val[index.val])) = true := by
        rw [← b_post, ← b1_post, ‹b = true›]; simpa using ‹¬b1 = true›
      rw [← hinv, List.drop_eq_getElem_cons hi, checkLeaves_cons, List.getElem_map, hv]
      rfl
    · subst i_post
      have hi512 := copy_lt_512 ‹index < 512#usize›
      have hi' : index.val < table.val.length := copy_lt_val_length table ‹index < 512#usize›
      have hi : index.val < (table.val.map word64).length := by rw [List.length_map]; exact hi'
      have hb' : b = false := by simpa using ‹¬b = true›
      have hv : (isValid (word64 table.val[index.val]) &&
          !copyableLeaf (byte bits) (word64 table.val[index.val])) = false := by
        rw [← b_post, hb', Bool.false_and]
      refine ⟨?_, by omega⟩
      rw [index1_post, ← hinv, List.drop_eq_getElem_cons hi, checkLeaves_cons, List.getElem_map, hv]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [← hinv, List.drop_eq_nil_of_le (by
        rw [List.length_map, table.property,
            copy_usize_512]; exact copy_ge_512 ‹¬index < 512#usize›)]
      exact trivial
  · rfl

/-- `check_leaves(table, bits)` for a width below 64: `checkLeaves` of the
words of the table. -/
@[step] theorem copy_check_leaves_spec (table : Aeneas.Std.Array U64 512#usize) (bits : U8)
    (hb : bits.val < 64) :
    page_tables.copy.check_leaves table bits ⦃ r =>
      Agrees (fun _ _ => True) tableErrorOf r (checkLeaves (byte bits) (table.val.map word64)) ⦄ := by
  have h := copy_check_leaves_loop_spec table bits hb 0#usize
  have h0 : (0#usize).val = 0 := by simp
  rw [h0, List.drop_zero] at h
  exact h

/-- The loop of `walk_level2(pool, used, base, bits, table, levels)` from an
index, on marks that stand for a visit, for a record of at most `N` tables, a
width below 64 and a table of the pool: `Tables.walkLevel2` of the entries
of the table from that index, the marks after it standing for the visit
after it. -/
theorem copy_walk_level2_loop_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (base : U64) (bits : U8) (table : Usize) (levels : Aeneas.Std.Array U8 N) (start : Usize)
    (st : Visit) (hu : s.used.val ≤ N.val) (hb : bits.val < 64) (ht : table.val < N.val)
    (hV : VisitRepr levels.val st) :
    page_tables.copy.walk_level2_loop s.pool s.used base bits table levels start ⦃ r levels' =>
      Agrees (fun _ st' => VisitRepr levels'.val st') tableErrorOf r
        ((tablesOf s).walkLevel2 (word64 base) (byte bits)
          (((tablesOf s).table table.val).toList.drop start.val) st) ⦄ := by
  unfold page_tables.copy.walk_level2_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array U8 N × Usize) => 512 - x.2.val)
    (inv := fun (x : Aeneas.Std.Array U8 N × Usize) => ∃ st', VisitRepr x.1.val st' ∧
      (tablesOf s).walkLevel2 (word64 base) (byte bits)
          (((tablesOf s).table table.val).toList.drop x.2.val) st' =
        (tablesOf s).walkLevel2 (word64 base) (byte bits)
          (((tablesOf s).table table.val).toList.drop start.val) st)
  · rintro ⟨lv, index⟩ ⟨st', hV', hinv⟩
    simp only at hV' hinv
    unfold page_tables.copy.walk_level2_loop.body
    simp only [entries_eq, copy_leaves_eq]
    step*
    · obtain ⟨p, -, -, hlt, -⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      exact copy_lt_length _ (Nat.lt_of_lt_of_le hlt hu)
    · obtain ⟨p, -, -, hlt, -⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      exact copy_lt_length _ (Nat.lt_of_lt_of_le hlt hu)
    · obtain ⟨p, hp, hpe, hlt, hl, h0⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      subst hpe index_mut_back_post a_post entry_post a1_post
      have hck : checkLeaves (byte bits) ((tablesOf s).table val.val).toList = .ok () := by
        obtain ⟨u, hu', -⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› r1_post)
        rw [copy_table_toList s (copy_lt_val_length _ (Nat.lt_of_lt_of_le hlt hu))]; exact hu'
      have hd := copy_entry_lt s ht (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry table.val index.val) = true := by
        rw [hd, ← b_post]; exact ‹b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      refine ⟨⟨{ st' with reached := st'.reached ++ [val.val], leaves := st'.leaves ++ [val.val] },
        ?_, ?_⟩, by have := copy_lt_512 ‹index < 512#usize›; omega⟩
      · rw [Array.set_val_eq]; exact visitRepr_set3 hV' hl
      · rw [index1_post, ← hinv, clone_table_drop _ _ hi,
          walkLevel2_next _ _ _ _ hv (by rw [hd]; exact hp) hck]
    · obtain ⟨p, hp, hpe, hlt, hl, h0⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      subst hpe a_post entry_post a1_post
      have hck : checkLeaves (byte bits) ((tablesOf s).table val.val).toList =
          .error (tableErrorOf e) := by
        rw [copy_table_toList s (copy_lt_val_length _ (Nat.lt_of_lt_of_le hlt hu))]
        exact agrees_err_of_branch cf1_post ‹_› residual_post r1_post
      have hd := copy_entry_lt s ht (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry table.val index.val) = true := by
        rw [hd, ← b_post]; exact ‹b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      rw [r2_post, agrees_err_iff, ← hinv, clone_table_drop _ _ hi,
        walkLevel2_leaves_error _ _ _ _ hv (by rw [hd]; exact hp) hck, e_post]
    · subst a_post entry_post
      have hr := agrees_err_of_branch cf_post ‹_› residual_post r_post
      have hd := copy_entry_lt s ht (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry table.val index.val) = true := by
        rw [hd, ← b_post]; exact ‹b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      rw [r1_post, agrees_err_iff, ← hinv, clone_table_drop _ _ hi,
        walkLevel2_reach_error _ _ _ _ hv (by rw [hd]; exact hr), e_post]
    · subst a_post entry_post
      have hd := copy_entry_lt s ht (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry table.val index.val) = false := by
        rw [hd, ← b_post]; simpa using ‹¬b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      refine ⟨⟨st', hV', ?_⟩, by have := copy_lt_512 ‹index < 512#usize›; omega⟩
      rw [index1_post, ← hinv, clone_table_drop _ _ hi, walkLevel2_invalid _ _ _ _ _ hv]
    · have hge : ENTRIES ≤ index.val := copy_ge_512 ‹¬index < 512#usize›
      rw [← hinv, clone_table_drop_end _ _ hge]
      exact hV'
  · exact ⟨st, hV, rfl⟩

/-- What `walk_level2(pool, used, base, bits, table, levels)` returns: for
every visit that the marks stand for, `Tables.walkLevel2` of the entries of
the table, the marks after it standing for the visit after it. -/
def Level2Post {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) (base : U64) (bits : U8)
    (table : Usize) (levels : Aeneas.Std.Array U8 N)
    (r : core.result.Result Unit page_tables.TableError) (levels' : Aeneas.Std.Array U8 N) : Prop :=
  ∀ st, VisitRepr levels.val st → Agrees (fun _ st' => VisitRepr levels'.val st') tableErrorOf r
    ((tablesOf s).walkLevel2 (word64 base) (byte bits) ((tablesOf s).table table.val).toList st)

/-- `walk_level2(pool, used, base, bits, table, levels)` on marks that stand
for a visit, for a record of at most `N` tables, a width below 64 and a
table of the pool: for every visit that the marks stand for,
`Tables.walkLevel2` of the entries of the table, the marks after it standing
for the visit after it. -/
@[step] theorem copy_walk_level2_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (base : U64) (bits : U8) (table : Usize) (levels : Aeneas.Std.Array U8 N)
    (hu : s.used.val ≤ N.val) (hb : bits.val < 64) (ht : table.val < N.val)
    (hV : ∃ st, VisitRepr levels.val st) :
    page_tables.copy.walk_level2 s.pool s.used base bits table levels ⦃ r levels' =>
      Level2Post s base bits table levels r levels' ⦄ := by
  have H : ∀ st, VisitRepr levels.val st →
      page_tables.copy.walk_level2 s.pool s.used base bits table levels ⦃ r levels' =>
        Agrees (fun _ st' => VisitRepr levels'.val st') tableErrorOf r
          ((tablesOf s).walkLevel2 (word64 base) (byte bits) ((tablesOf s).table table.val).toList
            st) ⦄ := by
    intro st hst
    have h := copy_walk_level2_loop_spec s base bits table levels 0#usize st hu hb ht hst
    have h0 : (0#usize).val = 0 := by simp
    rw [h0, List.drop_zero] at h
    exact h
  obtain ⟨st0, h0⟩ := hV
  obtain ⟨⟨r, lv⟩, ha, -⟩ := spec_iff.1 (H st0 h0)
  refine spec_of_eq ha ?_
  intro st hst
  have h := eq_of_spec ha (H st hst)
  exact h

/-- The loop of `walk_root(pool, used, base, bits, levels)` from an index, on
marks that stand for a visit, for a record of at most `N` tables, a width
below 64 and a pool of at least one table: `Tables.walkRoot` of the entries
of the root from that index. -/
theorem copy_walk_root_loop_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (base : U64) (bits : U8) (levels : Aeneas.Std.Array U8 N) (start : Usize) (st : Visit)
    (hu : s.used.val ≤ N.val) (hb : bits.val < 64) (hN : 0 < N.val)
    (hV : VisitRepr levels.val st) :
    page_tables.copy.walk_root_loop s.pool s.used base bits levels start ⦃ r levels' =>
      Agrees (fun _ st' => VisitRepr levels'.val st') tableErrorOf r
        ((tablesOf s).walkRoot (word64 base) (byte bits)
          (((tablesOf s).table 0).toList.drop start.val) st) ⦄ := by
  unfold page_tables.copy.walk_root_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array U8 N × Usize) => 512 - x.2.val)
    (inv := fun (x : Aeneas.Std.Array U8 N × Usize) => ∃ st', VisitRepr x.1.val st' ∧
      (tablesOf s).walkRoot (word64 base) (byte bits)
          (((tablesOf s).table 0).toList.drop x.2.val) st' =
        (tablesOf s).walkRoot (word64 base) (byte bits)
          (((tablesOf s).table 0).toList.drop start.val) st)
  · rintro ⟨lv, index⟩ ⟨st', hV', hinv⟩
    simp only at hV' hinv
    unfold page_tables.copy.walk_root_loop.body
    simp only [entries_eq, copy_level2_eq]
    step*
    · obtain ⟨p, -, -, hlt, -⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      exact copy_lt_length _ (Nat.lt_of_lt_of_le hlt hu)
    · obtain ⟨p, -, -, hlt, -⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      exact Nat.lt_of_lt_of_le hlt hu
    · obtain ⟨p, -, -, -, hl, h0⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      exact ⟨_, by rw [levels1_post, Array.set_val_eq]; exact visitRepr_set2 hV' hl h0⟩
    · obtain ⟨p, hp, hpe, -, hl, h0⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      subst hpe a_post entry_post
      have hV1 : VisitRepr levels1.val { st' with reached := st'.reached ++ [val.val] } := by
        rw [levels1_post, Array.set_val_eq]; exact visitRepr_set2 hV' hl h0
      obtain ⟨st'', hw, hV''⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› (r1_post _ hV1))
      have hd := copy_entry_lt s hN (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry 0 index.val) = true := by
        rw [hd, ← b_post]; exact ‹b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      refine ⟨⟨st'', hV'', ?_⟩, by have := copy_lt_512 ‹index < 512#usize›; omega⟩
      rw [index1_post, ← hinv, clone_table_drop _ _ hi,
        walkRoot_next _ _ _ _ hv (by rw [hd]; exact hp) hw]
    · obtain ⟨p, hp, hpe, -, hl, h0⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      subst hpe a_post entry_post
      have hV1 : VisitRepr levels1.val { st' with reached := st'.reached ++ [val.val] } := by
        rw [levels1_post, Array.set_val_eq]; exact visitRepr_set2 hV' hl h0
      have hw := agrees_err_of_branch cf1_post ‹_› residual_post (r1_post _ hV1)
      have hd := copy_entry_lt s hN (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry 0 index.val) = true := by
        rw [hd, ← b_post]; exact ‹b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      rw [r2_post, agrees_err_iff, ← hinv, clone_table_drop _ _ hi,
        walkRoot_level2_error _ _ _ _ hv (by rw [hd]; exact hp) hw, e_post]
    · subst a_post entry_post
      have hr := agrees_err_of_branch cf_post ‹_› residual_post r_post
      have hd := copy_entry_lt s hN (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry 0 index.val) = true := by
        rw [hd, ← b_post]; exact ‹b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      rw [r1_post, agrees_err_iff, ← hinv, clone_table_drop _ _ hi,
        walkRoot_reach_error _ _ _ _ hv (by rw [hd]; exact hr), e_post]
    · subst a_post entry_post
      have hd := copy_entry_lt s hN (copy_lt_512 ‹index < 512#usize›)
      have hv : isValid ((tablesOf s).entry 0 index.val) = false := by
        rw [hd, ← b_post]; simpa using ‹¬b = true›
      have hi : index.val < ENTRIES := copy_lt_512 ‹index < 512#usize›
      refine ⟨⟨st', hV', ?_⟩, by have := copy_lt_512 ‹index < 512#usize›; omega⟩
      rw [index1_post, ← hinv, clone_table_drop _ _ hi, walkRoot_invalid _ _ _ _ _ hv]
    · have hge : ENTRIES ≤ index.val := copy_ge_512 ‹¬index < 512#usize›
      rw [← hinv, clone_table_drop_end _ _ hge]
      exact hV'
  · exact ⟨st, hV, rfl⟩

/-- `walk_root(pool, used, base, bits, levels)` on the marks of the start of
the walk, for a record of at most `N` tables, a width below 64 and a pool of
at least one table: `Tables.walkRoot` of the entries of the root from the
visit of the root. -/
@[step] theorem copy_walk_root_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (base : U64) (bits : U8) (levels : Aeneas.Std.Array U8 N)
    (hu : s.used.val ≤ N.val) (hb : bits.val < 64) (hN : 0 < N.val)
    (hV : VisitRepr levels.val ⟨[0], []⟩) :
    page_tables.copy.walk_root s.pool s.used base bits levels ⦃ r levels' =>
      Agrees (fun _ st' => VisitRepr levels'.val st') tableErrorOf r
        ((tablesOf s).walkRoot (word64 base) (byte bits) ((tablesOf s).table 0).toList
          ⟨[0], []⟩) ⦄ := by
  have h := copy_walk_root_loop_spec s base bits levels 0#usize ⟨[0], []⟩ hu hb hN hV
  have h0 : (0#usize).val = 0 := by simp
  rw [h0, List.drop_zero] at h
  exact h

/-- The loop of `all_reached(levels, used)` from a table, every table below
it marked, for a record of at most `N` tables: whether every table in use is
marked. -/
theorem all_reached_loop_spec {N : Usize} (levels : Aeneas.Std.Array U8 N) (used start : Usize)
    (hu : used.val ≤ N.val)
    (hs : ∀ t, t < start.val → ∃ h : t < levels.val.length, (levels.val[t]'h).val ≠ 0) :
    page_tables.copy.all_reached_loop levels used start ⦃ b =>
      (b = true ↔ ∀ t, t < used.val →
        ∃ h : t < levels.val.length, (levels.val[t]'h).val ≠ 0) ⦄ := by
  unfold page_tables.copy.all_reached_loop
  apply loop.spec_decr_nat
    (measure := fun (t : Usize) => used.val - t.val)
    (inv := fun (t : Usize) => ∀ t', t' < t.val → ∃ h : t' < levels.val.length,
      (levels.val[t']'h).val ≠ 0)
  · intro table hinv
    unfold page_tables.copy.all_reached_loop.body
    simp only [copy_unreached_eq]
    step*
    have htu : table.val < used.val := ‹table < used›
    refine ⟨fun t' ht' => ?_, by omega⟩
    by_cases htt : t' < table.val
    · exact hinv t' htt
    · have ht : t' = table.val := by omega
      subst ht
      refine ⟨copy_lt_val_length _ (Nat.lt_of_lt_of_le htu hu), fun h0 => ‹¬i = 0#u8› ?_⟩
      rw [copy_u8_eq_zero_iff, i_post]; exact h0
  · exact hs

/-- `all_reached(levels, used)` for a record of at most `N` tables: whether
every table in use is marked. -/
@[step] theorem all_reached_spec {N : Usize} (levels : Aeneas.Std.Array U8 N) (used : Usize)
    (hu : used.val ≤ N.val) :
    page_tables.copy.all_reached levels used ⦃ b =>
      (b = true ↔ ∀ t, t < used.val →
        ∃ h : t < levels.val.length, (levels.val[t]'h).val ≠ 0) ⦄ :=
  all_reached_loop_spec levels used 0#usize hu (fun t ht => by simp at ht)

/-- The loop of `next_valid(pool, used, table, entry)`, for a record of at
most `N` tables: the next valid entry of the source in table-major order,
`NextValid`. -/
theorem next_valid_loop_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (table entry : Usize) (hu : s.used.val ≤ N.val) :
    page_tables.copy.next_valid_loop s.pool s.used table entry ⦃ t' i' =>
      NextValid (tablesOf s) table.val entry.val t'.val i'.val ⦄ := by
  unfold page_tables.copy.next_valid_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Usize × Usize) => (s.used.val - p.1.val) * 513 + (512 - p.2.val))
    (inv := fun (p : Usize × Usize) => ∀ sb base leaf,
      restStores (tablesOf s) sb base leaf p.1.val p.2.val =
        restStores (tablesOf s) sb base leaf table.val entry.val)
  · rintro ⟨tb, en⟩ hinv
    simp only at hinv
    unfold page_tables.copy.next_valid_loop.body
    simp only [entries_eq]
    step*
    · subst a_post i_post
      have htu : tb.val < s.used.val := ‹tb < s.used›
      have hd := copy_entry_lt s (Nat.lt_of_lt_of_le htu hu) (copy_lt_512 ‹en < 512#usize›)
      have hv : isValid ((tablesOf s).entry tb.val en.val) = true := by
        rw [hd, ← b_post]; exact ‹b = true›
      have hi : en.val < ENTRIES := copy_lt_512 ‹en < 512#usize›
      have ht : tb.val < (tablesOf s).used := htu
      refine Or.inl ⟨ht, hi, hv, fun sb base leaf => ?_⟩
      rw [← hinv sb base leaf, restStores_valid _ _ _ _ ht hi hv]
    · subst a_post i_post
      have htu : tb.val < s.used.val := ‹tb < s.used›
      have hd := copy_entry_lt s (Nat.lt_of_lt_of_le htu hu) (copy_lt_512 ‹en < 512#usize›)
      have hv : isValid ((tablesOf s).entry tb.val en.val) = false := by
        rw [hd, ← b_post]; simpa using ‹¬b = true›
      have hi : en.val < ENTRIES := copy_lt_512 ‹en < 512#usize›
      have ht : tb.val < (tablesOf s).used := htu
      refine ⟨fun sb base leaf => ?_, by have := copy_lt_512 ‹en < 512#usize›; omega⟩
      rw [entry1_post, ← hinv sb base leaf, restStores_invalid _ _ _ _ ht hi hv]
    · have hi : ENTRIES ≤ en.val := copy_ge_512 ‹¬en < 512#usize›
      have htu : tb.val < s.used.val := ‹tb < s.used›
      have ht : tb.val < (tablesOf s).used := htu
      have h0 : (0#usize).val = 0 := by simp
      refine ⟨fun sb base leaf => ?_, by omega⟩
      rw [table1_post, h0, ← hinv sb base leaf, restStores_end _ _ _ _ ht hi]
    · refine Or.inr ⟨Nat.le_refl _, fun sb base leaf => ?_⟩
      rw [← hinv sb base leaf, restStores_ge _ _ _ _ _ (Nat.le_of_not_lt ‹¬tb < s.used›)]
  · intro sb base leaf; rfl

/-- `next_valid(pool, used, table, entry)`, for a record of at most `N`
tables: the next valid entry of the source in table-major order,
`NextValid`. -/
@[step] theorem next_valid_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (table entry : Usize) (hu : s.used.val ≤ N.val) :
    page_tables.copy.next_valid s.pool s.used table entry ⦃ t' i' =>
      NextValid (tablesOf s) table.val entry.val t'.val i'.val ⦄ :=
  next_valid_loop_spec s table entry hu

/-! ## The plan iterator -/

/-- A plan iterator of a copy stands for the rest `l` of the plan of
`Tables.cloneKernelFrom`, with `leaf` telling the level 3 tables of the
source: the record of its source is at most `N`; a table in use is a level
3 table exactly when its mark is 3; a valid entry of any other table in use
points at or above the source's pool and below `N` tables from it; the
target's pool ends below $2^{64}$; and either the iterator is not done and
`l` is the `Zero` steps from `zeroed` to `zero_tables`, the stores from its
position (`restStores`) and `Sync`, or it is done, past its `Zero` steps,
and `l` is empty. -/
def CloneRest {N : Usize} {upper : Bool} (leaf : Nat → Bool) (it : page_tables.ClonePlan N upper)
    (l : Plan) : Prop :=
  it.source.used.val ≤ N.val ∧
  (∀ t (h : t < it.levels.val.length), t < it.source.used.val →
    (leaf t = true ↔ (it.levels.val[t]'h).val = 3)) ∧
  (∀ t, t < it.source.used.val → leaf t = false → ∀ i, i < ENTRIES →
    isValid ((tablesOf it.source).entry t i) = true →
    it.source_base.val ≤ (outputAddress ((tablesOf it.source).entry t i)).toNat ∧
    ((outputAddress ((tablesOf it.source).entry t i)).toNat - it.source_base.val) / PAGE_SIZE <
      N.val) ∧
  it.base.val + PAGE_SIZE * N.val < 2 ^ 64 ∧
  ((it.done = false ∧
      l = (List.range' it.zeroed.val (it.zero_tables.val - it.zeroed.val)).map Step.zero ++
        restStores (tablesOf it.source) (word64 it.source_base) (word64 it.base) leaf
          it.table.val it.entry.val ++ [.sync]) ∨
    (it.done = true ∧ it.zero_tables.val ≤ it.zeroed.val ∧ l = []))

/-- `ClonePlan::next()` once done and past the `Zero` steps: none, and the
same iterator. -/
theorem clone_next_done {N : Usize} {upper : Bool} (it : page_tables.ClonePlan N upper)
    (hd : it.done = true) (hz : it.zero_tables.val ≤ it.zeroed.val) :
    page_tables.copy.ClonePlan.next it = .ok (none, it) := by
  unfold page_tables.copy.ClonePlan.next
  have h : ¬ it.zeroed < it.zero_tables := by scalar_tac
  simp only [h, ↓reduceIte, hd]

/-- `ClonePlan::next()` on an iterator that stands for `b :: l`: a step that
stands for `b`, and an iterator that stands for `l`. -/
theorem clone_next_cons {N : Usize} {upper : Bool} (leaf : Nat → Bool)
    (it : page_tables.ClonePlan N upper) (b : Step) (l : Plan) (h : CloneRest leaf it (b :: l)) :
    page_tables.copy.ClonePlan.next it ⦃ o it' =>
      ∃ a, o = some a ∧ StepRepr a b ∧ CloneRest leaf it' l ⦄ := by
  obtain ⟨hu, hlv, hnl, hbase, hph⟩ := h
  rcases hph with ⟨hd, hl⟩ | ⟨-, -, hl⟩
  swap
  · cases hl
  unfold page_tables.copy.ClonePlan.next
  simp only [page_size_eq, copy_leaves_eq]
  step*
  · -- a `Zero` step
    have hz : it.zeroed.val < it.zero_tables.val := ‹it.zeroed < it.zero_tables›
    simp only [clone_zeros_succ hz, List.cons_append, List.cons.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨_, rfl, rfl, hu, hlv, hnl, hbase, Or.inl ⟨hd, ?_⟩⟩
    dsimp only
    rw [i_post]
  · -- no valid entry left: `Sync`
    have hz : it.zero_tables.val ≤ it.zeroed.val :=
      Nat.le_of_not_lt ‹¬it.zeroed < it.zero_tables›
    have hr : restStores (tablesOf it.source) (word64 it.source_base) (word64 it.base) leaf
        it.table.val it.entry.val = [] := by
      rcases table_post with ⟨hlt, -⟩ | ⟨-, h⟩
      · exact absurd ‹table ≥ it.source.used› (Nat.not_le.2 hlt)
      · exact h _ _ _
    rw [hr, show it.zero_tables.val - it.zeroed.val = 0 by omega, List.range'_zero, List.map_nil,
      List.nil_append, List.nil_append, List.cons.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨_, rfl, rfl, hu, hlv, hnl, hbase, Or.inr ⟨rfl, hz, rfl⟩⟩
  · have hi : entry.val < ENTRIES := by
      rcases table_post with ⟨-, hi, -⟩ | ⟨hge, -⟩
      · exact hi
      · exact absurd hge ‹¬table ≥ it.source.used›
    have hi' : entry.val < 512 := hi
    scalar_tac
  · have hi : entry.val < ENTRIES := by
      rcases table_post with ⟨-, hi, -⟩ | ⟨hge, -⟩
      · exact hi
      · exact absurd hge ‹¬table ≥ it.source.used›
    have hi' : entry.val < 512 := hi
    subst a_post
    scalar_tac
  · -- a store into a level 3 table: the entry itself
    obtain ⟨hlt, hi, hv, hst⟩ : table.val < (tablesOf it.source).used ∧ entry.val < ENTRIES ∧
        isValid ((tablesOf it.source).entry table.val entry.val) = true ∧
        ∀ sb base leaf, restStores (tablesOf it.source) sb base leaf it.table.val it.entry.val =
          .store table.val entry.val (copyValue sb base (leaf table.val)
            ((tablesOf it.source).entry table.val entry.val)) ::
            restStores (tablesOf it.source) sb base leaf table.val (entry.val + 1) := by
      rcases table_post with h | ⟨hge, -⟩
      · exact h
      · exact absurd hge ‹¬table ≥ it.source.used›
    have hi' : entry.val < 512 := hi
    subst a_post d_post
    have he := copy_entry_lt it.source (Nat.lt_of_lt_of_le hlt hu) hi'
    have hz : it.zero_tables.val ≤ it.zeroed.val :=
      Nat.le_of_not_lt ‹¬it.zeroed < it.zero_tables›
    have hleaf : leaf table.val = true := by
      rw [hlv table.val (by rw [it.levels.property]; exact Nat.lt_of_lt_of_le hlt hu) hlt,
        ← i1_post, ‹i1 = 3#u8›]
      rfl
    rw [hst, show it.zero_tables.val - it.zeroed.val = 0 by omega, List.range'_zero, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨_, rfl, ?_, hu, hlv, hnl, hbase, Or.inl ⟨rfl, ?_⟩⟩
    · rw [hleaf]
      exact congrArg (Step.store table.val entry.val) he.symm
    · dsimp only
      rw [i_post, show it.zero_tables.val - it.zeroed.val = 0 by omega, List.range'_zero,
        List.map_nil, List.nil_append]
  · -- the output address of a table descriptor is at or above the source's pool
    obtain ⟨hlt, hi, hv, -⟩ : table.val < (tablesOf it.source).used ∧ entry.val < ENTRIES ∧
        isValid ((tablesOf it.source).entry table.val entry.val) = true ∧ True := by
      rcases table_post with ⟨h1, h2, h3, -⟩ | ⟨hge, -⟩
      · exact ⟨h1, h2, h3, trivial⟩
      · exact absurd hge ‹¬table ≥ it.source.used›
    have hi' : entry.val < 512 := hi
    subst a_post d_post
    have he := copy_entry_lt it.source (Nat.lt_of_lt_of_le hlt hu) hi'
    have hleaf : leaf table.val = false := by
      rw [← Bool.not_eq_true,
          hlv table.val (by rw [it.levels.property]; exact Nat.lt_of_lt_of_le hlt hu)
        (by rw [tablesOf_used] at hlt; exact hlt), ← i1_post]
      intro h3; exact ‹¬i1 = 3#u8› (copy_u8_eq_three_iff.2 h3)
    obtain ⟨h1, -⟩ := hnl table.val hlt hleaf entry.val hi hv
    have hi2 : i2.val = (outputAddress ((tablesOf it.source).entry table.val entry.val)).toNat := by
      rw [he, ← i2_post, word64_toNat]
    rw [hi2]; exact h1
  · -- the target's table fits in 64 bits
    obtain ⟨hlt, hi, hv, -⟩ : table.val < (tablesOf it.source).used ∧ entry.val < ENTRIES ∧
        isValid ((tablesOf it.source).entry table.val entry.val) = true ∧ True := by
      rcases table_post with ⟨h1, h2, h3, -⟩ | ⟨hge, -⟩
      · exact ⟨h1, h2, h3, trivial⟩
      · exact absurd hge ‹¬table ≥ it.source.used›
    have hi' : entry.val < 512 := hi
    subst a_post d_post
    have he := copy_entry_lt it.source (Nat.lt_of_lt_of_le hlt hu) hi'
    have hleaf : leaf table.val = false := by
      rw [← Bool.not_eq_true,
          hlv table.val (by rw [it.levels.property]; exact Nat.lt_of_lt_of_le hlt hu)
        (by rw [tablesOf_used] at hlt; exact hlt), ← i1_post]
      intro h3; exact ‹¬i1 = 3#u8› (copy_u8_eq_three_iff.2 h3)
    obtain ⟨-, h2⟩ := hnl table.val hlt hleaf entry.val hi hv
    have hi2 : i2.val = (outputAddress ((tablesOf it.source).entry table.val entry.val)).toNat := by
      rw [he, ← i2_post, word64_toNat]
    have hidx : index.val < N.val := by
      rw [index_post, i3_post, hi2]; exact h2
    have hi4 : i4.val = index.val := by
      rw [i4_post]; exact UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := N.hmax; omega)
    have hb' : it.base.val + 4096 * N.val < 2 ^ 64 := hbase
    rw [hi4]; omega
  · -- a store into a level 1 or 2 table: the table descriptor of the target's table
    obtain ⟨hlt, hi, hv, hst⟩ : table.val < (tablesOf it.source).used ∧ entry.val < ENTRIES ∧
        isValid ((tablesOf it.source).entry table.val entry.val) = true ∧
        ∀ sb base leaf, restStores (tablesOf it.source) sb base leaf it.table.val it.entry.val =
          .store table.val entry.val (copyValue sb base (leaf table.val)
            ((tablesOf it.source).entry table.val entry.val)) ::
            restStores (tablesOf it.source) sb base leaf table.val (entry.val + 1) := by
      rcases table_post with h | ⟨hge, -⟩
      · exact h
      · exact absurd hge ‹¬table ≥ it.source.used›
    have hi' : entry.val < 512 := hi
    subst a_post d_post
    have he := copy_entry_lt it.source (Nat.lt_of_lt_of_le hlt hu) hi'
    have hz : it.zero_tables.val ≤ it.zeroed.val :=
      Nat.le_of_not_lt ‹¬it.zeroed < it.zero_tables›
    have hleaf : leaf table.val = false := by
      rw [← Bool.not_eq_true,
          hlv table.val (by rw [it.levels.property]; exact Nat.lt_of_lt_of_le hlt hu)
        (by rw [tablesOf_used] at hlt; exact hlt), ← i1_post]
      intro h3; exact ‹¬i1 = 3#u8› (copy_u8_eq_three_iff.2 h3)
    obtain ⟨-, h2⟩ := hnl table.val hlt hleaf entry.val hi hv
    have hi2 : i2.val = (outputAddress ((tablesOf it.source).entry table.val entry.val)).toNat := by
      rw [he, ← i2_post, word64_toNat]
    have hidx : index.val < N.val := by
      rw [index_post, i3_post, hi2]; exact h2
    have hi4 : i4.val = ((outputAddress ((tablesOf it.source).entry table.val entry.val)).toNat -
        (word64 it.source_base).toNat) / PAGE_SIZE := by
      rw [i4_post, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := N.hmax; omega),
        index_post, i3_post, hi2, word64_toNat]
      rfl
    rw [hst, show it.zero_tables.val - it.zeroed.val = 0 by omega, List.range'_zero, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨_, rfl, ?_, hu, hlv, hnl, hbase, Or.inl ⟨rfl, ?_⟩⟩
    · rw [hleaf]
      show Step.store table.val entry.val (word64 i5) = _
      rw [i5_post, address_post1, hi4]
      rfl
    · dsimp only
      rw [i_post, show it.zero_tables.val - it.zeroed.val = 0 by omega, List.range'_zero,
        List.map_nil, List.nil_append]

/-- A plan iterator of a copy that stands for the rest of the plan, by
`CloneRest`, stands for it as an iterator. -/
theorem clone_stands {N : Usize} {upper : Bool} (leaf : Nat → Bool)
    (it : page_tables.ClonePlan N upper) (l : Plan) (h : CloneRest leaf it l) :
    Stands page_tables.copy.ClonePlan.next StepRepr it l := by
  refine stands_of_sim (CloneRest leaf) ?_ (clone_next_cons leaf) l it h
  intro s hs
  obtain ⟨-, -, -, -, hph⟩ := hs
  rcases hph with ⟨-, hl⟩ | ⟨hd, hz, -⟩
  · simp at hl
  · have hn := clone_next_done s hd hz
    rw [hn, spec_ok, uncurry'_pair]
    exact ⟨rfl, hn⟩

/-! ## The entry -/

/-- A first check of a pool that the code passed: its check of the
specification passes. -/
theorem clone_pool_ok {N : Usize} {base : U64} {bits : U8} {v : Unit}
    (hr : Agrees (fun _ _ => True) tableErrorOf (.Ok v : core.result.Result Unit page_tables.TableError)
      (checkPool N.val (word64 base) (byte bits))) :
    checkPool N.val (word64 base) (byte bits) = .ok () := by
  obtain ⟨u, hu, -⟩ := agrees_ok_iff.1 hr
  exact hu

/-- Two pools that pass their first checks: at least one table, ends at or
below $2^{48}$, a width below 64. -/
theorem clone_pools {N : Usize} {sb base : U64} {bits : U8}
    (h1 : checkPool N.val (word64 sb) (byte bits) = .ok ())
    (h2 : checkPool N.val (word64 base) (byte bits) = .ok ()) :
    0 < N.val ∧ sb.val + 4096 * N.val ≤ 2 ^ 48 ∧ base.val + 4096 * N.val ≤ 2 ^ 48 ∧
      bits.val < 64 := by
  obtain ⟨hN, hs, hb⟩ := clone_checkPool_bound h1
  obtain ⟨-, hs2, -⟩ := clone_checkPool_bound h2
  rw [word64_toNat] at hs hs2
  rw [byte_toNat] at hb
  exact ⟨hN, hs, hs2, hb⟩

/-- A failure of the code that leaves the set as it was, against a failure of
the specification with the error of the same name. -/
theorem clone_writes_err {N : Usize} {upper : Bool} {s : page_tables.Tables N upper}
    {E : Except TableError (Tables (regionOf upper) N.val × Plan)} {x : page_tables.TableError}
    (h : E = .error (tableErrorOf x)) :
    Writes (fun s' S => tablesOf s' = S) (Stands page_tables.copy.ClonePlan.next StepRepr)
      (fun x1 x2 => tableErrorOf x1 = x2) s
      (.Err x : core.result.Result (page_tables.ClonePlan N upper) page_tables.TableError) s E := by
  subst h; exact ⟨rfl, rfl⟩

/-- The success of the entry, for pools that pass their first checks and do
not overlap, a record of the source from 1 to `N`, a walk of the source that
succeeds with marks that stand for its visit and mark every table in use,
and `zero_tables` the tables in use of the target: the set with the record
of the source, and a plan iterator at its start that stands for the plan of
the specification. -/
theorem clone_ok_writes {N : Usize} {upper : Bool} (s source : page_tables.Tables N upper)
    (sourceBase base : U64) (bits : U8) (levels : Aeneas.Std.Array U8 N) (zt : Usize) (st : Visit)
    (hp1 : checkPool N.val (word64 sourceBase) (byte bits) = .ok ())
    (hp2 : checkPool N.val (word64 base) (byte bits) = .ok ())
    (h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧ base.val < sourceBase.val + 4096 * N.val))
    (hu : source.used.val ≤ N.val) (h0 : source.used.val ≠ 0)
    (hw : (tablesOf source).walkRoot (word64 sourceBase) (byte bits)
      ((tablesOf source).table 0).toList ⟨[0], []⟩ = .ok st)
    (hV : VisitRepr levels.val st)
    (hall : ∀ t, t < source.used.val → ∃ h : t < levels.val.length, (levels.val[t]'h).val ≠ 0)
    (hz : zt.val = min s.used.val N.val) :
    Writes (fun s' S => tablesOf s' = S) (Stands page_tables.copy.ClonePlan.next StepRepr)
      (fun x1 x2 => tableErrorOf x1 = x2) s
      (.Ok { source := source, source_base := sourceBase, base := base, levels := levels,
             zero_tables := zt, zeroed := 0#usize, table := 0#usize, entry := 0#usize,
             done := false })
      ({ s with used := source.used } : page_tables.Tables N upper)
      ((tablesOf s).cloneKernelFrom (tablesOf source) (word64 sourceBase) (word64 base)
        (byte bits)) := by
  obtain ⟨hN, hb1, hb2, hbits⟩ := clone_pools hp1 hp2
  have hl : (tablesOf source).used ≤ levels.val.length := by
    rw [tablesOf_used, levels.property]; exact hu
  have ha := (visitRepr_all hV hl).2 hall
  have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
      (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
    rw [word64_toNat, word64_toNat]; exact h3
  have h4 : ¬ ((tablesOf source).used = 0 ∨ N.val < (tablesOf source).used) := by
    rw [tablesOf_used]; omega
  rw [cloneKernelFrom_ok hp1 hp2 h3' h4 hw ha]
  refine ⟨clone_stands (fun t => st.leaves.contains t) _ _
    ⟨hu, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩, rfl⟩
  · intro t h _
    exact visitRepr_leaves hV h
  · intro t ht hlf i hi hv
    have hr : t ∈ st.reached := (hV.1 t).2 (hall t ht)
    have hnl : t ∉ st.leaves := by simpa using hlf
    obtain ⟨c, hc⟩ := walkRoot_child hw hr hnl hi hv
    have hci := child?_index hc
    have hcu := child?_some hc
    have hle := clone_child?_le hc
    rw [word64_toNat] at hci hle
    refine ⟨hle, ?_⟩
    rw [← hci]; exact hcu.2
  · show base.val + 4096 * N.val < 2 ^ 64
    omega
  · dsimp only
    have h0' : (0#usize).val = 0 := by simp
    rw [h0', restStores_zero, hz, Nat.sub_zero, ← List.range_eq_range']
    rfl

/-- `Tables::clone_kernel_from(source, source_base, base, bits)`: the
statement `TablesCloneKernelFrom` without its premise. -/
theorem clone_kernel_from_spec {N : Usize} {upper : Bool} (s source : page_tables.Tables N upper)
    (sourceBase base : U64) (bits : U8) :
    page_tables.copy.Tables.clone_kernel_from s source sourceBase base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (Stands page_tables.copy.ClonePlan.next StepRepr)
        (tableErrorOf · = ·) s r s'
        ((tablesOf s).cloneKernelFrom (tablesOf source) (word64 sourceBase) (word64 base)
          (byte bits)) ⦄ := by
  unfold page_tables.copy.Tables.clone_kernel_from
  simp only [page_size_eq, copy_unreached_eq, copy_root_eq]
  step*
  · -- the size of a pool fits in 64 bits
    obtain ⟨hN, hb1, hb2, hbits⟩ :=
      clone_pools (clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post))
      (clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post))
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h4096 : (4096#u64).val = 4096 := rfl
    rw [u64_max_eq, h4096, hiv]
    omega
  · -- the end of the target's pool fits in 64 bits
    obtain ⟨hN, hb1, hb2, hbits⟩ :=
      clone_pools (clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post))
      (clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post))
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    rw [u64_max_eq]
    omega
  · -- the end of the source's pool fits in 64 bits
    obtain ⟨hN, hb1, hb2, hbits⟩ :=
      clone_pools (clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post))
      (clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post))
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    rw [u64_max_eq]
    omega
  · -- the pools overlap
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h1' : sourceBase.val < i1.val := ‹sourceBase < i1›
    have h2' : base.val < i2.val := ‹base < i2›
    have h3 : (word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val := by
      rw [word64_toNat, word64_toNat]; show _ < _ + 4096 * N.val; omega
    have h4 : (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val := by
      rw [word64_toNat, word64_toNat]; show _ < _ + 4096 * N.val; omega
    exact clone_writes_err (cloneKernelFrom_overlap hp1 hp2 h3 h4)
  · -- no table in use in the source
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨-, h2⟩; exact ‹¬base < i2› (show base.val < i2.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    exact clone_writes_err (cloneKernelFrom_used hp1 hp2 h3'
      (by rw [tablesOf_used, ‹source.used = 0#usize›]; left; simp))
  · -- more tables in use in the source than the pool holds
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨-, h2⟩; exact ‹¬base < i2› (show base.val < i2.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    exact clone_writes_err (cloneKernelFrom_used hp1 hp2 h3'
      (Or.inr ‹source.used > N›))
  · exact (clone_pools (clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post))
      (clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post))).2.2.2
  · have hN := (clone_pools (clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post))
      (clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post))).1
    have h0 : (0#usize).val = 0 := by simp
    rw [levels1_post, Array.set_val_eq, Array.repeat_val, h0]
    exact visitRepr_root hN
  · -- success
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨-, h2⟩; exact ‹¬base < i2› (show base.val < i2.val by omega)
    obtain ⟨st, hw, hV2⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf2_post ‹_› r2_post)
    exact clone_ok_writes s source sourceBase base bits levels2 zero_tables st hp1 hp2 h3
      (Nat.le_of_not_lt ‹¬source.used > N›) (copy_usize_ne_zero ‹¬source.used = 0#usize›)
      hw hV2
      (b_post.1 ‹b = true›) zero_tables_post
  · -- a table in use that the walk did not reach
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨-, h2⟩; exact ‹¬base < i2› (show base.val < i2.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    have hu0 : source.used.val ≠ 0 := copy_usize_ne_zero ‹¬source.used = 0#usize›
    have huN : source.used.val ≤ N.val := Nat.le_of_not_lt ‹¬source.used > N›
    have h4 : ¬ ((tablesOf source).used = 0 ∨ N.val < (tablesOf source).used) := by
      rw [tablesOf_used]; omega
    obtain ⟨st, hw, hV2⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf2_post ‹_› r2_post)
    have hl : (tablesOf source).used ≤ levels2.val.length := by
      rw [tablesOf_used, levels2.property]; exact huN
    have ha : ((List.range (tablesOf source).used).any fun t => !st.reached.contains t) = true := by
      rw [← Bool.not_eq_false]
      intro h
      exact ‹¬b = true› (b_post.2 ((visitRepr_all hV2 hl).1 h))
    exact clone_writes_err (cloneKernelFrom_unreached hp1 hp2 h3' h4 hw ha)
  · -- the walk of the source fails
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨-, h2⟩; exact ‹¬base < i2› (show base.val < i2.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    have hu0 : source.used.val ≠ 0 := copy_usize_ne_zero ‹¬source.used = 0#usize›
    have huN : source.used.val ≤ N.val := Nat.le_of_not_lt ‹¬source.used > N›
    have h4 : ¬ ((tablesOf source).used = 0 ∨ N.val < (tablesOf source).used) := by
      rw [tablesOf_used]; omega
    have hw := agrees_err_of_branch cf2_post ‹_› residual_post r2_post
    rw [r3_post]
    exact clone_writes_err (by rw [cloneKernelFrom_walk hp1 hp2 h3' h4 hw, e_post])
  · -- no table in use in the source
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨h1, -⟩; exact ‹¬sourceBase < i1› (show sourceBase.val < i1.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    exact clone_writes_err (cloneKernelFrom_used hp1 hp2 h3'
      (by rw [tablesOf_used, ‹source.used = 0#usize›]; left; simp))
  · -- more tables in use in the source than the pool holds
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨h1, -⟩; exact ‹¬sourceBase < i1› (show sourceBase.val < i1.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    exact clone_writes_err (cloneKernelFrom_used hp1 hp2 h3'
      (Or.inr ‹source.used > N›))
  · exact (clone_pools (clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post))
      (clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post))).2.2.2
  · have hN := (clone_pools (clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post))
      (clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post))).1
    have h0 : (0#usize).val = 0 := by simp
    rw [levels1_post, Array.set_val_eq, Array.repeat_val, h0]
    exact visitRepr_root hN
  · -- success
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨h1, -⟩; exact ‹¬sourceBase < i1› (show sourceBase.val < i1.val by omega)
    obtain ⟨st, hw, hV2⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf2_post ‹_› r2_post)
    exact clone_ok_writes s source sourceBase base bits levels2 zero_tables st hp1 hp2 h3
      (Nat.le_of_not_lt ‹¬source.used > N›) (copy_usize_ne_zero ‹¬source.used = 0#usize›)
      hw hV2
      (b_post.1 ‹b = true›) zero_tables_post
  · -- a table in use that the walk did not reach
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨h1, -⟩; exact ‹¬sourceBase < i1› (show sourceBase.val < i1.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    have hu0 : source.used.val ≠ 0 := copy_usize_ne_zero ‹¬source.used = 0#usize›
    have huN : source.used.val ≤ N.val := Nat.le_of_not_lt ‹¬source.used > N›
    have h4 : ¬ ((tablesOf source).used = 0 ∨ N.val < (tablesOf source).used) := by
      rw [tablesOf_used]; omega
    obtain ⟨st, hw, hV2⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf2_post ‹_› r2_post)
    have hl : (tablesOf source).used ≤ levels2.val.length := by
      rw [tablesOf_used, levels2.property]; exact huN
    have ha : ((List.range (tablesOf source).used).any fun t => !st.reached.contains t) = true := by
      rw [← Bool.not_eq_false]
      intro h
      exact ‹¬b = true› (b_post.2 ((visitRepr_all hV2 hl).1 h))
    exact clone_writes_err (cloneKernelFrom_unreached hp1 hp2 h3' h4 hw ha)
  · -- the walk of the source fails
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have hp2 := clone_pool_ok (agrees_of_branch_ok cf1_post ‹_› r1_post)
    have hiv : i.val = N.val := by rw [i_post, usize_cast_u64_val]
    have h3 : ¬ (sourceBase.val < base.val + 4096 * N.val ∧
        base.val < sourceBase.val + 4096 * N.val) := by
      rintro ⟨h1, -⟩; exact ‹¬sourceBase < i1› (show sourceBase.val < i1.val by omega)
    have h3' : ¬ ((word64 sourceBase).toNat < (word64 base).toNat + PAGE_SIZE * N.val ∧
        (word64 base).toNat < (word64 sourceBase).toNat + PAGE_SIZE * N.val) := by
      rw [word64_toNat, word64_toNat]; exact h3
    have hu0 : source.used.val ≠ 0 := copy_usize_ne_zero ‹¬source.used = 0#usize›
    have huN : source.used.val ≤ N.val := Nat.le_of_not_lt ‹¬source.used > N›
    have h4 : ¬ ((tablesOf source).used = 0 ∨ N.val < (tablesOf source).used) := by
      rw [tablesOf_used]; omega
    have hw := agrees_err_of_branch cf2_post ‹_› residual_post r2_post
    rw [r3_post]
    exact clone_writes_err (by rw [cloneKernelFrom_walk hp1 hp2 h3' h4 hw, e_post])
  · -- the first checks of the target's pool fail
    have hp1 := clone_pool_ok (agrees_of_branch_ok cf_post ‹_› r_post)
    have he := agrees_err_of_branch cf1_post ‹_› residual_post r1_post
    rw [r3_post]
    exact clone_writes_err (by rw [cloneKernelFrom_pool2 hp1 he, e_post])
  · -- the first checks of the source's pool fail
    have he := agrees_err_of_branch cf_post ‹_› residual_post r_post
    rw [r3_post]
    exact clone_writes_err (by rw [cloneKernelFrom_pool1 he, e_post])

end Krepi.Proofs.PageTables.Refinement
