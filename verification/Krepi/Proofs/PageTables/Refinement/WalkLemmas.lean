module

public import Krepi.Statements.PageTables.Representation
public import Krepi.Proofs.PageTables.Refinement.WalkSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the encodings, the ranges and the walk

The triples of the generated functions of the `page-tables` component that
encode descriptors, build and compare physical ranges, check the arguments of
an entry, walk a set and read its records, each a `@[step]` lemma, so that
the proof of a caller steps over the call with the triple of the callee and a
mutant of a callee fails the proof of the callee alone. Each holds without
the premise `Usize64`.

- Constants of the code: `read_only_eq`, `el0_eq`, `inner_shareable_eq`,
  `normal_eq`, `access_eq`, `not_global_eq`, `pxn_eq`, `uxn_eq`,
  `va_limit_eq`, `gib_size_eq` (the constants that are computations, as
  values), `page_size_eq`, `block_size_eq`, `entries_eq`, `direct_base_val`,
  and the words of the masks and type bits: `word64_address_mask`,
  `word64_block_address_mask`, `word64_table_or_page`, `word64_block`,
  `word64_direct_base`.
- Encodings: `kind_bits_spec`, `descriptor_spec` (the statement
  `Descriptor` without its premise), `block_descriptor_spec`,
  `table_descriptor_spec`, `output_address_spec`, `type_bits_spec`,
  `is_valid_spec`.
- Physical ranges: `phys_range_new_spec` (the statement `PhysRangeNew`
  without its premise); `phys_range_end_spec`, `phys_range_contains_spec`,
  `phys_range_overlaps_spec` and `direct_address_spec`, on the numbers of
  ranges whose end fits in 64 bits, with `phys_range_end_repr_spec`,
  `phys_range_contains_repr_spec`, `phys_range_overlaps_repr_spec` and
  `direct_address_repr_spec`, their statements on ranges that stand for
  ranges; and `physRange_start`, `physRange_len`, `physRange_fits`,
  `physRange_endNat`, what a range of the code that stands for a range
  gives.
- Indices: `index1_spec`, `index2_spec`, `index3_spec`.
- Sets of tables: `poolOf_eq` (`poolOf` is `poolView`), `tablesOf_used`,
  `tablesOf_pool`, `tablesOf_mk`, `tablesOf_with_used` (a set whose record
  changes) and `tablesOf_entry` (an entry of the set is the word of the
  descriptor of the code); `planOf_steps`, a write plan with no `Zero`
  steps.
- The walk: `in_use_spec`, `child_index_spec` (against `childIndex`),
  `child_spec` (`Tables.child?`), `walk_level2_spec` (`Tables.walk2`, for a
  pool of at least one table).
- The checks of an entry: `width_ok_spec`, `pool_fits_spec` (for a width
  below 64), `check_pool_spec` (`checkPool`), `in_region_spec`,
  `check_entry_spec` (`checkEntry`, for a nonzero alignment),
  `check_physical_spec` (`checkPhysical`, for a nonzero alignment and a
  width below 64), `table_address_spec` (`tableAddress`, for an address
  that fits in 64 bits).
- Records: `free_tables_spec` (`N - used`), `used_spec` (the statement
  `TablesUsed` without its premise), `new_spec` (`TablesNew` without its
  premise), `is_free_spec`, `room_spec` (`E - extent_count`) and
  `ownershipRepr_extents_length`.
-/
@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Constants of the code -/

theorem read_only_eq : page_tables.encoding.READ_ONLY = ok 128#u64 := by
  unfold page_tables.encoding.READ_ONLY; rfl

theorem el0_eq : page_tables.encoding.EL0 = ok 64#u64 := by
  unfold page_tables.encoding.EL0; rfl

theorem inner_shareable_eq : page_tables.encoding.INNER_SHAREABLE = ok 768#u64 := by
  unfold page_tables.encoding.INNER_SHAREABLE; rfl

theorem normal_eq : page_tables.encoding.NORMAL = ok 4#u64 := by
  unfold page_tables.encoding.NORMAL; rfl

theorem access_eq : page_tables.encoding.ACCESS = ok 1024#u64 := by
  unfold page_tables.encoding.ACCESS; rfl

theorem not_global_eq : page_tables.encoding.NOT_GLOBAL = ok 2048#u64 := by
  unfold page_tables.encoding.NOT_GLOBAL; rfl

theorem pxn_eq : page_tables.encoding.PXN = ok 9007199254740992#u64 := by
  unfold page_tables.encoding.PXN; rfl

theorem uxn_eq : page_tables.encoding.UXN = ok 18014398509481984#u64 := by
  unfold page_tables.encoding.UXN; rfl

theorem va_limit_eq : page_tables.VA_LIMIT = ok 549755813888#u64 := by
  unfold page_tables.VA_LIMIT; rfl

theorem page_size_eq : page_tables.PAGE_SIZE = 4096#u64 := by
  unfold page_tables.PAGE_SIZE; rfl

theorem block_size_eq : page_tables.BLOCK_SIZE = 2097152#u64 := by
  unfold page_tables.BLOCK_SIZE; rfl

theorem entries_eq : page_tables.ENTRIES = 512#usize := by
  unfold page_tables.ENTRIES; rfl

theorem gib_size_eq : page_tables.boot.GIB_SIZE = ok 1073741824#u64 := by
  unfold page_tables.boot.GIB_SIZE; rfl

theorem word64_block : word64 page_tables.encoding.BLOCK = BLOCK := by
  unfold page_tables.encoding.BLOCK; rfl

theorem word64_address_mask : word64 page_tables.encoding.ADDRESS_MASK = ADDRESS_MASK := by
  unfold page_tables.encoding.ADDRESS_MASK; rfl

theorem word64_block_address_mask :
    word64 page_tables.encoding.BLOCK_ADDRESS_MASK = BLOCK_ADDRESS_MASK := by
  unfold page_tables.encoding.BLOCK_ADDRESS_MASK; rfl

theorem word64_table_or_page : word64 page_tables.encoding.TABLE_OR_PAGE = TABLE_OR_PAGE := by
  unfold page_tables.encoding.TABLE_OR_PAGE; rfl

theorem direct_base_val : page_tables.DIRECT_BASE.val = 18446743523953737728 := by
  unfold page_tables.DIRECT_BASE; rfl

theorem word64_direct_base : word64 page_tables.DIRECT_BASE = DIRECT_BASE := by
  unfold page_tables.DIRECT_BASE; rfl

/-! ## Encodings -/

/-- `Kind::bits()`: the bits of the attributes of the kind. -/
@[step] theorem kind_bits_spec (k : page_tables.Kind) :
    page_tables.encoding.Kind.bits k ⦃ b => word64 b = (kindOf k).attributes.bits ⦄ := by
  cases k <;>
    simp only [page_tables.encoding.Kind.bits, read_only_eq, el0_eq, inner_shareable_eq,
      normal_eq, access_eq, not_global_eq, pxn_eq, uxn_eq, bind_ok, lift] <;>
    exact spec_of_eq rfl (by decide)

/-- `descriptor(kind, address)`: the page descriptor of `descriptor`. -/
@[step] theorem descriptor_spec (k : page_tables.Kind) (address : U64) :
    page_tables.descriptor k address ⦃ d => word64 d = descriptor (kindOf k) (word64 address) ⦄ := by
  unfold page_tables.descriptor
  step*
  rw [word64_or, word64_congr i2_post, word64_or, word64_congr i_post, word64_and, i1_post,
    word64_address_mask, word64_table_or_page]
  rfl

/-- `block_descriptor(address)`: the block descriptor of `blockDescriptor`. -/
@[step] theorem block_descriptor_spec (address : U64) :
    page_tables.encoding.block_descriptor address ⦃ d =>
      word64 d = blockDescriptor (word64 address) ⦄ := by
  unfold page_tables.encoding.block_descriptor
  step*
  rw [word64_and, i1_post, i2_post, word64_not, word64_congr i_post, word64_and,
    word64_block_address_mask]
  rfl

/-- `table_descriptor(address)`: the table descriptor of `tableDescriptor`. -/
@[step] theorem table_descriptor_spec (address : U64) :
    page_tables.encoding.table_descriptor address ⦃ d =>
      word64 d = tableDescriptor (word64 address) ⦄ := by
  unfold page_tables.encoding.table_descriptor
  step*
  rw [word64_or, word64_congr i_post, word64_and, word64_address_mask, word64_table_or_page]
  rfl

/-- `output_address(d)`: bits 12 to 47, `outputAddress`. -/
@[step] theorem output_address_spec (d : U64) :
    page_tables.encoding.output_address d ⦃ a => word64 a = outputAddress (word64 d) ⦄ := by
  unfold page_tables.encoding.output_address
  exact spec_of_eq rfl (by rw [word64_and, word64_address_mask]; rfl)

/-- `type_bits(d)`: bits 1 and 0, `typeBits`. -/
@[step] theorem type_bits_spec (d : U64) :
    page_tables.encoding.type_bits d ⦃ t => word64 t = typeBits (word64 d) ⦄ := by
  unfold page_tables.encoding.type_bits
  exact spec_of_eq rfl (by rw [word64_and]; rfl)

/-- `is_valid(d)`: `isValid`. -/
@[step] theorem is_valid_spec (d : U64) :
    page_tables.encoding.is_valid d ⦃ b => b = isValid (word64 d) ⦄ := by
  unfold page_tables.encoding.is_valid
  step*
  rw [isValid, ← i_post, word64_bne_zero]

/-! ## Physical ranges -/

theorem physRange_start {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R) :
    R.start.toNat = r.start.val := by rw [h.1, word64_toNat]

theorem physRange_len {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R) :
    R.len.toNat = r.len.val := by rw [h.2, word64_toNat]

/-- The end of a range of the code that stands for a range fits in 64 bits.
-/
theorem physRange_fits {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R) :
    r.start.val + r.len.val < 2 ^ 64 := by
  have := R.fits; rwa [physRange_start h, physRange_len h] at this

theorem physRange_endNat {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R) :
    R.endNat = r.start.val + r.len.val := endNat_of h.1 h.2

/-- `PhysRange::new(start, len)`: the range of `PhysRange.new`, or its error. -/
@[step] theorem phys_range_new_spec (start len : U64) :
    page_tables.range.PhysRange.new start len ⦃ r =>
      Agrees PhysRangeRepr ownershipErrorOf r (PhysRange.new (word64 start) (word64 len)) ⦄ := by
  unfold page_tables.range.PhysRange.new
  step*
  · simp only [PhysRange.new]; rfl
  · have h0 : word64 len ≠ 0 := by
      rw [ne_eq, word64_eq_iff, UInt64.toNat_zero, ← u64_eq_zero_iff]; exact ‹¬len = 0#u64›
    have hf : ¬ (word64 start).toNat + (word64 len).toNat < 2 ^ 64 := by
      subst_vars; simp only [u64_max_eq] at o_post; rw [word64_toNat, word64_toNat]; omega
    simp only [PhysRange.new, h0, hf, ↓reduceDIte]; rfl
  · have h0 : word64 len ≠ 0 := by
      rw [ne_eq, word64_eq_iff, UInt64.toNat_zero, ← u64_eq_zero_iff]; exact ‹¬len = 0#u64›
    have hf : (word64 start).toNat + (word64 len).toNat < 2 ^ 64 := by
      subst_vars; simp only [u64_max_eq] at o_post; rw [word64_toNat, word64_toNat]; omega
    simp only [PhysRange.new, h0, hf, ↓reduceDIte, agrees_ok_ok]
    exact ⟨rfl, rfl⟩

/-- `PhysRange::end()`: the end `start + len` of a range whose end fits in 64
bits. -/
@[step] theorem phys_range_end_spec (r : page_tables.PhysRange)
    (h : r.start.val + r.len.val < 2 ^ 64) :
    page_tables.range.PhysRange.end r ⦃ n => n.val = r.start.val + r.len.val ⦄ := by
  unfold page_tables.range.PhysRange.end
  step*

/-- `PhysRange::end()` of a range of the code that stands for a range: its end,
`PhysRange.endAddr`. -/
theorem phys_range_end_repr_spec (r : page_tables.PhysRange) (R : PhysRange)
    (h : PhysRangeRepr r R) :
    page_tables.range.PhysRange.end r ⦃ n => word64 n = R.endAddr ⦄ :=
  spec_mono (phys_range_end_spec r (physRange_fits h)) fun n hn => by
    rw [word64_eq_iff, endAddr_toNat, physRange_endNat h, hn]

/-- `PhysRange::contains(other)` of ranges whose ends fit in 64 bits. -/
@[step] theorem phys_range_contains_spec (r o : page_tables.PhysRange)
    (hr : r.start.val + r.len.val < 2 ^ 64) (ho : o.start.val + o.len.val < 2 ^ 64) :
    page_tables.range.PhysRange.contains r o ⦃ b =>
      b = decide (r.start.val ≤ o.start.val ∧ o.start.val + o.len.val ≤ r.start.val + r.len.val) ⦄ := by
  unfold page_tables.range.PhysRange.contains
  step*

/-- `PhysRange::contains(other)` of ranges of the code that stand for ranges:
`PhysRange.contains`. -/
theorem phys_range_contains_repr_spec (r o : page_tables.PhysRange) (R O : PhysRange)
    (hr : PhysRangeRepr r R) (ho : PhysRangeRepr o O) :
    page_tables.range.PhysRange.contains r o ⦃ b => b = R.contains O ⦄ :=
  spec_mono (phys_range_contains_spec r o (physRange_fits hr) (physRange_fits ho)) fun b hb => by
    rw [hb, PhysRange.contains, physRange_start hr, physRange_start ho, physRange_endNat hr,
      physRange_endNat ho, Bool.decide_and]

/-- `PhysRange::overlaps(other)` of ranges whose ends fit in 64 bits. -/
@[step] theorem phys_range_overlaps_spec (r o : page_tables.PhysRange)
    (hr : r.start.val + r.len.val < 2 ^ 64) (ho : o.start.val + o.len.val < 2 ^ 64) :
    page_tables.range.PhysRange.overlaps r o ⦃ b =>
      b = decide (r.start.val < o.start.val + o.len.val ∧ o.start.val < r.start.val + r.len.val) ⦄ := by
  unfold page_tables.range.PhysRange.overlaps
  step*

/-- `PhysRange::overlaps(other)` of ranges of the code that stand for ranges:
`PhysRange.overlaps`. -/
theorem phys_range_overlaps_repr_spec (r o : page_tables.PhysRange) (R O : PhysRange)
    (hr : PhysRangeRepr r R) (ho : PhysRangeRepr o O) :
    page_tables.range.PhysRange.overlaps r o ⦃ b => b = R.overlaps O ⦄ :=
  spec_mono (phys_range_overlaps_spec r o (physRange_fits hr) (physRange_fits ho)) fun b hb => by
    rw [hb, PhysRange.overlaps, physRange_start hr, physRange_start ho, physRange_endNat hr,
      physRange_endNat ho, Bool.decide_and]

/-- `direct_address(range)` of a range whose end fits in 64 bits:
`DIRECT_BASE | start` when the range ends at or below $2^{39}$. -/
@[step] theorem direct_address_spec (r : page_tables.PhysRange)
    (h : r.start.val + r.len.val < 2 ^ 64) :
    page_tables.direct_address r ⦃ o =>
      o.map word64 = if r.start.val + r.len.val ≤ 2 ^ 39 then some (DIRECT_BASE ||| word64 r.start)
        else none ⦄ := by
  unfold page_tables.direct_address
  simp only [va_limit_eq]
  step*
  · have hc : r.start.val + r.len.val ≤ 2 ^ 39 := by have := ‹i ≤ 549755813888#u64›; scalar_tac
    simp only [hc, ↓reduceIte, Option.map_some, word64_congr i2_post, word64_or,
      word64_direct_base]
  · have hc : ¬ r.start.val + r.len.val ≤ 2 ^ 39 := by
      have := ‹¬i ≤ 549755813888#u64›; scalar_tac
    simp only [hc, ↓reduceIte, Option.map_none]

/-- `direct_address(range)` of a range of the code that stands for a range:
`directAddress`. -/
theorem direct_address_repr_spec (r : page_tables.PhysRange) (R : PhysRange)
    (h : PhysRangeRepr r R) :
    page_tables.direct_address r ⦃ o => o.map word64 = directAddress R ⦄ :=
  spec_mono (direct_address_spec r (physRange_fits h)) fun o ho => by
    rw [ho, directAddress_eq, physRange_endNat h, h.1]

/-! ## Indices -/

/-- `index1(va)`: the root index of `index1`. -/
@[step] theorem index1_spec (va : U64) :
    page_tables.walk.index1 va ⦃ i => i.val = index1 (word64 va) ∧ i.val < 512 ⦄ := by
  unfold page_tables.walk.index1
  step*
  have h1 : i1.val = va.val / 2 ^ 30 % 512 := by
    rw [i1_post, UScalar.val_and, i_post]; exact shiftRight_and_511 _ _
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (lt_usize_pow (by omega)), h1, index1_eq,
    word64_toNat]
  exact ⟨rfl, Nat.mod_lt _ (by decide)⟩

/-- `index2(va)`: the level 2 index of `index2`. -/
@[step] theorem index2_spec (va : U64) :
    page_tables.walk.index2 va ⦃ i => i.val = index2 (word64 va) ∧ i.val < 512 ⦄ := by
  unfold page_tables.walk.index2
  step*
  have h1 : i1.val = va.val / 2 ^ 21 % 512 := by
    rw [i1_post, UScalar.val_and, i_post]; exact shiftRight_and_511 _ _
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (lt_usize_pow (by omega)), h1, index2_eq,
    word64_toNat]
  exact ⟨rfl, Nat.mod_lt _ (by decide)⟩

/-- `index3(va)`: the level 3 index of `index3`. -/
@[step] theorem index3_spec (va : U64) :
    page_tables.walk.index3 va ⦃ i => i.val = index3 (word64 va) ∧ i.val < 512 ⦄ := by
  unfold page_tables.walk.index3
  step*
  have h1 : i1.val = va.val / 2 ^ 12 % 512 := by
    rw [i1_post, UScalar.val_and, i_post]; exact shiftRight_and_511 _ _
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (lt_usize_pow (by omega)), h1, index3_eq,
    word64_toNat]
  exact ⟨rfl, Nat.mod_lt _ (by decide)⟩

/-! ## Sets of tables -/

theorem poolOf_eq {N : Usize} (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N) :
    poolOf pool = poolView pool := rfl

@[simp] theorem tablesOf_used {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) :
    (tablesOf s).used = s.used.val := rfl

@[simp] theorem tablesOf_pool {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) :
    (tablesOf s).pool = poolOf s.pool := rfl

/-- A set built from a pool and a record. -/
theorem tablesOf_mk {N : Usize} {upper : Bool}
    (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N) (used : Usize) :
    tablesOf ({ pool, used } : page_tables.Tables N upper) = ⟨poolOf pool, used.val⟩ := rfl

/-- A set whose record of the tables in use changes. -/
theorem tablesOf_with_used {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (used : Usize) :
    tablesOf ({ s with used } : page_tables.Tables N upper) =
      ({ tablesOf s with used := used.val } : Tables (regionOf upper) N.val) := rfl

/-- An entry of the set of the code: the word of its descriptor. -/
theorem tablesOf_entry {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) {t i : Nat}
    (ht : t < s.pool.val.length) (hi : i < (s.pool.val[t]'ht).val.length) :
    (tablesOf s).entry t i = word64 ((s.pool.val[t]'ht).val[i]'hi) :=
  entry_poolView s.pool s.used.val ht hi

/-- A write plan with no `Zero` steps: the first `len` of its steps. -/
theorem planOf_steps (steps : Aeneas.Std.Array page_tables.Step 7#usize) (len : Usize) :
    planOf { zero_tables := 0#usize, steps, len } = (steps.val.take len.val).map stepOf := by
  simp only [planOf]; rfl

/-! ## The walk -/

/-- `Tables::in_use()`: the tables in use, at most `N`. -/
@[step] theorem in_use_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) :
    page_tables.walk.Tables.in_use s ⦃ n => n.val = min s.used.val N.val ⦄ := by
  unfold page_tables.walk.Tables.in_use
  step*

/-- `child_index(entry, base, limit)`: the index of the table that the
descriptor points at, among the first `limit` tables of the pool at `base`. -/
@[step] theorem child_index_spec (entry base : U64) (limit : Usize) :
    page_tables.walk.child_index entry base limit ⦃ o =>
      o.map (·.val) = childIndex (outputAddress (word64 entry)).toNat base.val limit.val ⦄ := by
  unfold page_tables.walk.child_index
  simp only [page_size_eq]
  step*
  all_goals
    have ha : (outputAddress (word64 entry)).toNat = address.val := by
      rw [← address_post, word64_toNat]
    unfold childIndex
    rw [ha]
    simp only [PAGE_SIZE]
  · have hc : ¬ (base.val ≤ address.val ∧ (address.val - base.val) / 4096 < limit.val) := by
      have : address.val < base.val := ‹address < base›
      omega
    simp only [hc, ↓reduceIte, Option.map_none]
  · have hi1 : i1.val = limit.val := by rw [i1_post, usize_cast_u64_val]
    have hlim : index.val < limit.val := by rw [← hi1]; exact ‹index < i1›
    have hi2 : i2.val = index.val := by
      rw [i2_post]
      exact UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := limit.hmax; omega)
    have hc : base.val ≤ address.val ∧ (address.val - base.val) / 4096 < limit.val := by
      omega
    simp only [hc, and_self, ↓reduceIte, Option.map_some, hi2, index_post, i_post]
  · have hi1 : i1.val = limit.val := by rw [i1_post, usize_cast_u64_val]
    have hlim : ¬ index.val < limit.val := by rw [← hi1]; exact ‹¬index < i1›
    have hc : ¬ (base.val ≤ address.val ∧ (address.val - base.val) / 4096 < limit.val) := by
      omega
    simp only [hc, ↓reduceIte, Option.map_none]

/-- `Tables::child(entry, base)`: the table in use that the descriptor points
at, `Tables.child?`. -/
@[step] theorem child_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (entry base : U64) :
    page_tables.walk.Tables.child s entry base ⦃ o =>
      o.map (·.val) = (tablesOf s).child? (word64 base) (word64 entry) ⦄ := by
  unfold page_tables.walk.Tables.child
  step*
  rw [o_post, child?_eq, word64_toNat, i_post]
  rfl

/-- `Tables::walk_level2(va, base)` on a pool of at least one table: the level
2 step of the walk, `Tables.walk2`. -/
@[step] theorem walk_level2_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper)
    (va base : U64) (hN : 0 < N.val) :
    page_tables.walk.Tables.walk_level2 s va base ⦃ r =>
      Agrees (fun o O => o.map (fun p => (p.1.val, word64 p.2)) = O) tableErrorOf r
        ((tablesOf s).walk2 (word64 base) (word64 va)) ⦄ := by
  unfold page_tables.walk.Tables.walk_level2
  step*
  · subst a_post root_post
    have hv : isValid ((tablesOf s).entry 0 (index1 (word64 va))) = true := by
      rw [← i_post, tablesOf_entry s (by scalar_tac) (by scalar_tac), ← b_post]; exact ‹b = true›
    have hc : (tablesOf s).child? (word64 base) ((tablesOf s).entry 0 (index1 (word64 va))) =
        none := by
      rw [← i_post, tablesOf_entry s (by scalar_tac) (by scalar_tac), ← o_post, ‹o = none›]; rfl
    rw [walk2_backing hv hc]; rfl
  · have hc := o_post
    rw [‹o = some table›, Option.map_some] at hc
    have h1 : table.val < N.val := child?_lt hc.symm
    scalar_tac
  · subst a_post root_post a1_post i2_post
    have hv : isValid ((tablesOf s).entry 0 (index1 (word64 va))) = true := by
      rw [← i_post, tablesOf_entry s (by scalar_tac) (by scalar_tac), ← b_post]; exact ‹b = true›
    have hc : (tablesOf s).child? (word64 base) ((tablesOf s).entry 0 (index1 (word64 va))) =
        some table.val := by
      rw [← i_post, tablesOf_entry s (by scalar_tac) (by scalar_tac), ← o_post, ‹o = some table›]; rfl
    rw [walk2_some hv hc, agrees_ok_ok, Option.map_some, ← i1_post, tablesOf_entry s (by scalar_tac) (by scalar_tac)]
  · subst a_post root_post
    have hv : isValid ((tablesOf s).entry 0 (index1 (word64 va))) = false := by
      rw [← i_post, tablesOf_entry s (by scalar_tac) (by scalar_tac), ← b_post]; simpa using ‹¬b = true›
    rw [walk2_invalid hv]; rfl

/-! ## The checks of an entry -/

/-- `width_ok(bits)`: whether `bits` is a physical width, `widthOk`. -/
@[step] theorem width_ok_spec (bits : U8) :
    page_tables.walk.width_ok bits ⦃ b => b = widthOk (byte bits) ⦄ := by
  unfold page_tables.walk.width_ok
  step*
  all_goals
    rw [widthOk_eq, byte_toNat, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.false_eq_true, false_iff]
    scalar_tac

/-- `pool_fits(count, base, bits)` for a width below 64: whether the pool of
`count` tables at `base` holds a table and ends at or below
$2^{\mathrm{bits}}$, `poolFits`. -/
@[step] theorem pool_fits_spec (count : Usize) (base : U64) (bits : U8) (hb : bits.val < 64) :
    page_tables.walk.pool_fits count base bits ⦃ b =>
      b = poolFits count.val (word64 base) (byte bits) ⦄ := by
  unfold page_tables.walk.pool_fits
  simp only [page_size_eq]
  step*
  all_goals
    have hl : limit.val = 2 ^ bits.val := by rw [limit_post, u64_size]; exact one_shiftLeft hb
    have h64 : 2 ^ bits.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hb
    rw [Bool.eq_iff_iff, poolFits_iff, word64_toNat, byte_toNat]
    simp only [PAGE_SIZE, ne_eq, decide_eq_true_eq, Bool.false_eq_true, false_iff, not_and]
  · intro h; exact absurd h (by scalar_tac)
  · have hi : i.val = count.val := by rw [i_post, usize_cast_u64_val]
    intro _; scalar_tac
  · have hi : i2.val = count.val := by rw [i2_post, usize_cast_u64_val]
    simp only [‹o = none›] at o_post
    rw [u64_max_eq] at o_post
    intro _; omega
  · have hi : i2.val = count.val := by rw [i2_post, usize_cast_u64_val]
    simp only [‹o = some «end»›] at o_post
    have := ‹¬count = 0#usize›
    constructor
    · intro h; constructor <;> scalar_tac
    · intro h; scalar_tac

/-- `check_pool(count, base, bits)`: the first checks of an entry on a pool,
`checkPool`. -/
@[step] theorem check_pool_spec (count : Usize) (base : U64) (bits : U8) :
    page_tables.walk.check_pool count base bits ⦃ r =>
      Agrees (fun _ _ => True) tableErrorOf r (checkPool count.val (word64 base) (byte bits)) ⦄ := by
  unfold page_tables.walk.check_pool
  simp only [page_size_eq]
  step*
  · have hB : base.val % 4096 ≠ 0 := by rw [← i_post]; exact bne_zero_iff.1 ‹_›
    simp only [checkPool_eq, word64_toNat, PAGE_SIZE, hB, ne_eq, not_false_eq_true, ↓reduceIte,
      agrees_err_error, tableErrorOf]
  · exact lt_64_of_widthOk (by rw [← b_post]; exact ‹b = true›)
  · have hB : base.val % 4096 = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hD : widthOk (byte bits) = true := by rw [← b_post]; exact ‹b = true›
    have hE : poolFits count.val (word64 base) (byte bits) = true := by
      rw [← b1_post]; exact ‹b1 = true›
    simp only [checkPool_eq, word64_toNat, PAGE_SIZE, hB, hD, hE, ne_eq, not_true_eq_false,
      Bool.true_eq_false, ↓reduceIte, agrees_ok_ok]
  · have hB : base.val % 4096 = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hD : widthOk (byte bits) = true := by rw [← b_post]; exact ‹b = true›
    have hE : poolFits count.val (word64 base) (byte bits) = false := by
      rw [← b1_post]; simpa using ‹¬b1 = true›
    simp only [checkPool_eq, word64_toNat, PAGE_SIZE, hB, hD, hE, ne_eq, not_true_eq_false,
      Bool.true_eq_false, ↓reduceIte, agrees_err_error, tableErrorOf]
  · have hB : base.val % 4096 = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hD : widthOk (byte bits) = false := by rw [← b_post]; simpa using ‹¬b = true›
    simp only [checkPool_eq, word64_toNat, PAGE_SIZE, hB, hD, ne_eq, not_true_eq_false,
      ↓reduceIte, agrees_err_error, tableErrorOf]

/-- `in_region(upper, va)`: whether the address lies in the region, `holds`. -/
@[step] theorem in_region_spec (upper : Bool) (va : U64) :
    page_tables.walk.in_region upper va ⦃ b => b = (regionOf upper).holds (word64 va) ⦄ := by
  unfold page_tables.walk.in_region
  simp only [va_limit_eq]
  cases upper <;> step*
  · show _ = Region.holds .lower (word64 va)
    rw [holds_lower, word64_toNat, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    scalar_tac
  · show _ = Region.holds .upper (word64 va)
    have := direct_base_val
    rw [holds_upper, word64_toNat, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    scalar_tac

/-- `check_entry(upper, count, va, align, base, bits)` for a nonzero
alignment: the first checks of an entry on a set, `checkEntry`. -/
@[step] theorem check_entry_spec (upper : Bool) (count : Usize) (va align base : U64) (bits : U8)
    (ha : align.val ≠ 0) :
    page_tables.walk.check_entry upper count va align base bits ⦃ r =>
      Agrees (fun _ _ => True) tableErrorOf r
        (checkEntry (regionOf upper) count.val (word64 va) align.val (word64 base) (byte bits)) ⦄ := by
  unfold page_tables.walk.check_entry
  simp only [page_size_eq]
  step*
  · have hA : va.val % align.val ≠ 0 := by rw [← i_post]; exact bne_zero_iff.1 ‹_›
    simp only [checkEntry_eq, word64_toNat, hA, ne_eq, not_false_eq_true, true_or, ↓reduceIte,
      agrees_err_error, tableErrorOf]
  · have hA : va.val % align.val = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hB : base.val % 4096 ≠ 0 := by rw [← i1_post]; exact bne_zero_iff.1 ‹_›
    simp only [checkEntry_eq, word64_toNat, PAGE_SIZE, hA, hB, ne_eq, not_true_eq_false,
      not_false_eq_true, or_true, ↓reduceIte, agrees_err_error, tableErrorOf]
  · exact lt_64_of_widthOk (by rw [← b1_post]; exact ‹b1 = true›)
  · have hA : va.val % align.val = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hB : base.val % 4096 = 0 := by rw [← i1_post]; exact not_bne_zero_iff.1 ‹_›
    have hC : (regionOf upper).holds (word64 va) = true := by rw [← b_post]; exact ‹b = true›
    have hD : widthOk (byte bits) = true := by rw [← b1_post]; exact ‹b1 = true›
    have hE : poolFits count.val (word64 base) (byte bits) = true := by
      rw [← b2_post]; exact ‹b2 = true›
    simp only [checkEntry_eq, word64_toNat, PAGE_SIZE, hA, hB, hC, hD, hE, ne_eq,
      not_true_eq_false, or_self, Bool.true_eq_false, ↓reduceIte, agrees_ok_ok]
  · have hA : va.val % align.val = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hB : base.val % 4096 = 0 := by rw [← i1_post]; exact not_bne_zero_iff.1 ‹_›
    have hC : (regionOf upper).holds (word64 va) = true := by rw [← b_post]; exact ‹b = true›
    have hD : widthOk (byte bits) = true := by rw [← b1_post]; exact ‹b1 = true›
    have hE : poolFits count.val (word64 base) (byte bits) = false := by
      rw [← b2_post]; simpa using ‹¬b2 = true›
    simp only [checkEntry_eq, word64_toNat, PAGE_SIZE, hA, hB, hC, hD, hE, ne_eq,
      not_true_eq_false, or_self, Bool.true_eq_false, ↓reduceIte, agrees_err_error, tableErrorOf]
  · have hA : va.val % align.val = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hB : base.val % 4096 = 0 := by rw [← i1_post]; exact not_bne_zero_iff.1 ‹_›
    have hC : (regionOf upper).holds (word64 va) = true := by rw [← b_post]; exact ‹b = true›
    have hD : widthOk (byte bits) = false := by rw [← b1_post]; simpa using ‹¬b1 = true›
    simp only [checkEntry_eq, word64_toNat, PAGE_SIZE, hA, hB, hC, hD, ne_eq,
      not_true_eq_false, or_self, Bool.true_eq_false, or_true, ↓reduceIte, agrees_err_error,
      tableErrorOf]
  · have hA : va.val % align.val = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hB : base.val % 4096 = 0 := by rw [← i1_post]; exact not_bne_zero_iff.1 ‹_›
    have hC : (regionOf upper).holds (word64 va) = false := by
      rw [← b_post]; simpa using ‹¬b = true›
    simp only [checkEntry_eq, word64_toNat, PAGE_SIZE, hA, hB, hC, ne_eq,
      not_true_eq_false, or_self, true_or, ↓reduceIte, agrees_err_error, tableErrorOf]

/-- `check_physical(pa, align, bits)` for a nonzero alignment and a width
below 64: the checks of a physical address, `checkPhysical`. -/
@[step] theorem check_physical_spec (pa align : U64) (bits : U8) (ha : align.val ≠ 0)
    (hb : bits.val < 64) :
    page_tables.walk.check_physical pa align bits ⦃ r =>
      Agrees (fun _ _ => True) tableErrorOf r (checkPhysical (word64 pa) align.val (byte bits)) ⦄ := by
  unfold page_tables.walk.check_physical
  step*
  · have hA : pa.val % align.val ≠ 0 := by rw [← i_post]; exact bne_zero_iff.1 ‹_›
    simp only [checkPhysical_eq, word64_toNat, hA, ne_eq, not_false_eq_true, ↓reduceIte,
      agrees_err_error, tableErrorOf]
  · have hA : pa.val % align.val = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hl : i1.val = 2 ^ bits.val := by rw [i1_post, u64_size]; exact one_shiftLeft hb
    have hW : 2 ^ bits.val ≤ pa.val := by have := ‹pa ≥ i1›; scalar_tac
    simp only [checkPhysical_eq, word64_toNat, byte_toNat, hA, hW, ne_eq, not_true_eq_false,
      ↓reduceIte, agrees_err_error, tableErrorOf]
  · have hA : pa.val % align.val = 0 := by rw [← i_post]; exact not_bne_zero_iff.1 ‹_›
    have hl : i1.val = 2 ^ bits.val := by rw [i1_post, u64_size]; exact one_shiftLeft hb
    have hW : ¬ 2 ^ bits.val ≤ pa.val := by have := ‹¬pa ≥ i1›; scalar_tac
    simp only [checkPhysical_eq, word64_toNat, byte_toNat, hA, hW, ne_eq, not_true_eq_false,
      ↓reduceIte, agrees_ok_ok]

/-- `table_address(base, table)` when the address fits in 64 bits:
`tableAddress`. -/
@[step] theorem table_address_spec (base : U64) (table : Usize)
    (h : base.val + 4096 * table.val < 2 ^ 64) :
    page_tables.walk.table_address base table ⦃ a =>
      a.val = base.val + 4096 * table.val ∧ word64 a = tableAddress (word64 base) table.val ⦄ := by
  unfold page_tables.walk.table_address
  simp only [page_size_eq]
  step*
  have hi : i.val = table.val := by rw [i_post, usize_cast_u64_val]
  have ha : a.val = base.val + 4096 * table.val := by rw [a_post, i1_post, hi]
  refine ⟨ha, ?_⟩
  rw [tableAddress, word64_ofNat_iff, word64_toNat, ha, show PAGE_SIZE = 4096 from rfl,
    Nat.mod_eq_of_lt h]

/-! ## Records -/

/-- `Tables::free_tables()`: the tables of the pool not in use. -/
@[step] theorem free_tables_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) :
    page_tables.write.Tables.free_tables s ⦃ n => n.val = N.val - s.used.val ⦄ := by
  unfold page_tables.write.Tables.free_tables
  step*
  have := ‹¬s.used < N›
  scalar_tac

/-- `Tables::used()`: the number of tables in use, `Tables.usedTables`. -/
@[step] theorem used_spec {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) :
    page_tables.walk.Tables.used s ⦃ n => n.val = (tablesOf s).usedTables ⦄ := by
  unfold page_tables.walk.Tables.used
  exact spec_of_eq rfl rfl

/-- `Tables::new(storage)`: the set of `Tables.new` of the storage. -/
@[step] theorem new_spec {N : Usize} (upper : Bool)
    (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N) :
    page_tables.walk.Tables.new upper pool ⦃ s =>
      tablesOf s = (Tables.new (poolOf pool) : Tables (regionOf upper) N.val) ⦄ := by
  unfold page_tables.walk.Tables.new
  exact spec_of_eq rfl rfl

/-- `is_free(holding)`: whether the holding is free. -/
@[step] theorem is_free_spec (h : page_tables.Holding) :
    page_tables.ownership.is_free h ⦃ b => b = (holdingOf h == .free) ⦄ := by
  unfold page_tables.ownership.is_free
  cases h <;> exact spec_of_eq rfl (by simp [holdingOf])

/-- `Ownership::room()`: the extents free in the capacity. -/
@[step] theorem room_spec {E X : Usize} (t : page_tables.Ownership E X) :
    page_tables.ownership.Ownership.room t ⦃ n => n.val = E.val - t.extent_count.val ⦄ := by
  unfold page_tables.ownership.Ownership.room
  step*
  have := ‹¬t.extent_count < E›
  scalar_tac

/-- The extents of a table that the code's table stands for are its first
`extent_count` extents. -/
theorem ownershipRepr_extents_length {E X : Usize} {t : page_tables.Ownership E X}
    {T : Ownership E.val X.val} (h : OwnershipRepr t T) :
    T.extents.length = t.extent_count.val := by
  obtain ⟨-, hc, -, -, -, he, -⟩ := h
  rw [← listRel_length he, List.length_take, t.extents.property]
  omega

end Krepi.Proofs.PageTables.Refinement
