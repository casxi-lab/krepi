module

public import Krepi.Statements.PageTables.Representation

/-!
# Page tables: refinement of the descriptors, the ranges and the table sets

One statement for each function of lines 107 to 111 of the entry table of
the contract (`docs/domains/memory/page-tables/contract.md`), and for the
`next` of the plan of a copy: for every input of its machine widths, under
the premises that its arguments need, the function returns, and its result
agrees with that of its function of `Krepi.Spec.PageTables` through the
representation of `Krepi.Statements.PageTables.Representation`, the same
error with the same priority included. A write entry returns its set after
its write phase, which stands for the set that its specification gives, and
its plan; on a failure it returns the set unchanged and no plan. The entries
on a set check every rule that their specifications state of a set, so they
take no invariant of it. The theorems below
`Krepi.Proofs.PageTables.Refinement` prove them.
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice U8 U64 Usize)
open KrepiGen.PageTables
open Krepi.Spec.PageTables

namespace Krepi.Statements.PageTables

/-! ## Descriptors and ranges -/

/-- `page_tables::descriptor(kind, address)`: the descriptor of `descriptor`
of the kind and the address.
Feature: `krepi.kernel.kernel-memory`. -/
def Descriptor : Prop :=
  Usize64 →
  ∀ (kind : page_tables.Kind) (address : U64),
    page_tables.descriptor kind address ⦃ d => word64 d = descriptor (kindOf kind) (word64 address) ⦄

/-- `page_tables::direct_address(range)`: the address of `directAddress` of
the range, or none.
Feature: `krepi.kernel.kernel-memory`. -/
def DirectAddress : Prop :=
  Usize64 →
  ∀ (range : page_tables.PhysRange) (R : PhysRange), PhysRangeRepr range R →
    page_tables.direct_address range ⦃ o => o.map word64 = directAddress R ⦄

/-- `PhysRange::new(start, len)`: the range of `PhysRange.new`, or its
error.
Feature: `krepi.kernel.kernel-memory`. -/
def PhysRangeNew : Prop :=
  Usize64 →
  ∀ start len : U64,
    page_tables.range.PhysRange.new start len ⦃ r =>
      Agrees PhysRangeRepr ownershipErrorOf r (PhysRange.new (word64 start) (word64 len)) ⦄

/-- `PhysRange::end()`: the end of the range, `PhysRange.endAddr`.
Feature: `krepi.kernel.kernel-memory`. -/
def PhysRangeEnd : Prop :=
  Usize64 →
  ∀ (range : page_tables.PhysRange) (R : PhysRange), PhysRangeRepr range R →
    page_tables.range.PhysRange.end range ⦃ n => word64 n = R.endAddr ⦄

/-- `PhysRange::contains(other)`: whether the range holds the other,
`PhysRange.contains`.
Feature: `krepi.kernel.kernel-memory`. -/
def PhysRangeContains : Prop :=
  Usize64 →
  ∀ (range other : page_tables.PhysRange) (R O : PhysRange),
    PhysRangeRepr range R → PhysRangeRepr other O →
    page_tables.range.PhysRange.contains range other ⦃ b => b = R.contains O ⦄

/-- `PhysRange::overlaps(other)`: whether the ranges share an address,
`PhysRange.overlaps`.
Feature: `krepi.kernel.kernel-memory`. -/
def PhysRangeOverlaps : Prop :=
  Usize64 →
  ∀ (range other : page_tables.PhysRange) (R O : PhysRange),
    PhysRangeRepr range R → PhysRangeRepr other O →
    page_tables.range.PhysRange.overlaps range other ⦃ b => b = R.overlaps O ⦄

/-! ## Entries that write nothing -/

/-- `Tables::lookup_page(va, base, bits)`: the page descriptor of
`Tables.lookupPage`, or its error.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesLookupPage : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s : page_tables.Tables N upper) (va base : U64) (bits : U8),
    page_tables.walk.Tables.lookup_page s va base bits ⦃ r =>
      Agrees (fun d D => word64 d = D) tableErrorOf r
        ((tablesOf s).lookupPage (word64 va) (word64 base) (byte bits)) ⦄

/-- `Tables::lookup_block(va, base, bits)`: the block descriptor of
`Tables.lookupBlock`, or its error.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesLookupBlock : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s : page_tables.Tables N upper) (va base : U64) (bits : U8),
    page_tables.walk.Tables.lookup_block s va base bits ⦃ r =>
      Agrees (fun d D => word64 d = D) tableErrorOf r
        ((tablesOf s).lookupBlock (word64 va) (word64 base) (byte bits)) ⦄

/-- `Tables::used()`: the number of tables in use, `Tables.usedTables`.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesUsed : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s : page_tables.Tables N upper),
    page_tables.walk.Tables.used s ⦃ n => n.val = (tablesOf s).usedTables ⦄

/-! ## Creation, reset and copy -/

/-- `Tables::new(storage)`: the set of `Tables.new` of the storage, of the
region of `UPPER`.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesNew : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N),
    page_tables.walk.Tables.new upper pool ⦃ s =>
      tablesOf s = (Tables.new (poolOf pool) : Tables (regionOf upper) N.val) ⦄

/-- `Tables::reset()`: the set after the write phase and the plan of
`Tables.reset`.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesReset : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s : page_tables.Tables N upper),
    page_tables.write.Tables.reset s ⦃ plan s' =>
      WritePlanRepr plan (tablesOf s).reset.2 ∧ tablesOf s' = (tablesOf s).reset.1 ⦄

/-- `Tables::clone_kernel_from(source, source_base, base, bits)`: the set
after the write phase of `Tables.cloneKernelFrom` and a plan iterator that
stands for its plan, or its error with the set unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesCloneKernelFrom : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s source : page_tables.Tables N upper) (sourceBase base : U64)
    (bits : U8),
    page_tables.copy.Tables.clone_kernel_from s source sourceBase base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (Stands page_tables.copy.ClonePlan.next StepRepr)
        (tableErrorOf · = ·) s r s'
        ((tablesOf s).cloneKernelFrom (tablesOf source) (word64 sourceBase) (word64 base)
          (byte bits)) ⦄

/-- `ClonePlan::next()`: one call gives the next step of the plan that the
iterator stands for and leaves it standing for the rest; at the end it gives
none and stays at the end.
Feature: `krepi.kernel.kernel-memory`. -/
def ClonePlanNext : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (it : page_tables.ClonePlan N upper) (l : Plan),
    Stands page_tables.copy.ClonePlan.next StepRepr it l →
    Advances page_tables.copy.ClonePlan.next StepRepr it l

/-! ## Pages and blocks -/

/-- `Tables::map_page(va, pa, kind, base, bits)`: the set after the write
phase and the plan of `Tables.mapPage`, or its error with the set unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesMapPage : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s : page_tables.Tables N upper) (va pa : U64)
    (kind : page_tables.Kind) (base : U64) (bits : U8),
    page_tables.write.Tables.map_page s va pa kind base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) WritePlanRepr (tableErrorOf · = ·) s r s'
        ((tablesOf s).mapPage (word64 va) (word64 pa) (kindOf kind) (word64 base) (byte bits)) ⦄

/-- `Tables::map_block(va, pa, base, bits)`: the set after the write phase
and the plan of `Tables.mapBlock`, or its error with the set unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesMapBlock : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s : page_tables.Tables N upper) (va pa base : U64) (bits : U8),
    page_tables.write.Tables.map_block s va pa base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) WritePlanRepr (tableErrorOf · = ·) s r s'
        ((tablesOf s).mapBlock (word64 va) (word64 pa) (word64 base) (byte bits)) ⦄

/-- `Tables::unmap_page(va, base, bits)`: the plan and the physical page of
`Tables.unmapPage`, with the set unchanged, or its error.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesUnmapPage : Prop :=
  Usize64 →
  ∀ (N : Usize) (upper : Bool) (s : page_tables.Tables N upper) (va base : U64) (bits : U8),
    page_tables.write.Tables.unmap_page s va base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S)
        (fun (plan, pa) (P, A) => WritePlanRepr plan P ∧ word64 pa = A) (tableErrorOf · = ·) s r s'
        (((tablesOf s).unmapPage (word64 va) (word64 base) (byte bits)).map (tablesOf s, ·)) ⦄

end Krepi.Statements.PageTables
