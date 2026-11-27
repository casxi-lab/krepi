module

public import Krepi.Statements.PageTables.Tables
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.Refinement.WalkLemmas
import Krepi.Proofs.PageTables.Refinement.WriteLemmas

/-!
# Page tables: refinement of the descriptors, the ranges and the table sets

One theorem for each statement of `Krepi.Statements.PageTables.Tables`,
whose type is exactly that statement.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Refinement.Tables

open Krepi.Statements.PageTables Krepi.Proofs.PageTables.Refinement Krepi.Proofs.Fdt.Refinement

/-- Proves `Descriptor`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem descriptor : Descriptor := fun _ => descriptor_spec

/-- Proves `DirectAddress`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem directAddress : DirectAddress := fun _ => direct_address_repr_spec

/-- Proves `PhysRangeNew`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeNew : PhysRangeNew := fun _ => phys_range_new_spec

/-- Proves `PhysRangeEnd`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeEnd : PhysRangeEnd := fun _ => phys_range_end_repr_spec

/-- Proves `PhysRangeContains`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeContains : PhysRangeContains := fun _ => phys_range_contains_repr_spec

/-- Proves `PhysRangeOverlaps`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeOverlaps : PhysRangeOverlaps := fun _ => phys_range_overlaps_repr_spec

/-- Proves `TablesLookupPage`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesLookupPage : TablesLookupPage :=
  fun _ _ _ s va base bits => lookup_page_spec s va base bits

/-- Proves `TablesLookupBlock`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesLookupBlock : TablesLookupBlock :=
  fun _ _ _ s va base bits => lookup_block_spec s va base bits

/-- Proves `TablesUsed`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesUsed : TablesUsed := fun _ _ _ s => used_spec s

/-- Proves `TablesNew`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesNew : TablesNew := fun _ _ upper pool => new_spec upper pool

/-- Proves `TablesReset`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesReset : TablesReset :=
  fun _ _ _ s => reset_spec s

/-- Proves `TablesCloneKernelFrom`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesCloneKernelFrom : TablesCloneKernelFrom := by
  sorry

/-- Proves `ClonePlanNext`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem clonePlanNext : ClonePlanNext := fun _ _ _ _ _ h => advances_of_stands h

/-- Proves `TablesMapPage`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesMapPage : TablesMapPage :=
  fun _ _ _ s va pa kind base bits => map_page_spec s va pa kind base bits

/-- Proves `TablesMapBlock`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesMapBlock : TablesMapBlock :=
  fun _ _ _ s va pa base bits => map_block_spec s va pa base bits

/-- Proves `TablesUnmapPage`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesUnmapPage : TablesUnmapPage :=
  fun _ _ _ s va base bits => unmap_page_spec s va base bits

end Krepi.Proofs.PageTables.Refinement.Tables
