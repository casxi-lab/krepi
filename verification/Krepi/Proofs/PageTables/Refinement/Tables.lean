module

public import Krepi.Statements.PageTables.Tables
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.Refinement.WalkLemmas

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
public theorem tablesLookupPage : TablesLookupPage := by
  sorry

/-- Proves `TablesLookupBlock`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesLookupBlock : TablesLookupBlock := by
  sorry

/-- Proves `TablesUsed`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesUsed : TablesUsed := fun _ _ _ s => used_spec s

/-- Proves `TablesNew`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesNew : TablesNew := fun _ _ upper pool => new_spec upper pool

/-- Proves `TablesReset`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesReset : TablesReset := by
  sorry

/-- Proves `TablesCloneKernelFrom`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesCloneKernelFrom : TablesCloneKernelFrom := by
  sorry

/-- Proves `ClonePlanNext`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem clonePlanNext : ClonePlanNext := fun _ _ _ _ _ h => advances_of_stands h

/-- Proves `TablesMapPage`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesMapPage : TablesMapPage := by
  sorry

/-- Proves `TablesMapBlock`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesMapBlock : TablesMapBlock := by
  sorry

/-- Proves `TablesUnmapPage`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesUnmapPage : TablesUnmapPage := by
  sorry

end Krepi.Proofs.PageTables.Refinement.Tables
