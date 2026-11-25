module

public import Krepi.Statements.PageTables.Tables
import Mathlib.Util.CountHeartbeats

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

open Krepi.Statements.PageTables

/-- Proves `Descriptor`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem descriptor : Descriptor := by
  sorry

/-- Proves `DirectAddress`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem directAddress : DirectAddress := by
  sorry

/-- Proves `PhysRangeNew`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeNew : PhysRangeNew := by
  sorry

/-- Proves `PhysRangeEnd`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeEnd : PhysRangeEnd := by
  sorry

/-- Proves `PhysRangeContains`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeContains : PhysRangeContains := by
  sorry

/-- Proves `PhysRangeOverlaps`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem physRangeOverlaps : PhysRangeOverlaps := by
  sorry

/-- Proves `TablesLookupPage`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesLookupPage : TablesLookupPage := by
  sorry

/-- Proves `TablesLookupBlock`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesLookupBlock : TablesLookupBlock := by
  sorry

/-- Proves `TablesUsed`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesUsed : TablesUsed := by
  sorry

/-- Proves `TablesNew`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesNew : TablesNew := by
  sorry

/-- Proves `TablesReset`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesReset : TablesReset := by
  sorry

/-- Proves `TablesCloneKernelFrom`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem tablesCloneKernelFrom : TablesCloneKernelFrom := by
  sorry

/-- Proves `ClonePlanNext`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem clonePlanNext : ClonePlanNext := by
  sorry

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
