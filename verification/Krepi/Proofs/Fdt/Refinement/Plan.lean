module

public import Krepi.Statements.Fdt.Plan
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: refinement of the boot memory map

One theorem for each statement of `Krepi.Statements.Fdt.Plan`,
whose type is exactly that statement.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Plan

open Krepi.Statements.Fdt

/-- Proves `MemoryPlanAllRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanAllRam : MemoryPlanAllRam := by
  sorry

/-- Proves `MemoryPlanNew`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanNew : MemoryPlanNew := by
  sorry

/-- Proves `MemoryPlanFromBootMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanFromBootMemory : MemoryPlanFromBootMemory := by
  sorry

/-- Proves `MemoryPlanManagedBanks`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanManagedBanks : MemoryPlanManagedBanks := by
  sorry

/-- Proves `MemoryPlanRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanRam : MemoryPlanRam := by
  sorry

/-- Proves `MemoryPlanReservations`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanReservations : MemoryPlanReservations := by
  sorry

/-- Proves `MemoryPlanBootRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanBootRanges : MemoryPlanBootRanges := by
  sorry

/-- Proves `MemoryPlanFirmwareRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanFirmwareRanges : MemoryPlanFirmwareRanges := by
  sorry

/-- Proves `MemoryPlanDescribedBytes`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanDescribedBytes : MemoryPlanDescribedBytes := by
  sorry

/-- Proves `MemoryPlanManagedBytes`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanManagedBytes : MemoryPlanManagedBytes := by
  sorry

/-- Proves `MemoryPlanContainsRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanContainsRam : MemoryPlanContainsRam := by
  sorry

/-- Proves `MemoryPlanIsAvailable`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanIsAvailable : MemoryPlanIsAvailable := by
  sorry

/-- Proves `MemoryPlanPermitsBacking`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanPermitsBacking : MemoryPlanPermitsBacking := by
  sorry

/-- Proves `MemoryPlanAvailableRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanAvailableRanges : MemoryPlanAvailableRanges := by
  sorry

/-- Proves `AvailableRangesNext`. Feature: `krepi.platform.device-tree`. -/
public theorem availableRangesNext : AvailableRangesNext := by
  sorry

end Krepi.Proofs.Fdt.Refinement.Plan
