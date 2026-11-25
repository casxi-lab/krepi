module

public import Krepi.Statements.Fdt.Plan
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.PlanQueryLemmas
import Krepi.Proofs.Fdt.Refinement.PlanBuildLemmas

/-!
# Device tree: refinement of the boot memory map

One theorem for each statement of `Krepi.Statements.Fdt.Plan`,
whose type is exactly that statement.

Fourteen of the fifteen are proved. The constructions `memoryPlanAllRam` and
`memoryPlanNew` restate `all_ram_spec` and `new_spec` of
`Krepi.Proofs.Fdt.Refinement.PlanBuildLemmas`. The lists, the queries and the
iterator of the usable ranges each restate the triple of its function in
`Krepi.Proofs.Fdt.Refinement.AccessorLemmas` (`memory_plan_managed_banks_spec`,
`memory_plan_ram_spec`, `memory_plan_reservations_spec`,
`memory_plan_boot_ranges_spec` and `memory_plan_firmware_ranges_spec`) or
`Krepi.Proofs.Fdt.Refinement.PlanQueryLemmas` (`described_bytes_spec`,
`managed_bytes_spec`, `contains_ram_spec`, `is_available_spec`,
`permits_backing_spec` and `available_ranges_spec`). All of these triples hold
without the premise `Usize64`, and `availableRangesNext` follows from
`Stands` alone (`advances_of_stands`). The construction from a boot memory,
`memoryPlanFromBootMemory`, is planned: its proof is `sorry`, and
`verification/statements.json` registers it as `planned`, so that no module
imports this one. `from_boot_memory_spec` of
`Krepi.Proofs.Fdt.Refinement.PlanBuildLemmas` proves its refinement for
further spans whose number plus two is a `usize`. Mathlib is imported so that
the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Plan

open Krepi.Statements.Fdt Krepi.Proofs.Fdt.Refinement

/-- Proves `MemoryPlanAllRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanAllRam : MemoryPlanAllRam :=
  fun _ ram boot firmware => all_ram_spec ram boot firmware

/-- Proves `MemoryPlanNew`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanNew : MemoryPlanNew :=
  fun _ window ram boot firmware => new_spec window ram boot firmware

/-- Proves `MemoryPlanFromBootMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanFromBootMemory : MemoryPlanFromBootMemory := by
  sorry

/-- Proves `MemoryPlanManagedBanks`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanManagedBanks : MemoryPlanManagedBanks :=
  fun _ _ _ h => memory_plan_managed_banks_spec h

/-- Proves `MemoryPlanRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanRam : MemoryPlanRam :=
  fun _ _ _ h => memory_plan_ram_spec h

/-- Proves `MemoryPlanReservations`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanReservations : MemoryPlanReservations :=
  fun _ _ _ h => memory_plan_reservations_spec h

/-- Proves `MemoryPlanBootRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanBootRanges : MemoryPlanBootRanges :=
  fun _ _ _ h => memory_plan_boot_ranges_spec h

/-- Proves `MemoryPlanFirmwareRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanFirmwareRanges : MemoryPlanFirmwareRanges :=
  fun _ _ _ h => memory_plan_firmware_ranges_spec h

/-- Proves `MemoryPlanDescribedBytes`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanDescribedBytes : MemoryPlanDescribedBytes :=
  fun _ _ _ h hw => described_bytes_spec h hw

/-- Proves `MemoryPlanManagedBytes`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanManagedBytes : MemoryPlanManagedBytes :=
  fun _ _ _ h hw => managed_bytes_spec h hw

/-- Proves `MemoryPlanContainsRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanContainsRam : MemoryPlanContainsRam :=
  fun _ _ _ range h _ => contains_ram_spec h range

/-- Proves `MemoryPlanIsAvailable`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanIsAvailable : MemoryPlanIsAvailable :=
  fun _ _ _ range h _ => is_available_spec h range

/-- Proves `MemoryPlanPermitsBacking`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanPermitsBacking : MemoryPlanPermitsBacking :=
  fun _ _ _ range h _ => permits_backing_spec h range

/-- Proves `MemoryPlanAvailableRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryPlanAvailableRanges : MemoryPlanAvailableRanges :=
  fun _ _ _ h hw => available_ranges_spec h hw

/-- Proves `AvailableRangesNext`. Feature: `krepi.platform.device-tree`. -/
public theorem availableRangesNext : AvailableRangesNext :=
  fun _ _ _ h => advances_of_stands h

end Krepi.Proofs.Fdt.Refinement.Plan
