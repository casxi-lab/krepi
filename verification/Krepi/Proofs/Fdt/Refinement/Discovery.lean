module

public import Krepi.Statements.Fdt.Discovery
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: refinement of the memory discovery and the boot memory

One theorem for each statement of `Krepi.Statements.Fdt.Discovery`,
whose type is exactly that statement.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Discovery

open Krepi.Statements.Fdt

/-- Proves `FdtDiscoverMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverMemory : FdtDiscoverMemory := by
  sorry

/-- Proves `MemoryMapRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapRam : MemoryMapRam := by
  sorry

/-- Proves `MemoryMapReserved`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapReserved : MemoryMapReserved := by
  sorry

/-- Proves `MemoryMapDynamic`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapDynamic : MemoryMapDynamic := by
  sorry

/-- Proves `FdtDiscoverBootMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverBootMemory : FdtDiscoverBootMemory := by
  sorry

/-- Proves `BootMemoryRam`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryRam : BootMemoryRam := by
  sorry

/-- Proves `BootMemoryReserved`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryReserved : BootMemoryReserved := by
  sorry

/-- Proves `BootMemoryDynamic`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryDynamic : BootMemoryDynamic := by
  sorry

/-- Proves `BootMemoryDtb`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryDtb : BootMemoryDtb := by
  sorry

/-- Proves `BootMemoryImage`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryImage : BootMemoryImage := by
  sorry

/-- Proves `BootMemoryRamBytes`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryRamBytes : BootMemoryRamBytes := by
  sorry

/-- Proves `BootMemoryIsAvailable`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryIsAvailable : BootMemoryIsAvailable := by
  sorry

/-- Proves `BootMemoryFindAvailable`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryFindAvailable : BootMemoryFindAvailable := by
  sorry

end Krepi.Proofs.Fdt.Refinement.Discovery
