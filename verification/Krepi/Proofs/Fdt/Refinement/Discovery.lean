module

public import Krepi.Statements.Fdt.Discovery
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.AccessorLemmas

/-!
# Device tree: refinement of the memory discovery and the boot memory

One theorem for each statement of `Krepi.Statements.Fdt.Discovery`,
whose type is exactly that statement.

The accessors of the memory map and of the boot memory are proved: each
restates the triple of its function in
`Krepi.Proofs.Fdt.Refinement.AccessorLemmas` (`memory_map_ram_spec`,
`memory_map_reserved_spec`, `memory_map_dynamic_spec`, `boot_memory_ram_spec`,
`boot_memory_reserved_spec`, `boot_memory_dynamic_spec`,
`boot_memory_dtb_spec`, `boot_memory_image_spec` and
`boot_memory_ram_bytes_spec`), which holds without the premise `Usize64`. The
discoveries and the queries of a boot memory, `fdtDiscoverMemory`,
`fdtDiscoverBootMemory`, `bootMemoryIsAvailable` and
`bootMemoryFindAvailable`, are planned: their proofs are `sorry`, and
`verification/statements.json` registers them as `planned`, so that no
module imports this one. Mathlib is imported so that the gate counts the
heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Discovery

open Krepi.Statements.Fdt Krepi.Proofs.Fdt.Refinement

/-- Proves `FdtDiscoverMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverMemory : FdtDiscoverMemory := by
  sorry

/-- Proves `MemoryMapRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapRam : MemoryMapRam := fun _ _ _ h => memory_map_ram_spec h

/-- Proves `MemoryMapReserved`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapReserved : MemoryMapReserved := fun _ _ _ h => memory_map_reserved_spec h

/-- Proves `MemoryMapDynamic`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapDynamic : MemoryMapDynamic := fun _ _ _ h => memory_map_dynamic_spec h

/-- Proves `FdtDiscoverBootMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverBootMemory : FdtDiscoverBootMemory := by
  sorry

/-- Proves `BootMemoryRam`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryRam : BootMemoryRam := fun _ _ _ h => boot_memory_ram_spec h

/-- Proves `BootMemoryReserved`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryReserved : BootMemoryReserved := fun _ _ _ h => boot_memory_reserved_spec h

/-- Proves `BootMemoryDynamic`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryDynamic : BootMemoryDynamic := fun _ _ _ h => boot_memory_dynamic_spec h

/-- Proves `BootMemoryDtb`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryDtb : BootMemoryDtb := fun _ _ _ h => boot_memory_dtb_spec h

/-- Proves `BootMemoryImage`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryImage : BootMemoryImage := fun _ _ _ h => boot_memory_image_spec h

/-- Proves `BootMemoryRamBytes`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryRamBytes : BootMemoryRamBytes :=
  fun _ _ _ h => boot_memory_ram_bytes_spec h

/-- Proves `BootMemoryIsAvailable`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryIsAvailable : BootMemoryIsAvailable := by
  sorry

/-- Proves `BootMemoryFindAvailable`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryFindAvailable : BootMemoryFindAvailable := by
  sorry

end Krepi.Proofs.Fdt.Refinement.Discovery
