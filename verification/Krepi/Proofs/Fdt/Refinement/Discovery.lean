module

public import Krepi.Statements.Fdt.Discovery
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.AccessorLemmas
import Krepi.Proofs.Fdt.Refinement.MemoryLemmas
import Krepi.Proofs.Fdt.Refinement.BootLemmas

/-!
# Device tree: refinement of the memory discovery and the boot memory

One theorem for each statement of `Krepi.Statements.Fdt.Discovery`,
whose type is exactly that statement. All of them are proved; each restates
the triple of its function in a helper module.

- The memory discovery: `fdtDiscoverMemory` restates
  `fdt_discover_memory_spec` of `Krepi.Proofs.Fdt.Refinement.MemoryLemmas`.
- The accessors of the memory map and of the boot memory restate the triples
  of `Krepi.Proofs.Fdt.Refinement.AccessorLemmas` (`memory_map_ram_spec`,
  `memory_map_reserved_spec`, `memory_map_dynamic_spec`,
  `boot_memory_ram_spec`, `boot_memory_reserved_spec`,
  `boot_memory_dynamic_spec`, `boot_memory_dtb_spec`, `boot_memory_image_spec`
  and `boot_memory_ram_bytes_spec`), which hold without the premise
  `Usize64`.
- The boot memory: `fdtDiscoverBootMemory`, `bootMemoryIsAvailable` and
  `bootMemoryFindAvailable` restate `fdt_discover_boot_memory_spec`,
  `boot_memory_is_available_spec` and `boot_memory_find_available_spec` of
  `Krepi.Proofs.Fdt.Refinement.BootLemmas`. The availability holds without
  the premise `Usize64` and without the invariants of the boot memory; the
  selection holds without `Usize64` and uses the invariants for the ends of
  the RAM ranges and of the exclusions, which its code adds without a check.

Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Discovery

open Krepi.Statements.Fdt Krepi.Proofs.Fdt.Refinement

/-- Proves `FdtDiscoverMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverMemory : FdtDiscoverMemory := fdt_discover_memory_spec

/-- Proves `MemoryMapRam`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapRam : MemoryMapRam := fun _ _ _ h => memory_map_ram_spec h

/-- Proves `MemoryMapReserved`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapReserved : MemoryMapReserved := fun _ _ _ h => memory_map_reserved_spec h

/-- Proves `MemoryMapDynamic`. Feature: `krepi.platform.device-tree`. -/
public theorem memoryMapDynamic : MemoryMapDynamic := fun _ _ _ h => memory_map_dynamic_spec h

/-- Proves `FdtDiscoverBootMemory`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverBootMemory : FdtDiscoverBootMemory :=
  fun hu t T handOver dtbAddress image h =>
    fdt_discover_boot_memory_spec hu t T handOver dtbAddress image h

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
public theorem bootMemoryIsAvailable : BootMemoryIsAvailable :=
  fun _ _ _ span h _ _ => boot_memory_is_available_spec h span

/-- Proves `BootMemoryFindAvailable`. Feature: `krepi.platform.device-tree`. -/
public theorem bootMemoryFindAvailable : BootMemoryFindAvailable :=
  fun _ _ _ size alignment minimum limit h hw hc =>
    boot_memory_find_available_spec h hw hc size alignment minimum limit

end Krepi.Proofs.Fdt.Refinement.Discovery
