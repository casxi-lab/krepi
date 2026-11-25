module

public import Krepi.Statements.Fdt.Representation
public import Krepi.SpecProperties.Fdt.Invariants

/-!
# Device tree: refinement of the memory discovery and the boot memory

One statement for each function of lines 111 to 113 of the entry table of
the contract (`docs/domains/boot-platform/fdt/contract.md`): for every input
of its machine widths, under the premises that its arguments need, the
function returns, and its result agrees with that of its function of
`Krepi.Spec.Fdt` through the representation of
`Krepi.Statements.Fdt.Representation`, the same error with the same
priority included. None of these functions writes anything. The queries of
a boot memory take the two invariants that the discovery of the boot memory
establishes, `MemoryMap.WellFormed` and `BootMemory.Consistent`, the
premises of the proof path. The theorems below
`Krepi.Proofs.Fdt.Refinement` prove them.
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice Str U8 U32 U64)
open KrepiGen.Fdt
open Krepi.Spec.Fdt

namespace Krepi.Statements.Fdt

/-! ## The memory map -/

/-- `Fdt::discover_memory()`: a memory map that stands for that of
`Fdt.discoverMemory`, or its error.
Feature: `krepi.platform.device-tree`. -/
def FdtDiscoverMemory : Prop :=
  Usize64 →
  ∀ (t : fdt.Fdt) (T : Fdt), FdtRepr t T →
    fdt.discovery.Fdt.discover_memory t ⦃ r => Agrees MemoryMapRepr errorOf r T.discoverMemory ⦄

/-- `MemoryMap::ram()`: the RAM ranges of the memory map.
Feature: `krepi.platform.device-tree`. -/
def MemoryMapRam : Prop :=
  Usize64 →
  ∀ (m : fdt.MemoryMap) (M : MemoryMap), MemoryMapRepr m M →
    fdt.discovery.MemoryMap.ram m ⦃ s => spansOf s = M.ram ⦄

/-- `MemoryMap::reserved()`: the reserved regions of the memory map.
Feature: `krepi.platform.device-tree`. -/
def MemoryMapReserved : Prop :=
  Usize64 →
  ∀ (m : fdt.MemoryMap) (M : MemoryMap), MemoryMapRepr m M →
    fdt.discovery.MemoryMap.reserved m ⦃ s => regionsOf s = M.reserved ⦄

/-- `MemoryMap::dynamic()`: the number of dynamic reservations of the memory
map.
Feature: `krepi.platform.device-tree`. -/
def MemoryMapDynamic : Prop :=
  Usize64 →
  ∀ (m : fdt.MemoryMap) (M : MemoryMap), MemoryMapRepr m M →
    fdt.discovery.MemoryMap.dynamic m ⦃ n => word64 n = M.dynamic ⦄

/-! ## The boot memory -/

/-- `Fdt::discover_boot_memory(hand_over, dtb_address, image)`: a boot memory
that stands for that of `Fdt.discoverBootMemory` of the profile, the address
and the span, or its error.
Feature: `krepi.platform.device-tree`. -/
def FdtDiscoverBootMemory : Prop :=
  Usize64 →
  ∀ (t : fdt.Fdt) (T : Fdt) (handOver : fdt.HandOverProfile) (dtbAddress : U64)
    (image : fdt.Span), FdtRepr t T →
    fdt.hand_over.Fdt.discover_boot_memory t handOver dtbAddress image ⦃ r =>
      Agrees BootMemoryRepr errorOf r
        (T.discoverBootMemory (handOverOf handOver) (word64 dtbAddress) (spanOf image)) ⦄

/-- `BootMemory::ram()`: the RAM ranges, `BootMemory.ram`.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryRam : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory), BootMemoryRepr m M →
    fdt.hand_over.BootMemory.ram m ⦃ s => spansOf s = M.ram ⦄

/-- `BootMemory::reserved()`: the reserved regions, `BootMemory.reserved`.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryReserved : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory), BootMemoryRepr m M →
    fdt.hand_over.BootMemory.reserved m ⦃ s => regionsOf s = M.reserved ⦄

/-- `BootMemory::dynamic()`: the number of dynamic reservations,
`BootMemory.dynamic`.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryDynamic : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory), BootMemoryRepr m M →
    fdt.hand_over.BootMemory.dynamic m ⦃ n => word64 n = M.dynamic ⦄

/-- `BootMemory::dtb()`: the span of the tree.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryDtb : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory), BootMemoryRepr m M →
    fdt.hand_over.BootMemory.dtb m ⦃ s => spanOf s = M.dtb ⦄

/-- `BootMemory::image()`: the span of the image.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryImage : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory), BootMemoryRepr m M →
    fdt.hand_over.BootMemory.image m ⦃ s => spanOf s = M.image ⦄

/-- `BootMemory::ram_bytes()`: the sum of the RAM ranges.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryRamBytes : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory), BootMemoryRepr m M →
    fdt.hand_over.BootMemory.ram_bytes m ⦃ n => word64 n = M.ramBytes ⦄

/-- `BootMemory::is_available(span)`: whether the span is available, or the
error, of `BootMemory.isAvailable`, for a boot memory that keeps its
invariants.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryIsAvailable : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory) (span : fdt.Span), BootMemoryRepr m M →
    M.memory.WellFormed → M.Consistent →
    fdt.hand_over.BootMemory.is_available m span ⦃ r =>
      Agrees (· = ·) errorOf r (M.isAvailable (spanOf span)) ⦄

/-- `BootMemory::find_available(size, alignment, minimum, limit)`: the span
of `BootMemory.findAvailable`, none when no RAM range has one, or its error,
for a boot memory that keeps its invariants.
Feature: `krepi.platform.device-tree`. -/
def BootMemoryFindAvailable : Prop :=
  Usize64 →
  ∀ (m : fdt.BootMemory) (M : BootMemory) (size alignment minimum limit : U64),
    BootMemoryRepr m M → M.memory.WellFormed → M.Consistent →
    fdt.hand_over.selection.BootMemory.find_available m size alignment minimum limit ⦃ r =>
      Agrees (OptionRel SpanRepr) errorOf r
        (M.findAvailable (word64 size) (word64 alignment) (word64 minimum) (word64 limit)) ⦄

end Krepi.Statements.Fdt
