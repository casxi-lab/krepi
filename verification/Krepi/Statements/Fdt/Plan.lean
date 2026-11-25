module

public import Krepi.Statements.Fdt.Representation
public import Krepi.SpecProperties.Fdt.Invariants

/-!
# Device tree: refinement of the boot memory map

One statement for each function of lines 116 and 117 of the entry table of
the contract (`docs/domains/boot-platform/fdt/contract.md`), and for the
`next` of the iterator of the usable ranges: for every input of its machine
widths, under the premises that its arguments need, the function returns,
and its result agrees with that of its function of `Krepi.Spec.Fdt` through
the representation of `Krepi.Statements.Fdt.Representation`, the same error
with the same priority included. None of these functions writes anything.
The queries that read the spans of a boot memory map take
`MemoryPlan.WellFormed`, which its three constructors establish, and the
construction from a boot memory takes the invariants of the boot memory,
premises of the proof path. The theorems below
`Krepi.Proofs.Fdt.Refinement` prove them.
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice Str U8 U32 U64)
open KrepiGen.Fdt
open Krepi.Spec.Fdt

namespace Krepi.Statements.Fdt

/-! ## Construction -/

/-- `MemoryPlan::all_ram(ram, boot, firmware)`: a boot memory map that stands
for that of `MemoryPlan.allRam` of the spans and the regions, or its error.
Feature: `krepi.platform.device-tree`. -/
def MemoryPlanAllRam : Prop :=
  ∀ (ram boot : Slice fdt.Span) (firmware : Slice fdt.ReservedRegion),
    fdt.plan.MemoryPlan.all_ram ram boot firmware ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (MemoryPlan.allRam (spansOf ram) (spansOf boot) (regionsOf firmware)) ⦄

/-- `MemoryPlan::new(window, ram, boot, firmware)`: a boot memory map that
stands for that of `MemoryPlan.new`, or its error. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanNew : Prop :=
  ∀ (window : fdt.Span) (ram boot : Slice fdt.Span)
    (firmware : Slice fdt.ReservedRegion),
    fdt.plan.MemoryPlan.new window ram boot firmware ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (MemoryPlan.new (spanOf window) (spansOf ram) (spansOf boot) (regionsOf firmware)) ⦄

/-- `MemoryPlan::from_boot_memory(memory, window, more)`: a boot memory map
that stands for that of `MemoryPlan.fromBootMemory`, or its error, for a
boot memory that keeps its invariants. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanFromBootMemory : Prop :=
  ∀ (m : fdt.BootMemory) (M : BootMemory) (window : fdt.Span) (more : Slice fdt.Span),
    BootMemoryRepr m M → M.memory.WellFormed → M.Consistent →
    fdt.plan.MemoryPlan.from_boot_memory m window more ⦃ r =>
      Agrees MemoryPlanRepr planErrorOf r
        (MemoryPlan.fromBootMemory M (spanOf window) (spansOf more)) ⦄

/-! ## The lists -/

/-- `MemoryPlan::managed_banks()`: the managed banks. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanManagedBanks : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P →
    fdt.plan.MemoryPlan.managed_banks p ⦃ s => spansOf s = P.managedBanks ⦄

/-- `MemoryPlan::ram()`: the banks. Feature: `krepi.platform.device-tree`. -/
def MemoryPlanRam : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P →
    fdt.plan.MemoryPlan.ram p ⦃ s => spansOf s = P.ram ⦄

/-- `MemoryPlan::reservations()`: the boot storage and then the firmware
reservations, `MemoryPlan.reservations`. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanReservations : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P →
    fdt.plan.MemoryPlan.reservations p ⦃ s => spansOf s = P.reservations ⦄

/-- `MemoryPlan::boot_ranges()`: the boot storage. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanBootRanges : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P →
    fdt.plan.MemoryPlan.boot_ranges p ⦃ s => spansOf s = P.bootRanges ⦄

/-- `MemoryPlan::firmware_ranges()`: the firmware reservations. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanFirmwareRanges : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P →
    fdt.plan.MemoryPlan.firmware_ranges p ⦃ s => spansOf s = P.firmwareRanges ⦄

/-! ## The queries -/

/-- `MemoryPlan::described_bytes()`: the sum of the banks, for a well-formed
map. Feature: `krepi.platform.device-tree`. -/
def MemoryPlanDescribedBytes : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P → P.WellFormed →
    fdt.plan.MemoryPlan.described_bytes p ⦃ n => word64 n = P.describedBytes ⦄

/-- `MemoryPlan::managed_bytes()`: the sum of the managed banks, for a
well-formed map. Feature: `krepi.platform.device-tree`. -/
def MemoryPlanManagedBytes : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P → P.WellFormed →
    fdt.plan.MemoryPlan.managed_bytes p ⦃ n => word64 n = P.managedBytes ⦄

/-- `MemoryPlan::contains_ram(range)`: whether one bank holds the range, for
a well-formed map. Feature: `krepi.platform.device-tree`. -/
def MemoryPlanContainsRam : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan) (range : fdt.Span),
    MemoryPlanRepr p P → P.WellFormed →
    fdt.plan.MemoryPlan.contains_ram p range ⦃ b => b = P.containsRam (spanOf range) ⦄

/-- `MemoryPlan::is_available(range)`: whether the range is available, for a
well-formed map. Feature: `krepi.platform.device-tree`. -/
def MemoryPlanIsAvailable : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan) (range : fdt.Span),
    MemoryPlanRepr p P → P.WellFormed →
    fdt.plan.MemoryPlan.is_available p range ⦃ b => b = P.isAvailable (spanOf range) ⦄

/-- `MemoryPlan::permits_backing(range)`: whether a managed bank holds the
range and it is available, for a well-formed map. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanPermitsBacking : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan) (range : fdt.Span),
    MemoryPlanRepr p P → P.WellFormed →
    fdt.plan.MemoryPlan.permits_backing p range ⦃ b => b = P.permitsBacking (spanOf range) ⦄

/-! ## The usable ranges -/

/-- `MemoryPlan::available_ranges()`: an iterator that stands for the usable
ranges, `MemoryPlan.availableRanges`, for a well-formed map. Feature:
`krepi.platform.device-tree`. -/
def MemoryPlanAvailableRanges : Prop :=
  ∀ (p : fdt.MemoryPlan) (P : MemoryPlan), MemoryPlanRepr p P → P.WellFormed →
    fdt.plan.MemoryPlan.available_ranges p ⦃ it =>
      Stands fdt.plan.available.AvailableRanges.next SpanRepr it P.availableRanges ⦄

/-- `AvailableRanges::next()`: one call gives the next range of the list that
the iterator stands for and leaves it standing for the rest; at the end it
gives none and stays at the end. Feature: `krepi.platform.device-tree`. -/
def AvailableRangesNext : Prop :=
  ∀ (it : fdt.AvailableRanges) (l : List Span),
    Stands fdt.plan.available.AvailableRanges.next SpanRepr it l →
    Advances fdt.plan.available.AvailableRanges.next SpanRepr it l

end Krepi.Statements.Fdt
