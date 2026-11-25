module

public import Krepi.Proofs.Fdt.Refinement.SpanLemmas

/-!
# Device tree: refinement of the accessors of the memory values

The triples of the generated accessors of a memory map, a boot memory and a
boot memory map, each a `@[step]` lemma under the representation of its
value, so that the proof of a caller steps over the call with the triple of
the accessor:

- the memory map: `memory_map_ram_spec`, `memory_map_reserved_spec` and
  `memory_map_dynamic_spec`, the statements `MemoryMapRam`,
  `MemoryMapReserved` and `MemoryMapDynamic` without their premise
  `Usize64`;
- the boot memory: `boot_memory_ram_spec`, `boot_memory_reserved_spec`,
  `boot_memory_dynamic_spec`, `boot_memory_dtb_spec`,
  `boot_memory_image_spec` and `boot_memory_ram_bytes_spec`, the statements
  `BootMemoryRam`, `BootMemoryReserved`, `BootMemoryDynamic`,
  `BootMemoryDtb`, `BootMemoryImage` and `BootMemoryRamBytes` without their
  premise `Usize64`;
- the lists of the boot memory map: `memory_plan_ram_spec`,
  `memory_plan_managed_banks_spec`, `memory_plan_reservations_spec`,
  `memory_plan_boot_ranges_spec` and `memory_plan_firmware_ranges_spec`, the
  statements `MemoryPlanRam`, `MemoryPlanManagedBanks`,
  `MemoryPlanReservations`, `MemoryPlanBootRanges` and
  `MemoryPlanFirmwareRanges` without their premise `Usize64`.

A list is the prefix or the part of an array that the counts of the
representation bound, so `prefix_spec` and `part_spec` of
`Krepi.Proofs.Fdt.Refinement.SpanLemmas` give it.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The memory map -/

/-- `MemoryMap::ram()`: the RAM ranges of the memory map. -/
@[step] theorem memory_map_ram_spec {m : fdt.MemoryMap} {M : MemoryMap} (h : MemoryMapRepr m M) :
    fdt.discovery.MemoryMap.ram m ⦃ s => spansOf s = M.ram ⦄ := by
  obtain ⟨h1, -, rfl⟩ := h
  unfold fdt.discovery.MemoryMap.ram
  step*
  · simp only [s_post, Array.length_to_slice]; exact h1
  · subst_vars; simp only [spansOf, s_post, Array.val_to_slice]

/-- `MemoryMap::reserved()`: the reserved regions of the memory map. -/
@[step] theorem memory_map_reserved_spec {m : fdt.MemoryMap} {M : MemoryMap}
    (h : MemoryMapRepr m M) :
    fdt.discovery.MemoryMap.reserved m ⦃ s => regionsOf s = M.reserved ⦄ := by
  obtain ⟨-, h2, rfl⟩ := h
  unfold fdt.discovery.MemoryMap.reserved
  step*
  · simp only [s_post, Array.length_to_slice]; exact h2
  · subst_vars; simp only [regionsOf, s_post, Array.val_to_slice]

/-- `MemoryMap::dynamic()`: the number of dynamic reservations. -/
@[step] theorem memory_map_dynamic_spec {m : fdt.MemoryMap} {M : MemoryMap}
    (h : MemoryMapRepr m M) :
    fdt.discovery.MemoryMap.dynamic m ⦃ n => word64 n = M.dynamic ⦄ := by
  obtain ⟨-, -, rfl⟩ := h
  simp only [fdt.discovery.MemoryMap.dynamic, spec_ok]

/-! ## The boot memory -/

/-- `BootMemory::ram()`: the RAM ranges of its memory map. -/
@[step] theorem boot_memory_ram_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M) :
    fdt.hand_over.BootMemory.ram m ⦃ s => spansOf s = M.ram ⦄ :=
  memory_map_ram_spec h.1

/-- `BootMemory::reserved()`: the reserved regions of its memory map. -/
@[step] theorem boot_memory_reserved_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M) :
    fdt.hand_over.BootMemory.reserved m ⦃ s => regionsOf s = M.reserved ⦄ :=
  memory_map_reserved_spec h.1

/-- `BootMemory::dynamic()`: the number of dynamic reservations of its memory
map. -/
@[step] theorem boot_memory_dynamic_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M) :
    fdt.hand_over.BootMemory.dynamic m ⦃ n => word64 n = M.dynamic ⦄ :=
  memory_map_dynamic_spec h.1

/-- `BootMemory::dtb()`: the span of the tree. -/
@[step] theorem boot_memory_dtb_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M) :
    fdt.hand_over.BootMemory.dtb m ⦃ s => spanOf s = M.dtb ⦄ := by
  simp only [fdt.hand_over.BootMemory.dtb, spec_ok]; exact h.2.1.symm

/-- `BootMemory::image()`: the span of the image. -/
@[step] theorem boot_memory_image_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M) :
    fdt.hand_over.BootMemory.image m ⦃ s => spanOf s = M.image ⦄ := by
  simp only [fdt.hand_over.BootMemory.image, spec_ok]; exact h.2.2.1.symm

/-- `BootMemory::ram_bytes()`: the sum of the RAM ranges. -/
@[step] theorem boot_memory_ram_bytes_spec {m : fdt.BootMemory} {M : BootMemory}
    (h : BootMemoryRepr m M) :
    fdt.hand_over.BootMemory.ram_bytes m ⦃ n => word64 n = M.ramBytes ⦄ := by
  simp only [fdt.hand_over.BootMemory.ram_bytes, spec_ok]; exact h.2.2.2.1.symm

/-! ## The lists of the boot memory map -/

/-- `MemoryPlan::ram()`: the banks. -/
@[step] theorem memory_plan_ram_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) :
    fdt.plan.MemoryPlan.ram p ⦃ s => spansOf s = P.ram ⦄ := by
  obtain ⟨h1, -, -, -, rfl⟩ := h
  unfold fdt.plan.MemoryPlan.ram
  step*
  · simp only [s_post, Array.length_to_slice]; exact h1
  · subst_vars; simp only [spansOf, s_post, Array.val_to_slice]

/-- `MemoryPlan::managed_banks()`: the managed banks. -/
@[step] theorem memory_plan_managed_banks_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) :
    fdt.plan.MemoryPlan.managed_banks p ⦃ s => spansOf s = P.managedBanks ⦄ := by
  obtain ⟨-, h2, -, -, rfl⟩ := h
  unfold fdt.plan.MemoryPlan.managed_banks
  step*
  · simp only [s_post, Array.length_to_slice]; exact h2
  · subst_vars; simp only [spansOf, s_post, Array.val_to_slice, MemoryPlan.managedBanks]

/-- `MemoryPlan::boot_ranges()`: the boot storage. -/
@[step] theorem memory_plan_boot_ranges_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) :
    fdt.plan.MemoryPlan.boot_ranges p ⦃ s => spansOf s = P.bootRanges ⦄ := by
  obtain ⟨-, -, h3, h4, rfl⟩ := h
  unfold fdt.plan.MemoryPlan.boot_ranges
  step*
  · simp only [s_post, Array.length_to_slice, MemoryPlan.MAX_BOOT_SPANS,
      MemoryPlan.MAX_FIRMWARE] at h4 ⊢
    scalar_tac
  · subst_vars; simp only [spansOf, s_post, Array.val_to_slice, MemoryPlan.bootRanges]

/-- `MemoryPlan::reservations()`: the boot storage and then the firmware
reservations, the first `reserved_count` entries of the array. -/
@[step] theorem memory_plan_reservations_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) :
    fdt.plan.MemoryPlan.reservations p ⦃ s => spansOf s = P.reservations ⦄ := by
  obtain ⟨-, -, h3, h4, rfl⟩ := h
  unfold fdt.plan.MemoryPlan.reservations
  step*
  · simp only [s_post, Array.length_to_slice, MemoryPlan.MAX_BOOT_SPANS,
      MemoryPlan.MAX_FIRMWARE] at h4 ⊢
    scalar_tac
  · subst_vars
    have e : List.take p.boot_count.val p.reserved.val =
        List.take p.boot_count.val (List.take p.reserved_count.val p.reserved.val) := by
      rw [List.take_take, Nat.min_eq_left h3]
    simp only [spansOf, s_post, Array.val_to_slice, MemoryPlan.reservations, ← List.map_append, e,
      List.take_append_drop]

/-- `MemoryPlan::firmware_ranges()`: the firmware reservations. -/
@[step] theorem memory_plan_firmware_ranges_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) :
    fdt.plan.MemoryPlan.firmware_ranges p ⦃ s => spansOf s = P.firmwareRanges ⦄ := by
  obtain ⟨-, -, h3, h4, rfl⟩ := h
  unfold fdt.plan.MemoryPlan.firmware_ranges
  step*
  · simp only [s_post, Array.length_to_slice, MemoryPlan.MAX_BOOT_SPANS,
      MemoryPlan.MAX_FIRMWARE] at h4 ⊢
    scalar_tac
  · subst_vars
    simp only [spansOf, s_post, Array.val_to_slice, MemoryPlan.firmwareRanges, List.drop_take]

end Krepi.Proofs.Fdt.Refinement
