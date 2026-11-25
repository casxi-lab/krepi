module

public import Krepi.Statements.PageTables.Representation
public import Krepi.Spec.PageTables.Witnesses.TableSets

/-!
# Page tables: refinement of the kernel mappings

One statement for each function of line 112 of the entry table of the
contract (`docs/domains/memory/page-tables/contract.md`), and for the `next`
of each of their plan iterators: for every input of its machine widths,
under the premises that its arguments need, the function returns, and its
result agrees with that of its function of `Krepi.Spec.PageTables` through
the representation of `Krepi.Statements.PageTables.Representation`, the
same error with the same priority included. Each entry returns its set after
its write phase, which stands for the set that its specification gives, and
a plan iterator that stands for the plan `mapPlan` of its specification; on
a failure it returns the set unchanged and no plan. `kernel_map` takes a
layout of at most 16 ranges, which the representation of a layout keeps,
and `direct_map` a boot memory map that the entries of the `fdt` component
built (`BuiltPlan`), premises of the proof path. The theorems below
`Krepi.Proofs.PageTables.Refinement` prove them.
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice U8 U64 Usize)
open KrepiGen.PageTables
open Krepi.Spec.PageTables

namespace Krepi.Statements.PageTables

/-- `page_tables::kernel_map(layout, base, bits)` on a set of the lower
region: the set after the write phase of `Tables.kernelMap` and a plan
iterator that stands for its plan, or its error with the set unchanged.
Feature: `krepi.kernel.kernel-memory`. -/
def KernelMap : Prop :=
  ∀ (N : Usize) (s : page_tables.Tables N false) (layout : page_tables.Layout) (L : Layout)
    (base : U64) (bits : U8), LayoutRepr layout L →
    page_tables.kernel_map s layout base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (Stands page_tables.boot.layout.KernelMapPlan.next StepRepr)
        (tableErrorOf · = ·) s r s' ((tablesOf s).kernelMap L (word64 base) (byte bits)) ⦄

/-- `KernelMapPlan::next()`: one call gives the next step of the plan that
the iterator stands for and leaves it standing for the rest; at the end it
gives none and stays at the end. Feature: `krepi.kernel.kernel-memory`. -/
def KernelMapPlanNext : Prop :=
  ∀ (N : Usize) (it : page_tables.KernelMapPlan N) (l : Plan),
    Stands page_tables.boot.layout.KernelMapPlan.next StepRepr it l →
    Advances page_tables.boot.layout.KernelMapPlan.next StepRepr it l

/-- `page_tables::direct_map(memory, base, bits)` on a set of the upper
region: the set after the write phase of `Tables.directMap` and a plan
iterator that stands for its plan, or its error with the set unchanged, for
a boot memory map that the entries of the `fdt` component built. Feature:
`krepi.kernel.kernel-memory`. -/
def DirectMap : Prop :=
  ∀ (N : Usize) (s : page_tables.Tables N true) (memory : fdt.MemoryPlan)
    (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8),
    MemoryPlanRepr memory P → Witnesses.TableSets.BuiltPlan P →
    page_tables.direct_map s memory base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (Stands page_tables.boot.direct.DirectMapPlan.next StepRepr)
        (tableErrorOf · = ·) s r s' ((tablesOf s).directMap P (word64 base) (byte bits)) ⦄

/-- `DirectMapPlan::next()`: one call gives the next step of the plan that
the iterator stands for and leaves it standing for the rest; at the end it
gives none and stays at the end. Feature: `krepi.kernel.kernel-memory`. -/
def DirectMapPlanNext : Prop :=
  ∀ (N : Usize) (it : page_tables.DirectMapPlan N) (l : Plan),
    Stands page_tables.boot.direct.DirectMapPlan.next StepRepr it l →
    Advances page_tables.boot.direct.DirectMapPlan.next StepRepr it l

end Krepi.Statements.PageTables
