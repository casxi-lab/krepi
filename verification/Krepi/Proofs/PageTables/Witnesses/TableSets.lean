module

public import Krepi.Spec.PageTables.Witnesses.TableSets
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Plan
import Krepi.Proofs.Fdt.PlanLemmas
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.ListLemmas

/-!
# Page tables: proofs of the unreachable error branches of the table sets

One theorem for each proposition of `Krepi.Spec.PageTables.Witnesses.TableSets`
that the module does not prove itself, whose type is exactly that
proposition: for each error branch that no input of its entry reaches, that
the entry never takes it.

Every theorem here is proved. The usable ranges of a boot memory map that
the fdt entries build are well-formed (`Krepi.Proofs.Fdt.Plan`): on pages,
and in address order with each ending at or before the start of the next,
so that sorting them by their start leaves them as they are; and the check
of the target pool takes the width that the check of the source pool has
accepted. Mathlib is imported so that the gate counts the heartbeats of each
theorem.
-/

namespace Krepi.Proofs.PageTables.Witnesses.TableSets

open Krepi.Spec.PageTables Krepi.Spec.PageTables.Witnesses.TableSets
open Krepi.Proofs.PageTables

/-- A boot memory map that an entry of the fdt specification builds is
well-formed. -/
private theorem built_wf {p : Krepi.Spec.Fdt.MemoryPlan} (hp : BuiltPlan p) : p.WellFormed := by
  rcases hp with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩
  · exact Krepi.Proofs.Fdt.Plan.allRamWellFormed _ _ _ _ h
  · exact Krepi.Proofs.Fdt.Plan.memoryPlanNewWellFormed _ _ _ _ _ h

/-! ## Unreachable error branches -/

public theorem directMapRangesOnPages : DirectMapRangesOnPages := by
  intro p hp u hu
  exact ((Krepi.Proofs.Fdt.Plan.availableRangesWellFormed p (built_wf hp)).1 u hu).2

public theorem directMapRangesApart : DirectMapRangesApart := by
  intro p hp
  obtain ⟨hne, hpw, -⟩ := Krepi.Proofs.Fdt.Plan.availableRangesWellFormed p (built_wf hp)
  have hle : p.availableRanges.Pairwise (fun a b => a.start.toNat ≤ b.start.toNat) := by
    refine List.Pairwise.imp_of_mem ?_ hpw
    intro a b ha _ hab
    have := Krepi.Proofs.Fdt.nonempty_lt (hne a ha).1
    omega
  rw [sortByKey_of_pairwise _ _ hle]
  exact hpw

public theorem cloneTargetWidthChecked : CloneTargetWidthChecked := by
  intro N sb base bits h1 h2
  have := (checkPool_ok.1 h1).2.1
  unfold checkPool at h2
  by_cases ha : base.toNat % PAGE_SIZE = 0 <;> by_cases hc : poolFits N base bits = true <;>
    simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

end Krepi.Proofs.PageTables.Witnesses.TableSets
