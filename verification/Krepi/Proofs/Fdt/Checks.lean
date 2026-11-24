module

public import Krepi.SpecProperties.Fdt.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.DiscoveryLemmas

/-!
# Device tree: proofs about the checks of the invariants

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the checks of the invariants, whose type is exactly that statement:
that each computable check agrees with its invariant on every value.

Every theorem here is proved, by rewriting each conjunct of a check into the
conjunct of its invariant: the checks of spans and of pairs with the lemmas
of `Krepi.Proofs.Fdt.SpanLemmas` (`nonempty_iff`, `onPages_iff`,
`withinWidth_iff`, `allPairs_iff`), the checks of the nodes of a tree one
index at a time (`checkNode_iff`), and the check of the topology of the
hand-over with the profile that the topology holds, which is the profile of
the discovery that built it (`discoverCpus_ok` of
`Krepi.Proofs.Fdt.DiscoveryLemmas`). Mathlib is imported so that the gate
counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Checks

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- `Fdt.checkNode` decides `Fdt.NodeWellFormed`. -/
theorem checkNode_iff {t : Fdt} {i : Nat} {r : NodeRecord} :
    t.checkNode i r = true ↔ t.NodeWellFormed i r := by
  rcases r with ⟨name, parent, props⟩
  unfold Fdt.checkNode Fdt.NodeWellFormed
  by_cases hi : i = 0
  · simp [hi, allPairs_iff, and_assoc]
  · cases parent <;> simp [hi, allPairs_iff, and_assoc]

/-- The check of every index below `n`, one index at a time. -/
theorem all_range_iff {n : Nat} {g : Nat → Bool} {P : (i : Nat) → i < n → Prop}
    (hg : ∀ i (h : i < n), g i = true ↔ P i h) :
    (List.range n).all g = true ↔ ∀ i (h : i < n), P i h := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    exact (hg i hi).1 (h i (List.mem_range.2 hi))
  · intro h i hi
    exact (hg i (List.mem_range.1 hi)).2 (h i (List.mem_range.1 hi))

public theorem checkFdtWellFormed : CheckFdtWellFormed := by
  intro t
  unfold Fdt.checkWellFormed Fdt.WellFormed
  simp only [Bool.and_eq_true]
  rw [all_range_iff (P := fun i h => t.NodeWellFormed i t.records[i]) ?_]
  · simp only [decide_eq_true_eq, List.all_eq_true, nonempty_iff, allPairs_iff,
      Bool.not_eq_true', and_assoc]
  · intro i h
    rw [getElem?_pos t.records i h]
    exact checkNode_iff

public theorem checkRegWellFormed : CheckRegWellFormed := by
  intro r cells
  unfold Reg.checkWellFormed Reg.WellFormed
  simp [withinWidth_iff]

public theorem checkAddressMapWellFormed : CheckAddressMapWellFormed := by
  intro m
  rcases m with ⟨windows, cc, pc, sc⟩
  unfold AddressMap.checkWellFormed AddressMap.WellFormed
  cases windows <;> simp [Window.WellFormed, withinWidth_iff, and_assoc]

public theorem checkMemoryMapWellFormed : CheckMemoryMapWellFormed := by
  intro m
  unfold MemoryMap.checkWellFormed MemoryMap.WellFormed
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_eq_false_iff, nonempty_iff, allPairs_iff, and_assoc]

public theorem checkBootMemoryConsistent : CheckBootMemoryConsistent := by
  intro m
  unfold BootMemory.checkConsistent BootMemory.Consistent
  simp [nonempty_iff, and_assoc]

public theorem checkCpuTopologySupported : CheckCpuTopologySupported := by
  intro t
  unfold CpuTopology.checkSupported CpuTopology.Supported CpuProfile.allows
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    and_assoc]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h4 : (4 : UInt64).toNat = 4 := rfl
  rw [h1, h4]
  constructor
  · rintro ⟨h0, hle, hb⟩
    exact ⟨by omega, hle, hb⟩
  · rintro ⟨h0, hle, hb⟩
    exact ⟨by omega, hle, hb⟩

public theorem checkMemoryPlanWellFormed : CheckMemoryPlanWellFormed := by
  intro p
  unfold MemoryPlan.checkWellFormed MemoryPlan.WellFormed
  simp [nonempty_iff, onPages_iff, allPairs_iff, and_assoc]

public theorem checkBootStateWellFormed : CheckBootStateWellFormed := by
  intro s
  unfold BootState.checkWellFormed BootState.WellFormed
  cases s.plan with
  | none => simp
  | some p => simpa using checkMemoryPlanWellFormed p

public theorem checkBootStateFromHandOver : CheckBootStateFromHandOver := by
  intro s
  unfold BootState.checkFromHandOver BootState.FromHandOver
  cases s.topology with
  | none => simp
  | some t =>
    simp only [Option.some.injEq, forall_eq']
    constructor
    · intro h
      refine ⟨t.profile, ?_⟩
      generalize s.tree.bind (fun f => f.discoverCpus t.profile) = x at h
      cases x <;> simp_all
    · rintro ⟨profile, h⟩
      obtain ⟨_, -, hd⟩ := except_bind_ok.1 h
      obtain ⟨_, -, rfl⟩ := discoverCpus_ok hd
      dsimp only
      rw [h]
      simp

public theorem checkBootStateStartOrder : CheckBootStateStartOrder := by
  intro s
  unfold BootState.checkStartOrder BootState.StartOrder
  cases s.secondaries <;> simp

end Krepi.Proofs.Fdt.Checks
