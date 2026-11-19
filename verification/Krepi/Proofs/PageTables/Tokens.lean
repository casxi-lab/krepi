module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.Tables

/-!
# Page tables: proofs about the shared state

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the shared state, whose type is
exactly that statement: that the shared state of the boot is well-formed and
keeps the offset of the direct map, that `direct_map` keeps that offset, and
that each transaction keeps the shared state well-formed.

The theorems about the boot, `enable` and the fill of the lower kernel set
are proved: each transaction on a kernel set is the entry on that set, whose
well-formedness is a theorem of `Krepi.Proofs.PageTables.Tables`, and leaves
the other fields as they are. The other theorems are still planned: their
proof is `sorry`, and `verification/statements.json` registers them as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Tokens

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables

/-- A map of a result succeeds exactly when the result is a success. -/
private theorem except_map_ok {ε α β : Type} {f : α → β} {x : Except ε α} {b : β} :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Except.map]

/-- Every entry of the set of `Tables::new` on a zero pool is 0. -/
private theorem new_entry_zero {r : Region} {N : Nat} (t i : Nat) :
    (Tables.new (Pool.zero N) : Tables r N).entry t i = 0 := by
  simp only [Tables.entry, Tables.table, Tables.new, Pool.zero]
  split <;> (try split) <;> simp [Table.zero]

public theorem bootWellFormed : BootWellFormed := by
  intro E X cfg h1 h2
  refine ⟨Tables.newWellFormed _ _ _ _ h1, Tables.newWellFormed _ _ _ _ h2, ?_⟩
  intro t ht; simp [Shared.boot] at ht

public theorem bootDirectMapOffset : BootDirectMapOffset := by
  intro E X cfg v l hM
  have hw : (Tables.new (Pool.zero DIRECT_MAP_TABLES) : Tables .upper DIRECT_MAP_TABLES).walk
      cfg.directBase v = .ok .root := by
    simp [Tables.walk, Tables.walk2, new_entry_zero, isValid, typeBits, bind, Except.bind, pure,
      Except.pure]
  obtain ⟨-, -, ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩⟩ := hM <;>
    simp only [Shared.boot] at h <;> rw [hw] at h <;> cases h

public theorem buildDirectMapOffset : BuildDirectMapOffset := by
  sorry

public theorem buildKernelMapWellFormed : BuildKernelMapWellFormed := by
  sorry

public theorem buildDirectMapWellFormed : BuildDirectMapWellFormed := by
  sorry

public theorem enableWellFormed : EnableWellFormed := by
  intro E X cfg cpu s s' hs h
  unfold Shared.enable at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact hs

public theorem fillKernelWellFormed : FillKernelWellFormed := by
  intro E X cfg tok s v p k s' plan hs h
  unfold Shared.fillKernel at h
  split at h
  · simp only [Option.some.injEq, except_map_ok] at h
    obtain ⟨⟨t, pl⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨Tables.mapPageWellFormed _ _ _ _ _ _ _ _ _ _ hs.1 h1, hs.2.1, hs.2.2⟩
  · simp at h

public theorem newOwnershipSharedWellFormed : NewOwnershipSharedWellFormed := by
  sorry

public theorem withOwnershipWellFormed : WithOwnershipWellFormed := by
  sorry

public theorem allocateWellFormed : AllocateWellFormed := by
  sorry

end Krepi.Proofs.PageTables.Tokens
