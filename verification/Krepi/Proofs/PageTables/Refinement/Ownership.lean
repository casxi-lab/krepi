module

public import Krepi.Statements.PageTables.Ownership
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.Refinement.PlaceLemmas

/-!
# Page tables: refinement of the page ownership table

One theorem for each statement of `Krepi.Statements.PageTables.Ownership`,
whose type is exactly that statement.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Refinement.Ownership

open Krepi.Statements.PageTables Krepi.Proofs.PageTables.Refinement

/-- Proves `OwnershipNew`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipNew : OwnershipNew := by
  sorry

/-- Proves `OwnershipChoose`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipChoose : OwnershipChoose :=
  fun _ _ _ t T owner pages alignment placement P ht _ hP =>
    ownership_choose_spec t T owner pages alignment placement P ht hP

/-- Proves `OwnershipAssign`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipAssign : OwnershipAssign :=
  fun _ _ _ t T choice C zeroed ht _ hc _ => ownership_assign_spec t T choice C zeroed ht hc

/-- Proves `OwnershipReserve`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipReserve : OwnershipReserve :=
  fun _ _ _ t T owner pages alignment placement P ht _ hP =>
    ownership_reserve_spec t T owner pages alignment placement P ht hP

/-- Proves `ReservationInitialized`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem reservationInitialized : ReservationInitialized :=
  fun _ r R zeroed h => reservation_initialized_spec r R zeroed h

/-- Proves `OwnershipPublish`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipPublish : OwnershipPublish := by
  sorry

/-- Proves `OwnershipCancel`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipCancel : OwnershipCancel := by
  sorry

/-- Proves `OwnershipRelease`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipRelease : OwnershipRelease := by
  sorry

/-- Proves `OwnershipOwner`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipOwner : OwnershipOwner := by
  sorry

/-- Proves `OwnershipValidate`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipValidate : OwnershipValidate := by
  sorry

/-- Proves `OwnershipStats`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipStats : OwnershipStats := by
  sorry

end Krepi.Proofs.PageTables.Refinement.Ownership
