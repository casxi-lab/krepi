module

public import Krepi.Statements.PageTables.Ownership
public import Krepi.Proofs.PageTables.Refinement.ReceiptLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.Refinement.PlaceLemmas
import Krepi.Proofs.PageTables.Refinement.OwnNewLemmas

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
public theorem ownershipPublish : OwnershipPublish :=
  fun _ _ _ t T owner packet I hT _ hI => ownership_publish_spec t T owner packet I hT hI

/-- Proves `OwnershipCancel`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipCancel : OwnershipCancel :=
  fun _ _ _ t T owner r R hT _ hR => ownership_cancel_spec t T owner r R hT hR

/-- Proves `OwnershipRelease`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipRelease : OwnershipRelease :=
  fun _ _ _ t T owner a A hT _ hA => ownership_release_spec t T owner a A hT hA

/-- Proves `OwnershipOwner`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipOwner : OwnershipOwner :=
  fun _ _ _ t T address h _ => ownership_owner_spec t T h address

/-- Proves `OwnershipValidate`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipValidate : OwnershipValidate :=
  fun _ _ _ t T owner a A s hT _ hA => ownership_validate_spec t T owner a A s hT hA

/-- Proves `OwnershipStats`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem ownershipStats : OwnershipStats :=
  fun _ _ _ t T h hi => ownership_stats_spec t T h hi.1

end Krepi.Proofs.PageTables.Refinement.Ownership
