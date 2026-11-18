module

public import Krepi.SpecTests.PageTables.Stp
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs of the specification tests

One theorem for each specification test of `Krepi.SpecTests.PageTables`,
whose type is exactly that test: for each requirement of the component,
PGT-R01 to PGT-R12, the input that the specification accepts with its result
and the input that it rejects with its error.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Stp

open Krepi.SpecTests.PageTables

/-! ## PGT-R01 -/

public theorem descriptorsFollowKindRows : DescriptorsFollowKindRows := by
  sorry

public theorem descriptorKeepsOnlyItsBits : DescriptorKeepsOnlyItsBits := by
  sorry

/-! ## PGT-R02 -/

public theorem mapPageThenLookup : MapPageThenLookup := by
  sorry

public theorem mapPageRefusesMappedPage : MapPageRefusesMappedPage := by
  sorry

/-! ## PGT-R03 -/

public theorem eightGibOfBlocksInNineTables : EightGibOfBlocksInNineTables := by
  sorry

public theorem blockBeyondNineTablesRefused : BlockBeyondNineTablesRefused := by
  sorry

/-! ## PGT-R04 -/

public theorem unmapAndResetFollowContract : UnmapAndResetFollowContract := by
  sorry

public theorem unmapRefusesUnmappedPage : UnmapRefusesUnmappedPage := by
  sorry

/-! ## PGT-R05 -/

public theorem directMapCountsOfPi5Models : DirectMapCountsOfPi5Models := by
  sorry

public theorem directMapOmitsExcludedPages : DirectMapOmitsExcludedPages := by
  sorry

/-! ## PGT-R06 -/

public theorem kernelMapGivesKindsAndGuard : KernelMapGivesKindsAndGuard := by
  sorry

public theorem kernelMapRefusesSharedPage : KernelMapRefusesSharedPage := by
  sorry

/-! ## PGT-R07 -/

public theorem plansFollowContractOrder : PlansFollowContractOrder := by
  sorry

public theorem kernelFillRefusesValidEntry : KernelFillRefusesValidEntry := by
  sorry

/-! ## PGT-R08 -/

public theorem ownershipOfBoardShapes : OwnershipOfBoardShapes := by
  sorry

public theorem ownershipRefusesOverlappingBanks : OwnershipRefusesOverlappingBanks := by
  sorry

/-! ## PGT-R09 -/

public theorem allocationTakesWindowAndGeneration : AllocationTakesWindowAndGeneration := by
  sorry

public theorem releaseRefusesStaleReceipt : ReleaseRefusesStaleReceipt := by
  sorry

/-! ## PGT-R10 -/

public theorem reservationPublishesAfterZeroing : ReservationPublishesAfterZeroing := by
  sorry

public theorem cancelRefusesAttemptedReservation : CancelRefusesAttemptedReservation := by
  sorry

/-! ## PGT-R11 -/

public theorem capacitiesAtTheirLimits : CapacitiesAtTheirLimits := by
  sorry

public theorem capacitiesRefuseOneMore : CapacitiesRefuseOneMore := by
  sorry

/-! ## PGT-R12 -/

public theorem copyIsPrivateAndOrdered : CopyIsPrivateAndOrdered := by
  sorry

public theorem copyRefusesPrivateLeaf : CopyRefusesPrivateLeaf := by
  sorry

end Krepi.Proofs.PageTables.Stp
