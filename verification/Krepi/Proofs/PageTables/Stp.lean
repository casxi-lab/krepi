module

public import Krepi.SpecTests.PageTables.Stp
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.StpLemmas

/-!
# Page tables: proofs of the specification tests

One theorem for each specification test of `Krepi.SpecTests.PageTables`,
whose type is exactly that test: for each requirement of the component,
PGT-R01 to PGT-R12, the input that the specification accepts with its result
and the input that it rejects with its error.

The tests of PGT-R01, PGT-R02, PGT-R04, PGT-R06, PGT-R07 and PGT-R12, and the
rejecting test of PGT-R05 (`directMapOmitsExcludedPages`), are proved, and
`verification/statements.json` registers each as `proved`: each is decided by
the kernel on its concrete inputs once its proposition is unfolded, with the
equality of `Except` values of `Krepi.Proofs.Fdt.decEqExcept` as a local
instance. The two tests whose results are tuples of six and ten values,
`unmapAndResetFollowContract` and `copyIsPrivateAndOrdered`, raise
`synthInstance.maxSize` so that the instance of their equality is found. The
other theorems are planned: their proof is `sorry` until a
proof pull request proves them, and `verification/statements.json` registers
each as `planned`. They are the tests of PGT-R03, PGT-R08 to PGT-R11, and the
accepting test of PGT-R05, `directMapCountsOfPi5Models`. Mathlib is imported
so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Stp

open Krepi.SpecTests.PageTables

attribute [local instance] Krepi.Proofs.Fdt.decEqExcept

/-! ## PGT-R01 -/

public theorem descriptorsFollowKindRows : DescriptorsFollowKindRows := by
  unfold DescriptorsFollowKindRows; decide +kernel

public theorem descriptorKeepsOnlyItsBits : DescriptorKeepsOnlyItsBits := by
  unfold DescriptorKeepsOnlyItsBits; decide +kernel

/-! ## PGT-R02 -/

public theorem mapPageThenLookup : MapPageThenLookup := by
  unfold MapPageThenLookup; decide +kernel

public theorem mapPageRefusesMappedPage : MapPageRefusesMappedPage := by
  unfold MapPageRefusesMappedPage; decide +kernel

/-! ## PGT-R03 -/

public theorem eightGibOfBlocksInNineTables : EightGibOfBlocksInNineTables := by
  sorry

public theorem blockBeyondNineTablesRefused : BlockBeyondNineTablesRefused := by
  sorry

/-! ## PGT-R04 -/

set_option synthInstance.maxSize 4096 in
public theorem unmapAndResetFollowContract : UnmapAndResetFollowContract := by
  unfold UnmapAndResetFollowContract; decide +kernel

public theorem unmapRefusesUnmappedPage : UnmapRefusesUnmappedPage := by
  unfold UnmapRefusesUnmappedPage; decide +kernel

/-! ## PGT-R05 -/

public theorem directMapCountsOfPi5Models : DirectMapCountsOfPi5Models := by
  sorry

public theorem directMapOmitsExcludedPages : DirectMapOmitsExcludedPages := by
  unfold DirectMapOmitsExcludedPages; decide +kernel

/-! ## PGT-R06 -/

public theorem kernelMapGivesKindsAndGuard : KernelMapGivesKindsAndGuard := by
  unfold KernelMapGivesKindsAndGuard; decide +kernel

public theorem kernelMapRefusesSharedPage : KernelMapRefusesSharedPage := by
  unfold KernelMapRefusesSharedPage; decide +kernel

/-! ## PGT-R07 -/

public theorem plansFollowContractOrder : PlansFollowContractOrder := by
  unfold PlansFollowContractOrder; decide +kernel

public theorem kernelFillRefusesValidEntry : KernelFillRefusesValidEntry := by
  unfold KernelFillRefusesValidEntry; decide +kernel

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

set_option synthInstance.maxSize 4096 in
public theorem copyIsPrivateAndOrdered : CopyIsPrivateAndOrdered := by
  unfold CopyIsPrivateAndOrdered; decide +kernel

public theorem copyRefusesPrivateLeaf : CopyRefusesPrivateLeaf := by
  unfold CopyRefusesPrivateLeaf; decide +kernel

end Krepi.Proofs.PageTables.Stp
