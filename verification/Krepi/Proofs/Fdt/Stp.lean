module

public import Krepi.SpecTests.Fdt.Stp
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs of the specification tests

One theorem for each specification test of `Krepi.SpecTests.Fdt`, whose
type is exactly that test: for each requirement of the component, FDT-R01 to
FDT-R10, the input that the specification accepts with its result and the
input that it rejects with its error.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Stp

open Krepi.SpecTests.Fdt

/-! ## FDT-R01 -/

public theorem parseAcceptsNameAtLimit : ParseAcceptsNameAtLimit := by
  sorry

public theorem parseRejectsNameAboveLimit : ParseRejectsNameAboveLimit := by
  sorry

/-! ## FDT-R02 -/

public theorem entriesReturnOnChangedByte : EntriesReturnOnChangedByte := by
  sorry

public theorem parseRejectsPrefix : ParseRejectsPrefix := by
  sorry

/-! ## FDT-R03 -/

public theorem discoveryAcceptsMaxRamRanges : DiscoveryAcceptsMaxRamRanges := by
  sorry

public theorem discoveryRejectsExcessRamRanges : DiscoveryRejectsExcessRamRanges := by
  sorry

/-! ## FDT-R04 -/

public theorem discoveryRecordsDynamicReservations : DiscoveryRecordsDynamicReservations := by
  sorry

public theorem discoveryRejectsEmptyStaticReservation : DiscoveryRejectsEmptyStaticReservation := by
  sorry

/-! ## FDT-R05 -/

public theorem pi5AcceptsTreeAtLimit : Pi5AcceptsTreeAtLimit := by
  sorry

public theorem pi5RejectsTreeAboveLimit : Pi5RejectsTreeAboveLimit := by
  sorry

/-! ## FDT-R06 -/

public theorem pi5ModelsBuildBootMemoryMaps : Pi5ModelsBuildBootMemoryMaps := by
  sorry

public theorem bootMemoryMapRejectsRamAboveCapacity : BootMemoryMapRejectsRamAboveCapacity := by
  sorry

/-! ## FDT-R07 -/

public theorem allRamAcceptsMaxBootStorage : AllRamAcceptsMaxBootStorage := by
  sorry

public theorem allRamRejectsExcessBootStorage : AllRamRejectsExcessBootStorage := by
  sorry

/-! ## FDT-R08 -/

public theorem cpusAcceptsQemuPair : CpusAcceptsQemuPair := by
  sorry

public theorem cpusRejectsRepeatedId : CpusRejectsRepeatedId := by
  sorry

/-! ## FDT-R09 -/

public theorem translateRegThroughBus : TranslateRegThroughBus := by
  sorry

public theorem translationRejectsTwoWindows : TranslationRejectsTwoWindows := by
  sorry

/-! ## FDT-R10 -/

public theorem seedsDoNotReachResults : SeedsDoNotReachResults := by
  sorry

public theorem chosenDeviceTypeIsRead : ChosenDeviceTypeIsRead := by
  sorry

end Krepi.Proofs.Fdt.Stp
