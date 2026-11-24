module

public import Krepi.SpecTests.Fdt.Stp
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.StpLemmas
import Krepi.Proofs.Fdt.StpParse
import Krepi.Proofs.Fdt.StpMemory
import Krepi.Proofs.Fdt.StpPi5

/-!
# Device tree: proofs of the specification tests

One theorem for each specification test of `Krepi.SpecTests.Fdt`, whose
type is exactly that test: for each requirement of the component, FDT-R01 to
FDT-R10, the input that the specification accepts with its result and the
input that it rejects with its error.

Every theorem here is proved, and `verification/statements.json` registers
each as `proved`. The tests are decided by the kernel on their concrete
inputs. The tests that parse a tree that `Builder` finishes without
overwrites rewrite the parse into the walk of its structure block first
(`parse_fast` of `Krepi.Proofs.Fdt.StpLemmas`), so that no decision copies a
whole tree; the small trees of FDT-R01 are decided on their bytes. The tests
of FDT-R01 to FDT-R06 and FDT-R10 are proved in `Krepi.Proofs.Fdt.StpParse`,
`Krepi.Proofs.Fdt.StpMemory` and `Krepi.Proofs.Fdt.StpPi5`, which keeps each
module quick to build, and restated here; those of FDT-R07 to FDT-R09 are
proved here. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Stp

open Krepi.SpecTests.Fdt

attribute [local instance] decEqExcept

/-! ## FDT-R01 -/

public theorem parseAcceptsNameAtLimit : ParseAcceptsNameAtLimit :=
  StpParse.parseAcceptsNameAtLimit

public theorem parseRejectsNameAboveLimit : ParseRejectsNameAboveLimit :=
  StpParse.parseRejectsNameAboveLimit

/-! ## FDT-R02 -/

public theorem entriesReturnOnChangedByte : EntriesReturnOnChangedByte :=
  StpParse.entriesReturnOnChangedByte

public theorem parseRejectsPrefix : ParseRejectsPrefix :=
  StpParse.parseRejectsPrefix

/-! ## FDT-R03 -/

public theorem discoveryAcceptsMaxRamRanges : DiscoveryAcceptsMaxRamRanges :=
  StpMemory.discoveryAcceptsMaxRamRanges

public theorem discoveryRejectsExcessRamRanges : DiscoveryRejectsExcessRamRanges :=
  StpMemory.discoveryRejectsExcessRamRanges

/-! ## FDT-R04 -/

public theorem discoveryRecordsDynamicReservations : DiscoveryRecordsDynamicReservations :=
  StpMemory.discoveryRecordsDynamicReservations

public theorem discoveryRejectsEmptyStaticReservation : DiscoveryRejectsEmptyStaticReservation :=
  StpMemory.discoveryRejectsEmptyStaticReservation

/-! ## FDT-R05 -/

public theorem pi5AcceptsTreeAtLimit : Pi5AcceptsTreeAtLimit :=
  StpPi5.pi5AcceptsTreeAtLimit

public theorem pi5RejectsTreeAboveLimit : Pi5RejectsTreeAboveLimit :=
  StpPi5.pi5RejectsTreeAboveLimit

/-! ## FDT-R06 -/

public theorem pi5ModelsBuildBootMemoryMaps : Pi5ModelsBuildBootMemoryMaps :=
  StpPi5.pi5ModelsBuildBootMemoryMaps

public theorem bootMemoryMapRejectsRamAboveCapacity : BootMemoryMapRejectsRamAboveCapacity :=
  StpPi5.bootMemoryMapRejectsRamAboveCapacity

/-! ## FDT-R07 -/

public theorem allRamAcceptsMaxBootStorage : AllRamAcceptsMaxBootStorage := by
  unfold AllRamAcceptsMaxBootStorage; decide +kernel

public theorem allRamRejectsExcessBootStorage : AllRamRejectsExcessBootStorage := by
  unfold AllRamRejectsExcessBootStorage; decide +kernel

/-! ## FDT-R08 -/

public theorem cpusAcceptsQemuPair : CpusAcceptsQemuPair := by
  unfold CpusAcceptsQemuPair cpusTree; rw [parse_fast0]; decide +kernel

public theorem cpusRejectsRepeatedId : CpusRejectsRepeatedId := by
  unfold CpusRejectsRepeatedId cpusTree; rw [parse_fast0]; decide +kernel

/-! ## FDT-R09 -/

public theorem translateRegThroughBus : TranslateRegThroughBus := by
  unfold TranslateRegThroughBus onNode busTree; rw [parse_fast0]; decide +kernel

public theorem translationRejectsTwoWindows : TranslationRejectsTwoWindows := by
  unfold TranslationRejectsTwoWindows; decide +kernel

/-! ## FDT-R10 -/

public theorem seedsDoNotReachResults : SeedsDoNotReachResults :=
  StpMemory.seedsDoNotReachResults

public theorem chosenDeviceTypeIsRead : ChosenDeviceTypeIsRead :=
  StpMemory.chosenDeviceTypeIsRead

end Krepi.Proofs.Fdt.Stp
