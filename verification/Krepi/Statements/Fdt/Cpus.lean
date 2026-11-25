module

public import Krepi.Statements.Fdt.Representation
public import Krepi.SpecProperties.Fdt.Invariants

/-!
# Device tree: refinement of the CPU nodes

One statement for each function of line 114 of the entry table of the
contract (`docs/domains/boot-platform/fdt/contract.md`): for every input of
its machine widths, under the premises that its arguments need, the
function returns, and its result agrees with that of its function of
`Krepi.Spec.Fdt` through the representation of
`Krepi.Statements.Fdt.Representation`, the same error with the same
priority included. None of these functions writes anything. A CPU topology
and a CPU profile carry no field that the code hides from the
specification, so each stands for its value of the specification; the
queries of a topology that read its count take `CpuTopology.Supported`,
which the discovery establishes, a premise of the proof path. The theorems
below `Krepi.Proofs.Fdt.Refinement` prove them.
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice Str U8 U32 U64)
open KrepiGen.Fdt
open Krepi.Spec.Fdt

namespace Krepi.Statements.Fdt

/-- `Fdt::discover_cpus(profile)`: the topology of `Fdt.discoverCpus` of the
profile, or its error.
Feature: `krepi.platform.device-tree`. -/
def FdtDiscoverCpus : Prop :=
  ∀ (t : fdt.Fdt) (T : Fdt) (profile : fdt.CpuProfile), FdtRepr t T →
    fdt.cpus.Fdt.discover_cpus t profile ⦃ r =>
      Agrees (fun c C => topologyOf c = C) errorOf r (T.discoverCpus (profileOf profile)) ⦄

/-- `CpuTopology::count()`: the number of CPUs of the topology.
Feature: `krepi.platform.device-tree`. -/
def CpuTopologyCount : Prop :=
  ∀ t : fdt.CpuTopology, fdt.cpus.CpuTopology.count t ⦃ n => word64 n = (topologyOf t).count ⦄

/-- `CpuTopology::profile()`: the profile of the topology.
Feature: `krepi.platform.device-tree`. -/
def CpuTopologyProfile : Prop :=
  ∀ t : fdt.CpuTopology,
    fdt.cpus.CpuTopology.profile t ⦃ p => profileOf p = (topologyOf t).profile ⦄

/-- `CpuTopology::affinity(index)`: the affinity of `CpuTopology.affinity` of
the index, none from the count on, for a supported topology.
Feature: `krepi.platform.device-tree`. -/
def CpuTopologyAffinity : Prop :=
  ∀ (t : fdt.CpuTopology) (index : U64), (topologyOf t).Supported →
    fdt.cpus.CpuTopology.affinity t index ⦃ o =>
      o.map word64 = (topologyOf t).affinity (word64 index) ⦄

/-- `CpuTopology::validate_timers(interrupts)`: success exactly when
`CpuTopology.validateTimers` of the bytes succeeds, and its error otherwise,
for a supported topology.
Feature: `krepi.platform.device-tree`. -/
def CpuTopologyValidateTimers : Prop :=
  ∀ (t : fdt.CpuTopology) (interrupts : Slice U8), (topologyOf t).Supported →
    fdt.cpus.CpuTopology.validate_timers t interrupts ⦃ r =>
      Agrees (fun _ _ => True) errorOf r ((topologyOf t).validateTimers (bytesOf interrupts)) ⦄

/-- `CpuProfile::logical_id(mpidr)`: the logical ID of `CpuProfile.logicalId`
of the value of `MPIDR_EL1`, or none.
Feature: `krepi.platform.device-tree`. -/
def CpuProfileLogicalId : Prop :=
  ∀ (p : fdt.CpuProfile) (mpidr : U64),
    fdt.cpus.CpuProfile.logical_id p mpidr ⦃ o =>
      o.map word64 = (profileOf p).logicalId (word64 mpidr) ⦄

/-- `CpuProfile::affinity_shift()`: the shift of the affinity level of the
profile.
Feature: `krepi.platform.device-tree`. -/
def CpuProfileAffinityShift : Prop :=
  ∀ p : fdt.CpuProfile,
    fdt.cpus.CpuProfile.affinity_shift p ⦃ n => word64 n = (profileOf p).affinityShift ⦄

/-- `CpuProfile::conduit()`: the PSCI conduit of the profile.
Feature: `krepi.platform.device-tree`. -/
def CpuProfileConduit : Prop :=
  ∀ p : fdt.CpuProfile,
    fdt.cpus.CpuProfile.conduit p ⦃ c => conduitOf c = (profileOf p).conduit ⦄

end Krepi.Statements.Fdt
