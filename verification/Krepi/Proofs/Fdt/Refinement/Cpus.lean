module

public import Krepi.Statements.Fdt.Cpus
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.CpusLemmas

/-!
# Device tree: refinement of the CPU nodes

One theorem for each statement of `Krepi.Statements.Fdt.Cpus`,
whose type is exactly that statement.

All eight are proved, and `verification/statements.json` registers them as
`proved`. Each restates the triple of its function of
`Krepi.Proofs.Fdt.Refinement.CpusLemmas`: `discover_cpus_spec`,
`cpu_topology_count_spec`, `cpu_topology_profile_spec`,
`cpu_topology_affinity_spec`, `validate_timers_spec`,
`cpu_profile_logical_id_spec`, `cpu_profile_affinity_shift_spec` and
`cpu_profile_conduit_spec`. Only `fdtDiscoverCpus` uses the `Usize64`
premise, for the size of the structure block; only
`cpuTopologyValidateTimers` uses `CpuTopology.Supported`, for the count of
1 to 4 CPUs whose flags the code and the specification compute alike.
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Cpus

open Krepi.Statements.Fdt

/-- Proves `FdtDiscoverCpus`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverCpus : FdtDiscoverCpus :=
  fun hu t T profile h => discover_cpus_spec hu t T profile h

/-- Proves `CpuTopologyCount`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyCount : CpuTopologyCount := fun _ => cpu_topology_count_spec

/-- Proves `CpuTopologyProfile`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyProfile : CpuTopologyProfile := fun _ => cpu_topology_profile_spec

/-- Proves `CpuTopologyAffinity`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyAffinity : CpuTopologyAffinity :=
  fun _ t index _ => cpu_topology_affinity_spec t index

/-- Proves `CpuTopologyValidateTimers`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyValidateTimers : CpuTopologyValidateTimers :=
  fun _ t interrupts hs => validate_timers_spec t interrupts hs

/-- Proves `CpuProfileLogicalId`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuProfileLogicalId : CpuProfileLogicalId := fun _ => cpu_profile_logical_id_spec

/-- Proves `CpuProfileAffinityShift`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuProfileAffinityShift : CpuProfileAffinityShift :=
  fun _ => cpu_profile_affinity_shift_spec

/-- Proves `CpuProfileConduit`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuProfileConduit : CpuProfileConduit := fun _ => cpu_profile_conduit_spec

end Krepi.Proofs.Fdt.Refinement.Cpus
