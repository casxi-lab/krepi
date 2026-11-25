module

public import Krepi.Statements.Fdt.Cpus
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: refinement of the CPU nodes

One theorem for each statement of `Krepi.Statements.Fdt.Cpus`,
whose type is exactly that statement.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Cpus

open Krepi.Statements.Fdt

/-- Proves `FdtDiscoverCpus`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtDiscoverCpus : FdtDiscoverCpus := by
  sorry

/-- Proves `CpuTopologyCount`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyCount : CpuTopologyCount := by
  sorry

/-- Proves `CpuTopologyProfile`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyProfile : CpuTopologyProfile := by
  sorry

/-- Proves `CpuTopologyAffinity`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyAffinity : CpuTopologyAffinity := by
  sorry

/-- Proves `CpuTopologyValidateTimers`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuTopologyValidateTimers : CpuTopologyValidateTimers := by
  sorry

/-- Proves `CpuProfileLogicalId`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuProfileLogicalId : CpuProfileLogicalId := by
  sorry

/-- Proves `CpuProfileAffinityShift`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuProfileAffinityShift : CpuProfileAffinityShift := by
  sorry

/-- Proves `CpuProfileConduit`. Feature: `krepi.platform.device-tree`. -/
public theorem cpuProfileConduit : CpuProfileConduit := by
  sorry

end Krepi.Proofs.Fdt.Refinement.Cpus
