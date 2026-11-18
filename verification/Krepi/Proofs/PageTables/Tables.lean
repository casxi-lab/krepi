module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about the well-formedness of table sets

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the well-formedness of table sets,
whose type is exactly that statement: that `Tables::new` on zero storage and
the kernel tables that `kernel_map` and `direct_map` write into such sets
are well-formed, and that each write entry of a set keeps a set well-formed.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Tables

open Krepi.SpecProperties.PageTables

public theorem newWellFormed : NewWellFormed := by
  sorry

public theorem bootKernelMapWellFormed : BootKernelMapWellFormed := by
  sorry

public theorem bootDirectMapWellFormed : BootDirectMapWellFormed := by
  sorry

public theorem resetWellFormed : ResetWellFormed := by
  sorry

public theorem cloneKernelFromWellFormed : CloneKernelFromWellFormed := by
  sorry

public theorem mapPageWellFormed : MapPageWellFormed := by
  sorry

public theorem mapBlockWellFormed : MapBlockWellFormed := by
  sorry

public theorem unmapPageWellFormed : UnmapPageWellFormed := by
  sorry

public theorem kernelMapWellFormed : KernelMapWellFormed := by
  sorry

public theorem directMapWellFormed : DirectMapWellFormed := by
  sorry

end Krepi.Proofs.PageTables.Tables
