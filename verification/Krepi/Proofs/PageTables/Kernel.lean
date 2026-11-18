module

public import Krepi.SpecProperties.PageTables.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about the kernel tables

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the kernel tables, whose type is
exactly that statement: that no frame is mapped writable and executable,
that the direct map is unchanged after boot, and that the kernel tables are
written only with empty entries.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Kernel

open Krepi.SpecProperties.PageTables

public theorem noWritableExecutable : NoWritableExecutable := by
  sorry

public theorem directMapUnchangedAfterBoot : DirectMapUnchangedAfterBoot := by
  sorry

public theorem kernelTablesOnlyFilled : KernelTablesOnlyFilled := by
  sorry

end Krepi.Proofs.PageTables.Kernel
