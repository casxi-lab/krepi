module

public import Krepi.SpecProperties.PageTables.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: proofs about the abstract mapping and the plans

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the abstract mapping and the plans,
whose type is exactly that statement: that every write changes the abstract
mapping as the contract says, that the tables in use are counted by $G$ and
$P$, and that the plans publish in order.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Mapping

open Krepi.SpecProperties.PageTables

public theorem afterEveryWrite : AfterEveryWrite := by
  sorry

public theorem tablesInUseCounted : TablesInUseCounted := by
  sorry

public theorem plansPublishInOrder : PlansPublishInOrder := by
  sorry

end Krepi.Proofs.PageTables.Mapping
