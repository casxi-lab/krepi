module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about the parse

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the parse, whose type is exactly that statement: that the tree of the
parse is well-formed, that each of its limits is exact, and that every
prefix of an accepted tree is rejected.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Parse

open Krepi.SpecProperties.Fdt

public theorem parseWellFormed : ParseWellFormed := by
  sorry

public theorem parseLimitsExact : ParseLimitsExact := by
  sorry

public theorem prefixesRejected : PrefixesRejected := by
  sorry

end Krepi.Proofs.Fdt.Parse
