module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about memory discovery and the Pi 5 boot memory

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about memory discovery and the Pi 5 boot memory, whose type is exactly that
statement: that the memory map of a well-formed tree is well-formed, that a
Pi 5 boot memory is consistent, and that the values that the discoveries
leave unread do not reach their results.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Discovery

open Krepi.SpecProperties.Fdt

public theorem discoverMemoryWellFormed : DiscoverMemoryWellFormed := by
  sorry

public theorem discoverPi5BootMemoryWellFormed : DiscoverPi5BootMemoryWellFormed := by
  sorry

public theorem discoverPi5BootMemoryConsistent : DiscoverPi5BootMemoryConsistent := by
  sorry

public theorem unreadValuesIgnored : UnreadValuesIgnored := by
  sorry

end Krepi.Proofs.Fdt.Discovery
