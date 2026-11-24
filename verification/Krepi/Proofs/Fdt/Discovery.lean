module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.DiscoveryLemmas
import Krepi.Proofs.Fdt.UnreadLemmas

/-!
# Device tree: proofs about memory discovery and the boot memory

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about memory discovery and the boot memory, whose type is exactly that
statement: that the memory map of a well-formed tree is well-formed, that a
boot memory is consistent, and that the values that the discoveries
leave unread do not reach their results.

`DiscoverMemoryWellFormed` is proved; the other three theorems are planned:
each proof is `sorry` until a proof pull request proves it. The proofs come
from the lemmas of
`Krepi.Proofs.Fdt.DiscoveryLemmas` (the steps of a successful discovery)
and `Krepi.Proofs.Fdt.UnreadLemmas` (the nodes of a tree that differs only
in unread values give the same results). Mathlib is imported so that the
gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Discovery

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

public theorem discoverMemoryWellFormed : DiscoverMemoryWellFormed := by
  intro t m ht h
  obtain ⟨-, -, -, hram, hne, hrsv, d, hd, hdyn⟩ := discoverMemory_ok h
  have hrsv := hrsv ht.2.2.2.1
  refine ⟨hne, hram.1, hram.2.1, hram.2.2, hrsv.1, hrsv.2, ?_⟩
  have htok := ht.2.2.2.2.2.2.1
  have h65 : MAX_TOKENS.toNat = 65536 := rfl
  have hs : UInt64.size = 18446744073709551616 := rfl
  rw [hdyn, UInt64.toNat_ofNat_of_lt' (by omega)]
  omega

public theorem discoverBootMemoryWellFormed : DiscoverBootMemoryWellFormed := by
  sorry

public theorem discoverBootMemoryConsistent : DiscoverBootMemoryConsistent := by
  sorry

public theorem unreadValuesIgnored : UnreadValuesIgnored := by
  sorry

end Krepi.Proofs.Fdt.Discovery
