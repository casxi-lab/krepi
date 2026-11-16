module

public import Krepi.Spec.Fdt.Witnesses
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs of the planned witnesses

One theorem for each witness of `Krepi.Spec.Fdt.Witnesses` that the module
does not prove itself, whose type is exactly that proposition: the success
of `Fdt::discover_cpus` and the `AmbiguousMapping` of the lookup of
`/reserved-memory` in the two memory discoveries, whose inputs the kernel
cannot evaluate in a module, and, for each error branch that no input of its
entry reaches, that the entry never takes it.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Witnesses

open Krepi.Spec.Fdt.Witnesses

/-! ## Witnesses -/

public theorem discoverMemoryAmbiguousMapping : DiscoverMemoryAmbiguousMapping := by
  sorry

public theorem discoverPi5BootMemoryAmbiguousMapping :
    DiscoverPi5BootMemoryAmbiguousMapping := by
  sorry

public theorem discoverCpusOk : DiscoverCpusOk := by
  sorry

/-! ## Unreachable error branches -/

public theorem headerNoOverflow : HeaderNoOverflow := by
  sorry

public theorem reservationEntriesFit : ReservationEntriesFit := by
  sorry

public theorem tokensNoOverflow : TokensNoOverflow := by
  sorry

public theorem reservationFuelSuffices : ReservationFuelSuffices := by
  sorry

public theorem discoverMemoryNoBadTree : DiscoverMemoryNoBadTree := by
  sorry

public theorem discoverPi5BootMemoryNoBadTree : DiscoverPi5BootMemoryNoBadTree := by
  sorry

public theorem ramBytesFit : RamBytesFit := by
  sorry

public theorem climbRangesNoBadTree : ClimbRangesNoBadTree := by
  sorry

public theorem translateRegFuelSuffices : TranslateRegFuelSuffices := by
  sorry

public theorem windowTranslationNoOverflow : WindowTranslationNoOverflow := by
  sorry

public theorem findAvailableNoLimitExceeded : FindAvailableNoLimitExceeded := by
  sorry

public theorem bankBytesFit : BankBytesFit := by
  sorry

end Krepi.Proofs.Fdt.Witnesses
