module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about spans, cells and address translation

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about spans, cells and address translation, whose type is exactly that
statement: the well-formedness of the spans, regions and address maps that
the entries of address translation give, and that a translation goes through
the one window that holds the request.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Translate

open Krepi.SpecProperties.Fdt

public theorem spanNewWellFormed : SpanNewWellFormed := by
  sorry

public theorem regNewWellFormed : RegNewWellFormed := by
  sorry

public theorem addressMapNewWellFormed : AddressMapNewWellFormed := by
  sorry

public theorem nodeRegWellFormed : NodeRegWellFormed := by
  sorry

public theorem nodeRangesWellFormed : NodeRangesWellFormed := by
  sorry

public theorem nodeDmaRangesWellFormed : NodeDmaRangesWellFormed := by
  sorry

public theorem toParentWellFormed : ToParentWellFormed := by
  sorry

public theorem toChildWellFormed : ToChildWellFormed := by
  sorry

public theorem translateRegWellFormed : TranslateRegWellFormed := by
  sorry

public theorem translationThroughOneWindow : TranslationThroughOneWindow := by
  sorry

end Krepi.Proofs.Fdt.Translate
