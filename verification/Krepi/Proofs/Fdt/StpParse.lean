module

public import Krepi.SpecTests.Fdt.Stp
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.StpLemmas
import Krepi.Proofs.Fdt.Parse

/-!
# Device tree: the specification tests of the parse

The specification tests of FDT-R01 and FDT-R02, which `Krepi.Proofs.Fdt.Stp`
restates. The trees of FDT-R01 write over the padding of a property value, so
their parse is a kernel decision on their bytes; the tree with a changed byte
is the finished tree of another builder (a kernel decision on the bytes),
whose parse is its walk (`parse_fast0`); a prefix of `minimal` is rejected by
`PrefixesRejected`.
-/

public section

namespace Krepi.Proofs.Fdt.StpParse

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt Krepi.SpecTests.Fdt

attribute [local instance] decEqExcept

/-- FDT-R01, accepted. -/
theorem parseAcceptsNameAtLimit : ParseAcceptsNameAtLimit := by
  unfold ParseAcceptsNameAtLimit; decide +kernel

/-- FDT-R01, rejected. -/
theorem parseRejectsNameAboveLimit : ParseRejectsNameAboveLimit := by
  unfold ParseRejectsNameAboveLimit; decide +kernel

/-- FDT-R02, accepted: the changed byte gives the reg of another builder. -/
theorem entriesReturnOnChangedByte : EntriesReturnOnChangedByte := by
  unfold EntriesReturnOnChangedByte
  rw [show flipByte minimal 165 = (Builder.empty.root |>.beginNode "memory@100000000"
    |>.string "device_type" "memory" |>.cells "reg" [1, 0, 0, 0xdf_0000] |>.endNode
    |>.endNode).finish by decide +kernel, parse_fast0]
  decide +kernel

/-- FDT-R02, rejected: `minimal` is accepted with a `totalsize` of its length. -/
theorem parseRejectsPrefix : ParseRejectsPrefix := by
  unfold ParseRejectsPrefix
  have h : okAnd (Fdt.parse minimal) (fun t => decide (minimal.size - 1 < t.totalSize.toNat)) =
      true := by
    unfold minimal; rw [parse_fast0]; decide +kernel
  obtain ⟨t, ht, hlt⟩ := okAnd_spec h
  exact Parse.prefixesRejected minimal t ht _ (of_decide_eq_true hlt)

end Krepi.Proofs.Fdt.StpParse
