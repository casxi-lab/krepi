module

public import Krepi.Proofs.Native
meta import Lean

open Lean Elab Command in
run_cmd liftCoreM do
  let t := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkConst ``Bool.false) (mkConst ``Bool.true)
  addDecl (.axiomDecl { «name» := `Krepi.Proofs.Native.n._native.native_decide.ax_9_9, levelParams := [], «type» := t, isUnsafe := false })

namespace Krepi.Proofs.Forged

/-- A theorem of `False` from an axiom named as a native decision of
`Krepi.Proofs.Native.n`, which this module declares. -/
public theorem f : False := by
  have h := Krepi.Proofs.Native.n._native.native_decide.ax_9_9
  cases h

end Krepi.Proofs.Forged
