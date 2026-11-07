import Krepi
set_option pp.privateNames true

example : Krepi.Statements.Counter.S := Krepi.Proofs.Counter.t
example : Krepi.Proofs.Other.P := Krepi.Proofs.Other.v
example : Krepi.Statements.Counter.Missing := Krepi.Proofs.Counter.s
example : Krepi.Statements.Counter.W := Krepi.Proofs.Coerced.c

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf : Name → Name := fun n =>
    ((env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)).getD .anonymous
  let planned : Array Name := #[`Krepi.Proofs.Other.u]
  let own : Array Name := #[`Krepi.HB.Fixture, `Krepi.Proofs.Coerced, `Krepi.Proofs.Counter, `Krepi.Proofs.Other, `Krepi.Qualification.Arithmetic, `Krepi.Qualification.Checked, `Krepi.Qualification.Models.Arc, `Krepi.Qualification.Models.FromStr, `Krepi.Qualification.SingleLoop, `Krepi.Spec.Counter, `Krepi.Statements.Counter]
  for (module, data) in env.header.moduleNames.zip env.header.moduleData do
    unless own.contains module do continue
    logInfo m!"krepi-audit module {module}"
    for decl in data.constNames do
      let some (.thmInfo _) := env.find? decl | continue
      unless isPrivateName decl || decl.isInternalDetail || planned.contains decl do
        elabCommand (← `(#print axioms $(mkIdent decl)))
        for ax in ← collectAxioms decl do
          if ax.components.contains `_native then
            logInfo m!"krepi-audit native {ax} {moduleOf ax}"
      if let some ranges ← findDeclarationRanges? decl then
        logInfo m!"krepi-audit range {decl} {ranges.range.pos.line}"
  for (statement, thm) in (#[(`Krepi.Statements.Counter.S, `Krepi.Proofs.Counter.t), (`Krepi.Proofs.Other.P, `Krepi.Proofs.Other.v), (`Krepi.Statements.Counter.Missing, `Krepi.Proofs.Counter.s), (`Krepi.Statements.Counter.W, `Krepi.Proofs.Coerced.c)] : Array (Name × Name)) do
    let exact := (env.find? thm).any fun c => c.isTheorem && c.type == mkConst statement
    logInfo m!"krepi-audit statement {statement} {moduleOf statement} {exact}"
