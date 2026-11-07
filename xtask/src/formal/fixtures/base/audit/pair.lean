import Krepi.HB.Pair
set_option pp.privateNames true


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf : Name → Name := fun n =>
    ((env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)).getD .anonymous
  let planned : Array Name := #[]
  let own : Array Name := #[`Krepi.HB.Pair]
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
  for (statement, thm) in (#[] : Array (Name × Name)) do
    let exact := (env.find? thm).any fun c => c.isTheorem && c.type == mkConst statement
    logInfo m!"krepi-audit statement {statement} {moduleOf statement} {exact}"
