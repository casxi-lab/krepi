-- Reviewed external types of the qualification case `match-machine-arc`.
-- `cargo xtask formal run` installs this file in place of the template that
-- Aeneas generates. `alloc.sync.Arc` is not declared here: it is the
-- structure of the qualification definitions `Krepi.Qualification.Models.Arc`,
-- a structure with one field of type `T`, the shared value itself, imported
-- in place of the generated axiom, so that the recursive term kind whose
-- children are `Arc` pointers is accepted by the kernel. Pointer identity
-- and the reference count are not part of the value.
module
public import Aeneas
public import Krepi.Qualification.Models.Arc
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
