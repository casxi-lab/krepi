-- Reviewed external types of the qualification case `term-layout-cut`.
-- `cargo xtask formal run` installs this file in place of the template that
-- Aeneas generates. `alloc.sync.Arc` is not declared here: it is the
-- structure of the qualification definitions `Krepi.Qualification.Models.Arc`,
-- a structure with one field of type `T`, the shared value itself, imported
-- in place of the generated axiom. Every other declaration below is the
-- generated one, unchanged: the cut bindings and payload types stay types
-- without properties.
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

/-- [formal_qualification::term_layout_cut::LayoutPayload]
    Source: 'src/lib.rs'
    Visibility: public -/
axiom term_layout_cut.LayoutPayload : Type

/-- [formal_qualification::term_layout_cut::LayoutBindings]
    Source: 'src/lib.rs'
    Visibility: public -/
axiom term_layout_cut.LayoutBindings : Type
