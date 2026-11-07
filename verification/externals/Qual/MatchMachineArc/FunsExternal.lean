-- Reviewed external functions of the qualification case `match-machine-arc`.
-- `cargo xtask formal run` installs this file in place of the template that
-- Aeneas generates. `clone` and `deref` are the qualification definitions
-- `Krepi.Qualification.Models.Arc.clone` and `.deref`, over the structure
-- that `TypesExternal.lean` imports: `clone` returns the same value and
-- `deref` returns the field; both never fail, so the abort of `clone` on a
-- reference-count overflow is outside the definitions. The signatures are
-- the generated ones, with the type parameters in `Type`.
module
public import Aeneas
public import KrepiGen.Qual.MatchMachineArc.Types
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
open KrepiGen.Qual.MatchMachineArc

/-- [alloc::sync::{impl core::clone::Clone for alloc::sync::Arc<T>}::clone]:
    the definition `Krepi.Qualification.Models.Arc.clone`, the same value.
    Name pattern: [alloc::sync::{core::clone::Clone<alloc::sync::Arc<@T>>}::clone] -/
@[rust_fun "alloc::sync::{core::clone::Clone<alloc::sync::Arc<@T>>}::clone"]
def alloc.sync.Arc.Insts.CoreCloneClone.clone
  {T : Type} {A : Type} (coreallocAllocatorCloneInst :
  core.alloc.AllocatorClone A) :
  alloc.sync.Arc T → Result (alloc.sync.Arc T) :=
  fun a => ok (Krepi.Qualification.Models.Arc.clone a)

/-- [alloc::sync::{impl core::ops::deref::Deref<T> for alloc::sync::Arc<T>}::deref]:
    the definition `Krepi.Qualification.Models.Arc.deref`, the field.
    Name pattern: [alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref] -/
@[rust_fun
  "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref"]
def alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  {T : Type} (A : Type) : alloc.sync.Arc T → Result T :=
  fun a => ok (Krepi.Qualification.Models.Arc.deref a)
