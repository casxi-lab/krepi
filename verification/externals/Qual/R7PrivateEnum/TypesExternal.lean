-- Reviewed external types of the qualification case `r7-private-enum`.
-- `cargo xtask formal run` installs this file in place of the template that
-- Aeneas generates. It records item R7 of the provable Rust subset: the
-- external type `Phase`, which the case extracts without its definition, is
-- defined here as an enumeration that is private in Lean, with the
-- `discriminant` attribute that generated code puts on every enumeration.
-- The declaration lies outside a `public section` and is marked `private`.
-- The expectation of the case records whether this file type-checks.
module
public import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [formal_qualification::r7_private_enum::Phase], as a private enumeration
    with the generated form of an enumeration. -/
@[discriminant isize]
private inductive r7_private_enum.Phase where
| Idle : r7_private_enum.Phase
| Running : r7_private_enum.Phase
