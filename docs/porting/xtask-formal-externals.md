---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/run.rs
destination:
  - xtask/src/formal/externals.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/externals.rs

## Summary

The installation of the generated files of a proof target in its stage,
from the proof gate of the CAS project: `install_externals` of `run.rs`
(lines 244 to 308), which copies the files that Aeneas generated and puts
the reviewed declarations of the target's `models` directory, or the
generated ones when it has none, in place of each template, refusing a
reviewed file that declares an axiom that the template does not declare or
uses `sorry`, and returning the declarations that remain axioms. It is
taken because the installation decides which declarations a target's
theorems may assume, and every reviewed file must keep to what the tools
generated ([proof targets](../formal-verification.md#proof-targets)). It is
released under the MIT License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

The rest of `xtask/src/formal/externals.rs` is new code: `provided`, the
check that each declaration that a reviewed file turns into a definition
is of an item that a model of the model registry lists for the target,
and `stage`, which creates the stage of a target from the Lake project of
the export and installs its files with the model registry of the export.

## Changes

- A reviewed file may define a generated declaration only when a model of
  `models.json` lists the Rust item of the declaration among its `items`
  and the target among the keys of its `used_by`. The item is found by the
  Lean name of the declaration in the functions and the types of the
  translation. The CAS project accepted any definition of a generated
  declaration, which only review then checked against its model.
- The function takes the model registry and the project directory of the
  stage, and returns a nested result, the outer error for a file that
  cannot be read or written and the inner one for a reviewed file that is
  missing or does not fit the extraction, as the qualification of krepi
  returns its installation; the CAS project returned an error enum with
  the two kinds. A missing reviewed file is named by its path relative to
  the root, not by its absolute path.
- The files of the extraction are those of the translation's module in
  the output of Aeneas, keyed by their path below that output, as the
  extraction of krepi records them.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `run.rs` `tests::models_that_do_not_fit_are_told_from_files_that_cannot_be_written`, line 4259 | `tests::the_generated_declarations_are_installed_without_reviewed_ones`, `tests::a_reviewed_declaration_that_adds_an_axiom_rejects_the_target`, `tests::a_reviewed_declaration_that_uses_sorry_rejects_the_target`, `tests::a_definition_that_no_registered_model_provides_rejects_the_target` and `tests::a_stage_that_cannot_be_written_is_a_tool_failure` | The templates are those that the pinned Aeneas writes, whose declarations lie outside the generated namespace; a reviewed file that defines a declaration fits only with a registered model, and a missing one does not fit |

## Behaviour changes

- A reviewed definition that no registered model provides rejects the
  target. Test:
  `tests::a_definition_that_no_registered_model_provides_rejects_the_target`.

## Hardware evidence to re-obtain

None: the installation copies and reads text on the host.

## Not carried over

- The error enum of the preparation of a target and its conversion from the
  errors of the extraction, which the gate of krepi classes through its
  commands.
