---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/registry.rs
destination:
  - xtask/src/formal/registry.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/registry.rs

## Summary

`declared_axioms` (lines 347 to 390) of the proof gate of the CAS project:
the names that a Lean file declares with `axiom`, qualified by the
enclosing `namespace` declarations, including the long names that Aeneas
writes on the line after a bare `axiom`. It is taken because the
qualification compares the axioms of a reviewed external declaration with
those of the template that Aeneas generated, and the audit of a proof
allows the declarations of its own templates. It is released under the MIT
License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

The rest of `xtask/src/formal/registry.rs` is new code: the targets and
specifications of `verification/targets.json` in its schema 2, with the
state and budget of a target and its cut points as objects; the static rules
of the registry and of `verification/axioms.json`; and the refusal of what
the gate does not support yet. `cargo xtask formal check` reports both:
the rules ([proof targets](../formal-verification.md#proof-targets)), and
premises, `exclude` cut points and the models of
`verification/models.json`. The rules cover those that the CAS project
applied while it read its registry, such as unique names and modules, a
theorem registered once, an obligation and a mutant for every target and
disjoint lists, and add the planned state, the sources and reasons of cut
points and library axioms, and the bound on the mutants of a target; they
report every problem rather than stopping at the first.

## Changes

- A line that declares an axiom may begin with attributes (`@[...]`, with
  brackets inside strings skipped) and the modifiers `public`, `private`,
  `protected`, `noncomputable`, `unsafe` and `partial`, and `axiom` may be
  followed by any white space. The CAS project read only lines that begin
  with `axiom`, so a reviewed external declaration in a `module` file that
  declared `public axiom x` was not seen to declare `x`.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `tests::axioms_are_qualified_by_namespace`, lines 426 to 437 | `tests::axioms_are_qualified_by_namespace` | Unchanged |

The tests `tests::axioms_after_attributes_and_modifiers_are_read` and
`tests::the_axioms_of_a_captured_template_are_read` are new. The second
reads the templates of external functions and types that the pinned Aeneas
wrote for two shapes of the qualification crate, kept in
`xtask/src/formal/fixtures/extraction/`, and a file of generated
definitions, which declares no axiom.

## Behaviour changes

- An axiom declared after attributes or modifiers is read, so a reviewed
  external declaration that adds one is not installed. Tests:
  `tests::axioms_after_attributes_and_modifiers_are_read` here and
  `qualify::tests::reviewed_externals_may_declare_only_generated_axioms`.

## Hardware evidence to re-obtain

None: the function reads text on the host.

## Not carried over

- `TARGETS`, `SPEC_PREFIX`, `Specification`, `Obligation`, `TrustedAxiom`,
  `Mutant`, `Premise`, `Target`, `load`, `parse` and `specifications`
  (lines 16 to 342), with the test
  `tests::specifications_must_exist_below_the_namespace_with_their_theorems`
  (lines 404 to 423): they read the registry of the CAS project, whose
  schema is not krepi's. krepi's registry is read into types of its own
  schema, written anew.
