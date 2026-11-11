---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/run.rs
destination:
  - xtask/src/formal/mutants.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/mutants.rs

## Summary

The judgement of a mutant of a target, from the proof gate of the CAS
project: `prepare_edited` of `run.rs` (lines 819 to 865), which copies the
package, edits it as the mutant says when its pattern occurs once and
extracts it, an extraction that fails being inconclusive; `Verdict` (lines
903 to 920) and `verdict` (lines 927 to 961, with `position`, lines 988 to
990), which judge the build of a mutant by where its errors fall in the
declaration ranges of the target's build; `unknown_failures` (lines 966 to
985), the problem of a mutant that names a theorem outside the proof
modules; and `build_failure` (lines 997 to 1025) with `messages` (lines
1029 to 1036), which tell a failed build of the proofs from one of
generated or model code. They are taken because a mutant is rejected only
when its build fails in a named theorem and nothing else explains the
failure ([mutants](../formal-verification.md#mutants)). They are released
under the MIT License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

The rest of the file is new code: the units of the mutants and the budget
that they share with their target, the seconds of the receipt, the build of
the proofs of a stage, the run of the registered mutants after their
target, the generation of the source mutants with its operators, the run of
`cargo xtask formal mutants`, the list of survivors and its checks.

## Changes

- `prepare_edited` becomes the first part of `build`: the pattern is
  counted in the file of the export before anything is copied; the package
  is copied from the export with the Cargo configuration of the export into
  the work directory of the mutant; for a source mutant, `cargo check`
  builds the edited copy first, and a mutant that it does not build is
  counted and not run. The same function installs the generated files in a
  new stage, builds the proofs there and judges the build. A stage is not
  seeded from the build of the target: each mutant builds its stage anew.
- `verdict` reads a command of the gate: Lake or Lean killed as
  `outcome::killed` finds it, and the status of its exit.
- `unknown_failures` takes the theorems of the mutant, and its problem does
  not name the target and the mutant, which its unit names.
- `build_failure` returns the problem of a proof failure or the reason of a
  tool failure, with the same texts, and judges the build of the proofs of
  a target as well; `messages`: none.
- An inconclusive mutant concludes its unit `REJECTED`, with a reason that
  starts with `inconclusive`, since a run has no status of that name; a
  mutant whose build was killed is a tool failure.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `run.rs` `tests::a_mutant_is_rejected_only_by_errors_in_the_proofs`, line 3769 | `tests::a_mutant_is_rejected_only_by_errors_in_the_proofs` | The logs and the range tables of the pinned Lean 4.35.0 in `fixtures/mutants/`, with a private theorem as the named one |
| `tests::a_killed_build_of_a_mutant_tells_nothing_about_it`, line 3894 | `tests::a_killed_build_of_a_mutant_tells_nothing_about_it` | A Lake ended by a signal or its limit, an exit above 128 and a line `Lean exited with code 137` |
| `tests::a_mutant_names_theorems_of_the_proofs`, line 3924 | `tests::a_mutant_names_theorems_of_the_proofs` and `tests::a_mutant_is_rejected_unless_it_is_judged_rejected_by_its_proofs` | The names of the fixture; the pattern that occurs neither once nor twice and the unknown theorem in runs of the gate |
| `tests::a_failed_target_build_is_a_proof_failure_only_with_a_message_in_the_proofs`, line 3959, and `tests::a_killed_build_of_a_target_is_a_tool_failure`, line 4016 | `tests::a_failed_target_build_is_a_proof_failure_only_with_a_message_in_the_proofs` | The captured log of a mutant of the calibration, with the file of its message moved to a generated module, and a Lake ended by a signal |

The other tests of the module are new.

## Behaviour changes

- Every mutant builds in a new stage, without the build of its target, and
  its commands share the budget of the target. Test:
  `tests::a_mutant_whose_extraction_fails_or_that_survives_fails_the_run`.

## Hardware evidence to re-obtain

None: the mutants are built and judged on the host.

## Not carried over

`mutant_extraction`, whose fields the receipt of krepi does not have;
`prepare_again`, `keep_probe` and `record_failed_probe`, which serve the
store of results; the seeding of the stages and the inventories of their
builds; and `run_each_prepared`, which prepares a mutant while the one
before it builds.
