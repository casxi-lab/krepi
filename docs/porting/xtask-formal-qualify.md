---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/qualify.rs
destination:
  - xtask/src/formal/qualify.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/qualify.rs

## Summary

The tool qualification of the proof gate of the CAS project, which extracts
each case of `verification/qualification/cases.json`, compares it with its
expectation, type-checks what translates and audits the proofs about the
cases:

- `load_cases` (lines 96 to 169), the reading of the cases, and `sorted`
  (lines 171 to 178);
- `case_path` (lines 182 to 184), `names_case_file` (lines 189 to 193),
  `case_errors` (lines 200 to 205) and `errors_in` (lines 209 to 212),
  which find the type errors of a case in a build log;
- `installed_external` (lines 384 to 409), the rule for reviewed external
  declarations;
- `Extracted` (lines 412 to 418) and `Extracted::of` (lines 422 to 430),
  which become `receipt::Observed` and `observed`, `compare` (lines 456 to
  458), which `qualify_case` does, and `differences` (lines 461 to 512), the
  comparison of an extraction with its expectation;
- `install` (lines 519 to 548), which installs the generated files of a
  case;
- `audit_source_path` (lines 576 to 582), `audit_source` (lines 585 to
  596), `audit_case_proofs` (lines 598 to 647) and `judge_case_audit`
  (lines 867 to 912), the audit of the proofs of a case.

They are taken because the comparison, the rule for reviewed declarations,
the reading of type errors and the audit rule were worked out against the
behaviour of the pinned tools and are what the expectations of the cases
were recorded with. The code is released under the MIT License as part of
krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

Written in krepi after the CAS project, and not copied:

- `Outcome` (lines 64 to 71) and `Case` (lines 73 to 94) become `Expect`
  and `Case`, the types that `cases.json` is read into with `serde`; the
  receipt records the `Expect` of each case;
- `CaseProof` (lines 553 to 557) is not needed: each case is audited alone;
- the main flow (`qualify`, lines 694 to 850) becomes `phase`, `qualify`,
  `qualify_case` and `prove`, which run each case through the gate of
  `cargo xtask formal run`;
- the judgement of an ill-typed case, `judge_build`, is written after
  `ill_typed_failure` (lines 284 to 307) for one case built alone.

New in krepi are the units of the cases and their theorems, the `parts`
form of a case and the module that imports its parts, the check of the
extraction configuration and of the crate's manifest and build script, the
record of the qualification in the receipt, and the check that no command
of the phase wrote to the Aeneas Lean library, its packages or the Lean
toolchain of the installation.

## Changes

- The qualification is a phase of `cargo xtask formal run`, with a budget
  of 3,600 s, in place of the qualification command of the CAS project
  with its own receipt. Each case is a unit `qualification/<case>`, and
  each theorem of a case a unit `qualification/<case>/<theorem>`; the cases
  are read from the checkout at the start of the run to register them, and
  the export's `cases.json` must be the same file.
- `load_cases` reads `cases.json` with `serde` and refuses a field that it
  does not know. It checks, besides what the CAS project checked, the
  schema, the name of a case (it names directories), the module paths, that
  a case has roots or parts, that `models` names a directory below
  `verification/externals`, and that a proof, of a translated case alone,
  lies below `Krepi.Qualification` and names its theorems once each, each
  below the proof's module.
- Each case is extracted alone, in its own work directory with its own
  Cargo target directory, which is removed when the extraction ends; the
  CAS project extracted three at a time, each worker with a target
  directory that it kept until the extractions ended.
- A command that was killed, ran out of time or could not start forces the
  conclusion of its case through the gate, in place of an error that failed
  the qualification.
- `Extracted` is the record type `Observed` of
  `xtask/src/formal/receipt.rs`, with the same five fields, so that the
  receipt records what the comparison read. `Extracted::of` becomes
  `observed`, which reads the extractions of a case, one, or one for each
  of its parts, and joins what they show; the loops strip the namespace
  that each extraction holds.
- Each case that expects a translation, and whose extraction is complete,
  builds alone in a stage of its own, in place of one Lake build of the
  cases that translate and one of the ill-typed cases. An ill-typed case
  must exit with 1 with type errors only in the file that it records, and
  every `error:` and `warning:` line of its log must name that file, apart
  from Lake's closing lines; the log of a job is not read. A case that
  expects a rejection is not built, even when it starts to translate.
- `case_path` and `names_case_file` are folded into `case_errors`.
  `case_errors` and `errors_in` take the directory of the case's generated
  modules, `KrepiGen/<module path>/`, in place of the module of its
  definitions. The matching is unchanged: a file directly in that
  directory, named by the path that Lake prints.
- `installed_external` reads the reviewed files below the export, and names
  a reviewed file that it cannot read by its path in the repository, as
  `models` gives it, so that the difference does not depend on the run
  directory. `install`
  copies from the output of Aeneas, whose files the extraction lists, and
  returns a reviewed file that is not installed as a difference of the case
  apart from an error of the files of the run, which stops the phase.
- The audit of a case runs in the stage of the case, always as
  `Audit.lean` there (`audit_source_path` becomes a constant), and
  `audit_source` audits one case. `audit_case_proofs` becomes `prove`,
  which builds the proof module and then audits it, both as commands of the
  case's unit, and concludes each theorem.
- `judge_case_audit` returns the problems of each theorem in place of
  adding them to the failures of the qualification, and judges the axioms
  that one audit command reported, a command whose class is a passed or
  failed command; a killed audit is a tool failure that the gate records. A
  theorem that the audit reports twice, which only a shared audit could do,
  is not checked.
- The axioms that `judge_case_audit` allows are no longer a closure of the
  function: it asks `allows` of `xtask/src/formal/lean.rs` with the kind of
  a qualification theorem, so that one table of the base round admits the
  axioms of every audit, and the axiom of a native decision is never
  allowed, even when the case declares it.
- The check of `judge_case_audit` that the audit belongs to the cases that
  it judges (lines 877 to 879), and the fields that `audit_case_proofs`
  recorded for it to check (`qualification_cases`, `audit_source` and
  `audit_source_sha256`, lines 616 to 624, and the `axioms` map), are
  dropped. Each audit is a command of its own case, run in that case's
  stage on the `Audit.lean` that `audit_source` writes there from
  `cases.json`, whose SHA-256 the receipt records with the arguments and
  the digests of the output of the command; no audit is taken over from an
  earlier run. The axioms that the audit reported for each theorem are in
  the record of the theorem.
- The generated namespace is that of the layout, `KrepiGen`.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `tests::ill_typed_cases_count_errors_in_their_own_generated_files`, lines 2314 to 2338 | `tests::ill_typed_cases_count_errors_in_their_own_generated_files` | The paths name `KrepiGen` as Lake 4.35 prints them, relative to the project, in place of the generated directory of the CAS project. `case_errors` and `errors_in` take the directory of the case's generated modules, such as `KrepiGen/Qual/SharedTerm/`, in place of the module of its definitions; the counts are unchanged |

The tests of the CAS project of `differences` and `judge_case_audit` ran
through the judgement of a copied qualification. They are replaced by
`tests::a_rejection_where_a_translation_is_expected_is_a_difference`,
`tests::a_translation_where_a_rejection_is_expected_is_a_difference`,
`tests::a_missing_diagnostic_is_a_difference`,
`tests::an_extra_diagnostic_is_a_difference`,
`tests::a_missing_external_function_is_a_difference`,
`tests::an_extra_external_function_is_a_difference`,
`tests::a_missing_external_type_is_a_difference`,
`tests::an_extra_external_type_is_a_difference`,
`tests::a_missing_loop_source_is_a_difference` and
`tests::an_extra_loop_source_is_a_difference`, which compare the extractions
that the pinned tools wrote for three shapes with edited cases, and by
`tests::a_theorem_that_uses_a_declaration_of_another_case_fails_its_audit`
and `tests::an_audit_that_does_not_report_a_theorem_fails`.

Other new tests run the phase on fixtures with stand-ins for the tools:

- `tests::a_qualification_of_every_kind_of_case_is_verified`, with a case of
  each expectation, reviewed declarations and a proof;
- `tests::the_committed_case_list_is_frozen`;
- `tests::a_case_that_differs_from_its_expectation_rejects_the_run` and
  `tests::the_captured_extractions_are_as_their_cases_expect`;
- `tests::a_killed_ill_typed_build_is_a_tool_failure_and_not_as_expected`,
  `tests::an_ill_typed_build_with_an_error_in_another_file_is_not_as_expected`
  and `tests::an_ill_typed_build_that_passes_is_not_as_expected`;
- `tests::a_killed_audit_concludes_its_theorems_as_tool_failures` and
  `tests::a_proof_that_does_not_build_rejects_its_theorems`;
- `tests::reviewed_externals_may_declare_only_generated_axioms`;
- `tests::a_case_without_a_root_fails_the_run`,
  `tests::a_crate_that_cargo_would_build_otherwise_stops_the_phase` and
  `tests::the_cases_file_of_the_snapshot_must_be_the_one_read_at_the_start`;
- `tests::the_parts_of_a_case_are_imported_together`;
- `tests::an_ignored_lean_file_does_not_reach_a_case_stage`;
- `tests::a_failed_copy_into_a_case_stage_gives_an_incomplete_tool_failure_receipt`
  and `tests::a_tool_that_writes_the_backend_stops_the_qualification`;
- `tests::the_case_audit_judges_through_the_allowlist`;
- `tests::every_convention_has_its_class_at_the_qualification_sites`, which
  runs each convention of `outcome.rs` through Charon, Aeneas, the
  qualification build, the ill-typed build and the case audit, with a case
  that expects a rejection and an ill-typed case among those it meets;
- `tests::the_qualification_crate_is_a_workspace_of_one_package`.

## Behaviour changes

- A tool failure of any command of a case concludes the case and its
  theorems as tool failures, and the run goes on with the next case. Test:
  `tests::every_convention_has_its_class_at_the_qualification_sites`.
- Each ill-typed case is built alone. An error in another file of the case
  or elsewhere, and a warning there, is a difference of the case; in the
  CAS project the shared build failed for every ill-typed case. Tests:
  `tests::an_ill_typed_build_with_an_error_in_another_file_is_not_as_expected`
  and `tests::a_killed_ill_typed_build_is_a_tool_failure_and_not_as_expected`.
- A case whose proof does not build stays as expected, and its theorems are
  rejected; in the CAS project the shared build failed the qualification.
  Test: `tests::a_proof_that_does_not_build_rejects_its_theorems`.
- A case that expects a rejection and starts to translate is not built.
  Test: `tests::a_case_that_differs_from_its_expectation_rejects_the_run`.
- A stage that cannot be created or filled, such as a project file that
  cannot be copied into it, stops the phase as an internal error, with a
  receipt. Test:
  `tests::a_failed_copy_into_a_case_stage_gives_an_incomplete_tool_failure_receipt`.

## Hardware evidence to re-obtain

None: the qualification runs on the host.

## Not carried over

- `cargo_target`, `EXTRACTION_WORKERS` and `RUN_CARGO_TARGETS` (lines 40 to
  60) and the extraction on workers: each case is extracted alone.
- `IllTyped`, `ill_typed_build_problems`, `ill_typed_failure`,
  `judge_ill_typed`, `build_ill_typed` (lines 213 to 382) and
  `lean_build_failure` (lines 851 to 863), with the tests
  `tests::ill_typed_cases_fail_their_one_build_with_type_errors_alone`,
  `tests::the_ill_typed_cases_are_built_together_in_their_order` and
  `tests::a_qualification_builds_its_ill_typed_cases_apart_from_the_others`:
  the shared builds are replaced by one build of each case.
- `audit_batches` (lines 559 to 574) and the call of it in
  `audit_case_proofs`, with the test
  `tests::qualification_audits_keep_colliding_externals_in_separate_environments`:
  each case is audited in its own stage.
- `Extracted::of_record` (lines 435 to 453), `judge_copy`,
  `judge_copied_audits` and `judge_copied_model_check` (lines 914 to 1076),
  `input_files` (lines 1078 to 1105) and the tests of copied
  qualifications: krepi does not take a qualification over from an earlier
  run.
- The model check and its vectors (lines 1107 to 1480): krepi has no model
  of the qualification cases.
- `qualify_into` (lines 656 to 692), `run` (lines 1482 to 1520) and
  `stand_in` (lines 1522 to 1682), with their receipt and its `aborted`
  field, and the tests
  `tests::an_interrupted_qualification_extracts_no_further_case_and_builds_nothing`,
  `tests::a_qualification_extracts_in_target_directories_of_its_own_that_it_removes`
  and `tests::a_qualification_that_stops_keeps_its_receipt`: the phase runs
  in the gate, whose receipt records it, and a stop signal ends the run.
- `GENERATOR_LIMIT` (line 42): there is no generator.
