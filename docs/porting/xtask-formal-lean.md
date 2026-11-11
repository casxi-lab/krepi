---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/lean.rs
destination:
  - xtask/src/formal/lean.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/lean.rs

## Summary

`parse_axioms` (lines 314 to 349) of the Lean steps of the proof gate of the
CAS project: the theorems and their axioms that `#print axioms` prints,
across the lines into which Lean wraps long lists and with names that end
in primes. It is taken because the audit of the qualification proofs reads
the output of the pinned Lean with it. Also `diagnostic` and
`proof_messages` (lines 413 to 444): the errors and warnings that the log of
a Lake build reports in the source files of given modules, which decide
whether a failed build of the base round is a proof failure. And the
reading of the build of a mutant: `FAILURE_SUMMARY` and `job_line` (lines
395 to 411), `confined_errors` (lines 456 to 551), which tells whether a
failed build failed in the proof modules alone; the printer of the
declaration ranges, `RANGES` (lines 560 to 587), with `ranges_source`
(lines 590 to 601); its reading, `Declared`, `Ranges`, `Printed`,
`range_line`, `Ranges::parse`, `Ranges::at`, `Ranges::theorem` and
`top_level` (lines 607 to 759); and `declaration_ranges` with `ranges_of`
(lines 765 to 796), which run the printer and refuse what a failed or
killed Lean printed ([mutants](../formal-verification.md#mutants)). They
are released under the MIT License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

Taken unchanged from outside the copy list, so not counted among its
items: the value of `STANDARD_AXIOMS` (line 42), with a new comment, and
the bodies of `errors` (lines 381 to 387) and `module_file` (lines 389 to
392). Written in krepi after the CAS project: `PROJECT_FILES` (line 37),
and the stage of a unit, `create_stage`, after `Stage::create` (lines 141
to 172) and `link_backend` (lines 107 to 130).
The arguments of the Lake commands, `build_args` and `check_args`, follow
`build` (lines 237 to 257) and `check_file` (lines 262 to 284), whose
commands run through the gate of `cargo xtask formal run`; `build_args`
also builds several targets, with or without warnings as errors, as the
two builds of the base round do. The audit file of the base round,
`audit_source`, and the reading of its output, `audit_output`, are written
after `audit` (lines 288 to 312). `copy_into`, the source rules, the
registries of library axioms and of the trusted base, the allowlist, the
root module, the read checks of `leanchecker` and of the version query, the
heartbeat counts and the listing of the installation are new.

## Changes

- `parse_axioms`, `diagnostic` and `proof_messages`: none.
- `confined_errors`: a line `error: Lean exited with code` is a problem
  whatever its code, since Lean 4.35.0 prints it only when Lean ends
  otherwise than with 1 after an error; the CAS project allowed the code 1.
  A module that the failure summary lists without a warning or an error in
  its file has a problem text of its own.
- The printer prints `krepi-range`, `krepi-ranges-module` and
  `krepi-ranges-missing` lines, with its own command and namespace. Its
  documentation names a failed `simp` attribute as the message that Lean
  places at the start of a command.
- `declaration_ranges` writes the printer into the stage project and runs
  it as a command of the gate, at the call site of the declaration ranges;
  `ranges_of` reads that command, killed as `outcome::killed` finds it.
- The project files of a stage are `lakefile.toml`, `lean-toolchain` and
  `lake-manifest.json`: the Lake project of krepi is configured in TOML, so
  that its configuration runs no Lean code.
- A stage is a directory of one unit, which holds the project files of the
  export and the files that the unit installs, not every Lean file of the
  project, and its links point to the Aeneas Lean library of the
  installation itself, which is read in place, in place of a writable clone
  of it.
- The generated definitions lie below `KrepiGen/` in the project of the
  stage, in place of a directory of generated definitions outside it.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `tests::axiom_lists_are_parsed_across_lines`, lines 999 to 1006 | `tests::axiom_lists_are_parsed_across_lines` | Unchanged |
| `tests::primed_names_are_parsed`, lines 1008 to 1016 | `tests::primed_names_are_parsed` | Unchanged |
| `tests::the_messages_of_the_proofs_are_found_anywhere_in_a_log`, lines 1258 to 1279 | `tests::the_messages_of_the_proofs_are_found_anywhere_in_a_log` | The module and path names of krepi; the generated file lies inside the project, as Lake prints the files of a stage relative to it |
| `tests::errors_confined_to_the_proofs_are_returned`, line 1027 | `tests::errors_confined_to_the_proofs_are_returned` | The logs of the pinned Lean 4.35.0 in `fixtures/mutants/`: a failed build of the fixture module, one that failed on a warning and that of a mutant of the calibration |
| `tests::failures_outside_the_proofs_are_reported`, line 1079 | `tests::each_rule_of_the_log_of_a_rejected_mutant_is_kept` | One case for each rule, an edit of a captured log |
| `tests::the_range_printer_imports_and_names_the_modules`, line 1284, and `tests::a_name_is_read_to_the_end_of_its_line`, line 1449 | `tests::the_range_printer_imports_and_names_the_modules` | The names of krepi's printer |
| `tests::errors_count_against_the_declaration_whose_range_holds_them`, line 1381, and `tests::a_nested_range_may_start_where_the_one_around_it_starts`, line 1433 | `tests::errors_count_against_the_declaration_whose_range_holds_them` | The range table that the pinned Lean printed for the fixture module, at the positions of the errors of its failed build |
| `tests::an_incomplete_or_inconsistent_range_table_is_rejected`, line 1457 | `tests::an_incomplete_or_inconsistent_range_table_is_rejected` | Edits of the captured table |
| `tests::ranges_that_a_killed_lean_printed_are_not_read`, line 967 | `tests::ranges_that_a_failed_or_killed_lean_printed_are_not_read` | The captured output of a printer that imports a module without a build |

The other tests of the module are new.

## Behaviour changes

- A stage links the installation's library and does not clone it. Test:
  `tests::a_stage_holds_the_project_files_and_links_the_installation`.

## Hardware evidence to re-obtain

None: the Lean steps run on the host.

## Not carried over

`killed` and `exit_codes` are in `xtask/src/formal/outcome.rs`
([its record](xtask-formal-outcome.md)). `clone_backend`,
`clone_tree` and `Stage::seed_from` are not taken, because the
installation is read in place; `build_files` and `compiled_modules` are
not taken, because no build is reused. `audit` and `check_file` are
rewritten, as stated above. The other functions of the file, with their
tests, are not taken.
