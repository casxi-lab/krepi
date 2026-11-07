---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/extract.rs
destination:
  - xtask/src/formal/extract.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/extract.rs

## Summary

The extraction of the proof gate of the CAS project, which runs Charon and
then Aeneas on the roots of one module and reads what Aeneas wrote:

- `Extraction` (lines 45 to 54), the outcome of one extraction;
- its accessors `external_functions` (lines 58 to 72), `external_types`
  (lines 75 to 88), `local_functions` (lines 93 to 107) and `loop_sources`
  (lines 116 to 139);
- `diagnostics` (lines 211 to 242), the `[Error]` and `[Warn ]` messages of
  Aeneas and the `error` lines of Charon, with terminal escapes removed;
- `extract_under` (lines 281 to 464), the extraction itself, which becomes
  `extract`.

They are taken because the arguments of the two tools, the reading of
`translation.json` and the rules for external items and loops were worked
out against the behaviour of the pinned tools and are what the
qualification expectations were recorded with. `charon_killed` (lines 248
to 271) is ported into `xtask/src/formal/outcome.rs`
([its record](xtask-formal-outcome.md)). The code is released under the MIT
License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

New in krepi are the types that `translation.json` is read into
(`Translation`, `Function`, `Type`, `Source`, `Loop`), the request with its
unit, `read_output`, which reads what Aeneas wrote before Aeneas is
classified, the reading of the extraction configuration
`verification/extraction.toml` (`Configuration`, `configuration`), and
`package_problems` with `MANIFEST`, the check that the manifest of the
qualification crate makes it a workspace of its own and holds only the
tables and keys that do not change what Cargo compiles and that Charon
does not read. The commands run through the gate of
`cargo xtask formal run`, whose `Gate::run` and `Gate::skip` in
`xtask/src/formal/run.rs` are new code as well.

## Changes

- `extract_under` becomes `extract`, which takes the `Gate` of the run in
  place of the tools and an interrupt. Each command runs through the gate
  with its call site, `charon` or `aeneas`, which gives it the environment
  of `xtask/src/formal/toolchain.rs`, limits it by the cap of the call site
  (1,800 s and 3,600 s, as `CHARON_LIMIT` and `AENEAS_LIMIT` were) and the
  budgets, and classifies it once with `outcome::classify`. The extraction
  no longer calls `charon_killed` or `Outcome::killed` itself (lines 356 to
  361 and 415 to 420): a killed command is a tool failure of its unit,
  which forces the conclusion of the unit, and the extraction returns what
  it read in place of an error.
- `Error` (lines 183 to 202) is replaced. What was `Error::Unfinished` is
  the class of the command. What was `Error::Failed` is either a tool
  failure of a command (a tool that cannot start, an output file that
  cannot be read, a `translation.json` that is not one) or an internal
  error, which `extract` returns and which stops the phase: a request
  without a root, a work directory that has been used, a path that is not
  UTF-8, a work directory that cannot be created and a Cargo target
  directory that cannot be removed.
- The request names the unit of the commands. It has no `exclude`, and no
  `cargo_target`: the Cargo target directory is `target/` of the work
  directory, removed when the two commands have ended, and a work directory
  that already holds it is refused as one that holds `extract.llbc` or
  `aeneas/` is.
- The generated namespace is that of the layout, `KrepiGen`, in place of
  the CAS project's.
- `translation.json` is read with `serde` into `Translation`, with only the
  fields that the accessors use, every one of them required apart from
  `loop`, which Aeneas writes only on the entries of a loop and of its body.
  The CAS project read any JSON and skipped an entry without a field.
  `entries` (lines 173 to 180) is dropped: the accessors read
  `Extraction::translation`, which is empty when Aeneas wrote none.
- A `translation.json` that cannot be read, a directory among them, is a
  tool failure of Aeneas; the CAS project skipped a path that was not a
  file. So is a missing `translation.json` after Aeneas exited with 0,
  since Aeneas writes it at the end of every run; after any other exit a
  missing one is no translation, as in the CAS project.
- The Lean files that Aeneas wrote are not copied to `generated/` of the
  work directory. `Extraction::generated` is the output directory of
  Aeneas, and `Extraction::files` maps each Lean file, relative to it, to
  its SHA-256, which the record's `generated_sha256` held.
- `Extraction::record` and the JSON record of each command are dropped: the
  receipt of the run records each command. So is
  `Extraction::aeneas_status`: the receipt records the exit code of Aeneas
  with its command. `Extraction` holds the namespace of the translation,
  and `loop_sources` takes no argument and strips that namespace, where it
  took the module and put the generated namespace of the CAS project before
  it.
- When Charon does not pass, or passes without writing the LLBC file,
  Aeneas is recorded as a command that did not start, with the reason; the
  CAS project left it out.
- The comment on `CARGO_INCREMENTAL` (lines 316 to 322) is rewritten:
  Charon at commit `6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2` no longer
  gives Cargo a new `RUSTC_WORKSPACE_WRAPPER` in every run; it removes that
  variable and sets `CHARON_SELECTED_CRATE_<crate>` to a new value
  (`charon/src/bin/charon/main.rs`, lines 237 to 250), with the same effect
  on the reuse of the crate's build. The two variables of the extraction
  are set by the environment builder of `xtask/src/formal/toolchain.rs`.
- `local_functions` has no caller until the target phase, and is marked so
  outside the tests.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `tests::a_killed_tool_is_a_tool_failure_and_no_rejection`, lines 531 to 580 | `tests::a_killed_tool_is_a_tool_failure_and_no_rejection` | The stand-ins are installed in the `bin` directory of the installation and found through `PATH`, and each extraction runs through the gate in a phase that concludes the case `VERIFIED`. Each killed tool is a `TOOL_FAILURE` command with the reason of the CAS project test without the module that it started with, and forces the conclusion of the case. The tools that fail by themselves are `PROOF_FAILURE` commands, with the same diagnostics, and the case stays `VERIFIED`; Aeneas after a Charon that fails is `NOT_RUN`. The exit status of Aeneas is read from its command in the receipt, in place of `aeneas_status`. The check of the recorded Cargo target directory is left to the test of the arguments and the environment. A Charon that exits with 0 without writing the LLBC file is added |
| `tests::a_tool_that_cannot_start_or_a_file_it_cannot_use_fails_the_extraction`, lines 598 to 626 | `tests::a_tool_that_cannot_start_or_a_file_it_cannot_use_fails_the_extraction` | A tool that cannot start, a `translation.json` that cannot be parsed and a generated file that cannot be read are tool failures of Aeneas and of the case, with reasons that start with `aeneas: cannot start aeneas: `, contain `is not a translation: `, and start with `aeneas: cannot read `. The work file that Charon makes impossible to write is a Cargo target directory that cannot be removed, because no generated files are copied; it stops the phase |
| `tests::charon_builds_without_incremental_compilation`, lines 629 to 643 | `tests::charon_builds_without_incremental_compilation` | Unchanged; the target directory ends with `/work/cases/f/target`. That the environment of Lake has no `CARGO_INCREMENTAL` is tested by `toolchain::tests::every_tool_gets_exactly_its_variables` |
| `tests::aeneas_translates_on_one_thread`, lines 646 to 682 | `tests::aeneas_translates_on_one_thread` | The arguments with the namespace `KrepiGen.Qual.F`, the program `aeneas` and `RUN` for the run directory; the arguments are also part of `tests::the_extraction_commands_have_the_frozen_arguments_and_environment` |
| `tests::loop_sources_name_each_translated_loop_with_its_file`, lines 685 to 732 | `tests::loop_sources_name_each_translated_loop_with_its_file` | Unchanged. The entries name `KrepiGen` and have a `lean_file`, and the translation has `types`, which the reading requires |
| `tests::diagnostics_strip_escapes_and_progress_bars`, lines 780 to 790 | `tests::diagnostics_strip_escapes_and_progress_bars` | Unchanged |

New tests:

- `tests::the_extraction_commands_have_the_frozen_arguments_and_environment`:
  the arguments and the working directory of both commands, with two roots
  and two `--opaque` patterns, and the 14 variables that both stand-ins see;
- `tests::an_extraction_without_a_root_fails_before_charon_runs` and
  `tests::a_used_work_directory_is_refused`;
- `tests::external_functions_are_the_opaque_entries_of_the_function_template`,
  `tests::external_types_are_the_entries_of_the_type_template`,
  `tests::local_functions_are_read_with_their_source_files` and
  `tests::loops_are_the_entries_whose_loop_is_not_a_body`, on translations
  that the pinned tools wrote for three shapes of the qualification crate,
  kept in `xtask/src/formal/fixtures/extraction/`;
- `tests::a_captured_translation_is_read_with_the_files_that_aeneas_wrote`;
- `tests::an_unreadable_or_invalid_translation_is_a_tool_failure`;
- `tests::the_target_directory_is_removed_after_the_extraction`;
- `tests::the_extraction_configuration_is_read` and
  `tests::a_crate_manifest_that_charon_reads_or_that_changes_the_build_is_refused`.

## Behaviour changes

- A tool that was killed, ran out of time or could not start is a tool
  failure, or a budget, of the case, in place of an error that ended the
  qualification. Tests:
  `tests::a_killed_tool_is_a_tool_failure_and_no_rejection` and
  `tests::a_tool_that_cannot_start_or_a_file_it_cannot_use_fails_the_extraction`.
- A `translation.json` that cannot be read, that is not JSON or that lacks
  a field that the gate reads, or that is missing after Aeneas exited with
  0, is a tool failure of Aeneas, after the rules for killed commands.
  Test: `tests::an_unreadable_or_invalid_translation_is_a_tool_failure`.
- Each extraction has a Cargo target directory of its own, which is removed
  when it ends. Test:
  `tests::the_target_directory_is_removed_after_the_extraction`.
- A work directory that holds `target/` is refused as well. Test:
  `tests::a_used_work_directory_is_refused`.
- Aeneas that does not start is a `NOT_RUN` command, which does not decide
  the case. Test: `tests::a_killed_tool_is_a_tool_failure_and_no_rejection`.
- `--exclude` is never passed to Charon. Test:
  `tests::the_extraction_commands_have_the_frozen_arguments_and_environment`.

## Hardware evidence to re-obtain

None: the extraction runs on the host.

## Not carried over

- `Extraction::local_items` (lines 148 to 171), `words` (lines 204 to 207)
  and the test `tests::local_items_of_every_kind_are_named_by_kind` (lines
  735 to 777): they name the items of a translation for the keys of
  results taken over from an earlier run, which krepi does not take over.
- `extract`, which ran `extract_under` with the interrupt of the process
  (lines 275 to 277), and the test
  `tests::a_tool_that_a_signal_keeps_from_starting_leaves_the_extraction_unfinished`
  (lines 583 to 595): a stop signal ends the run of the gate without a
  receipt.
- The `--exclude` option (lines 332 to 337): no extraction of krepi
  excludes items.
- `CHARON_LIMIT` and `AENEAS_LIMIT` (lines 17 to 23): the caps are those of
  the call sites, `Site::cap` in `xtask/src/formal/outcome.rs`, with the
  same values.
- The record of the extraction (lines 362 to 367 and 456 to 462), with the
  digest of the LLBC file: the receipt of the run records the commands.
