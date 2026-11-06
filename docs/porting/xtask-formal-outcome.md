---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/lean.rs
  - xtask/src/formal/extract.rs
  - xtask/src/formal/process.rs
destination:
  - xtask/src/formal/outcome.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/outcome.rs

## Summary

Three functions of the proof gate of the CAS project that tell a tool that
was killed from a tool that failed by itself:

- `killed` (`xtask/src/formal/lean.rs`, lines 356 to 369) finds a Lake
  command that a signal ended or that ran out of time, and a Lean process
  that a signal ended, from the exit code of `lake env` or from the
  `error: Lean exited with code` lines of a `lake build` log;
- `exit_codes` (`xtask/src/formal/lean.rs`, lines 373 to 379) reads those
  codes from the log;
- `charon_killed` (`xtask/src/formal/extract.rs`, lines 248 to 271) finds a
  Charon that a signal ended or that ran out of time, a Charon that exited
  with 255 because a signal ended the Cargo it runs, and a Cargo that
  reports a process ended by a signal, as in `(signal: 9, SIGKILL: kill)`.

They are taken because the conventions that they encode come from the
behaviour of Lake, Lean, Charon and Cargo and were found on real failures.
The three functions are released under the MIT License as part of krepi, as
the [porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.
`stopped`, which all three call, is written again after `Outcome::killed`
(`xtask/src/formal/process.rs`, lines 124 to 141).

Everything else in `xtask/src/formal/outcome.rs` is new code: the call
sites of the gate's commands with their caps, the classes of a command's
result and the statuses of units and runs, the one classification function
that every call site uses, the conclusion that a unit's failed commands
force, the accounting of unit conclusions and the status of a run. The
module `xtask/src/formal/process.rs`, which runs each command in a process
group of its own with its output written to files, is new code as well and
takes nothing from the CAS project.

## Changes

- The functions take a `Ran`, the result of a command that
  `xtask/src/formal/process.rs` ran, in place of an `Outcome`. The exit code
  is `Ran::code`, which is `None` for a command that did not exit, in place
  of the field `status`, which was -1 for such a command; `charon_killed`
  tests `Ran::code() == Some(255)`.
- `stopped` replaces `Outcome::killed`. A command that ran until its limit
  takes the limit from `Ran::limit`, which may be fractional and is then
  written in seconds as the receipt writes it, rounded to milliseconds; the
  text is unchanged for the cap of the
  call site and adds `the rest of the budget of its phase` or `the rest of
  the budget of the gate` when a budget set the limit. A command that could
  not start or keep its output, which the CAS project reported as an error
  of the step rather than as an outcome, is stopped too, with the text of
  the failure after its name.
- `charon_killed` is public, so that the classification and its tests use
  it.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `xtask/src/formal/lean.rs` `tests::a_lean_process_ended_by_a_signal_is_reported`, lines 930 to 964 | `xtask/src/formal/outcome.rs` `tests::a_lean_process_ended_by_a_signal_is_reported` | Unchanged. The build log names the modules `Krepi.Proofs.Base` and `Krepi.Proofs.Main` in place of those of the CAS project, and the command that ran out of time has a limit of 7,200 s set by the cap of its call site. The test also checks the codes that `exit_codes` reads |

The test `tests::charon_killed_tells_how_charon_was_stopped` is new. It
takes the tool outputs and the texts of the CAS project test
`xtask/src/formal/extract.rs`
`tests::a_killed_tool_is_a_tool_failure_and_no_rejection` (lines 531 to
580) for a Charon that signal 9 ended, a Cargo that reports
`(signal: 9, SIGKILL: kill)` and exits with 101, and a Charon that exits
with 255, without the module prefix that the extraction puts before them,
and adds a Charon that fails by itself and one that passes, which are not
killed. The CAS project test runs Charon through the extraction, which this
module does not contain.

## Behaviour changes

- A command stopped at the limit of a phase or of the gate is `BUDGET`
  rather than a tool failure; stopped at the cap of its call site, it is a
  tool failure as before. Tests: the rows `timeout` and `timeout-at-budget`
  of `tests::every_convention_has_its_class_at_every_site_it_applies_to`,
  and `tests::a_timeout_names_the_limit_that_stopped_the_command`.
- A command whose process group still has processes after the kill is a
  tool failure. Test: `tests::a_group_that_survives_its_kill_is_a_tool_failure`.
- A command that could not start or keep its output is a tool failure of
  that command, in place of an error that ended the step. Test: the row
  `cannot-start` of
  `tests::every_convention_has_its_class_at_every_site_it_applies_to`.

## Hardware evidence to re-obtain

None: the functions run on the host and read the output of host tools.

## Not carried over

- `Ended::Interrupted`, `Interrupt`, `INTERRUPT`, `stop_on_signals`,
  `signal_name` and `interruption` (`xtask/src/formal/process.rs`): the
  proof gate writes no receipt for a run that a signal interrupted.
- `Outcome::of_record` and the JSON record of a command
  (`xtask/src/formal/process.rs`): no result is taken over from an earlier
  run, and the receipt of the gate records each command.
- `run_logged`, `run_unlogged`, `wait` and `kill_tree` with its repairs for
  macOS (`xtask/src/formal/process.rs`): each command now runs in a process
  group of its own, which is killed as a whole and waited for, and needs
  none of the repairs.
- `errors` and `module_file` (`xtask/src/formal/lean.rs`, lines 381 to
  392), which follow `exit_codes` but serve the Lean build rather than the
  classification.
