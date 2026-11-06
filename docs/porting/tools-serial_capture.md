---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/serial_capture.rs
  - tools/src/cycles.rs
  - tools/src/suites/platform/pi5_bundle.rs
  - tools/src/suites/platform/pi5_kernel.rs
  - tools/tests/platform/physical_entry.rs
  - tools/tests/support/pty.rs
  - tools/tests/support/child.rs
  - tools/tests/support/scratch.rs
  - tools/tests/support/rejection.rs
  - xtask/src/main.rs
  - xtask/tests/serial_capture.rs
destination:
  - tools/src/serial_capture.rs
  - tools/src/serial_capture/tests.rs
  - tools/src/pty.rs
  - tools/src/child.rs
  - tools/src/scratch.rs
  - xtask/src/main.rs
  - xtask/Cargo.toml
  - xtask/tests/serial_capture.rs
treatment: ported
features: none
---

# Porting record: tools/src/serial_capture.rs

## Summary

The bounded capture of what a board sends over a serial port, which does
not evaluate the board's boot, and the command `cargo xtask serial-capture`
that runs it. `capture_with` creates a new output directory, opens the port
read-only with the `Receiver` of [`tty`](tools-tty.md), receives until its
deadline, its byte limit or the end of the stream, restores the port and
writes `raw.bin`, `preview.txt` and the receipt `summary.json`; `parse`
reads the command line with `clap`, and `main` and `run_with` print the help
or a usage error, list the likely USB serial devices, print the preview, the
status and the receipt path, and give the exit status. The module is ported
with its unit tests, the tests of the capture in the legacy integration
tests and the tests of the command's binary.

The legacy module reproduced the Python script that it replaced: its
command line followed argparse, its numbers were read as Python reads them,
its rendering of text followed Python's Unicode 16.0 tables, and its error
texts, time stamps and report of a failed output write were Python's. These
forms are not carried over: `clap` reads the command line and writes its
help, usage and errors, and the other functions are written again in the
form described under [Changes](#changes), each with the test that fixes it
under [Behaviour changes](#behaviour-changes). The path normalization of
`suites/platform/pi5_bundle.rs`, the file error text of the same file, the
directory creation of `suites/platform/pi5_kernel.rs` and `random_hex` of
`cycles.rs`, which the legacy module took from those modules, are private
functions of this module.

## Changes

- `clap` `=4.6.7` reads the command line in place of the legacy
  reproduction of argparse; see
  [dependencies](../../CONTRIBUTING.md#dependencies). `cli` defines with
  clap's builder the seven options `-h`, `--help`, `--list`, `--port`,
  `--seconds`, `--max-bytes` and `--output-dir`, requires exactly one of
  `--list` and `--port`, and gives the limits their defaults, 30 and
  262144. `parse` reads the command line with it and then checks the limits
  with `check_limits`, so that a limit out of bounds is a usage error of
  clap whose message is the bound. An option with a value takes it after
  `=` or as the next argument, a repeated option keeps its last value
  (`args_override_self`), and `--seconds` and `--max-bytes` take a negative
  number as the next argument (`allow_negative_numbers`); everything else
  follows clap's rules. `parse` returns clap's error in place of a
  `Failure`, and `Command` has no `Help` variant: the help is clap's error
  of the kind `DisplayHelp`. `run` prints the help on standard output
  with status 0 and any other error of clap, a usage error, on standard
  error with status 2, through the command's own streams, so that a failed
  write makes the status 120 as before. The help, the usage and the usage
  errors are clap's texts, with the command's description and option texts
  of the legacy help. clap is built without its `color`, `suggestions` and
  `wrap_help` features, so the texts have no colour, no suggestion of a
  similar option and no wrapping to the terminal, and its derive macros are
  not used.
- `--seconds` is read by Rust's `f64` and `--max-bytes` by Rust's `u64`. A
  value that they refuse is a usage error of clap that names the option and
  quotes the value as given, `invalid value '<value>' for '--seconds
  <SECONDS>': invalid float literal` or `invalid value '<value>' for
  '--max-bytes <MAX_BYTES>': not a decimal integer`. A `--max-bytes` value of
  ASCII digits, after an optional `+`, that is too large for 64 bits is out
  of bounds; a value with any other character is an invalid value, also
  where its digits before that character are already too large.
  The type `Seconds`, which kept Python's `int` default apart from a
  `float` value, is gone: a duration is an `f64`, `DEFAULT_SECONDS` is
  `30.0`, and the byte limits are `u64`. `check_limits`, `capture`,
  `capture_with` and `Command::Capture` take these types; the new constants
  `MAX_SECONDS`, `SECONDS_BOUND` and `BYTES_BOUND` name the bound and the
  two bound messages.
- Text for a terminal, the preview, the names that `--list` prints, the
  receipt path and the message of `UART capture failed`, is rendered by
  `render` and `render_name` in place of `sanitize` and `sanitize_name`:
  newline, tab, backslash and both quotes stay, and each run of text
  between them is written as `str::escape_debug` writes it, which escapes
  control, format, private-use, default-ignorable and unassigned characters
  and white space other than the space, and a grapheme extender at the
  start of a run, by the Unicode tables of the toolchain, as `\u{1b}`, `\r`
  or `\0`. A byte of a name that is not UTF-8 is written `\xNN`. The preview
  is decoded with `String::from_utf8_lossy`, which replaces each maximal
  invalid sequence, as before.
- Errors carry the standard library's text of the operating-system error.
  An error about a file starts with its path in Rust's debug form,
  `"<path>": strerror (os error N)`, in place of `file_error` of
  `suites/platform/pi5_bundle.rs`, `[Errno N] strerror: '<path>'`; the
  errors of the port are those of [`tty`](tools-tty.md). A failed write of
  `raw.bin` is the error text alone.
- The output directory is created by `create_output` with the standard
  library, in place of the Python `mkdir` of
  `suites/platform/pi5_kernel.rs`, in the same order: `create_dir` for the
  directory, which must not exist, and only when a parent is missing,
  `create_dir_all` for its parent and `create_dir` again. An error names the
  path that its step was given: the directory, or its parent while the
  parents are created. The path is normalized by `pure_path`, taken from
  `suites/platform/pi5_bundle.rs`, without `posix_path`, which kept two
  leading slashes as Python's `PurePosixPath` does.
- The receipt is a `serde_json` object whose keys are sorted with
  `Value::sort_all_objects` and which `report::to_json` writes; non-ASCII
  text is written as UTF-8, and only control characters below U+0020, the
  quote and the backslash are escaped. `requested_seconds` is a JSON number
  with a fraction, `started_at` and `finished_at` are `report::utc_now`, and
  `sha256` is taken with `sha2` in place of the legacy SHA-256 module.
- `raw.bin` is written in a loop of single writes, and the bytes that reached
  the file before a write failed are counted in `bytes`, `sha256` and the
  preview, so that the receipt describes the file. The legacy `write_all`
  left those bytes in the file uncounted.
- The capture waits for input at most `capture_slice` of a `Timing`
  (`tools/src/timing.rs`) between two looks at its interrupt flag, in place
  of the constant `SLICE` of 100 ms. `capture`, `capture_with` and
  `run_with` take the `Timing`; `main` passes `Timing::PI5`, whose value is
  the legacy one.
- `list_ports` sorts the names by their bytes in place of the code points of
  Python's decoding, which gave a byte that is not UTF-8 the code point of
  its surrogate, from U+DC80 to U+DCFF, and so sorted it before the
  characters from U+E000 up.
- A failed write on standard output is reported at the end on standard
  error as `cargo xtask serial-capture: cannot write standard output:
  <error>`, in place of Python's report of a failed flush with the
  exception's class name; the exit status stays 120.
- `random_hex`, which names a run directory, is a private function of this
  module and takes its digests from `sha2`.
- `xtask/src/main.rs` registers `serial-capture` in `COMMANDS` and runs the
  command with the arguments after its name; the help of `cargo xtask`
  gives the command names a column of 14 characters. `xtask/Cargo.toml`
  depends on the host tooling crate by its path, so `xtask/Cargo.lock` holds
  the crates of `tools/Cargo.lock` that the module needs, in the same
  versions.
- The module documentation no longer refers to the Python script.
- The tests of the capture are unit tests in
  `tools/src/serial_capture/tests.rs`, in the submodules `properties`,
  `boundaries`, `resources` and `receipts` of their legacy groups, as no
  feature document gives them a module of integration tests and the faults
  that they inject need the seams of the crate's unit build. The receipt in
  a test is read with `serde_json::from_slice`, and its fields with
  `serde_json` indexing. The test support of the legacy integration tests is
  merged into the test-only modules that [`tty`](tools-tty.md) started, with
  the parts that these tests use:
  - `tools/src/pty.rs`: the board end `Master` of a pair, with which a board
    script on a thread of its own writes, reads the attributes of the slave
    and waits until the capture has made the port raw; `Script`, the
    thread's handle; `Attributes`, the attributes of a terminal; and, on
    `Pty`, writing to the master, reading what arrives on it within a short
    window, the slave's attributes, setting them, reading input that stayed
    queued on the slave, and closing the master.
  - `tools/src/child.rs`: a child with a changed environment
    (`spawn_with`), a child started by a command such as `nice -n 19`
    (`spawn_under`), waiting for a state that the child brings about,
    signalling the child, and the lines that the code under test printed.
  - `tools/src/scratch.rs`: the root of a scratch directory and reading a
    file in it.
- A test waits for an event at most `TEST_WAIT`, 60 s, in place of the 5 s of
  the board scripts and the 30 s of the child runner, and no test bounds the
  time that a step takes. A capture that a board script must see while the
  port is raw ends by its byte limit, by the end of the stream or by an
  interrupt, with a deadline of 120 s, never by a short deadline; a capture
  that ends `NO_DATA` by its deadline has no board script; and the check
  that nothing reached the board reads the master once the capture has
  ended. The queued input of a unit test is written with the slave's echo
  turned off, in place of discarding the echo with `tcflush`, which on
  Linux can discard input that the slave has not yet taken.
- The ports and directories of the tests use `krepi` in their names.

## Tests carried over

Legacy unit tests are in `tools/src/serial_capture.rs` below `tests`, and
krepi unit tests in `tools/src/serial_capture/tests.rs` below
`serial_capture::tests`. The legacy integration tests are in
`tools/tests/platform/physical_entry.rs` below `<group>::serial_capture`,
and their krepi tests below `serial_capture::tests::<group>`. Expected values
that changed are listed under [Behaviour changes](#behaviour-changes) as
well.

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tests::a_failed_wait_fails_the_receipt_and_restores_the_port` | Same name | Changed: `Input/output error (os error 5)` |
| `tests::a_failed_restoration_fails_the_receipt` | Same name | Changed: `attribute restoration failed: Input/output error (os error 5)` |
| `tests::refused_raw_attributes_keep_the_restoration` | Same name | Changed: `raw attributes refused: Input/output error (os error 5)`, then the restoration text above, in that order |
| `tests::an_interrupt_once_the_capture_has_ended_leaves_the_outcome` | Same name | Unchanged but the text of the failed wait, `Input/output error (os error 5)`. The queued input is written with echo off, and the row that ends by its byte limit has a deadline of 120 s in place of 5 s |
| `tests::an_interrupt_in_the_last_read_ends_the_capture` | Same name | Unchanged; echo off and a deadline of 120 s, as above |
| `tests::a_failed_write_of_the_capture_fails_the_receipt` | Same name | Changed: `No space left on device (os error 28)`; `bytes` 0, as the seam writes nothing |
| `tests::only_interrupted_and_fail_exit_with_another_code` | Same name | Unchanged |
| `tests::the_run_directory_keeps_the_python_form` | `tests::the_default_run_directory_is_a_utc_stamp_and_12_hex_digits` | Unchanged |
| `tools/src/suites/platform/pi5_bundle.rs` `tests::paths_are_normalized_as_pure_path_normalizes_them` | `tests::an_output_path_is_normalized_by_its_components` | Unchanged for the six rows; one row added: `//x/./y` gives `/x/y` |
| `properties::serial_capture::controls_are_rendered_as_python_renders_them` | `properties::the_preview_escapes_controls_and_unprintable_characters` | Changed: the escapes of `str::escape_debug`, such as `safe\n\t\u{1b}\r\u{7f}\u{9b}\u{202e}\u{200b}`; white space other than the space and default-ignorable characters are now escaped. The row of code points that only Unicode 17 assigns is left out, as the Unicode version of the toolchain decides them; a row shows a combining mark at the start of a run, and one NUL |
| `properties::serial_capture::undecodable_name_bytes_are_rendered_as_their_surrogates` | `properties::undecodable_name_bytes_are_rendered_as_hex_escapes` | Changed: `cu.usb\xff\u{1b}-` and U+03A3 |
| `properties::serial_capture::the_preview_replaces_invalid_utf8_as_python_does` | `properties::the_preview_replaces_each_maximal_invalid_sequence` | Unchanged replacement characters; the byte order mark is `\u{feff}` |
| `properties::serial_capture::the_held_port_is_raw_8n1_without_flow_control` | `properties::the_held_port_is_raw_8n1_without_flow_control` | Unchanged attributes. Changed procedure: the board reads the attributes and then sends the one byte that ends the capture by its byte limit, `CAPTURED` in place of `NO_DATA` at a deadline of 0.5 s |
| `properties::serial_capture::numbers_are_read_as_python_reads_them` | `properties::option_values_are_read_as_rust_numbers` | Changed: values with white space, underscores, digits other than ASCII ones or a minus sign before an integer are invalid values, usage errors of clap that name the option and quote the value; `1e-5`, `300`, `.5`, `5.`, `+7` and `16777216` read as before; `+inf`, `iNfInItY`, `-0`, `1e400` and `-1e-3` still fail the duration bound, and `16777217` the byte bound, each a usage error whose message is the bound. Each value follows `=`, so that clap takes it as it is; rows added: an empty `--max-bytes` value and a lone `+` are invalid values |
| `boundaries::serial_capture::invalid_limits_are_rejected_before_any_artifacts_or_port_open` | `boundaries::invalid_limits_are_rejected_before_any_artifacts_or_port_open` | Unchanged messages; the rows are numbers and unsigned integers, so the negative byte limit has no row |
| `boundaries::serial_capture::the_limits_hold_at_their_edges` | `boundaries::the_limits_hold_at_their_edges` | Unchanged; the row of the smallest integer duration is the smallest finite `f64`, and the byte bound fails at `u64::MAX` |
| `boundaries::serial_capture::an_existing_output_directory_is_never_overwritten` | `boundaries::an_existing_output_directory_is_never_overwritten` | Changed: `UART capture failed: "<dir>": File exists (os error 17)`; `--output-dir ''` names `"."`; two leading slashes name the directory with one |
| `boundaries::serial_capture::an_empty_port_is_refused_before_the_output_directory` | `boundaries::an_empty_port_is_refused_before_the_output_directory` | Unchanged |
| `boundaries::serial_capture::an_invalid_port_emits_a_failure_receipt` | `boundaries::an_invalid_port_emits_a_failure_receipt` | Changed: `"<missing>": No such file or directory (os error 2)` |
| `boundaries::serial_capture::a_regular_file_is_rejected_without_changing_it` | `boundaries::a_regular_file_is_rejected_without_changing_it` | Unchanged |
| `boundaries::serial_capture::the_byte_limit_is_exact_and_never_discards_unread_input` | `boundaries::the_byte_limit_is_exact_and_never_discards_unread_input` | Unchanged; a deadline of 120 s in place of 1 s |
| `boundaries::serial_capture::the_preview_is_bounded_separately_from_the_raw_capture` | `boundaries::the_preview_is_bounded_separately_from_the_raw_capture` | Unchanged; a deadline of 120 s in place of 1 s |
| `boundaries::serial_capture::the_command_line_requires_one_mode_and_valid_limits` | `boundaries::the_command_line_requires_one_mode_and_valid_limits` | Unchanged status 2 and bound messages. Changed: the errors are clap's, told by their kinds, `MissingRequiredArgument` for no mode and `ArgumentConflict` for both, with clap's usage on standard error; rows added for `--port` before `--list` and for limits out of bounds with `--list` |
| `boundaries::serial_capture::the_receipt_keeps_non_ascii_text_as_utf8` | `boundaries::the_receipt_keeps_non_ascii_text_as_utf8` | Unchanged port fields, the DEL in the port field included. Changed: the open error names the port in Rust's debug form, which writes a DEL `\u{7f}`, and the receipt holds no JSON `\uXXXX` escape in place of no `\u` at all |
| `boundaries::serial_capture::a_failed_write_makes_the_exit_status_120` | `boundaries::a_failed_write_makes_the_exit_status_120` | Unchanged statuses and counts of writes. Changed: the reports are `cargo xtask serial-capture: cannot write standard output: Broken pipe (os error 32)` and `... Input/output error (os error 5)` |
| `boundaries::serial_capture::other_numerics_and_overlong_literals_are_invalid_values` | `boundaries::other_numerics_and_overlong_literals_are_refused` | Changed: characters other than ASCII digits are invalid values, usage errors of clap as above, also after more digits than 64 bits hold; a `--max-bytes` literal is read whatever its length, so 4300 zeros followed by `1` read 1, 4301 zeros read 0 and fail the bound, and a value beyond 64 bits fails the bound; each value follows `=` |
| `resources::serial_capture::raw_hash_preview_and_restoration` | `resources::raw_hash_preview_and_restoration` | Unchanged digest and fields. Changed: the preview `CAS`, U+039E, `\r`, newline, `\0`, `\u{1b}[2J`, U+FFFD; a deadline of 120 s in place of 1 s |
| `resources::serial_capture::no_data_is_neither_boot_failure_nor_success` | `resources::no_data_is_neither_boot_failure_nor_success` | Unchanged values. Changed procedure: no board script; the upper bound of 1 s on `elapsed_seconds` is gone, the lower bound of 0.03 s stays |
| `resources::serial_capture::queued_input_is_preserved_and_the_port_is_read_only` | `resources::queued_input_is_preserved_and_the_port_is_read_only` | Unchanged capture, with a deadline of 120 s in place of 1 s. Changed: that nothing reached the board is read from the master after the capture, in place of a board script during it; the refused open is `"<slave>": Permission denied (os error 13)`, checked unless the test runs as root, which permissions do not restrict |
| `resources::serial_capture::an_interrupted_capture_restores_the_port_and_records_its_receipt` | `resources::an_interrupted_capture_restores_the_port_and_records_its_receipt` | Unchanged outcome. Changed: a deadline of 120 s in place of the default 30 s, so `requested_seconds` is `120.0`; `receipts::the_receipt_has_its_keys_and_values` checks the default, `30.0` |
| `resources::serial_capture::the_end_of_the_stream_ends_the_capture` | `resources::the_end_of_the_stream_ends_the_capture` | Split by host. On Darwin unchanged: `NO_DATA`, `end_of_stream`, attributes restored. Linux hangs the slave up when its master closes: a read fails with `EIO` until the hang-up completes and reads empty after it, and every terminal request after it fails with `EIO`, so the capture is `FAIL` with errors that each end with `Input/output error (os error 5)`. The upper bound of 20 s on the run is gone |
| `resources::serial_capture::an_interrupt_before_the_port_opens_leaves_it_alone` | `resources::an_interrupt_before_the_port_opens_leaves_it_alone` | Unchanged |
| `resources::serial_capture::the_handlers_are_installed_immediately_before_the_port_opens` | `resources::the_handlers_are_installed_immediately_before_the_port_opens` | Changed: `"<dir>": File exists (os error 17)`, `"/nonexistent/krepi-port": No such file or directory (os error 2)` and `Invalid argument (os error 22)` |
| `resources::serial_capture::an_interrupted_command_prints_its_receipt_and_exits_with_130` | `resources::an_interrupted_command_prints_its_receipt_and_exits_with_130` | Unchanged output and status. Changed: `--seconds 120` in place of the default 30 s, so `requested_seconds` is `120.0`, as above |
| `resources::serial_capture::a_signal_once_the_port_is_open_is_caught_and_the_port_restored` | `resources::a_signal_once_the_port_is_open_is_caught_and_the_port_restored` | Unchanged; a deadline of 120 s in place of 20 s |
| `resources::serial_capture::a_signal_before_the_port_opens_ends_the_process` | `resources::a_signal_before_the_port_opens_ends_the_process` | Unchanged; the output directory that cannot hold `raw.bin` is left out when the test runs as root, which permissions do not restrict |
| `resources::serial_capture::a_signal_once_the_capture_has_ended_is_caught` | `resources::a_signal_once_the_capture_has_ended_is_caught` | Unchanged |
| `resources::serial_capture::a_failed_write_of_raw_bin_ends_the_capture_in_that_read` | `resources::a_failed_write_of_raw_bin_ends_the_capture_in_that_read` | Changed: `File too large (os error 27)`; a deadline of 120 s, and no upper bound of 10 s on the run |
| `resources::serial_capture::a_write_past_a_file_size_limit_ends_the_process_by_its_signal` | `resources::a_write_past_a_file_size_limit_ends_the_process_by_its_signal` | Unchanged; a deadline of 120 s in place of 20 s |
| `receipts::serial_capture::the_receipt_has_the_python_keys_and_values` | `receipts::the_receipt_has_its_keys_and_values` | Unchanged keys and fields. Changed: `requested_seconds` is `30.0` for the default, `1.0` for `--seconds 1` and `0.00001` for `--seconds 1e-5`, and the time stamps have six fraction digits. The live capture has a deadline of 120 s in place of 1 s, which its `requested_seconds` records |
| `receipts::serial_capture::the_command_prints_the_preview_status_and_receipt` | `receipts::the_command_prints_the_preview_status_and_receipt` | Changed: the preview as above; the first run has a deadline of 120 s in place of 1 s, and the quiet run has no board script |
| `receipts::serial_capture::the_help_is_the_argparse_help_for_80_columns` | `receipts::the_help_lists_the_options_and_their_defaults` | Changed: clap's help in place of the text of argparse, which the test no longer compares as a whole: it starts with the command's description, holds the usage line `Usage: cargo xtask serial-capture`, lists the seven options one to a line and gives the defaults `[default: 30]` and `[default: 262144]`; `-h`, `--help` and `--port p -h` print the same help |
| `receipts::serial_capture::the_help_and_the_usage_keep_their_text_on_a_terminal` | `receipts::the_help_and_the_usage_keep_their_text_on_a_terminal` | Changed: clap's help and usage error in place of the texts of argparse, wrapped for 80 columns; the expected text is what the command writes into a buffer in the test process, which holds the usage line, in place of a fixed text. `CLICOLOR_FORCE` joins the colour variables, and the text holds no ESC byte |
| `receipts::serial_capture::the_default_output_is_a_new_run_below_the_root` | `receipts::the_default_output_is_a_new_run_below_the_root` | Unchanged |
| `receipts::serial_capture::the_list_filters_usb_candidates_without_opening_them` | `receipts::the_list_filters_usb_candidates_without_opening_them` | Unchanged order; ESC in a name is rendered `\u{1b}` |
| `xtask/tests/serial_capture.rs` `an_argument_that_is_not_utf8_ends_the_process_before_the_command_runs` | Same file, same name | Changed: exit status 101 without a signal, in place of SIGABRT |
| `xtask/tests/serial_capture.rs` `a_closed_stream_moves_no_text_to_the_other` | Same file, same name | Unchanged statuses and streams. Changed: the help holds clap's usage line `Usage: cargo xtask serial-capture` in place of starting with that of argparse |
| `xtask/tests/serial_capture.rs` `a_stream_whose_reader_has_gone_makes_the_exit_status_120` | Same file, same name | Changed: the report `cargo xtask serial-capture: cannot write standard output: Broken pipe (os error 32)` |
| `xtask/tests/serial_capture.rs` `the_help_and_the_usage_keep_their_text_on_a_pipe` | Same file, same name | Changed: the help and the usage error hold clap's usage line in place of starting with that of argparse; `CLICOLOR_FORCE` joins the colour variables, and the text holds no ESC byte |
| `xtask/tests/serial_capture.rs` `the_command_runs_outside_a_python_environment` | `the_command_runs_with_an_empty_environment_outside_the_repository` | Unchanged statuses. Changed: the help holds clap's usage line in place of starting with that of argparse |

New tests: `tests::a_partly_written_read_counts_what_raw_bin_holds`, a write of
`raw.bin` that takes three bytes of a read and then fails;
`boundaries::the_command_line_takes_the_seven_options`, the options that
clap reads with the settings of this module: their values and defaults, a
repeated option, the help after other options, a negative number for a
limit, and a usage error for a prefix of an option, an option or a word
that the command does not have, such as `--version`, an option without its
value and a value for `--list`; `boundaries::an_output_directory_that_cannot_be_created_is_named`,
output directories below a regular file and below a symbolic link to
nothing; and
`resources::the_quiet_capture_passes_at_the_lowest_priority`, which runs
`resources::no_data_is_neither_boot_failure_nor_success` alone in a child of
the test binary under `nice -n 19`, or on macOS under
`taskpolicy -c background`, and passes when the child reports the one test
as passed.

The legacy tests ran on Darwin only. The expected texts above hold on
Darwin and on Linux, where the error numbers that they name have the same
number and text, except where the table splits a test by host.

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| Options | Unique prefixes, `-h` joined to further short options, `--` ending the options, values that look like negative numbers or hold a space, `ignored explicit argument`, `ambiguous option` | clap's rules: whole option words, no prefixes; a value after `=` or as the next argument, unless that starts with `-` and is no negative number for `--seconds` or `--max-bytes`; a repeated option keeps its last value; anything else is an unexpected argument | `boundaries::the_command_line_takes_the_seven_options`; the other rules are clap's |
| An invalid value | `argument --seconds: invalid float value: 'abc'`, `argument --max-bytes: invalid int value: '1.5'` | `invalid value 'abc' for '--seconds <SECONDS>': invalid float literal`, `invalid value '1.5' for '--max-bytes <MAX_BYTES>': not a decimal integer`, the value as given, with no character escaped | `properties::option_values_are_read_as_rust_numbers`, `boundaries::the_command_line_takes_the_seven_options`; the texts are clap's |
| The help | The help of argparse wrapped for 80 columns: `usage: cargo xtask serial-capture [-h] (--list \| --port PORT)` over three lines, the description, `options:` and the option texts | The help of clap, not wrapped, with lines of up to 95 columns: the description, `Usage: cargo xtask serial-capture [OPTIONS] <--list\|--port <PORT>>`, `Options:`, the same option texts with `[default: 30]` and `[default: 262144]`, and `Print help` for `-h, --help`; the same for `-h` and `--help` | `receipts::the_help_lists_the_options_and_their_defaults`; the text is clap's |
| A usage error | The usage, then `cargo xtask serial-capture: error: <message>`, such as `one of the arguments --list --port is required` or `argument --port: not allowed with argument --list` | `error: <message>`, the usage for most errors and `For more information, try '--help'.`, such as `the following required arguments were not provided:` or `the argument '--list' cannot be used with '--port <PORT>'`; a limit out of bounds keeps its bound as the message | `boundaries::the_command_line_requires_one_mode_and_valid_limits`; the texts are clap's |
| The order of usage errors | The arguments in order: a value that cannot be read, an option without a value and the second mode stop the reading where they are read, and a help option prints the help where it is read, also after an unrecognized argument; then a missing mode comes before unrecognized arguments, and the limits come last | The arguments in order: an unexpected argument, a value that cannot be read and an option without a value stop the reading where they are read, and a help option prints the help where it is read, also after both modes, but not after an unexpected argument; then both modes or a missing mode, and the limits last | `boundaries::the_command_line_requires_one_mode_and_valid_limits` for the limits, `boundaries::the_command_line_takes_the_seven_options` for the help after both modes; the rest is clap's |
| Numbers | Python's `float` and `int`: surrounding white space, underscores between digits, the decimal digits of every script | Rust's `f64` and `u64`: none of these | `properties::option_values_are_read_as_rust_numbers`, `boundaries::other_numerics_and_overlong_literals_are_refused` |
| A long `--max-bytes` literal | More than 4300 digits, leading zeros included, is an invalid value | Read whatever its length; beyond 64 bits it fails the bound | `boundaries::other_numerics_and_overlong_literals_are_refused` |
| `requested_seconds` | `30` for the default, `1e-05` for `--seconds 1e-5` | `30.0`, `0.00001`; always a number with a fraction | `receipts::the_receipt_has_its_keys_and_values` |
| `started_at` and `finished_at` | No fraction when it is zero | Six fraction digits | `receipts::the_receipt_has_its_keys_and_values` |
| Text on a terminal | Python's category C of Unicode 16.0 as `\xNN` or `\uNNNN`; separators and default-ignorable letters kept | `str::escape_debug` per run between kept characters, as `\u{1b}`, `\r`, `\0`; white space other than the space and default-ignorable characters escaped | `properties::the_preview_escapes_controls_and_unprintable_characters`, `resources::raw_hash_preview_and_restoration`, `receipts::the_command_prints_the_preview_status_and_receipt` |
| A name byte that is not UTF-8 | `\udcNN`, the surrogate of Python's decoding | `\xNN` | `properties::undecodable_name_bytes_are_rendered_as_hex_escapes` |
| The order of `--list` | Code points of Python's decoding | Bytes of the names; the same for UTF-8 names | `receipts::the_list_filters_usb_candidates_without_opening_them` |
| Error about a file or port | `[Errno 17] File exists: '/x'` | `"/x": File exists (os error 17)` | `boundaries::an_existing_output_directory_is_never_overwritten`, `boundaries::an_invalid_port_emits_a_failure_receipt` |
| A DEL in an error | `\x7f`, as Python's `repr` writes it | `\u{7f}`, as Rust's debug form writes it | `boundaries::the_receipt_keeps_non_ascii_text_as_utf8` |
| An output path with two leading slashes | Kept, as `PurePosixPath` keeps them | One slash | `boundaries::an_existing_output_directory_is_never_overwritten`, `tests::an_output_path_is_normalized_by_its_components` |
| A missing parent of the output directory that cannot be created | The missing ancestor whose creation failed is named | The parent of the output directory, the path that `create_dir_all` was given, is named | `boundaries::an_output_directory_that_cannot_be_created_is_named` |
| A failed write on standard output | `Exception ignored while flushing sys.stdout:` and the exception, such as `BrokenPipeError: [Errno 32] Broken pipe`; status 120 | `cargo xtask serial-capture: cannot write standard output: Broken pipe (os error 32)`; status 120 | `boundaries::a_failed_write_makes_the_exit_status_120`, `a_stream_whose_reader_has_gone_makes_the_exit_status_120` of `xtask/tests/serial_capture.rs` |
| An argument that is not UTF-8 | The panic of `std::env::args` aborts the process, SIGABRT | The panic ends the process with status 101 | `an_argument_that_is_not_utf8_ends_the_process_before_the_command_runs` of `xtask/tests/serial_capture.rs` |
| Bytes written before a write of `raw.bin` fails | Left in the file and not counted, so that `raw.bin` was longer than `bytes` | Counted in `bytes`, `sha256` and the preview | `tests::a_partly_written_read_counts_what_raw_bin_holds` |

The legacy module documented the following rules as differences from the
Python script that it replaced, and its tests recorded two more. Each rule
is kept, apart from the changes in the table above, and fixed by a test:

| Rule | Test |
| --- | --- |
| SIGINT, SIGTERM and SIGHUP are caught from immediately before the port opens | `resources::the_handlers_are_installed_immediately_before_the_port_opens`, `resources::an_interrupt_before_the_port_opens_leaves_it_alone` |
| SIGTERM and SIGHUP, like SIGINT, end the capture as `INTERRUPTED` with the port restored and the receipt written | `resources::an_interrupted_capture_restores_the_port_and_records_its_receipt`, `resources::an_interrupted_command_prints_its_receipt_and_exits_with_130`, `resources::a_signal_once_the_port_is_open_is_caught_and_the_port_restored` |
| The handlers replace an inherited `SIG_IGN` | `tty::tests::a_signal_inherited_ignored_is_caught`, `resources::a_signal_once_the_port_is_open_is_caught_and_the_port_restored` |
| Before the port opens, the three signals keep the dispositions that the process started with | `resources::a_signal_before_the_port_opens_ends_the_process` |
| A signal caught once the capture has ended leaves the outcome as it is | `tests::an_interrupt_once_the_capture_has_ended_leaves_the_outcome`, `resources::a_signal_once_the_capture_has_ended_is_caught` |
| The capture always takes `TIOCEXCL` and releases it with `TIOCNXCL` | `tty::tests::a_receiver_opens_read_only_without_a_lock`, `tty::tests::a_receivers_failed_tiocexcl_fails_the_configuration`, `resources::raw_hash_preview_and_restoration` |
| The receipt holds non-ASCII text as UTF-8 | `boundaries::the_receipt_keeps_non_ascii_text_as_utf8` |
| A DEL stays as it is in the port field of the receipt | `boundaries::the_receipt_keeps_non_ascii_text_as_utf8` |
| `raw.bin` is written unbuffered, and a failed write is an error of the capture in the read that fails | `tests::a_failed_write_of_the_capture_fails_the_receipt`, `resources::a_failed_write_of_raw_bin_ends_the_capture_in_that_read` |
| A write past a file-size limit raises SIGXFSZ, whose default action ends the process without a receipt and with the port left raw | `resources::a_write_past_a_file_size_limit_ends_the_process_by_its_signal` |
| The usage and the help name the command `cargo xtask serial-capture` | `receipts::the_help_lists_the_options_and_their_defaults`, `boundaries::the_command_line_requires_one_mode_and_valid_limits` |
| The help and the usage keep their text whatever `COLUMNS` or the window say; they are no longer wrapped for 80 columns, see the table above | `receipts::the_help_and_the_usage_keep_their_text_on_a_terminal`, `the_help_and_the_usage_keep_their_text_on_a_pipe` of `xtask/tests/serial_capture.rs` |
| The help and the usage are never coloured, also with `FORCE_COLOR`, `PYTHON_COLORS` or `CLICOLOR_FORCE` set | The same two tests |
| A failed write on an output stream is reported once, on standard error, and the status is 120 | `boundaries::a_failed_write_makes_the_exit_status_120`, `a_stream_whose_reader_has_gone_makes_the_exit_status_120` of `xtask/tests/serial_capture.rs` |
| No `UART capture failed` line follows a capture whose output failed | `boundaries::a_failed_write_makes_the_exit_status_120` |
| Nothing is written on a closed stream, and no text moves to the other stream | `a_closed_stream_moves_no_text_to_the_other` of `xtask/tests/serial_capture.rs`, `boundaries::a_failed_write_makes_the_exit_status_120` |
| An argument that is not UTF-8 ends the process before the command runs | `an_argument_that_is_not_utf8_ends_the_process_before_the_command_runs` of `xtask/tests/serial_capture.rs` |
| The command has no condition on its environment | `the_command_runs_with_an_empty_environment_outside_the_repository` of `xtask/tests/serial_capture.rs` |
| The bytes that reach `raw.bin` before a failed write are the bytes of the receipt | `tests::a_partly_written_read_counts_what_raw_bin_holds`, `resources::a_failed_write_of_raw_bin_ends_the_capture_in_that_read` |

## Hardware evidence to re-obtain

The legacy command captured the UART of a Raspberry Pi 5 through a USB
serial adapter on the development host: the listing of the adapter, an
exclusive read-only open with raw 115200 8N1 attributes, the bytes of a
boot with their receipt, and the restored attributes. krepi obtains such a
capture again with its own image on the HIL bench (planned), with the bench
configuration of the firmware and lab registry (planned).

## Not carried over

- The argparse rules of the command line: `classify`, `short_help`, `Token`,
  `Match`, the negative-number pattern, and the messages `ignored explicit
  argument` and `ambiguous option`; with them the test
  `boundaries::serial_capture::the_command_line_follows_argparse`, whose
  rules are gone. clap reads the command line by its own rules, and
  `boundaries::the_command_line_takes_the_seven_options` fixes the settings
  of this module.
- The texts of argparse: the help, the usage and the messages of a usage
  error, which the legacy module wrote out. clap writes these texts, and its
  own tests cover them; the tests here look for the parts that this module
  gives them, such as the description, the options, the defaults and the
  bound messages.
- Python's reading of numbers: `python_float`, `python_int`, `ascii_number`,
  `strip_number`, `decimal`, `is_decimal`, the limit of 4300 digits and the
  type `Seconds`; with them the tests
  `properties::serial_capture::decimal_digits_of_every_script_are_read_as_python_reads_them`,
  two of whose values join `properties::option_values_are_read_as_rust_numbers`
  as invalid values, and
  `properties::serial_capture::exactly_the_unicode_16_decimal_digits_are_read`.
  The legacy module took `is_space` of `tools/src/python_text.rs`, with its
  test `tests::is_space_matches_python_isspace`, and `py_int` and `repr` of
  `tools/src/suites/platform/pi5_boot.rs`, with its tests
  `tests::integers_parse_as_cpython_parses_them`,
  `tests::a_literal_beyond_128_bits_is_rejected` and
  `tests::text_beyond_ascii_is_an_invalid_literal`, for this reading; they
  are not ported, and krepi's rule for long literals is fixed by
  `boundaries::other_numerics_and_overlong_literals_are_refused`.
- The rendering by Python's category C of Unicode 16.0, `other` and
  `escape`, which `fancy-regex` decided, the surrogate form of
  `sanitize_name` and the order `decoded`; with them the test
  `properties::serial_capture::exactly_the_unicode_16_category_c_is_rendered`.
  The escaped set is the standard library's.
- `exception`, the class name of the Python exception of a failed write, and
  the report of Python's failed flush; with them the test
  `tests::a_failed_write_is_named_as_python_names_it`.
- `posix_path`, which kept two leading slashes of an output path.
- `json::parse` of `tools/src/json.rs`, with which the legacy tests read
  receipts, and its tests `tests::documents_round_trip`,
  `tests::the_grammar_is_rfc_8259` and
  `tests::repeated_keys_are_rejected_when_their_object_closes`: the tests
  read JSON with `serde_json`, whose own tests cover it, and a receipt
  written from a `serde_json` object cannot repeat a key.
- The test support that these tests do not use: `ptr!`, `JsonExt` and the
  JSON helpers of `tools/tests/support/json.rs`, the needle assertions and
  table macro of `tools/tests/support/rejection.rs`, whose exact assertion
  is a helper of the test module, the line-by-line wait `await_line` of
  `tools/tests/support/child.rs`, the repository copies of
  `tools/tests/support/scratch.rs`, and the bounds `CHILD_WAIT` and
  `SCRIPT_WAIT`, which `TEST_WAIT` replaces.
- The upper bounds of the legacy tests on the time of a capture, 1 s, 10 s
  and 20 s.
- The module documentation's account of the Python script and of
  CPython 3.14.8, which recorded the values of the legacy tests.
