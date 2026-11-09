---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/qemu.rs
  - tools/src/probe.rs
  - tools/src/suites/platform/kernel_serial.rs
  - tools/src/tty.rs
  - tools/tests/kernel/user_execution.rs
  - tools/tests/platform/physical_entry.rs
  - tools/tests/platform/qemu_boot.rs
destination:
  - tools/src/qemu.rs
  - tools/src/qemu/tests.rs
treatment: ported
features: none
---

# Porting record: tools/src/qemu.rs

## Summary

The QEMU virt command, the guest check and the serial capture of a guest,
with the process helpers. `Clock`, `resolve_qemu`, `build_command` and
`version` give the command line of a guest on QEMU virt and the QEMU that
runs it; `spawn` and `spawn_with_stderr` start it. `Guest` is the far end of
a capture, which tells whether the guest is still there; a QEMU process is
one. `SerialCapture` keeps everything that a guest wrote, matches each phase
of a check from an offset of its own with the matchers of
[`receipt`](tools-receipt.md), sends input, and collects the diagnostics
that follow a failure. It reads the standard streams of a QEMU process, as
a plain capture or a guarded one that bounds the output, rejects fatal
records and writes its log only once the guest has stopped; or, through
`from_tty`, a board's serial port held by the transport of
[`tty`](tools-tty.md), with the rules of a board session. The process
helpers drain an output stream of a child (`spawn_reader`), tell how a
process ended (`exit_code`) and stop a child with a report of how it ended
(`stop_process`). The command `cargo xtask qemu`, in the new module
`tools/src/qemu_run.rs`, runs an image with this command line, a guarded
capture of the QEMU process and the process helpers. That module is new
code, not taken from the legacy tree, and
[testing](../conventions/testing.md#entry-points) describes the command.

The whole module is ported with its tests and with the tests of the legacy
integration tests that tested it: those of the board serial capture, of the
guarded capture and of the clock. The legacy module reproduced the QEMU
launcher and the serial receivers of Python programs; its documentation
named them, its limit text had the two casings of two Python programs, and
its timeout and error texts were Python's. These forms are not carried
over; see [Changes](#changes).

## Changes

- The machine is `virt-8.2`, a versioned machine type that QEMU 8.2 and its
  later versions provide alike, in place of `virt`, which names another
  machine version on each QEMU release; the options of the machine are
  unchanged.
- The command has `-nic none` before `-display`: the guest has no network
  card. The default network card of `virt` loads an option ROM, which an
  installation of QEMU without its recommended packages may lack.
- `resolve_qemu` takes the executable as an argument, the value of the
  `--qemu` option of the QEMU runner, in place of reading the variable
  `QEMU_SYSTEM_AARCH64`; without one it looks for `qemu-system-aarch64`, and
  a name without a `/` is looked for on the search path, as before. A
  refusal names it in Rust's debug form and points to the option:
  `QEMU executable not found or not executable: "<name>". Install
  qemu-system-aarch64 or pass its path with --qemu.`
- `version` gives the first line of the output of `--version`, without the
  white space around it, as its documentation said; the legacy code kept
  the whole output, which has a copyright line too.
- The guest check of a QEMU process names how the process ended with the
  standard library's text of its exit status, `exit status: 3` or
  `signal: 15 (SIGTERM)`, or `still running` for a process whose output
  ended first: `QEMU exited or closed serial output early (exit status: 3)`,
  in place of `(exit=3)`, `(exit=-15)` and `(exit=None)` with the legacy
  exit code.
- A failed write of the log of a board capture ends the session with the
  standard library's text of the error, `Bad file descriptor (os error 9)`,
  in place of Python's `[Errno 9] Bad file descriptor`.
- Output past the limit of a capture fails with one text that names the
  limit, `serial output exceeded <limit> bytes`, and in the cleanup of a
  guarded capture `serial output exceeded <limit> bytes during cleanup`. The
  legacy texts named a fixed 256 KiB whatever the limit was, a board
  capture's in lower case and a guarded capture's with a capital, as the two
  Python programs that they reproduced wrote them.
- A timeout is written by `seconds_text`, the seconds of a `Duration` as
  Rust writes an `f64`, in place of `format_seconds`, which took seconds as
  an `f64` and whose documentation named Python's `%g`. The text is the
  same for every duration: `8`, `2.5`, `0.01`, `0.00001`.
- The constructors of `SerialCapture` take a `Timing`
  (`tools/src/timing.rs`), from which the capture takes its waits in place
  of constants: `guest_slice` for one look of `wait_for` and of the failure
  tail (legacy 100 ms), `guest_idle` for the time a boundary may keep
  receiving (250 ms), and `guest_finish` and `guest_finish_slice` for the
  final collection of `finish` and `finish_guarded` (1 s and 50 ms).
  `from_tty` passes the timing on to the port's reader and writer.
- `Clock::name` gives the name that `Clock::parse` reads, and
  `SerialCapture::ended` tells whether the stream has ended, for the QEMU
  runner, which records the clock and waits without reading once the
  output of QEMU has ended.
- `collect_failure` takes the length of the tail as a `Duration`, more than
  zero and at most 120 s, in place of seconds as an `f64` with a check that
  also refused NaN; the message `invalid diagnostic capture duration` is
  kept. Its result is a `serde_json` value with the keys `additional_bytes`,
  `elapsed_seconds` and `terminal_halt` in that order.
- A wait whose end lies beyond the range of the clock has no end of its own
  and lasts until the guest ends it; the legacy arithmetic panicked on it.
- The failure text of a board capture whose output holds a fatal record is
  a named constant beside that of a guarded capture; both texts are kept.
- The documentation describes the capture and the rules of a board capture.
  It no longer names the Python runner whose command line the module
  reproduced, nor the Python receivers whose forms the plain, guarded and
  board captures took, and the contradictory documentation of
  `spawn_with_stderr`, which said both that QEMU's standard error joined the
  serial output and that it went to its own file, says the latter.
- `exit_code` returns the code a process exited with and the number of the
  signal that ended it, of which exactly one is given, in place of one number
  in the convention of Python's `Popen.returncode`, which gave a signal as
  its negative.
- The report of `stop_process` gives the two values as `exit_code` and
  `signal`, each null when it does not apply, and both null when the process
  has not ended within the wait after the kill. It is a `serde_json` value
  with the keys `intentional_shutdown`, `forced_kill`, `exit_code` and
  `signal` in that order.
- `spawn_reader` repeats a read that a caught signal interrupted, where the
  legacy reader ended the stream at any failed read. The interrupt handlers
  of `cargo xtask qemu`, which do not restart calls, make a read that is
  blocked when a signal reaches the reader's thread fail with `EINTR`, which
  would have dropped the rest of QEMU's output.
- `stop_process` takes a `Timing`: it waits `stop_grace` after SIGTERM and
  `kill_grace` after the kill, and looks at the process every `reap_poll`,
  in place of the constants 1 s, 1 s and 10 ms.
- The variants of `executable`, `exit_code` and `terminate` for hosts other
  than Unix are removed, as the crate builds on Unix hosts only, and with
  them the `allow` of unsafe code. `terminate` converts the process number
  with a check, and `wait_with_timeout` does not overflow the time at which
  it gives up.
- The tests are unit tests in `tools/src/qemu/tests.rs`, below
  `qemu::tests`, with the submodules `properties`, `boundaries` and
  `resources` of the legacy integration tests; the groups of the board
  serial capture are merged into the last two. The board guest `Board` of
  the legacy `tools/src/tty.rs`, which is not ported, gives way to a test
  guest with its rules: an interrupt flag that holds a signal ends the
  session with `interrupted`, and a stream that has ended ends it with the
  error that the port's reader recorded, or `serial device closed`. The
  fixture's session lasts 120 s in place of 5 s, a test waits for bytes at
  most 60 s in place of 1 or 2 s, and a failure tail that ends at
  `CASXI_HALTED` or at an error has 120 s, the longest tail, in place of
  1 s. The limit of 256 KiB and the fatal records of the legacy
  `tools/src/probe.rs`, and the fatal records of a board session of the
  legacy `tools/src/suites/platform/kernel_serial.rs`, are test constants.
  The test-only module `tools/src/pty.rs` gives a board script a read of the
  bytes that the port sent and lets a test wait until the device has hung
  up, and it holds the host checks for a second open of a held terminal,
  which the tests of `tty` and of this module share; `tools/src/scratch.rs`
  writes a fake QEMU, a shell script, and waits until it can be run.

## Tests carried over

The legacy unit tests are in `tools/src/qemu.rs` below `tests`; the legacy
tests of the board serial capture are in
`tools/tests/platform/physical_entry.rs` below
`<group>::board_serial`. The krepi tests are in `tools/src/qemu/tests.rs`
below `qemu::tests`. Expected values that changed are listed under
[Behaviour changes](#behaviour-changes) as well.

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/qemu.rs` `tests::command_follows_the_fixed_profile` | `qemu::tests::the_command_follows_the_fixed_profile` | Changed: the whole argument vector is compared for both clocks, with `virt-8.2` and `-nic none`, where the legacy test checked the executable, the accelerator, the clock and the image. A missing image fails with `ELF image not found: <path>. Build the image first.`, where the legacy test required a failure; a row added: a directory is refused with the same message for its canonical path. The files are in a scratch directory below the build directory in place of the system temporary directory |
| `tools/src/qemu.rs` `tests::seconds_format_like_python_g` | `qemu::tests::a_timeout_is_written_in_seconds` | Unchanged: `8` and `2.5`. Rows added: `0.01`, `0.00001` and `10000000000000000`, which the legacy function wrote the same way, where Python's `%g` writes `1e-05` and `1e+16` |
| `tools/tests/platform/qemu_boot.rs` `properties::clock_choice_does_not_change_tcg_threading` | `qemu::tests::properties::clock_choice_does_not_change_tcg_threading` | Unchanged; a scratch directory in place of the system temporary directory |
| `tools/tests/kernel/user_execution.rs` `properties::guarded_capture_defers_log_io_and_rejects_fatal_output` | `qemu::tests::properties::guarded_capture_defers_log_io_and_rejects_fatal_output` | Unchanged: the output `READY\nDONE\n`, the empty log before the guest stopped and the log equal to the output after it, and `Kernel fault or halt during EL0 validation`. The stop report must show that the shell ended by itself or by SIGTERM without a kill, where the legacy test only required the key `exit_code`. Added: a second `write_deferred_log` and `finish_guarded` write nothing more, and the log of the fatal capture equals its output. The waits are 60 s in place of 5 s |
| `boundaries::board_serial::fatal_split_across_reads_is_retained_and_rejected` | `qemu::tests::boundaries::fatal_split_across_reads_is_retained_and_rejected` | Unchanged |
| `boundaries::board_serial::output_is_bounded_at_limit_plus_one` | `qemu::tests::boundaries::output_is_bounded_at_limit_plus_one` | Changed: `serial output exceeded 8 bytes`. Unchanged: the output and log `012345678`, and `serial device closed` in the failure tail on every host, as the stream ends by the limit while the device is open; the tail has 120 s in place of 1 s |
| `boundaries::board_serial::boundary_stops_at_a_guard_error` | `qemu::tests::boundaries::boundary_stops_at_a_guard_error` | Unchanged: `boundary` fails with the fatal text and leaves the later output unread. Changed procedure: in place of four lines sent 100 ms apart through the port, so that each would arrive in a read of its own, the fatal line comes through the port and three lines are then handed to the capture through a channel of the test, so that three reads wait for the boundary on every host; `boundary` takes exactly the first of them, which the log holds too |
| `boundaries::board_serial::a_checked_read_fails_in_the_read_that_finds_a_failure` | `qemu::tests::boundaries::a_checked_read_fails_in_the_read_that_finds_a_failure` | Unchanged fatal text; changed: `serial output exceeded 8 bytes`. Split by host for the closed device: Darwin reads the slave empty, `serial device closed`; Linux hangs the slave up, and the port's reader either fails a read that is under way with `Input/output error (os error 5)`, which it records, or reads empty once the hang-up has completed, as scheduling decides, so the test accepts either with the recorded error |
| `boundaries::board_serial::a_failed_log_write_ends_the_session` | `qemu::tests::boundaries::a_failed_log_write_ends_the_session` | Changed: `Bad file descriptor (os error 9)` on every host; the log stays empty. The tail has 120 s in place of 1 s |
| `boundaries::board_serial::deadline_and_request_bound` | `qemu::tests::boundaries::deadline_and_request_bound` | Unchanged: `invalid serial request size` twice, `Expected serial response not received within 0.01s` and `serial session closed or exceeded total deadline` |
| `boundaries::board_serial::open_and_write_errors_and_a_closed_device_keep_the_python_text` | `qemu::tests::boundaries::open_and_write_errors_and_a_closed_device_are_reported` | Changed: `"/nonexistent/krepi-board": No such file or directory (os error 2)`, and for a name with a single quote `"/nonexistent/krepi-board's": ...`, where the legacy text switched to double quotes; `selected port is not a tty` unchanged. A request once the board end has closed fails with `Input/output error (os error 5)` on every host, with the record `[("3a", 0)]` unchanged; the test waits until the device has hung up before it sends, as a process that another test starts can keep the master open for a moment. Split by host for the end of the stream, as in the row above, with the recorded error; the log `boot\r\n` unchanged |
| `boundaries::board_serial::a_second_open_of_a_held_port_is_refused` | `qemu::tests::boundaries::a_second_open_of_a_held_port_is_refused` | Split by host. Where the kernel refuses a new open of a terminal held with `TIOCEXCL`, Linux without `CAP_SYS_ADMIN` such as the CI user: `"<slave>": Device or resource busy (os error 16)`. Elsewhere the lock refuses it: `Resource temporarily unavailable (os error 35)` on Darwin, `(os error 11)` on Linux. The rest is unchanged |
| `resources::board_serial::bidirectional_bytes_and_restoration` | `qemu::tests::resources::bidirectional_bytes_and_restoration` | Unchanged, with `PENDIN` left out of the comparison of the attributes on every host |
| `resources::board_serial::pcie_initialization_failure_keeps_split_diagnostics` | `qemu::tests::resources::pcie_initialization_failure_keeps_split_diagnostics` | Unchanged; the tail, which `CASXI_HALTED` ends, has 120 s in place of 1 s |
| `resources::board_serial::rp1_mmio_failure_keeps_split_diagnostics` | `qemu::tests::resources::rp1_mmio_failure_keeps_split_diagnostics` | As the row above |
| `resources::board_serial::failure_tail_keeps_the_fatal_tail_without_transmitting` | `qemu::tests::resources::failure_tail_keeps_the_fatal_tail_without_transmitting` | Unchanged, the keys in their order included; the tail has 120 s |
| `resources::board_serial::failure_tail_respects_its_limits` | `qemu::tests::resources::failure_tail_respects_its_limits` | Unchanged: `invalid diagnostic capture duration` for 121 s; a row added for a tail of no time. Changed: `serial output exceeded 8 bytes`, in a tail of 120 s in place of 1 s, which the limit ends |
| `resources::board_serial::a_checked_read_ends_at_the_session_deadline` | `qemu::tests::resources::a_checked_read_ends_at_the_session_deadline` | Unchanged values. Changed procedure: the session lasts 5 s in place of 1 s; the first read is given 120 s in place of 60 s and must end with the session, not before its end and within 60 s in place of 30 s. On a host that stalls past the end of the session before the first read starts, that read fails with the session's text as the second one does, which the test accepts as the end has passed then |
| `resources::board_serial::quiet_failure_tail_expires` | `qemu::tests::resources::quiet_failure_tail_expires` | Unchanged; a tail of 10 ms with nothing sent |
| `resources::board_serial::an_interrupt_flag_ends_the_board_session` | `qemu::tests::resources::an_interrupt_flag_ends_the_board_session` | Unchanged: `interrupted`, the record `[("40", 1)]`, and nothing more within 200 ms. The board waits for the request at most 60 s in place of 4 s, and so does the capture for the record that never comes |

New tests:

- `qemu::tests::a_child_guest_reports_how_it_ended`: a running process
  whose output is open is alive, one whose output has closed is still
  running, and one that exited names its exit status.
- `qemu::tests::the_version_is_the_first_line_of_the_version_output`: a
  fake QEMU prints the version line ending in `\r\n` and a copyright line,
  and a query that exits with 1 is refused.
- `qemu::tests::properties::a_guarded_capture_stops_at_its_limit`: output
  past the limit of a guarded capture, which keeps and logs the read that
  passed the limit whole, and output that passes it during the cleanup,
  which writes no log.
- `qemu::tests::boundaries::a_qemu_that_is_missing_or_not_executable_is_refused`:
  a missing file, a file without an execute bit, a directory, a name that
  the search path lacks and a name with quotes are refused; a fake QEMU is
  found at its canonical path, and the shell on the search path.
- `qemu::tests::boundaries::a_wait_beyond_the_range_of_the_clock_lasts_until_the_guest_ends`.
- `qemu::tests::boundaries::a_capture_of_a_process_ignores_a_failed_log_write`
  and
  `qemu::tests::boundaries::a_capture_of_a_process_drains_past_a_guard_error_until_idle`,
  the rules of a capture of a process beside those of a board capture. The
  second hands the output to the capture through a channel of the test, so
  that chunks wait for the boundary, and also fails a boundary at which the
  output keeps arriving for longer than the idle time.
- `qemu::tests::resources::an_interrupt_ends_the_failure_tail`: with the
  interrupt flag set once the fatal line is taken, a tail of 120 s ends at
  once with `interrupted`, without transmitting, and the port is restored.
- `qemu::tests::a_read_that_a_signal_interrupted_does_not_end_the_stream`:
  the reader of a child's output drains a stream whose reads give a chunk,
  two interrupted reads and a chunk, and keeps both chunks, and ends a
  stream at a read that fails with `EIO`. The stream's reads stand for the
  signal, so that none has to reach the reader's thread at the right moment.
- `qemu::tests::the_stop_report_gives_the_exit_code_or_the_signal` stops a
  child that has exited with code 3, a child that SIGTERM ends, and a child
  that ignores SIGTERM and is killed. The ignored disposition is set before
  the child prints a line that the test waits for, so that the test does
  not depend on scheduling.

The legacy tests of the board serial capture ran on Darwin only. The
expected texts above hold on Darwin and on Linux, where the error numbers
that they name have the same number and text, except where the table
splits a test by host.

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| The machine | `virt,secure=off,virtualization=off,gic-version=2` | `virt-8.2,secure=off,virtualization=off,gic-version=2` | `qemu::tests::the_command_follows_the_fixed_profile` |
| The network card | The default card of `virt` | None, `-nic none` | `qemu::tests::the_command_follows_the_fixed_profile` |
| The QEMU executable | `QEMU_SYSTEM_AARCH64` or the search path; `... not executable: 'x'. Install qemu-system-aarch64 or set QEMU_SYSTEM_AARCH64 to its path.` | The argument or the search path; `... not executable: "x". Install qemu-system-aarch64 or pass its path with --qemu.` | `qemu::tests::boundaries::a_qemu_that_is_missing_or_not_executable_is_refused` |
| The QEMU version | The whole output of `--version` | Its first line | `qemu::tests::the_version_is_the_first_line_of_the_version_output` |
| A QEMU process that has exited or closed its output | `QEMU exited or closed serial output early (exit=3)`, `(exit=None)` | `QEMU exited or closed serial output early (exit status: 3)`, `(still running)` | `qemu::tests::a_child_guest_reports_how_it_ended`, `qemu::tests::boundaries::a_wait_beyond_the_range_of_the_clock_lasts_until_the_guest_ends` |
| A failed log write of a board capture | `[Errno 9] Bad file descriptor` | `Bad file descriptor (os error 9)` | `qemu::tests::boundaries::a_failed_log_write_ends_the_session` |
| Output past the limit of a board capture | `serial output exceeded 256 KiB`, whatever the limit | `serial output exceeded 8 bytes` for a limit of 8 | `qemu::tests::boundaries::output_is_bounded_at_limit_plus_one`, `qemu::tests::boundaries::a_checked_read_fails_in_the_read_that_finds_a_failure`, `qemu::tests::resources::failure_tail_respects_its_limits` |
| Output past the limit of a guarded capture, and during its cleanup | `Serial output exceeded 256 KiB` and `... during cleanup`, whatever the limit | `serial output exceeded 8 bytes` and `... during cleanup` for a limit of 8 | `qemu::tests::properties::a_guarded_capture_stops_at_its_limit` |
| A wait whose end lies beyond the range of the clock | A panic | A wait until the guest ends it | `qemu::tests::boundaries::a_wait_beyond_the_range_of_the_clock_lasts_until_the_guest_ends` |
| A read of a child's output that a caught signal interrupted | Ends the stream | Is repeated | `qemu::tests::a_read_that_a_signal_interrupted_does_not_end_the_stream` |
| The stop report of a child that exited with code 3 | `exit_code: 3` | `exit_code: 3, signal: null` | `qemu::tests::the_stop_report_gives_the_exit_code_or_the_signal` |
| The stop report of a child that SIGTERM ended | `exit_code: -15` | `exit_code: null, signal: 15` | `qemu::tests::the_stop_report_gives_the_exit_code_or_the_signal` |
| The stop report of a child that SIGKILL ended | `forced_kill: true, exit_code: -9` | `forced_kill: true, exit_code: null, signal: 9` | `qemu::tests::the_stop_report_gives_the_exit_code_or_the_signal` |

The legacy module documented the following rules of its captures, the
board rules as differences from the Python program whose receiver a board
capture reproduced. Each rule is kept and fixed by a test:

| Rule | Test |
| --- | --- |
| Each read of the failure tail checks the guest, so that a caught interrupt ends the tail at once | `qemu::tests::resources::an_interrupt_ends_the_failure_tail` |
| The reads of a board capture keep at most one byte past the limit | `qemu::tests::boundaries::output_is_bounded_at_limit_plus_one` |
| Once a byte past the limit has arrived, the stream of a board capture counts as ended, the further bytes left unread | `qemu::tests::boundaries::output_is_bounded_at_limit_plus_one`, `qemu::tests::resources::failure_tail_respects_its_limits` |
| A failed write of the log of a board capture ends the session in the read that failed | `qemu::tests::boundaries::a_failed_log_write_ends_the_session` |
| `boundary` and `checked_read` of a board capture stop at the first read that finds a failure | `qemu::tests::boundaries::boundary_stops_at_a_guard_error`, `qemu::tests::boundaries::a_checked_read_fails_in_the_read_that_finds_a_failure` |
| A capture of a process instead drains its output at a boundary until the guest is idle, and ignores a failed write of its log | `qemu::tests::boundaries::a_capture_of_a_process_drains_past_a_guard_error_until_idle`, `qemu::tests::boundaries::a_capture_of_a_process_ignores_a_failed_log_write` |
| A guarded capture writes its log only once the guest has stopped, and each byte once | `qemu::tests::properties::guarded_capture_defers_log_io_and_rejects_fatal_output` |

## Hardware evidence to re-obtain

- The prototype ran its images on QEMU virt with one Cortex-A76 through
  this module: the boot to the ready line with the CPU identity record, the
  echo of input, the breakpoint exception with its fault trace and halt,
  and the QEMU suites that used the plain and the guarded capture. The
  QEMU boot suite of krepi, `cargo xtask qemu-boot`, obtains the boot to
  the ready line with the CPU identity record and the echo of input again
  with the krepi default image, through the QEMU runner; the breakpoint
  exception and the other results are obtained again with krepi images on
  QEMU virt (planned).
- The prototype's board sessions talked to a Raspberry Pi 5 through a
  serial port with the board capture: requests in both directions, the
  failure tail after a fatal record, and the end of a session at its
  deadline or by an interrupt. krepi obtains them again through the board
  runner on the HIL bench (planned), with the bench configuration of the
  firmware and lab registry (planned).
- krepi's first QEMU result through this module is the run of the test
  image of `tools/src/test_elf.rs` by `cargo xtask qemu` in the test
  `xtask/tests/qemu.rs`, which CI runs with QEMU 8.2 on every pull request
  to `main`: the guest's line reaches the transcript and its PSCI power-off
  ends QEMU with status 0. It boots no kernel and replaces none of the
  results above.

## Not carried over

- `DEFAULT_ELF`, the path of the prototype kernel image below the root of
  the prototype tree, which the prototype suites ran by default. The QEMU
  runner takes the image as an argument.
- The variable `QEMU_SYSTEM_AARCH64`; the executable is an argument.
- `defer_log`, which kept the bytes received from then on in memory until
  `write_deferred_log`, as the receiver of a Python program of the prototype
  had kept its log, and which nothing called; with it the test
  `resources::board_serial::a_deferred_log_is_written_once` of
  `tools/tests/platform/physical_entry.rs`. That a deferred log writes each
  byte once is fixed by
  `qemu::tests::properties::guarded_capture_defers_log_io_and_rejects_fatal_output`.
- `os_error_text`, Python's text of a failed log write, and
  `format_seconds`; the standard library gives the text, and
  `seconds_text` writes the seconds.
- The two casings and the fixed size of the limit text.
- The variants of `executable`, `exit_code` and `terminate` for hosts other
  than Unix, which no host of this repository builds.
- The board guest `Board` of the legacy `tools/src/tty.rs`, which is not
  ported ([`tty`](tools-tty.md#not-carried-over)); the tests use a test
  guest with its rules.
- The rest of the legacy files that the tests come from: the tests of the
  prototype's Pi 5 suites and of its other suites, and the probes of
  `tools/src/probe.rs` and the board session of
  `tools/src/suites/platform/kernel_serial.rs`, of which the tests take
  only the constants.
- The sleeps of 100 ms between the lines of
  `boundaries::board_serial::boundary_stops_at_a_guard_error`, and the upper
  bound of 30 s on the read of
  `resources::board_serial::a_checked_read_ends_at_the_session_deadline`.
