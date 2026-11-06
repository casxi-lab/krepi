---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/serial.rs
destination:
  - tools/src/serial.rs
treatment: ported
features: none
---

# Porting record: tools/src/serial.rs

## Summary

A bidirectional serial link to a guest over the standard streams of its
process, as a QEMU guest's PL011 reaches the host. Reader threads drain the
guest's standard output and standard error into one byte stream and a log;
a writer thread feeds scheduled input and counts the bytes the guest's pipe
accepted. `Link` splits the stream into complete `Line`s, each with the time
it arrived and the input count at that moment, waits for the ready line of
the guest and fails on an earlier fatal record, drains the diagnostics that
follow a failure, and finishes without sending leftover input. The module is
ported with its test. No module of this repository calls it yet; the
prototype suites of interrupts, memory and the runtime clock drove their
guests through it.

As in the legacy module, a failed write of the output log or the input log
is dropped: the counts of received and written bytes still include the
bytes that the log lacks, and nothing reports the failure, so a log can be
shorter than its count without a sign of it.

## Changes

- `Link::new` takes a `Timing` (`tools/src/timing.rs`), from which the link
  takes its waits in place of constants: `link_slice` for a wait once the
  output has ended, for one look while it waits for the ready line and while
  it drains (legacy 20 ms), `link_drain` for the drain after a failure
  (250 ms), and `link_finish` and `link_finish_slice` for the final read
  (1 s and 50 ms).
- `wait_ready` takes its timeout as a `Duration` in place of seconds as a
  float.
- `ensure_running` names how the process ended with the standard library's
  text of its exit status, `exit status: 1` or `signal: 15 (SIGTERM)`, or
  `still running` when the output ended first, in place of `exit=<code>`
  with the legacy exit code, a negative number for a signal, or
  `exit=None`.
- A fatal record before the ready line is quoted with the escapes of
  `<[u8]>::escape_ascii`, in place of `debug_bytes` of the legacy receipt
  module, Python's `repr` of bytes; the module no longer depends on the
  receipt module. The three record beginnings that end the wait are a named
  constant.
- The module documentation no longer refers to the Python runner whose link
  it reproduced.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/serial.rs` `tests::link_pairs_lines_with_input_progress` | `tools/src/serial.rs` `tests::a_link_pairs_lines_with_input_progress` | Unchanged for the lines, the counts and both logs. Added: the stop report of `cat`, which SIGTERM ends, is checked whole, `exit_code` null and `signal` 15 (see [the process helpers](tools-qemu.md#behaviour-changes)); and the failure of `ensure_running` afterwards is checked exactly, `QEMU exited or closed output early (signal: 15 (SIGTERM))`. The logs are written in a scratch directory below the build directory in place of the system temporary directory. The waits for the echo, the input count and the end of the output and of the process are bounds of 60 s, which only a failing test reaches, in place of 1 and 5 s |

New tests: `tests::a_fatal_record_before_ready_fails_with_its_line`, in
which `cat` echoes a fatal record with quotes, a backslash and a control
byte after an ordinary line, and before a ready line that the wait does not
reach; and `tests::output_that_ends_before_the_process_fails_the_link`, in
which a shell sends its output streams to `/dev/null`, so that both pipes
end, and becomes `cat`, which waits for input that the link never sends.

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| Failure of `ensure_running` for a process that SIGTERM ended | `QEMU exited or closed output early (exit=-15)` | `QEMU exited or closed output early (signal: 15 (SIGTERM))` | `tests::a_link_pairs_lines_with_input_progress` |
| Failure of `ensure_running` for a process whose output ended first | `QEMU exited or closed output early (exit=None)` | `QEMU exited or closed output early (still running)` | `tests::output_that_ends_before_the_process_fails_the_link` |
| A fatal record before the ready line | `Guest failed before ready: b'CASXI_PANIC at "main.rs" \'x\'\x01\\'` | `Guest failed before ready: CASXI_PANIC at \"main.rs\" \'x\'\x01\\` | `tests::a_fatal_record_before_ready_fails_with_its_line` |

## Hardware evidence to re-obtain

The prototype suites of interrupts, memory and the runtime clock ran their
guests on QEMU virt with one Cortex-A76 through this link. krepi obtains such
results again with its own image and suites on QEMU virt (planned). The link
has no board results: a board's serial port uses the transport of
[`tty`](tools-tty.md).

## Not carried over

Nothing of the module is left behind. The legacy test's directory in the
system temporary directory gives way to a scratch directory below the build
directory, as in the other modules of this crate.
