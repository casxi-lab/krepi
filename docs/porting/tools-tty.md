---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/tty.rs
  - tools/tests/support/pty.rs
  - tools/tests/support/child.rs
destination:
  - tools/src/tty.rs
  - tools/src/tty/tests.rs
  - tools/src/pty.rs
  - tools/src/child.rs
treatment: ported
features: none
---

# Porting record: tools/src/tty.rs

## Summary

The serial port transport of the host tools. `TtyPort` opens a POSIX
terminal for a session with a board: it locks the device, takes exclusive
access with `TIOCEXCL`, applies raw 115200 8N1 attributes derived by
`raw_attributes`, reads the port on a polling thread into a byte stream,
hands out a `TtyWriter` that sends bounded requests and records them, and
restores, releases and closes the port at `finish`. `Receiver` opens a
terminal read-only for a capture that only receives. `catch_interrupts`
installs the SIGINT, SIGTERM and SIGHUP handlers that store the first signal
into a process-wide flag, and `INTERRUPTED` is the text with which a caught
interrupt ends a session or a capture. The serial capture and the capture of
a board session through a port use these items, so the module is ported with
the tests of every item it keeps.

The legacy module also reproduced the texts of Python: its errors were those
of Python's `OSError` and `termios.error`, file names were quoted as Python's
`repr` quotes them, and time stamps had the form of Python's `isoformat`.
These forms are not carried over; the errors, names and time stamps are
written in the form described under [Changes](#changes). `Board` and
`die_by_signal` are not ported; see [Not carried over](#not-carried-over).

The unit tests use a pseudo-terminal pair and a runner that runs one test in
a child process. Both are test-only modules of the crate, `tools/src/pty.rs`
and `tools/src/child.rs`, merged from the test helpers of the legacy module
and from the support modules of the legacy integration tests.

## Changes

- Errors carry the standard library's text of the operating-system error,
  `strerror (os error N)`, in place of Python's `[Errno N] strerror`. An
  error that concerns a file name starts with the name in Rust's debug form,
  which escapes quotes, backslashes, control characters and bytes that are
  not printable, and the steps that read, set and restore attributes or
  release exclusive access name themselves before the error, in place of
  the tuple `(N, 'strerror')` of `termios.error`:

  | Error | Legacy | krepi |
  | --- | --- | --- |
  | A refused open of a port or a receiver | `[Errno 2] No such file or directory: '/dev/x'` | `"/dev/x": No such file or directory (os error 2)` |
  | A port name with a NUL byte | `invalid tty path` for a port, `embedded null byte` for a receiver | `"/dev/tty\0x": nul byte found in provided data at position: 8` for both |
  | A refused lock or `TIOCEXCL`, a failed wait, read or poll | `[Errno 9] Bad file descriptor` | `Bad file descriptor (os error 9)` |
  | A failed read of the original attributes | `(9, 'Bad file descriptor')` | `attribute read failed: Bad file descriptor (os error 9)` |
  | Refused raw attributes | `(5, 'Input/output error')` | `raw attributes refused: Input/output error (os error 5)` |
  | A failed `finish` of a port | `serial cleanup failed: (25, 'Inappropriate ioctl for device'); [Errno 25] Inappropriate ioctl for device` | `serial cleanup failed: attribute restoration failed: Inappropriate ioctl for device (os error 25); exclusive access release failed: Inappropriate ioctl for device (os error 25)` |
  | A failed `close` of a receiver | `attribute restoration failed: (5, 'Input/output error')`, `exclusive access release failed: [Errno 25] ...`, `port close failed: [Errno 9] ...` | The same labels, each followed by the standard library's text |
  | A failed wait or write of a writer | An I/O error whose text is Python's | The I/O error of the operating-system error |

  `TtyPort::finish` uses the labels of `Receiver::close` inside
  `serial cleanup failed: ...`, so both report a failed step the same way.
- The time stamp `at` of a transmitted request is `report::utc_now`, RFC 3339
  with six fraction digits and the offset `Z`, in place of `timestamp`,
  Python's `isoformat` with `Z`, which omitted a zero fraction. A request is
  recorded as a `serde_json` object with the keys `at`, `hex` and
  `sent_bytes` in that order.
- `start_reader` and `writer` take a `Timing` (`tools/src/timing.rs`): the
  reader waits for input at most `reader_poll` at a time and a request is
  sent within `request_transmit`, in place of the constants 100 ms and 2 s.
  A wait is rounded up to a whole millisecond from its nanoseconds.
- The poll and read of the reader thread are a function of their own, whose
  result the thread decides on, so that a test seam can give the reader a
  hang-up with a read that would block. The requests for exclusive access
  and the read of the original attributes are functions shared by the port
  and the receiver.
- The safety comments of the unsafe operations state the validity,
  alignment, initialization and exclusive use of the memory each call
  receives.
- The documentation no longer refers to the Python programs. The
  documentation of `TtyPort` states that Linux refuses a new open of a
  terminal held with `TIOCEXCL` to a process without `CAP_SYS_ADMIN`.
- The test seams are kept, with one more: `HANG_UP`, which the next reader
  thread that a port starts takes as its first look.
- The pseudo-terminal pair `tests::Pair` of the legacy module and the pair of
  the legacy support module `tools/tests/support/pty.rs` are one test-only
  module, `tools/src/pty.rs`, with the parts that these tests use: opening a
  pair close-on-exec, the path of its slave and a read of a given count of
  bytes from its master, and the host checks of a second open of a held
  terminal, which the tests of [`qemu`](tools-qemu.md) share: an open of
  the terminal outside the code under test, the text of a refused lock, and
  whether the kernel refuses this process a new open of a terminal held
  with `TIOCEXCL`. The child runner `tests::in_child` of the legacy
  module and `ChildTest` of `tools/tests/support/child.rs` are one test-only
  module, `tools/src/child.rs`, with the parts that these tests use: running
  one test of the binary alone with the variable `KREPI_TOOLS_TEST_CHILD`
  set, and waiting for its end. A test waits for an event at most
  `TEST_WAIT`, 60 s, in place of the legacy bounds of 1, 5, 10 and 30 s; the
  bound is reached only when a test fails.

## Tests carried over

All tests are in `tools/src/tty/tests.rs`, below `tty::tests`. Legacy tests
are in `tools/src/tty.rs` below `tests`.

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `raw_attributes_select_115200_8n1_without_flow_control_or_processing` | Same name | Unchanged |
| `a_failed_read_ends_the_stream_with_the_python_text` | `a_failed_read_ends_the_stream_and_keeps_its_error` | Changed: `Is a directory (os error 21)`. The assertions on the board guest are not carried over, as `Board` is not ported |
| `cleanup_failures_keep_the_python_texts` | `cleanup_failures_are_reported_in_order` | Changed: the labelled texts of both failed steps in that order, with `Inappropriate ioctl for device (os error 25)`; a second `finish` succeeds |
| `partial_transmit_is_completed_and_recorded` | Same name | Unchanged for the bytes, the count of writes and the record; the time stamp has the form of `utc_now`, and the keys are checked in order |
| `restore_failure_closes_and_releases` | Same name | Changed: `serial cleanup failed: attribute restoration failed: Input/output error (os error 5)` |
| `a_failed_cleanup_replaces_the_open_error` | Same name | Changed: `raw attributes refused: Input/output error (os error 5)`, and the cleanup text above |
| `a_failed_tiocexcl_at_open_fails_with_the_oserror_text` | `a_failed_tiocexcl_at_open_fails_the_open` | Changed: `Bad file descriptor (os error 9)`; one request changes the terminal, as before |
| `a_failed_tcgetattr_at_open_fails_with_the_termios_text` | `a_failed_tcgetattr_at_open_fails_the_open` | Changed: `attribute read failed: Bad file descriptor (os error 9)`; two requests, as before |
| `a_refused_second_open_changes_nothing` | Same name | Split by host. Where the kernel lets the open of a terminal held with `TIOCEXCL` through, Darwin and Linux with `CAP_SYS_ADMIN`, the lock refuses it: `Resource temporarily unavailable (os error 35)` on Darwin, `(os error 11)` on Linux. Linux refuses that open to a process without `CAP_SYS_ADMIN`, such as the CI user: `"<slave>": Device or resource busy (os error 16)`. The test finds which host it runs on with a pair of its own, on which it takes `TIOCEXCL` and opens the terminal again. No request changes the held terminal on any host |
| `a_failed_unlock_has_no_text_and_the_duplicates_keep_the_lock` | Same name | Changed: a refused lock is `Resource temporarily unavailable (os error N)` with `EWOULDBLOCK`, 35 on Darwin and 11 on Linux, and the cleanup text above |
| `a_receiver_opens_read_only_without_a_lock` | Same name | Unchanged flags. Changed procedure: the second descriptor of the terminal is opened before the receiver takes `TIOCEXCL`, as Linux refuses a later open to a process without `CAP_SYS_ADMIN`, and must then take the lock; on such a host the test also checks that a new open fails with `EBUSY` |
| `a_receiver_closes_after_a_failed_restoration` | Same name | Changed: `attribute restoration failed: Input/output error (os error 5)`; two requests, as before |
| `a_receivers_failed_tiocexcl_fails_with_the_oserror_text` | `a_receivers_failed_tiocexcl_fails_the_configuration` | Changed: `Bad file descriptor (os error 9)`; one request, as before |
| `a_receivers_cleanup_failures_keep_the_python_texts` | `a_receivers_cleanup_failures_are_reported_in_order` | Changed: `attribute restoration failed: Inappropriate ioctl for device (os error 25)` and `exclusive access release failed: Inappropriate ioctl for device (os error 25)`, in that order |
| `sigint_sigterm_and_sighup_are_caught_and_the_first_is_kept` | Same name | Unchanged; the assertion on the board guest gives way to the value of the flag, which already holds the first signal |
| `a_signal_inherited_ignored_is_caught` | Same name | Unchanged |

New tests: `a_hang_up_with_nothing_to_read_ends_the_stream_without_an_error`
fixes the end of the stream at a hang-up, which the legacy tests could not
provoke; `a_port_name_with_a_nul_byte_is_refused` and
`a_port_that_cannot_be_opened_is_named` fix the refusal texts of both opens;
and `a_port_locked_elsewhere_is_refused_before_it_changes_anything` holds the
advisory lock on another open of the terminal without `TIOCEXCL`, so that
the port's open succeeds on every host and its lock is refused before any
request changes the terminal.

The legacy tests ran on Darwin only. The expected texts above hold on Darwin
and on Linux, where `EISDIR`, `ENOTTY`, `EBADF`, `EIO` and `EAGAIN` have the
same text and, apart from `EAGAIN`, the same number.

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| Error texts of the port, the receiver and the writer | Python's `OSError` and `termios.error` texts | The standard library's text, after the debug form of the name or the label of the step; see [Changes](#changes) | The tests of the table above |
| A port name with a NUL byte | `invalid tty path`; `embedded null byte` for a receiver | The name and the reason of the refusal, the same for both | `tty::tests::a_port_name_with_a_nul_byte_is_refused` |
| A name in an open error | Python's `repr` after the error, escaping DEL as `\x7f` | Rust's debug form before the error, escaping DEL as `\u{7f}` | `tty::tests::a_port_that_cannot_be_opened_is_named` |
| The time stamp of a transmitted request | `2026-10-26T20:18:20Z` at a zero fraction | `2026-10-26T20:18:20.000000Z` | `tty::tests::partial_transmit_is_completed_and_recorded` |

The legacy module documented the following rules as differences from the
Python programs it replaced. Each rule is kept and fixed by a test:

| Rule | Test |
| --- | --- |
| A port holds an advisory `flock` besides `TIOCEXCL`, so that a second port on the same terminal is refused where the kernel lets its open through | `tty::tests::a_refused_second_open_changes_nothing` |
| The lock is taken before anything changes, so that a refused second port changes nothing on the held terminal | `tty::tests::a_port_locked_elsewhere_is_refused_before_it_changes_anything`, and where the kernel lets the open of a held terminal through `tty::tests::a_refused_second_open_changes_nothing` |
| `finish` releases the lock, so that the terminal opens again while a duplicate of the reader or the writer is still open | `tty::tests::a_failed_unlock_has_no_text_and_the_duplicates_keep_the_lock`, `tty::tests::restore_failure_closes_and_releases` |
| A failed release of the lock has no text of its own, and the lock then lasts until the duplicates are closed | `tty::tests::a_failed_unlock_has_no_text_and_the_duplicates_keep_the_lock` |
| A read that would block after a hang-up ends the stream without an error instead of polling the device again | `tty::tests::a_hang_up_with_nothing_to_read_ends_the_stream_without_an_error` |
| SIGINT, SIGTERM and SIGHUP are caught, the first is kept, and an inherited `SIG_IGN` is replaced | `tty::tests::sigint_sigterm_and_sighup_are_caught_and_the_first_is_kept`, `tty::tests::a_signal_inherited_ignored_is_caught` |
| A port takes `TIOCEXCL` at every open | `tty::tests::a_failed_tiocexcl_at_open_fails_the_open`, and on Linux without `CAP_SYS_ADMIN` `tty::tests::a_refused_second_open_changes_nothing` |
| A receiver takes `TIOCEXCL` at every configuration and releases it at its close | `tty::tests::a_receiver_opens_read_only_without_a_lock`, `tty::tests::a_receivers_failed_tiocexcl_fails_the_configuration`, `tty::tests::a_receiver_closes_after_a_failed_restoration` |
| A failed read of the original attributes at open is reported, with its own label, and the port is cleaned up | `tty::tests::a_failed_tcgetattr_at_open_fails_the_open` |

## Hardware evidence to re-obtain

The legacy board sessions talked to a Raspberry Pi 5 through this transport,
over a USB serial adapter on its UART: exclusive open, raw 115200 8N1,
bounded requests in both directions, restoration of the attributes, and the
end of the stream when the adapter goes away. krepi obtains such results
again with its own image through the board runner on the HIL bench
(planned), with the bench configuration of the firmware and lab registry
(planned).

As in the legacy module, neither the port nor the receiver reads the raw
attributes back. `tcsetattr` succeeds once it has applied any of the
requested attributes, so a serial driver that does not support 115200 8N1
can adjust them without an error, and the line settings of a capture
receipt are those requested. The results on the bench have to show the
settings that took effect.

## Not carried over

- `Board`, the guest of a board session behind a port, and its
  implementation of the guest check of the legacy `qemu` module. Only the
  board suites of the prototype and the tests of the board sessions used it;
  without it this module no longer depends on `qemu`. The tests of
  the board capture of [`qemu`](tools-qemu.md) use a test guest with its
  rules.
- `die_by_signal`, which ended the process by a caught signal, as Python's
  death by an uncaught `KeyboardInterrupt` did. Only the board suites of the
  prototype called it.
- `python_repr` and `printable`, Python's `repr` of a text with the
  printable characters of Unicode 16.0, which `fancy-regex` decided; names
  are written in Rust's debug form.
- `timestamp` and `isoformat`, Python's time stamps; `report::utc_now`
  replaces them.
- `strerror`, `last_error`, `termios_text` and `termios_error`, the Python
  texts of an operating-system error; the standard library gives the text.
- The tests `file_names_are_quoted_as_python_repr_quotes_them` and
  `exactly_the_unprintable_characters_of_python_are_escaped`, which tested
  `python_repr`; the debug form is the standard library's.
- The test `a_caught_signal_ends_the_process_by_that_signal`, which tested
  `die_by_signal`.
- The test `timestamps_follow_python_isoformat`, which tested `isoformat`;
  the test of `report::utc_now` fixes the form of the time stamps.
- The parts of `tools/tests/support/pty.rs` and `tools/tests/support/child.rs`
  that these tests do not use. The board scripts, the views of a pair's
  attributes and the other parts that the tests of the serial capture use
  are recorded with [`serial_capture`](tools-serial_capture.md#changes); the
  line-by-line wait for a child's output, which no test uses, is not taken.
