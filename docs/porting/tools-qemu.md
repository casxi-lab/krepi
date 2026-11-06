---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/qemu.rs
destination:
  - tools/src/qemu.rs
treatment: ported
features: none
---

# Porting record: tools/src/qemu.rs

## Summary

The process helpers of the legacy QEMU runner, which the serial link uses:
`spawn_reader` drains an output stream of a child process on a thread of its
own; `exit_code` tells how a process ended; and `stop_process` sends SIGTERM
to a child that still runs, kills it when it does not end in time, and
reports how it ended, with the private `terminate` and `wait_with_timeout`.
The rest of the module, the QEMU command and its version, the guest check
and the serial capture over the standard streams of QEMU or through a
serial port, with the two tests of the module, is taken in a later change,
which completes this record.

## Changes

- `exit_code` returns the code a process exited with and the number of the
  signal that ended it, of which exactly one is given, in place of one number
  in the convention of Python's `Popen.returncode`, which gave a signal as
  its negative.
- The report of `stop_process` gives the two values as `exit_code` and
  `signal`, each null when it does not apply, and both null when the process
  has not ended within the wait after the kill. It is a `serde_json` value
  with the keys `intentional_shutdown`, `forced_kill`, `exit_code` and
  `signal` in that order.
- `stop_process` takes a `Timing` (`tools/src/timing.rs`): it waits
  `stop_grace` after SIGTERM and `kill_grace` after the kill, and looks at
  the process every `reap_poll`, in place of the constants 1 s, 1 s and
  10 ms.
- The variants of `exit_code` and `terminate` for hosts other than Unix are
  removed, as the crate builds on Unix hosts only, and with them the
  `allow` of unsafe code. `terminate` converts the process number with a
  check, and `wait_with_timeout` does not overflow the time at which it gives
  up.
- The documentation no longer refers to the Python runner.

## Tests carried over

None in this change. The two tests of the module, which test the QEMU
command and the text of a timeout, are taken with the code they test.

New test: `tools/src/qemu.rs` `tests::the_stop_report_gives_the_exit_code_or_the_signal`
stops a child that has exited with code 3, a child that SIGTERM ends, and a
child that ignores SIGTERM and is killed. The ignored disposition is set
before the child prints a line that the test waits for, so that the test
does not depend on scheduling.

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| The stop report of a child that exited with code 3 | `exit_code: 3` | `exit_code: 3, signal: null` | `tests::the_stop_report_gives_the_exit_code_or_the_signal` |
| The stop report of a child that SIGTERM ended | `exit_code: -15` | `exit_code: null, signal: 15` | `tests::the_stop_report_gives_the_exit_code_or_the_signal` |
| The stop report of a child that SIGKILL ended | `forced_kill: true, exit_code: -9` | `forced_kill: true, exit_code: null, signal: 9` | `tests::the_stop_report_gives_the_exit_code_or_the_signal` |

## Hardware evidence to re-obtain

None for these helpers, which run on the host. The QEMU runs of the module
are recorded with the rest of the module.

## Not carried over

- The variants of `exit_code` and `terminate` for hosts other than Unix,
  which no host of this repository builds.
