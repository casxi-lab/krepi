---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/suites/platform/qemu_boot.rs
destination:
  - tools/src/qemu_boot.rs
  - tools/src/qemu_boot/tests.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: tools/src/qemu_boot.rs

## Summary

The QEMU boot suite, `cargo xtask qemu-boot`. The legacy suite
`platform/qemu-boot` booted the prototype image several times on QEMU virt
and checked, in phases, the ready line, the CPU identity record, the echo of
a challenge and a breakpoint exception that a serial byte triggered. This
module keeps the shape of its judgment, repeated cold boots with the CPU
identity check and the echo of the challenge `casxi-sim-check` and CR, and
its report of runs with their outcome, and judges the krepi default image
against the records of the
[boot contract](../domains/boot-platform/boot/contract.md#records). It
builds the image itself and runs each boot through the library entry of the
QEMU runner, `qemu_run::run_image_with`, which sends the challenge once the
ready record has arrived and writes the receipt of `cargo xtask qemu` with
the key `input`. That entry, with `Input`, is new code of
`tools/src/qemu_run.rs`, not taken from the legacy tree.
[Testing](../conventions/testing.md#entry-points) describes the command.

## Changes

- The suite is the command `cargo xtask qemu-boot`, with `--qemu` and
  `--output-dir` read by `clap`, in place of the legacy suite
  `platform/qemu-boot` of the prototype's suite runner, with `--elf`,
  `--repeats`, `--timeout` and `--output-dir` read by hand.
- It builds the default image with Cargo in `kernel/` and records the
  build, the toolchain and the image digest, in place of taking a built
  image from a fixed path.
- Each run is a run of the QEMU runner with its command line, on the host
  clock, with a window of 20 s and a limit of 4,096 bytes, and writes the
  runner's directory and receipt. The legacy suite started QEMU itself on a
  fixed instruction count, read its output through a plain capture and gave
  each phase the timeout.
- The judgment holds the whole transcript of each run against fixed
  expected records: the CPU identity record of a Cortex-A76, with the check
  of [`receipt`](tools-receipt.md), the boot and ready records of krepi, the
  challenge sent just after the ready record and exactly its echo with a
  line feed after the carriage return, and no fatal record. The legacy suite
  waited for the ready line and for the echo as an exact line anywhere after
  the boundary, and checked that the challenge had not appeared before it was
  sent.
- The three runs must use the same image and give identical transcripts; the
  legacy suite compared nothing across runs, and it stopped at the first
  failed boot. Every run of the case runs, unless one cannot start or an
  interrupt ends it.
- The suite receipt `summary.json` has the keys that testing describes, with
  each check and its result, in place of the legacy report with its phases
  and their times; it judges no time.
- Exit codes: 0, 1, 2, 120 and 130, by the rules of the other commands of
  the crate.
- The module and its tests carry the line
  `//! Feature: krepi.platform.qemu-virt-boot`, the feature whose QEMU
  evidence the suite produces, in place of the legacy annotation.

## Tests carried over

None: the legacy suite had no unit tests of its own. The tests of
`tools/tests/platform/qemu_boot.rs` tested the CPU identity check and the
QEMU command line, and are carried over with [`receipt`](tools-receipt.md)
and [`qemu`](tools-qemu.md).

## Behaviour changes

| Change | Test |
| --- | --- |
| A transcript passes only with the exact records and echo, and a missing, reordered or changed record, a missing or partial echo, an echo without its line feed, extra bytes or a fatal record fail | `qemu_boot::tests::receipts::missing_reordered_or_changed_records_fail`, `qemu_boot::tests::receipts::anything_but_the_exact_echo_fails`, `qemu_boot::tests::receipts::a_fatal_record_fails` |
| The challenge must have been sent just after the ready record | `qemu_boot::tests::receipts::a_challenge_sent_at_another_point_fails` |
| A run must end at its window, with no errors, on the runner's machine and one Cortex-A76, on the host clock without an instruction count, with the image of the build | `qemu_boot::tests::receipts::weakened_or_misattributed_receipts_fail` |
| The runs must use one image and give identical transcripts, and there must be three | `qemu_boot::tests::receipts::runs_that_differ_or_are_too_few_fail`, `qemu_boot::tests::receipts::three_good_runs_pass` |
| The image comes from Cargo's artifact message | `qemu_boot::tests::the_image_is_taken_from_the_artifact_message`, `qemu_boot::tests::the_build_command_names_the_default_image` |
| The case runs each boot through the runner into a directory of its own and passes, or fails or ends as an error, as a whole | `qemu_boot::tests::the_case_passes_with_a_guest_that_boots_and_echoes`, `qemu_boot::tests::the_case_fails_with_a_guest_at_another_level`, `qemu_boot::tests::a_run_that_cannot_start_is_an_error` |
| The command line takes `--qemu` and `--output-dir` | `qemu_boot::tests::the_command_line_takes_its_two_options` |

## Hardware evidence to re-obtain

- The three cold boots of the krepi default image on QEMU virt `virt-8.2`
  with one Cortex-A76, with the echo, in the `check` workflow of CI.

## Not carried over

- The exception phase: the breakpoint that the byte `!` triggered and its
  check of the exception record and the halt. The default image has no
  command that a byte triggers; the exception tests of krepi run test images
  of their own.
- The fixed instruction count of the legacy runs.
- The options `--elf`, `--repeats` and `--timeout`, the shared flag parser of
  the legacy suites and the phase report with its times.
- The legacy feature annotation `system.platform.qemu-boot`.
