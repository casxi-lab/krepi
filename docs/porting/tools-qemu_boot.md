---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/suites/platform/qemu_boot.rs
  - tools/src/suites/kernel/interrupts.rs
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
[boot contract](../domains/boot-platform/boot/contract.md#records). The
legacy suite `kernel/interrupts` checked that timer IRQs returned to the
interrupted code, that the registers survived an IRQ, and the record of a
deliberate FP/SIMD trap with the halt and silence after it; this module
takes its expected fields for the cases of the timer IRQ, of the registers
across an IRQ and of the FP/SIMD trap. The suite builds the images
itself and runs each boot through the library entry of the QEMU runner,
`qemu_run::run_image_on`, which sends the challenge of the default image
once the ready record has arrived, writes the receipt of `cargo xtask qemu`
with the key `input`, and runs the test image of the SError on the machine
with EL2. Those entries, with `Input` and `Machine`, are new code of
`tools/src/qemu_run.rs` and `tools/src/qemu.rs`, not taken from the legacy
tree. [Testing](../conventions/testing.md#entry-points) describes the
command.

## Changes

- The suite is the command `cargo xtask qemu-boot`, with `--qemu` and
  `--output-dir` read by `clap`, in place of the legacy suite
  `platform/qemu-boot` of the prototype's suite runner, with `--elf`,
  `--repeats`, `--timeout` and `--output-dir` read by hand.
- It builds the default image and the test images with one Cargo command
  in `kernel/` and records the build, the toolchain and the digest of each
  image, in place of taking a built image from a fixed path.
- The suite runs a table of cases, each with its image, machine, count of
  cold boots and judgment. The legacy suites each ran one image through
  phases that bytes on the serial port triggered; krepi runs one test image
  for each exception case, and no byte triggers anything.
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
- A case of a test image holds its transcript against an exact sequence of
  records: the start record of the image, the expected exception records,
  each with its vector, class, syndrome and return address, and then
  `CASXI_HALTED`, or the self-checks of the image with no failure and
  `CASXI_RESUMED`, or, for the image whose vectors halt after its dispatch,
  its self-checks alone; nothing else. The return address is that of a
  symbol of the ELF file, read with [`elf`](tools-elf.md), or lies between two
  symbols. The legacy suite of interrupts took the FP/SIMD trap from any
  line, required the exact syndrome `0x1fe00000` that QEMU writes and an
  EL1h return address, and then the frame trace and the halt; krepi requires
  the exception class `0x07`, which the Arm Architecture Reference Manual
  gives, the address of the trapping instruction, and the halt with nothing
  after it. The legacy suite counted timer IRQs and their hits in a
  labelled loop from a statistics record of the image, and took the
  register check from a probe that a serial byte started; krepi requires
  two IRQ records with return addresses in the waiting code and the
  image's own checks, and an IRQ taken at one known instruction with every
  register checked by the image after it. The cases `sp-el0-brk` and
  `unexpected-irq`, the halt of vector 0 and an interrupt that the board
  does not expect, are new.
- The receipt of a test image's run must name the machine of its case: the
  machine with EL2 for the SError, the runner's machine for the others.
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

None from either legacy suite. The suite `platform/qemu-boot` had no unit
tests of its own; the tests of `tools/tests/platform/qemu_boot.rs` tested
the CPU identity check and the QEMU command line, and are carried over with
[`receipt`](tools-receipt.md) and [`qemu`](tools-qemu.md). The tests of
the suite `kernel/interrupts` are not carried over; Not carried over lists
them.

## Behaviour changes

| Change | Test |
| --- | --- |
| A transcript passes only with the exact records and echo, and a missing, reordered or changed record, a missing or partial echo, an echo without its line feed, extra bytes or a fatal record fail | `qemu_boot::tests::receipts::missing_reordered_or_changed_records_fail`, `qemu_boot::tests::receipts::anything_but_the_exact_echo_fails`, `qemu_boot::tests::receipts::a_fatal_record_fails` |
| The challenge must have been sent just after the ready record | `qemu_boot::tests::receipts::a_challenge_sent_at_another_point_fails` |
| A run must end at its window, with no errors, on the runner's machine and one Cortex-A76, on the host clock without an instruction count, with the image of the build | `qemu_boot::tests::receipts::weakened_or_misattributed_receipts_fail` |
| The runs must use one image and give identical transcripts, and there must be three | `qemu_boot::tests::receipts::runs_that_differ_or_are_too_few_fail`, `qemu_boot::tests::receipts::three_good_runs_pass` |
| The images come from Cargo's artifact messages | `qemu_boot::tests::the_image_is_taken_from_the_artifact_message`, `qemu_boot::tests::the_build_command_names_the_images` |
| A test image passes only with its exact records: an exception record with another vector, class, syndrome or return address, a malformed record, a failed self-check, a missing or extra record, output after the halt, a missing end or a halt in a returning case fail | `qemu_boot::tests::records::good_runs_of_the_test_images_pass`, `qemu_boot::tests::records::a_record_with_other_fields_fails`, `qemu_boot::tests::records::the_serror_must_return_into_the_unmasking_code`, `qemu_boot::tests::records::malformed_records_are_refused`, `qemu_boot::tests::records::a_failed_self_check_fails`, `qemu_boot::tests::records::a_wrong_end_or_order_of_records_fails`, `qemu_boot::tests::records::a_missing_symbol_or_run_fails` |
| The case whose vectors halt after its dispatch passes only when nothing follows its self-check, and an unexpected interrupt only once | `qemu_boot::tests::records::a_case_that_halts_after_its_dispatch_fails_with_more_or_less` |
| The receipt of a test image must name the machine of its case and no input | `qemu_boot::tests::records::a_receipt_of_another_machine_or_with_input_fails` |
| The suite takes the worst outcome of its cases | `qemu_boot::tests::the_cases_name_their_symbols_images_and_outcome` |
| The case runs each boot through the runner into a directory of its own and passes, or fails or ends as an error, as a whole | `qemu_boot::tests::the_case_passes_with_a_guest_that_boots_and_echoes`, `qemu_boot::tests::the_case_fails_with_a_guest_at_another_level`, `qemu_boot::tests::a_run_that_cannot_start_is_an_error` |
| The command line takes `--qemu` and `--output-dir` | `qemu_boot::tests::the_command_line_takes_its_two_options` |

## Hardware evidence to re-obtain

- The three cold boots of the krepi default image on QEMU virt `virt-8.2`
  with one Cortex-A76, with the echo, and the runs of the test images, in
  the `check` workflow of CI.

## Not carried over

- The exception phase: the breakpoint that the byte `!` triggered and its
  check of the exception record and the halt. The default image has no
  command that a byte triggers; the exception tests of krepi run test images
  of their own.
- From `tools/src/suites/kernel/interrupts.rs`: the phases that serial bytes
  triggered, the `CASXI_IRQ` statistics record and its fields, the load and
  frame probes, the frame trace after the FP/SIMD trap and the command line
  with its options, all of which belonged to diagnostics of the default
  image.
- The unit test `records_parse_strictly` of
  `tools/src/suites/kernel/interrupts.rs`, which parsed the `CASXI_IRQ`
  and `CASXI_FRAME` records and a fault record with the exact syndrome
  `0x1fe00000`: krepi writes neither diagnostic record, and the tests of
  `qemu_boot::tests::records` judge the exception record of the FP/SIMD
  trap by its exception class.
- The five tests of the suite's test file `tools/tests/kernel/interrupts.rs`,
  `ex1_irq_snapshots_advance_with_the_timer`,
  `ex2_snapshots_that_break_the_timer_contract_are_rejected`,
  `ex3_the_register_probe_must_preserve_state_across_a_real_irq`,
  `ex4_the_fp_probe_reports_an_access_trap_from_aligned_el1h_code` and
  `echo_challenges_carry_no_control_bytes_and_echo_in_order`: they tested
  the statistics snapshots, the register and FP probes that serial bytes
  started and the challenges of those phases, none of which krepi has; the
  test images check the timer interrupts, the registers and the FP/SIMD
  trap themselves, and `qemu_boot::tests::records` tests their judgment.
- The fixed instruction count of the legacy runs.
- The options `--elf`, `--repeats` and `--timeout`, the shared flag parser of
  the legacy suites and the phase report with its times.
- The legacy feature annotations `system.platform.qemu-boot` and
  `system.kernel.interrupts`.
