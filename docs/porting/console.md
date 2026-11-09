---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/console.rs
  - src/diagnostics/polled.rs
  - src/diagnostics/polled_tests.rs
  - src/diagnostics/emitter.rs
  - src/diagnostics/tests.rs
  - src/fault.rs
destination:
  - kernel/boards/qemu-virt/src/console.rs
  - kernel/boards/qemu-virt/src/console/tests.rs
  - kernel/boards/qemu-virt/src/console/polled.rs
  - kernel/boards/qemu-virt/src/console/polled/tests.rs
  - kernel/boards/qemu-virt/src/console/emitter.rs
  - kernel/boards/qemu-virt/src/console/emitter/tests.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/boards/qemu-virt/src/console.rs

## Summary

The serial console of the kernel, as plain code that the host tests run:
`print`, which formats a record with each LF written as CR LF within the
console bounds of a board; `write`, which writes bytes unchanged within the
same bounds; `echo`, the echo rule; `report_panic`, the panic record;
`failure_marker` and `report_failure`, the marker of a failed write and its
bounded write; and `window_ticks`, which turns the window of a record into
counter ticks. It takes the board console of `src/board/console.rs` and the
two diagnostic writers that it used: the polled writer of
`src/diagnostics/polled.rs`, with a deadline on a counter and a bound on the
attempts per byte, as `console::polled`, and the bounded emitter of
`src/diagnostics/emitter.rs`, as `console::emitter`, with their tests. From
the fatal records of `src/fault.rs` it takes the lines of the panic record
and the text that replaces a message that is not static.

`src/diagnostics` is an area that the
[classification](../conventions/porting.md#classification-of-the-legacy-areas)
does not list. It is ported: the allocation-free records, the bounded
writers, the frame-pointer walk and the counter watchdog of the prototype
kernel are plain code with host tests, which krepi takes with the code that
uses each. This change takes the polled writer and `emit_bounded`; the
fixed-capacity record of `src/diagnostics/record.rs`,
`emit_progress_bounded` and their tests come with the fault records, the
frame walk of `src/diagnostics/frames.rs` with fault symbolization, and the
watchdog of `src/diagnostics/watchdog.rs`, which only diagnostic
controllers used, with its first caller.

## Changes

- The bounds of the legacy console, `ATTEMPTS_PER_BYTE` and
  `FAILURE_ATTEMPTS`, one million each, and the window of a record, a
  quarter of the counter frequency, are platform parameters: the fields
  `attempts_per_byte`, `failure_attempts` and `window_ms` of `Bounds`, whose
  QEMU virt values, one million, one million and 250 ms, are
  `CONSOLE_BOUNDS` of the crate root and are stated in the
  [boot contract](../domains/boot-platform/boot/contract.md#platform-parameters).
  `window_ticks` computes the ticks of the window as the frequency times the
  milliseconds divided by 1,000, rounded down, in 128-bit arithmetic, which
  equals the legacy quarter of the frequency for 250 ms; a window that does
  not fit in 64 bits gives `u64::MAX` ticks, which a write refuses.
  [Testing](../conventions/testing.md#determinism-and-time) requires spin
  limits and windows to be platform parameters.
- The legacy `print` took the counter from the selected board and halted on a
  failure. `console::print` takes the bounds, the frequency and the counter as
  arguments and returns the result; the PL011 driver writes the failure
  marker through `report_failure` and halts, so the halt and the device stay
  target-only and the rest runs on the host. The markers are unchanged.
- `write` and `echo` are new: the echo writes each received byte unchanged
  and, after a carriage return, a line feed, through the new
  `write_bytes_polled` of `console::polled`, which writes bytes without the
  expansion of LF and with the bounds of `write_polled`. Both share the
  writer of the legacy module, whose start, with the check of the budget, is
  the new `Writer::start`; `write_polled` is otherwise unchanged.
- `RECORD_BYTES` is the legacy `MESSAGE_BYTES`, 1,024.
- `report_panic` writes the lines of the panic record of the legacy `panic`
  of `src/fault.rs`, lines 126-159: `CASXI_PANIC` with the static message
  or `dynamic_panic_message_omitted`, now the constant
  `DYNAMIC_PANIC_MESSAGE`, `CASXI_PANIC_LOCATION` when the panic has a
  location, and `CASXI_HALTED`. The legacy function formatted them into one
  buffer of 3,072 bytes, with the message cut to 384 bytes and the field
  `truncated=` that said whether it was cut, and wrote the buffer with
  `emit_progress_bounded` and 131,072 attempts per byte. Here each line is
  a record of `print` within the console bounds, with no `truncated=`
  field: a message that fits is written whole, one too long for a record
  fails it with `length` after the bytes that fit, and a line that fails
  ends the panic record. The location is `PanicLocation`, so that the host
  tests can give one.
- The variants of `PolledError` and the fields of `Emission` have
  documentation, as `missing_docs` requires; the documentation of the
  functions is written again. The line
  `//! Feature: krepi.platform.qemu-virt-boot` names the feature in each
  file.
- The tests of the polled writer are in `console/polled/tests.rs` and the
  tests of `emit_bounded` in `console/emitter/tests.rs`, in place of
  `polled_tests.rs` and the shared `tests.rs`.

## Tests carried over

| Legacy test | krepi test |
| --- | --- |
| `src/diagnostics/polled_tests.rs`: `long_record_survives_more_polls_at_the_same_device_rate`, `deadline_stops_a_busy_device_before_its_poll_cap`, `stopped_clock_still_has_a_finite_stall_bound`, `deadline_is_not_renewed_after_success_and_handles_counter_wrap`, `crlf_counts_against_the_byte_limit`, `ignored_formatter_errors_cannot_restart_output`, `invalid_budgets_never_touch_clock_or_device`, `formatter_failure_is_not_silently_accepted` | The same names in `kernel/boards/qemu-virt/src/console/polled/tests.rs` |
| `src/diagnostics/tests.rs:264-337`: `permanently_full_output_spends_only_the_total_budget`, `intermittent_output_retries_without_skipping_or_transforming_bytes`, `successful_writes_also_consume_attempts`, `empty_output_and_zero_budget_never_call_device` | The same names in `kernel/boards/qemu-virt/src/console/emitter/tests.rs` |

No expected value changed.

## Behaviour changes

| Change | Test |
| --- | --- |
| The bounds and the window are arguments, with the legacy values on QEMU virt; the window of 250 ms gives the legacy quarter of the frequency, also 0 ticks, which a write refuses, for a counter slower than 4 Hz | `console::tests::examples::ex2_a_stalled_device_fails_the_write_and_is_reported`, `console::tests::boundaries::the_failure_marker_is_bounded_by_its_attempts`, `console::tests::boundaries::the_window_is_converted_to_ticks`, `console::tests::boundaries::a_counter_too_slow_for_the_window_is_refused` |
| A failure returns its error, and the failure marker is written by `report_failure` with the failure attempts | `console::tests::examples::ex2_a_stalled_device_fails_the_write_and_is_reported`, `console::tests::boundaries::each_failure_has_its_marker` |
| Bytes can be written unchanged within the bounds of a record, and a received byte is echoed with a line feed after a carriage return | `console::tests::examples::ex3_the_echo_adds_lf_after_cr_only`, `console::tests::boundaries::a_write_of_bytes_keeps_the_bounds_of_a_record` |
| The panic record has no `truncated=` field and no frame trace; each of its lines is a record within the console bounds, a message too long for a record fails it with `length`, and no line follows a failed one | `console::tests::panic_record::a_static_message_is_written_with_its_location`, `console::tests::panic_record::a_dynamic_message_is_replaced_by_the_fixed_text`, `console::tests::panic_record::a_panic_without_a_location_has_no_location_record`, `console::tests::panic_record::a_message_too_long_for_a_record_ends_the_panic_record` |

## Hardware evidence to re-obtain

- The records and the echo on QEMU virt with one Cortex-A76, which the case
  `cold-boot-echo` of `cargo xtask qemu-boot` obtains. QEMU's PL011 never
  refuses a byte, so the bounds are shown by the host tests only.
- The bounds on the Pi 5 UART, with its own values, on the HIL bench
  (planned).

## Not carried over

- From `src/diagnostics/emitter.rs`: `emit_progress_bounded`, which no code
  of this change calls; it comes with the fault records, with the tests of
  `src/diagnostics/emitter_tests.rs`.
- From `src/diagnostics/tests.rs`: the 11 tests of the frame walk at lines
  1-215, which come with fault symbolization, and the 4 tests of `Record` at
  lines 216-262, which come with the fault records.
- From `src/fault.rs`: everything but the lines of the panic record; the
  [qemu-virt](qemu-virt.md) record lists it.
- The legacy feature annotation `system.kernel.foundations` of the
  diagnostics module and of `src/fault.rs`.
