---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/receipt.rs
  - tools/tests/kernel/foundations.rs
  - tools/tests/kernel/runtime_clock.rs
  - tools/tests/platform/qemu_boot.rs
  - tools/tests/services/recovery.rs
destination:
  - tools/src/receipt.rs
  - tools/src/receipt/tests.rs
treatment: ported
features: none
---

# Porting record: tools/src/receipt.rs

## Summary

Line matchers over raw serial bytes, and the parsers of the serial records
that the prototype kernel prints. `lines`, `find_line`, `exact_line`,
`ready`, `ready_line_named` and `halted` find complete lines and report each
as a `Match` with its byte range; `brk_exception` finds the breakpoint
exception record and its ELR; `records_with_prefix` and
`check_cpu_identity` check the one CPU identity record of an Arm
Cortex-A76; `DiagnosticCheck` checks the fault trace of a fatal diagnostic
line by line, and `trace` the one trace of a transcript, with `hex_value`;
`object_fields`, `object_field` and `fields_value` check and give the
object record; `split_lines` splits a transcript into lines, `build_ids`
finds the build records, and `parse_fields` checks a record of `key=value`
fields against the names it must hold.

The records keep the names of the prototype kernel, which start with
`CASXI_`, and the kernel of this repository writes its records under the
same names, as the
[boot contract](../domains/boot-platform/boot/contract.md#records) fixes
them. The captures of [`qemu`](tools-qemu.md) return `Match`, and the QEMU
boot suite of [`qemu_boot`](tools-qemu_boot.md) checks the CPU identity
record with `check_cpu_identity`. The module is ported with its unit tests and
with the tests of the legacy integration tests that tested it.

The legacy module wrote the bytes of a rejected line, token or record as
Python's `repr` of bytes and the names of a record with unexpected fields
as a Python list, the forms of the Python test programs whose parsers it
reproduced. These forms are not carried over; the bytes and the names are
written in the forms described under [Changes](#changes).

## Changes

- The bytes of a rejected line, token or record are written with the
  escapes of `<[u8]>::escape_ascii`, without a `b'...'` around them, in
  place of `debug_bytes`, Python's `repr` of bytes. Both write `\t`, `\r`,
  `\n`, `\'` and `\\`, and `\xNN` for another byte outside the printable
  ASCII range; `escape_ascii` also escapes a double quote, `\"`. The
  messages concerned are `Invalid CPU identity record: <record>`,
  `Expected build-bound raw register record: <line>`, `Unexpected
  diagnostic output: <line>`, `Malformed <marker> field: <token>` and
  `Empty or duplicate field: <token>`. The [`serial`](tools-serial.md) link
  writes its fatal records the same way.
- `Unexpected <marker> fields` gives the names of the record sorted by
  their bytes in Rust's debug form, `["a", "b"]`, or `[]`, in place of the
  names between single quotes as they are, `['a', 'b']`. The debug form
  escapes a backslash, a double quote and a control character.
- `DiagnosticCheck::result` gives a `serde_json` value with the keys
  `registers`, `frames` and `stop`, and the keys of each in the legacy
  order, and `fields_value` an object of strings in record order
  ([report values](tools-report.md#changes)).
- The documentation states the rules of the matchers and parsers: a line
  ends at `\n` with one optional `\r` before it, `parse_fields` separates
  fields at the ASCII white space of `u8::is_ascii_whitespace`, and
  `split_lines` splits at `\n`, `\r` and `\r\n`. It no longer names the
  regular expressions and Python functions that the legacy documentation
  compared them with, nor the Python test programs that held the legacy
  parsers.
- The tests of the legacy integration tests are unit tests in
  `tools/src/receipt/tests.rs`, below `receipt::tests`. Their numbered
  examples have descriptive names, as no feature document numbers them,
  and the record constants that several legacy files defined, `RECORD`,
  `OBJECT`, `HEADER`, `FRAME`, `STOP` and the transcript of the trace, are
  defined once.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/receipt.rs` `tests::complete_trace_is_accepted_and_rendered` | `receipt::tests::complete_trace_is_accepted_and_rendered` | Unchanged |
| `tools/src/receipt.rs` `tests::trace_rules_reject_wrong_frames_stops_and_halts` | `receipt::tests::trace_rules_reject_wrong_frames_stops_and_halts` | Changed: `Unexpected diagnostic output: CASXI_HALTED`. The message for a frame record in place of the register record is checked whole, `Expected build-bound raw register record: CASXI_BT index=0 fp=0x0000000000001100 lr=0x0000000000005000`, where the legacy test checked its start, `... b'CASXI_BT`. The other messages are unchanged |
| `tools/src/receipt.rs` `tests::object_records_require_every_field_once` | `receipt::tests::object_records_require_every_field_once` | Unchanged, the rows of `split_lines` and `build_ids` included |
| `tools/src/receipt.rs` `tests::trace_transcripts_bind_exception_and_halt` | `receipt::tests::trace_transcripts_bind_exception_and_halt` | Unchanged |
| `tools/src/receipt.rs` `tests::lines_strip_one_carriage_return` | `receipt::tests::lines_strip_one_carriage_return` | Unchanged |
| `tools/src/receipt.rs` `tests::ready_requires_a_complete_line` | `receipt::tests::ready_requires_a_complete_line` | Unchanged |
| `tools/src/receipt.rs` `tests::brk_exception_captures_the_link_register` | `receipt::tests::brk_exception_captures_the_link_register` | Unchanged |
| `tools/src/receipt.rs` `tests::cpu_identity_follows_the_python_rules` | `receipt::tests::cpu_identity_requires_one_arm_cortex_a76_record` | Unchanged for the identity rows. The row of `debug_bytes`, `b'a\'\n\x01'`, gives way to the message for an invalid record with a quote and a control byte, `CASXI_CPU a'\x01` followed by a newline: `Invalid CPU identity record: CASXI_CPU a\'\x01`. The newline ends the record, so it is not part of the message |
| `tools/tests/platform/qemu_boot.rs` `examples::ex1_real_identity_surrounded_by_boot_output` | `receipt::tests::a_cpu_identity_among_boot_output_is_accepted` | Unchanged |
| `tools/tests/platform/qemu_boot.rs` `examples::ex2_variant_and_revision_are_not_part_of_model_identity` | `receipt::tests::variant_and_revision_are_not_part_of_the_cpu_identity` | Unchanged |
| `tools/tests/platform/qemu_boot.rs` `examples::ex3_missing_duplicate_or_malformed_records_are_rejected` | `receipt::tests::missing_duplicate_or_malformed_cpu_identity_records_are_rejected` | Unchanged for the eight outputs, each of which is rejected. Each message is now checked exactly, where the legacy test only required a rejection: `Expected one CPU identity record, got 0` and `got 2`, `Invalid CPU identity record: <record>` for another model, a digit that is not hexadecimal and a further field, and `CPU identity is not Arm Cortex-A76: MIDR=0x00000000414fd03f` and `MIDR=0x00000000514fd0b1` for another part and another implementer |
| `tools/tests/kernel/foundations.rs` `examples::ex1_a_complete_object_record_is_accepted_in_record_order` | `receipt::tests::a_complete_object_record_is_accepted_in_record_order` | Unchanged |
| `tools/tests/kernel/foundations.rs` `examples::ex2_object_records_with_omitted_duplicate_or_invalid_fields_are_rejected` | `receipt::tests::object_records_with_omitted_duplicate_or_invalid_fields_are_rejected` | Unchanged |
| `tools/tests/kernel/foundations.rs` `examples::ex3_a_complete_trace_transcript_binds_the_exception_and_the_halt` | `receipt::tests::a_complete_trace_transcript_binds_the_exception_and_the_halt` | Unchanged |
| `tools/tests/kernel/foundations.rs` `examples::ex4_trace_transcripts_with_wrong_frames_stops_halts_or_identities_are_rejected` | `receipt::tests::trace_transcripts_with_wrong_frames_stops_halts_or_identities_are_rejected` | Unchanged |
| `tools/tests/kernel/runtime_clock.rs` `examples::ex5_fatal_breakpoint_record_is_bound_to_its_trace_and_halt` | `receipt::tests::a_fatal_breakpoint_record_is_bound_to_its_trace_and_halt` | Unchanged |
| `tools/tests/services/recovery.rs` `examples::ex4_streamed_receipts_require_complete_lines` | `receipt::tests::a_record_is_found_only_once_its_line_is_complete` | In part: the rows of `find_line` and `lines` over every prefix of a summary line and of a stage line, which no prefix yields and the whole line yields once, unchanged. The two lines are literals in the format that the legacy test built them in, `CASXI_RECOVERY version=1 cycle=1 ...` and `CASXI_RECOVERY_STAGE v=1 phase=4 nonce=0x51 value=2 checksum=...`, and the match of the whole summary line is checked with its range. The assertions on the parsers of the recovery suite are not carried over; see [Not carried over](#not-carried-over) |

New tests: `receipt::tests::fields_split_at_ascii_white_space_but_not_at_a_vertical_tab`,
records whose fields are separated by a space, a tab, a carriage return, a
newline, a form feed or several of them, and by a vertical tab, which stays
inside its token, with the messages for another marker and a non-ASCII
value; and
`receipt::tests::rejected_tokens_records_and_field_names_are_written_with_escapes`,
the escaped bytes of a malformed token with a quote, of one with double
quotes, a backslash and a DEL, of an empty and a repeated field and of a
CPU identity record with a quote, and the names of unexpected fields with
a backslash, a control byte and a quote, and of a record with no field.

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| A rejected token in a message | `Malformed CASXI_X field: b'it\'s'` | `Malformed CASXI_X field: it\'s` | `receipt::tests::rejected_tokens_records_and_field_names_are_written_with_escapes` |
| A double quote in a rejected token | `"` | `\"` | `receipt::tests::rejected_tokens_records_and_field_names_are_written_with_escapes` |
| A rejected record or line in a message | `Invalid CPU identity record: b'CASXI_CPU it\'s'`, `Unexpected diagnostic output: b'CASXI_HALTED'` | `Invalid CPU identity record: CASXI_CPU it\'s`, `Unexpected diagnostic output: CASXI_HALTED` | `receipt::tests::rejected_tokens_records_and_field_names_are_written_with_escapes`, `receipt::tests::cpu_identity_requires_one_arm_cortex_a76_record`, `receipt::tests::trace_rules_reject_wrong_frames_stops_and_halts` |
| The names of unexpected fields | Each name between single quotes as it is: `['a\b', 'c', 'it's']` with the control byte U+0001 itself after `c` | `["a\\b", "c\u{1}", "it's"]` | `receipt::tests::rejected_tokens_records_and_field_names_are_written_with_escapes` |

The documentation of the legacy Pi 5 boot suite,
`tools/src/suites/platform/pi5_boot.rs`, recorded two rules of this module
as differences from the Python programs that the suite replaced. Each is
fixed by a test:

| Rule | Treatment | Test |
| --- | --- | --- |
| `parse_fields` does not separate fields at a vertical tab, where Python's `bytes.split()` does; the tab stays inside its token | Kept | `receipt::tests::fields_split_at_ascii_white_space_but_not_at_a_vertical_tab` |
| The token of `Malformed <marker> field` and `Empty or duplicate field` and the record of `Invalid CPU identity record` are written as `b'...'` with `\'` for a single quote, and the names of `Unexpected <marker> fields` between single quotes as they are | Changed: the escapes of `escape_ascii` without `b'...'`, and the names in Rust's debug form; see the table above | `receipt::tests::rejected_tokens_records_and_field_names_are_written_with_escapes` |

## Hardware evidence to re-obtain

None for the module, which runs on the host. The records that it parses
came from QEMU and board runs of prototype images; the records of krepi
images are obtained from their own runs on QEMU virt and on the HIL bench
(planned).

## Not carried over

- `debug_bytes`, Python's `repr` of bytes for messages; `escape_ascii`
  writes the bytes.
- The Python list form of the names in `Unexpected <marker> fields`.
- The parts of `examples::ex4_streamed_receipts_require_complete_lines` of
  `tools/tests/services/recovery.rs` that test the parsers of the recovery
  suite, `stage_line` and `stages`, and build its records from a document
  of the suite. The suite is not ported, and the record lines are literals.
- The other tests of the four legacy integration test files, which test
  modules that are not part of this module. The ELF parts of
  `tools/tests/kernel/foundations.rs` are recorded with
  [`elf`](tools-elf.md).
