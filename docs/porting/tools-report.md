---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/report.rs
destination:
  - tools/src/report.rs
treatment: ported
features: none
---

# Porting record: tools/src/report.rs

## Summary

The values that tool reports and receipts are built from: `Value`, a JSON
value whose objects keep the order in which their keys were set, with its
accessors, `sorted` for a copy with every object's keys in code-point order,
and `to_json` for its text; and the UTC time stamps that reports record. The
value type and its accessors are ported as they are. The legacy JSON text and
time stamps reproduced the output of Python's `json.dumps` and `isoformat`,
so that reports of the Rust and Python runners compared field by field; there
is no Python runner here. The layout of the JSON text and the quoting of its
strings now follow the receipt of `cargo xtask check`, and floats and time
stamps, which that receipt does not contain, follow the rules given under
[Changes](#changes).

## Changes

- String literals are quoted by the rule of `xtask/src/receipt.rs`: quotes,
  backslashes, line feed, carriage return and tab by their short escapes,
  every other C0 control character and DEL as `\u00XX`, and everything else,
  non-ASCII text included, as UTF-8.
- A finite float is written in its shortest round-trip digits, positional
  with at least one fractional digit for decimal exponents from -4 to 15 and
  otherwise scientific with an unpadded exponent that carries a sign only
  when negative. A NaN or an infinity, which JSON cannot represent, is
  written as `null`. The public `python_repr` that wrote Python's float text
  is removed; the float form is internal to the writer.
- `utc_now` writes RFC 3339 with six fraction digits and the offset `Z`.
  `utc_text` and `utc_stamp_of` format a given time, so that tests use fixed
  instants; `utc_now` and `utc_stamp` format the current time.
- The module and function documentation no longer refers to Python.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/report.rs` `tests::floats_print_like_pythons_repr` | `tools/src/report.rs` `tests::floats_print_in_their_shortest_round_trip_form` | Changed for four of the fifteen values, which are scientific: `1e-05`, `8.392747792833824e-08`, `1e+16` and `1.5e+300` become `1e-5`, `8.392747792833824e-8`, `1e16` and `1.5e300`. The positional values and `5e-324` are unchanged. The values are read from `to_json` |
| `tools/src/report.rs` `tests::json_matches_python_formatting` | `tools/src/report.rs` `tests::json_has_two_space_indentation_and_keeps_text_as_utf8` | Unchanged |
| `tools/src/report.rs` `tests::set_replaces_in_place` | `tools/src/report.rs` `tests::set_replaces_in_place` | Unchanged; extended with `insert_front` |
| `tools/src/report.rs` `tests::timestamps_have_python_shapes` | `tools/src/report.rs` `tests::timestamps_are_rfc_3339_and_basic_iso_8601_in_utc` | Changed: the offset `+00:00` becomes `Z`, and exact texts at fixed instants replace the lengths of the current time, which only keeps its shape checked. `civil_from_days(20_740)` is unchanged |

New tests cover non-finite values and negative zero, the escapes of every
control character and of DEL, nested arrays and integers of every width,
sorting of nested objects, and the integer accessor.

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| Backspace and form feed in strings | `\b`, `\f` | `\u0008`, `\u000c` | `tests::control_characters_and_del_are_escaped_and_other_text_is_kept` |
| DEL in strings and keys | Kept as it is, so that a port name with DEL appeared raw in the serial capture receipt | `\u007f` | `tests::control_characters_and_del_are_escaped_and_other_text_is_kept` |
| Non-ASCII text in strings and keys | Kept as UTF-8, where the Python runner escaped it | Unchanged: kept as UTF-8 | `tests::json_has_two_space_indentation_and_keeps_text_as_utf8`, `tests::control_characters_and_del_are_escaped_and_other_text_is_kept` |
| Scientific floats | Signed exponent of at least two digits, `1e+16`, `1e-05` | Unpadded exponent, signed only when negative, `1e16`, `1e-5` | `tests::floats_print_in_their_shortest_round_trip_form` |
| NaN and infinities | `NaN`, `Infinity`, `-Infinity`, which are not JSON | `null` | `tests::negative_zero_and_values_without_a_json_form` |
| `utc_now` | `2026-10-14T07:45:17.123456+00:00` | `2026-10-14T07:45:17.123456Z` | `tests::timestamps_are_rfc_3339_and_basic_iso_8601_in_utc` |

## Hardware evidence to re-obtain

None. The module runs on the host and had no QEMU or board results.

## Not carried over

- `python_repr`, Python's `repr` of a float, which outside the writer only a
  legacy record verifier called.
- `to_json_sorted_line`, `to_json_canonical`, `to_json_canonical_utf8` and
  the ASCII-escaping string writer behind them. They reproduced Python's
  `json.dumps` with sorted keys, compact separators and escaped non-ASCII
  text for the legacy record verifiers and the digests those verifiers
  compared, which are not ported.
- `write_json`, a helper that writes `to_json` to a file. No module of this
  crate calls it; the prototype suites, cycle runner and record verifiers
  wrote their reports with it.
