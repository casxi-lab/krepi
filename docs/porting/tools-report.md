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

The values that tool reports are built from, their JSON text, and the UTC
time stamps that reports record. The legacy module defined `Value`, a JSON
value whose objects kept the order in which their keys were set, with a
hand-written writer that reproduced the output of Python's `json.dumps`, so
that reports of the Rust and Python runners compared field by field. There
is no Python runner here, and the host tools take JSON from a crate
([dependencies](../../CONTRIBUTING.md#dependencies)): a report is a
`serde_json` value, and `to_json` writes the pretty form of the crate. The
time stamps are ported with the changes listed under [Changes](#changes).

## Changes

- `Value` is `serde_json::Value`, which the module re-exports with `Map`,
  the type of its objects. The crate is built with its `preserve_order`
  feature, so an object keeps the order in which its keys were first
  inserted, and inserting a key that is present replaces its value in place,
  as the legacy `set` did. The legacy constructor `object`, `set` and the
  accessors give way to `Map::new`, `Map::insert`, the `json!` macro,
  indexing and the accessors of the crate, which callers use directly.
- `to_json` is a function of the module that writes the pretty form of
  `serde_json` with a final newline: two-space indentation, `": "` after a
  key, and `[]` and `{}` for an empty array and an empty object, which is
  the layout of the legacy text. Strings are escaped as the legacy writer
  escaped them: quotes, backslashes and C0 control characters, with the
  short escapes for backspace, form feed, line feed, carriage return and tab;
  DEL and non-ASCII text are kept as UTF-8. Floats are written by the crate;
  see [Behaviour changes](#behaviour-changes).
- `utc_now` writes RFC 3339 with six fraction digits and the offset `Z`.
  `utc_text` and `utc_stamp_of` format a given time, so that tests use fixed
  instants; `utc_now` and `utc_stamp` format the current time.
- The module and function documentation no longer refers to Python.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/report.rs` `tests::json_matches_python_formatting` | `tools/src/report.rs` `tests::a_report_keeps_its_key_order_and_two_space_indentation` | Unchanged. The report is built with `json!` in the order in which the legacy test set its keys |
| `tools/src/report.rs` `tests::set_replaces_in_place` | `tools/src/report.rs` `tests::inserting_a_present_key_replaces_its_value_in_place` | Unchanged: `a` holds 3 and stays before `b`. The order is read from `to_json`, because the equality of `serde_json` objects does not compare the order of their keys |
| `tools/src/report.rs` `tests::timestamps_have_python_shapes` | `tools/src/report.rs` `tests::timestamps_are_rfc_3339_and_basic_iso_8601_in_utc` | Changed: the offset `+00:00` becomes `Z`, and exact texts at fixed instants replace the lengths of the current time, which only keeps its shape checked. `civil_from_days(20_740)` is unchanged |

`tests::floats_print_like_pythons_repr` is not carried over; see
[Not carried over](#not-carried-over).

## Behaviour changes

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| Floats with a decimal exponent from -9 to -5 | Python's `repr`: scientific, with an exponent of at least two digits, `1e-05`, `8.392747792833824e-08` | The shortest form of `serde_json`: positional at -5 and with an unpadded exponent below, `0.00001`, `8.392747792833824e-8`. The other thirteen values of the legacy float test, `1e+16`, `1.5e+300` and `5e-324` among them, are written as before | None; `serde_json` writes floats |
| NaN and infinities | `NaN`, `Infinity`, `-Infinity`, which are not JSON | `null`, the value that `serde_json` gives a float without a JSON form | None; `serde_json` converts floats |
| `utc_now` | `2026-10-14T07:45:17.123456+00:00` | `2026-10-14T07:45:17.123456Z` | `tests::timestamps_are_rfc_3339_and_basic_iso_8601_in_utc` |

## Hardware evidence to re-obtain

None. The module runs on the host and had no QEMU or board results.

## Not carried over

- The `Value` type, its accessors and conversions, and its hand-written JSON
  writer, which `serde_json` replaces. Of its parts without a counterpart in
  this module, `insert_front` has no caller in this crate, and `sorted`,
  which the legacy serial capture called, gives way there to
  `Value::sort_all_objects`. The crate offers close equivalents:
  `Map::shift_insert` at index 0 inserts a key at the front, but moves a
  present key there instead of leaving it in place, and
  `Value::sort_all_objects` sorts the keys of every object in the same byte
  order, in place instead of in a copy. `Value::Big`, an integer
  beyond 64 bits that held raw card identities, has no ported caller, and
  `serde_json` holds integers of at most 64 bits.
- `tests::floats_print_like_pythons_repr`. It tested `python_repr`, the
  hand-written float text, which is removed; `serde_json` writes floats, and
  krepi tests do not test the crate.
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
