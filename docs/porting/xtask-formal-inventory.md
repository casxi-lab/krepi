---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/inventory.rs
destination:
  - xtask/src/formal/inventory.rs
treatment: redesigned
features: none
---

# Porting record: xtask/src/formal/inventory.rs

## Summary

The inventory of the proof gate of the CAS project is a lexical scan of the
production Rust functions that skips comments and literals, follows `mod`,
`impl` and `trait` blocks, ignores items under `#[cfg(test)]` and digests
each function's text. krepi's inventory is written again on the syntax tree
that `syn` parses, with the rules of
[formal verification](../formal-verification.md#legacy-inventory-and-admission),
so the treatment is redesigned. Taken from the CAS project are the key of a
function, `<path>#[<inline module>::]<Owner>::<name>`, which the proof
target registry uses; the methods that the derived implementations of the
standard traits define (`derived_method`, lines 158 to 170); and the inputs
of five of its tests, which the tests of krepi's inventory use as
acceptance fixtures, with the results that krepi's rules give. They are
released under the MIT License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

Everything else in `xtask/src/formal/inventory.rs` is new code: the walk of
the module files by the rules of rustc from the roots that `cargo metadata`
reports, the numbering of keys, the tables of open obligations of the
contracts, `verification/open.json` and `cargo xtask formal check`.

## Changes

- A file that is not a regular file of UTF-8 text, or that `syn` does not
  parse, fails the check; the lexical scan read any text.
- The module files are found from the roots of the targets by the rules of
  rustc, `#[path]` and inline modules included, and a tracked file that no
  root and no `mod` declaration reaches fails the check. The CAS project
  scanned every file below its source directory.
- A file that a test module file reaches is test code as well; the CAS
  project counted it as production code.
- `#[cfg(test)]` marks test code only in exactly this form, on any item,
  an inline module, an implementation or a trait included.
- A file in which the identifier `include`, raw or not, appears at any
  depth of the tokens fails the check, so that neither a path, nor an
  import that renames it, nor a macro that is given its name reaches
  `include!`.
- Methods of trait implementations in one file that have the same key take
  `#2`, `#3` and so on in source order; any other repeated key fails the
  check. A method of an implementation whose self type has no path, such as
  a tuple, fails the check instead of being keyed.
- Functions inside function bodies are not counted, as in the CAS project,
  and functions in the initializers of constants and statics are. A
  production `macro_rules!` macro whose body holds `fn` fails the check: the
  CAS project counted the functions written in a macro body by their literal
  names where the macro is defined, which names no generated function.
- Neither line numbers nor digests of functions are recorded:
  `verification/legacy.json` stays empty, and the whole inventory is checked
  on every run.

## Tests carried over

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `tests::functions_are_found_with_owners`, lines 598 to 614, with its input `SOURCE` (lines 573 to 595) | `tests::functions_are_found_with_owners` | The names and the test module declaration unchanged; the line of a function is not recorded. The test also keys the functions in a crate of the fixture tree |
| `tests::test_module_files_are_not_production`, lines 626 to 655 | `tests::test_module_files_are_not_production` | The keys unchanged, below the fixture crate `kernel/demo/`. The test also checks the three test module files and that all seven files are reached |
| `tests::derives_name_the_methods_they_define`, lines 658 to 689 | `tests::derives_name_the_methods_they_define` | Unchanged. The last line of the input, `let s = "#[derive(Clone)] struct InString;";`, is not an item, which the lexical scan skipped and `syn` rejects; it is replaced by `const S: &str = "#[derive(Clone)] struct InString;";`. The unchanged input is that of `tests::a_file_that_does_not_parse_fails` |
| `tests::default_methods_map_to_the_scanned_key`, the scan of lines 713 to 715 and 721 | `tests::default_methods_are_keyed_by_their_trait` | `src/f.rs#Ring::normalize`, below the fixture crate |
| `tests::test_attributes_end_at_their_type`, lines 783 to 810 | `tests::test_attributes_end_at_their_type` | Unchanged |

The other tests of the module are new.

## Behaviour changes

- A file that is no UTF-8 regular file, does not parse, names `include` or
  is not reached fails the check. Tests:
  `tests::a_tracked_file_that_is_no_utf8_regular_file_fails`,
  `tests::a_file_that_does_not_parse_fails`,
  `tests::a_file_with_include_fails` and
  `tests::a_file_that_no_mod_reaches_fails`.
- Functions in initializers are counted, and a production macro whose body
  holds `fn` fails the check. Tests:
  `tests::functions_outside_function_bodies_are_found_in_initializers` and
  `tests::a_macro_whose_body_holds_fn_fails`.
- Test module files and the files that they reach are test code. Tests:
  `tests::test_module_files_are_not_production` and
  `tests::a_test_module_file_named_by_a_path_attribute_is_reached_and_skipped`.
- Methods of trait implementations with one key are numbered, and other
  repeated keys fail. Tests:
  `tests::methods_of_trait_implementations_with_one_name_are_numbered` and
  `tests::other_duplicate_keys_fail`.

## Hardware evidence to re-obtain

None: the inventory reads text on the host.

## Not carried over

- The lexical scanner, the digests and line numbers of functions and
  `production` (lines 1 to 157 and 173 to 490), with the test
  `tests::digests_ignore_layout_but_not_content` (lines 617 to 623): the
  inventory parses with `syn`, and `verification/legacy.json` records no
  digest.
- `key_for_rust_name`, `key_for_translated` and `is_derived_name`
  (lines 491 to 567), with the tests `tests::derived_names_are_recognised`
  (lines 692 to 709), `tests::aeneas_names_map_to_keys` (lines 813 to 829)
  and the half of `tests::default_methods_map_to_the_scanned_key` that maps
  translated names (lines 716 to 780): they map the names of the
  translation to keys, which the check of the registry against the
  extraction results (planned) needs.
