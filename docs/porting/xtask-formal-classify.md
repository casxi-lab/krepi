---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - xtask/src/formal/run.rs
  - xtask/src/formal/inventory.rs
  - xtask/src/formal/legacy.rs
destination:
  - xtask/src/formal/classify.rs
treatment: ported
features: none
---

# Porting record: xtask/src/formal/classify.rs

## Summary

The check of a proof target's registration against its extraction, from the
proof gate of the CAS project: `classify` and `classify_items` of
`run.rs` (lines 313 to 342 and 347 to 452), which hold the local functions
that an extraction translates and cuts and the external items that it
reaches against the `proves`, `unclosed`, `derived` and `unconstrained`
lists of the target; the mapping of the Rust names of the translation to
inventory keys, `key_for_rust_name`, `key_for_translated`,
`is_default_method` and `is_derived_name` of `inventory.rs` (lines 491 to
508, 518 to 528, 532 to 543 and 550 to 567); and `derived_problems` of
`legacy.rs` (lines 108 to 146), the check of the `derived` entries against
the source. They are taken because the registration of a target must agree
with what the pinned tools extract, under the keys that
`cargo xtask formal check` gives the production functions
([proof targets](../formal-verification.md#proof-targets)). They are
released under the MIT License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

The rest of `xtask/src/formal/classify.rs` is new code: `key_of`, which
finds the module of the reported source file in the inventory, maps the
name with it and refuses a name that maps to no function of the inventory,
and the record of what the check found. The phase of the gate that extracts
a target and calls the check is planned.

## Changes

- The key of a Rust name keeps every path segment between the module of its
  source file and the item, so that a function of an inline module has the
  key that the inventory gives it, `file#inner::f`, and a method of an
  implementation in one `file#inner::Type::f`. The CAS project kept only
  the last segment of a name without an implementation, and so mapped a
  function of an inline module to the key of a function of that name in the
  file. The mapping takes the crate and the module of the file from the
  inventory, which records the module of each production file, and returns
  nothing for a name that is not below the module. A derived method and a
  hand-written one of a type of the same name in an inline module, which
  the CAS project mapped to one key, so have two; a `derived` entry that
  several Rust names reach is still refused, such as the key of the
  derived `eq` of a type that also implements `PartialEq` for another type
  by hand.
- The default method of a trait keeps its trait as its owner, as in the CAS
  project, with the inline modules before the trait; with the module of the
  file, the key is the same as that of `key_for_rust_name`.
- The braces of the implementation in a name are its first opening brace
  and the one that closes it; the CAS project took the last opening and the
  last closing brace.
- A reached local function maps to exactly one function or derived method
  of the inventory, or it is not registered and the target fails: the body
  of a closure, which the CAS project assigned to its enclosing function
  with further checks, a loop that the tools place in a file outside the
  package, which the CAS project assigned through its parent, a function in
  the body of another, and a method of a trait implementation whose key the
  inventory numbers. The diagnostics name the rules of the
  [provable subset](../conventions/provable-subset.md) that avoid the first
  two. The code that assigned closures and loops to their owners is not
  taken, because the provable subset leaves out both.
- `classify` takes the inventory and the directory of the package, whose
  source paths the tools report, and returns the problems with a record of
  keys; the CAS project read the inventory from the checkout and returned a
  JSON record. The external items that the check compares with
  `unconstrained` leave out the local items that are cut, as in the CAS
  project.
- `derived_problems` checks a `derived` entry against the derived methods
  that the inventory records for the production types of its file, instead
  of scanning the file again.

## Tests carried over

The inputs are the translations that the pinned Charon and Aeneas wrote for
four modules of a crate, kept with its sources in
`xtask/src/formal/fixtures/classify/`, and not the names of the CAS tests,
which an earlier Aeneas spelled; the expected keys are those of krepi's
inventory. Where a test changes a captured translation, the test writes
the change.

| CAS project test | krepi test | Expected values |
| --- | --- | --- |
| `run.rs` `tests::default_and_derived_methods_are_classified`, line 2794 | `tests::default_and_derived_methods_are_classified` | A default method with its loop and two derived methods of the captured translation, which a registration that names them passes; a derived `eq` and a hand-written `eq` of the same key, which a `derived` entry refuses, with the hand-written one translated and cut |
| `inventory.rs` `tests::derived_names_are_recognised`, lines 692 to 709 | `tests::derived_names_are_recognised` | The derived methods of the captured translation, and the same forms that are not derived methods |
| `inventory.rs` `tests::aeneas_names_map_to_keys`, lines 813 to 829 | `tests::aeneas_names_map_to_keys` | The keys of an inherent method, a trait method, a free function, a function of an inline module and the methods of a generic type; every local function of the captured translations maps to a key of the inventory |
| `inventory.rs` `tests::default_methods_map_to_the_scanned_key`, the translated names of lines 716 to 780 | `tests::default_methods_map_to_the_scanned_key` | Default methods with one loop and with two, a default method named `default` and a free function named `default` with its loop, as the pinned Aeneas names them, map to the keys of the inventory; a loop index must be a number |
| `legacy.rs` `tests::derived_entries_need_a_derive_and_no_source`, line 759 | `tests::derived_entries_need_a_derive_and_no_source` | A production function, a malformed key and a key without a derive are refused |

The other tests of the module are new: one for each rule of the check, on
the captured translation with the change that breaks the rule written in the
test, and the names that map to no key.

## Behaviour changes

- A function of an inline module has its own key. Test:
  `tests::aeneas_names_map_to_keys`.
- A closure, a loop placed in another file, a function in a body and a
  method whose key is numbered are not registered. Tests:
  `tests::the_body_of_a_closure_maps_to_no_key_and_is_not_registered`,
  `tests::a_loop_in_the_file_of_a_macro_maps_to_no_key_and_is_not_registered`
  and `tests::names_that_do_not_tell_functions_apart_are_not_registered`.

## Hardware evidence to re-obtain

None: the check reads text on the host.

## Not carried over

- The assignment of closures and of loops in macro files to their owners
  (`source_owners.rs`), with its tests: the provable subset leaves out
  closures given as callbacks and macro loop conditions, and a function
  that maps to no key is not registered.
- The JSON record of the classification: the receipt of a target is
  written by the phase that extracts it.
