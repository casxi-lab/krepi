---
source: cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78
paths:
  - verification/qualification/Cargo.toml
  - verification/qualification/src/lib.rs
  - verification/qualification/cases.json
  - verification/Casxi/Qualification/Arithmetic.lean
  - verification/Casxi/Qualification/Checked.lean
  - verification/Casxi/Qualification/SingleLoop.lean
  - verification/externals/Qual/StrFrom/FunsExternal.lean
  - verification/externals/Qual/MatchMachineArc/FunsExternal.lean
  - verification/externals/Qual/MatchMachineArc/TypesExternal.lean
  - verification/externals/Qual/TermLayoutCut/FunsExternal.lean
  - verification/externals/Qual/TermLayoutCut/TypesExternal.lean
destination:
  - verification/qualification/
  - verification/Krepi/Qualification/Arithmetic.lean
  - verification/Krepi/Qualification/Checked.lean
  - verification/Krepi/Qualification/SingleLoop.lean
  - verification/externals/Qual/
treatment: ported
features: none
---

# Porting record: verification/qualification/

## Summary

The qualification of the proof gate of the CAS project, which records the
outcome of the pinned Charon and Aeneas on small code shapes:

- the qualification crate, one module per shape, with 103 of its 112 cases
  in `cases.json`: those whose expected external functions and types reach
  no `num-*` crate;
- the 3 proofs of those cases that the gate keeps, of the cases
  `arithmetic`, `checked` and `single-loop`;
- the 5 reviewed external declaration files of the 3 kept cases with a
  `models` directory, `str_from`, `match-machine-arc` and `term-layout-cut`.

They are taken because the expectations of these cases were worked out
against the behaviour of the tools and record which shapes they translate,
reject, or translate into Lean that does not type-check. The crate, the
cases, the proofs and the external declarations are released under the MIT
License as part of krepi, as the
[porting conventions](../conventions/porting.md#licensing-of-ported-code)
state for the tooling taken from the CAS project.

New in krepi, and not taken from the CAS project:

- the 9 cases after `division-walk` in `cases.json` and their modules at the
  end of `src/lib.rs`: `cfg-shape` and `const-generic`, and one case for each
  of the items R1 to R7 of the
  [provable Rust subset](../conventions/provable-subset.md#constructs-and-alternatives),
  whose shapes follow the Examples there;
- the reviewed external types of `r7-private-enum`,
  `verification/externals/Qual/R7PrivateEnum/TypesExternal.lean`;
- the definitions in `verification/Krepi/Qualification/Models/`
  (`Arc.lean` and `FromStr.lean`), which the external declarations of
  `str_from`, `match-machine-arc` and `term-layout-cut` use. They are
  written from the types that those declarations need and from the
  documentation of the Rust standard library alone; the definitions of the
  CAS project that its declarations used were not read. They serve only the
  type checking of these three cases: they are not models, are not
  registered in `verification/models.json`, and no proof target uses them.

## Changes

### The crate

- The package is renamed `formal-qualification`, so the crate is
  `formal_qualification`, in place of the names of the CAS project. Its
  manifest declares an empty `[workspace]`, so that the crate is a workspace
  of its own with its own `Cargo.lock`, which holds the crate alone. The
  manifest gains `license = "MIT"`, which every krepi manifest declares, and
  a new description, and keeps `unsafe_code = "forbid"`.
- The 4 dependencies (`num-bigint`, `num-integer`, `num-rational`,
  `num-traits`) are removed, so the crate depends on no crate. The lint
  table declares the configuration `board` with the value `pi5`, which
  `cfg_shape` tests.
- The modules of the 9 cases that reach a `num-*` crate are removed with
  their documentation (lines of `src/lib.rs`): `pub mod
  rewrite_value_providers;` (10) and the file
  `src/rewrite_value_providers.rs`, `big_integers` (351 to 362),
  `rationals` (364 to 384), `reference_slice` (720 to 777),
  `field_rational_instance` (1241 to 1305), `series_summer_owned` (1831 to
  2147), `to_primitive_default` (9153 to 9163), `to_primitive_own` (9165 to
  9178) and `series_parameters` (9180 to 10036). No other module refers to
  them. The helper modules `budget` and `meter`, which have no case of their
  own, are kept.
- Documentation:
  - the crate documentation (lines 1 to 8) names the krepi proof gate and
    `cargo xtask formal run`, says that the shapes up to `division_walk`
    come from the CAS project, whose library their documentation calls "the
    library", and that the modules after it record shapes of the provable
    subset;
  - the documentation of `str_from` (lines 12 to 14) says that the
    conversion is replaced by its reviewed external declaration, and no
    longer names the UTF-8 model and its vector generator;
  - the documentation of `default_self_call` expects the Lean error with
    the name derived from the new crate name,
    `...SelfCallSeven.Insts.Formal_qualificationDefault_self_callSelfCallDivisorsU8`,
    which the pinned tools report;
  - the documentation of `term_layout_cut` says that the case installs
    reviewed external declarations in which `Arc` is a structure, in place
    of the structure model of `Arc`.
- The 9 new modules are appended after `division_walk`: `cfg_shape`,
  `const_generic`, `r1_function_item_value`, `r2_iterator_any`,
  `r3_iterator_flatten`, `r4_closure_callback`,
  `r5_stop_path_borrow_join`, `r6_same_enum_name` with the modules `objects`
  and `capabilities`, and `r7_private_enum`. Each defines the types it uses.

### The cases

`cases.json` keeps schema 1 and the formatting of the CAS project. Its
cases are the 103 kept cases in the order of the CAS project, then the 9 new
ones. In the CAS project the kept cases are 67 translated, 28 rejected and
8 ill-typed (5 with their type errors in `Funs.lean`, 3 in `Types.lean`); 4
have `opaque`, 2 `loop_sources`, 3 `models` and 3 `proof`. After the
[revised expectations](#revised-expectations) of 27 of them, which follow
the pinned tools, they are 76 translated, 19 rejected and 8 ill-typed. The
other changes to the kept cases are mechanical and follow from the changes
to the crate:

| Rule | Field | Cases |
| --- | --- | --- |
| The cases that reach a `num-*` crate are removed | All | `big-integers`, `rationals`, `reference-slice`, `field-rational-instance`, `series-summer-owned`, `to-primitive-default`, `to-primitive-own`, `series-parameters`, `rewrite-value-providers` |
| The crate name of the CAS project becomes `formal_qualification` | `diagnostics`: 100 occurrences in 63 entries | `nested-loop`, `option-reference-eq`, `floats`, `return-before-loop`, `flag-before-loop`, `loop-in-branch`, `owned-before-loop`, `registry-static-reference`, `registry-str-names`, `const-str-names`, `string-literal-return`, `function-pointers`, `carried-term-walk`, `view-map-loop`, `view-map-range`, `view-index-loop`, `view-value-join`, `view-borrowed-helper`, `indexed-field-sum`, `collection-tree-walk`, `collection-tree-frame-enum`, `collection-tree-keyed-frames`, `collection-value-instance`, `moving-if-join`, `unwrap-in-loop` |
| The same | `external_functions`: 13 occurrences in 12 entries | `nested-loop`, `binary64-bits`, `binary64-values`, `observations`, `return-before-loop`, `flag-before-loop`, `loop-in-branch`, `owned-before-loop` |
| The same | `external_types`: 3 occurrences in 3 entries | `observations`, `term-layout-cut` |
| The proofs that are not kept are removed | `proof` | `str_from`, `binary64-values`, `clock`, `observations`, `field-interface`, `polynomial-interface`, `default-method`, `coefficient-map`, `registry-records`, `series-summer`, `literal-variant-match`, `registry-items`, `elimination-skeleton` |
| The kept proofs name the namespace `Krepi.Qualification` | `proof` | `arithmetic` (`Krepi.Qualification.Arithmetic.mul_mod_spec`), `checked` (`Krepi.Qualification.Checked.add_within_spec`), `single-loop` (`Krepi.Qualification.SingleLoop.charge_each_spec`) |
| The directories of reviewed external declarations keep their paths, which now hold the krepi files | `models` | `str_from`, `match-machine-arc`, `term-layout-cut` |
| The source file of a loop is reported relative to the crate, which is a workspace of its own | `loop_sources`: `verification/qualification/src/lib.rs` becomes `src/lib.rs` | `unwrap-in-helper` (1 entry), `division-walk` (4 entries) |

The 9 new cases record what the pinned tools gave on `darwin-arm64` with the
arguments and environment of the extraction of `cargo xtask formal run`,
each extraction and each Lake build in a directory of its own:

| Case | Expectation |
| --- | --- |
| `cfg-shape` | Translated; the one loop is that of `map_pages`, the helper of the default configuration |
| `const-generic` | Translated, without external items |
| `r1-function-item-value` | Rejected: Aeneas stops at a lifetime constraint that it does not support, and `Iterator::any` is an external function |
| `r2-iterator-any` | Translated; `Iterator::any` is an external function |
| `r3-iterator-flatten` | Ill-typed in `Funs.lean`: the library has no `flatten` in its `Iterator` |
| `r4-closure-callback` | Translated, without external items: the library defines `Result::map_err` |
| `r5-stop-path-borrow-join` | Translated, without external items |
| `r6-same-enum-name` | Ill-typed in `Check.lean`: the two `Discriminant` instances `instDiscriminantErrorIsize` cannot be imported together |
| `r7-private-enum` | Ill-typed in `TypesExternal.lean`: the `discriminant` attribute rejects the private enumeration with `invalid scope` |

`r6-same-enum-name` has a form that no case of the CAS project has: its
`start_from` is empty and its `parts` list two modules, each with its own
`module` and `start_from`, which are extracted separately; the gate writes a
module `Check.lean` in the directory of the case that imports the `Funs`
module of each part. `r7-private-enum` extracts `Phase` with `opaque`, so
that it is an external type, and names the directory of its reviewed
external types in `models`.

### The proofs

- The files move to `verification/Krepi/Qualification/`, and the proofs
  and the generated definitions take the namespaces `Krepi.Qualification`
  and `KrepiGen` in place of those of the CAS project.
- Each file is a Lean `module`: it imports the generated definitions with
  `public import`, and its theorem is `public`, so that its proof is
  private.
- The documentation of `Arithmetic.lean` says "as in prime-field
  arithmetic" in place of "as in the prime-field code".
- `SingleLoop.lean` uses `ite_false` where it used `if_false`, which Lean
  4.35.0 deprecates; the deprecation warning fails the build, which turns
  warnings into errors. The proofs are otherwise unchanged.

### The external declarations

- The names of the CAS project become the krepi names: the generated
  namespace `KrepiGen`, the definitions `Krepi.Qualification.Models.Arc`
  and `Krepi.Qualification.Models.FromStr` in place of the models of the CAS
  project, and the crate `formal_qualification`. The comments name
  `cargo xtask formal run` in place of the qualification command of the CAS
  project, and call the definitions they use qualification definitions in
  place of models.
- The comment of `StrFrom/FunsExternal.lean` no longer names the target
  that shared its definition, and describes the krepi definition: bytes that
  are not UTF-8 give the undefined-behaviour error.
- The files follow the templates that Aeneas at the pinned commit
  generates: their option headers set `linter.internalConstructors` as
  well, and the generated declarations of `TermLayoutCut/TypesExternal.lean`
  are in the order of the template, with the source file `src/lib.rs`. The
  templates write the type parameters of the `Arc` functions in `Type _`;
  the reviewed functions keep them in `Type`, as the structure `Arc` takes
  its value type in `Type`. Each file declares only axioms that its template
  declares.

## Tests carried over

The crate has no tests of its own: each kept case is a test of the pinned
tools, which the qualification of `cargo xtask formal run` compares with its
expectation, and each kept proof is built and its theorem audited there.

| CAS project | krepi | Expected values |
| --- | --- | --- |
| The 103 kept cases of `verification/qualification/cases.json` | The first 103 cases of `verification/qualification/cases.json` | Changed by the rules of the table above, and for 27 cases by the [revised expectations](#revised-expectations) |
| `mul_mod_spec` of `verification/Casxi/Qualification/Arithmetic.lean` | `Krepi.Qualification.Arithmetic.mul_mod_spec` | Unchanged statement |
| `add_within_spec` of `verification/Casxi/Qualification/Checked.lean` | `Krepi.Qualification.Checked.add_within_spec` | Unchanged statement |
| `charge_each_spec` of `verification/Casxi/Qualification/SingleLoop.lean` | `Krepi.Qualification.SingleLoop.charge_each_spec` | Unchanged statement |

### Revised expectations

The CAS project recorded the expectations of the kept cases with Charon
0.1.281, Aeneas `d119a47` and Lean 4.31.0. The pinned tools, Charon 0.1.312,
Aeneas `4acbb6d` with the reviewed patch and Lean 4.35.0, change the result
of 27 of them. Each of the 27 now expects what the pinned tools give, which
is the same in the image and on `darwin-arm64`: its `expect` is
`translated` where the translation is complete and the generated Lean
builds, and `rejected` where the translation is not complete; its
`diagnostics`, `external_functions` and `external_types` are those of the
extraction; and its other fields, `loop_sources` among them, are unchanged.

The evidence for every change is a controlled comparison. On this crate,
with the arguments and the environment of the extraction of
`cargo xtask formal run` and the same Rust toolchain, Charon 0.1.281 and
Aeneas `d119a47` reproduce all 103 expectations of the CAS project,
diagnostics, external items and loop sources included, and the pinned
Charon and Aeneas give exactly the 27 changes below. The crate, the host,
the Rust toolchain and the arguments are the same in the two runs, so
neither the port of the crate nor the host causes the changes. The old side
ran the release build of Aeneas `d119a47` without the patch; the CAS
project pins the patched build (its tool installation and
`verification/tooling/` at `f2d2fba`), and the release build reproduces all
103 of its expectations. The pinned side carries the reviewed patch,
which changes only the Lean translation of `Option<&mut T>::unwrap`, called
by none of the 27 cases, and the uniqueness of generated Lean names, on
which no compared field depends except the loop sources of `division-walk`,
unchanged.

Where a change of the tools that explains a case was found, its entry names
it. A commit whose diff adds the new message or the library model, or a
change of what Charon writes that its output shows, is named as the cause.
A commit whose content and tests match the case, found without bisection,
is named as the most likely cause, together with the other Aeneas commits
that the evidence does not exclude. Between `d119a47` and `4acbb6d`, 17
Aeneas commits also move its Charon pin, and with it the Charon that writes
the code Aeneas reads for each case; none of them is excluded for such an
entry either. Paths of Aeneas are at `4acbb6d` unless an entry says
`d119a47`. Two entries, `registry-str-names` and `const-str-names`, rest on
the comparison alone for the change of their error.

The `[Error]` line of a rejected case comes with `[Warn ]` lines saying
that the body of a function could not be translated because of the error;
an entry calls such a line the warning for that function.

#### A. Rejected before, translated now (9)

These cases expected a rejection. The pinned tools translate them
completely, without a diagnostic, and their generated Lean builds, so they
expect `translated`. Each difference is the translation itself and the
absence of the expected diagnostics.

- `registry-static-reference`: expected `[Error] Unreachable` and the
  warning for `arity`. At `d119a47`, reading `arity` through the
  `&'static FunctionRecord` that `record` returns found no loan for that
  borrow (`src/interp/InterpBorrowsCore.ml:629` at `d119a47`,
  `lookup_loan`). Most likely Aeneas `21345f80` (pull request #1438), which
  adds support for the `'static` region, whose loans a region abstraction of
  that region owns; its test `ret_static` in `tests/src/static.rs` returns a
  borrow of a static. Not excluded: `f383079c` (#1472), which fixes the
  support for `'static` and changes the file of the old error, and
  `fc321a28` (#1457).
- `static-str-table`: expected no diagnostic: Aeneas `d119a47` ended with the
  uncaught exception `Invalid_argument "option is None"` in
  `SymbolicToPureValues.tvalue_to_texpr`
  (`src/symbolic/SymbolicToPureValues.ml:127` at `d119a47`), the lookup of
  the loan of a shared borrow, with exit status 2 and no Lean. Most likely
  Aeneas `fc321a28` (#1457), which projects the loans of the `'static`
  borrows inside the value of a global, here the `&'static str` field of
  each element of `TABLE`; its test `StaticStr` in
  `tests/src/constants-lean.rs` has that shape. Not excluded: `21345f80`
  (#1438) and `f383079c` (#1472), which add and fix the support for
  `'static`.
- `string-literal-return`: expected
  `[Error] There should be no bottoms in the value` and the warning for
  `name`, from the check of a read place (`src/interp/InterpExpressions.ml:55`
  at `d119a47`). Most likely Aeneas `21345f80` (#1438); its test
  `branch_str` returns a string literal from each branch, as `name` does
  from each arm. Not excluded: `f383079c` (#1472), `fd23a233` (#1464), which
  rewrote the evaluation of places that this check is part of, and
  `fc321a28` (#1457).
- `view-map-range`, `view-value-join`, `moving-if-join`: expected
  `[Error] Internal error, please file an issue` and the warning for
  `term_after`, `scaled_next` or `reduce`. At `d119a47` the join after a
  `match` or an `if` met a borrow inside a shared loan while it mapped the
  region abstractions to their borrows and loans, which it cannot do
  (`src/interp/InterpMatchCtxs.ml:230` at `d119a47`, in
  `compute_abs_borrows_loans_maps`). Most likely Aeneas `fc321a28` (#1457),
  which detects that state before the join with a recoverable error, so that
  the translation duplicates the code after the branching instead of
  joining: the generated `term_after` matches on `term` in each arm of the
  `match` on `after`, `scaled_next` multiplies by 3 in each arm, and
  `reduce` repeats the rest of the function in each branch of the `if`. Not
  excluded: `21345f80` (#1438), which also changes the join.
  `view-map-range` also loses the external function `Borrow::borrow`
  (group D).
- `subtrait-loop`, `generic-into-iterator-loop`: expected
  `[Error] Could not find: type_var_id: 2 from ExtractBase.Item`, and
  `type_var_id: 0` respectively, from the extraction of the function of a
  loop (`src/extract/ExtractBase.ml:479` at `d119a47`). Most likely Aeneas
  `8e62dc3d` (#1465), which keeps, among the generic parameters of the
  function of a loop, those that appear only in a trait clause used in the
  loop; its tests in `tests/src/issue-1436-loop-generics.rs` include a loop
  over an `impl IntoIterator`, as in `total`, and a parameter used only
  through a supertrait clause, as `F: LoopTags` in `double_cells`. Not
  excluded: `6c2788d1` (#1412) and `34fb52a7` (#1452), which also change
  `src/extract/ExtractBase.ml`.
- `indexed-field-sum`: expected `[Error] Unimplemented binary operation` and
  the warning for `advance`. Charon 0.1.281 wrote `index + 1` of `advance` as
  the binary operation `AddChecked`, which Aeneas `d119a47` rejects
  (`src/interp/InterpExpressions.ml:1175` at `d119a47`); Charon 0.1.312 has
  no checked operations and writes it as `Add` that panics on overflow.
  Aeneas `308778ab` updated to that Charon (pin `373d840` to `f87da80`) and
  removed the rejection.

#### B. Still rejected, other diagnostics (7)

- `registry-str-names`, `const-str-names`: expected
  `[Error] Assertion failed: new value doesn't have the same type as its destination`
  and no external function; observed
  `[Error] Found a case of unsupported nested borrows` and the external
  function `core::str::traits::{impl core::cmp::PartialEq<str> for str}::eq`;
  the warning for `lookup` is unchanged. At `d119a47` the assertion
  (`src/interp/InterpPaths.ml:260` at `d119a47`), in the write of a value
  to a place, failed at the comparison `RECORDS[index].name == name`, a call
  of `<&A as PartialEq<&B>>::eq` (the error's span is that function in
  `core`); Aeneas then ended with the uncaught exception of
  `static-str-table`, exit status 2, and wrote no Lean and no list of
  external items. The pinned Aeneas reaches the loop of `lookup` and stops
  at its long-standing limitation on nested borrows
  (`src/interp/InterpBorrows.ml:2060`), with exit status 1 and its list of
  external items. The extra external function is the comparison of `str`,
  which both versions of Charon leave without a body. Reading the code
  points to Aeneas `fd23a233` (#1464) for the assertion: the old check
  compared a type whose regions it had erased with one whose regions it had
  not, and `fd23a233`, the only commit between `d119a47` and `4acbb6d` that
  changes `src/interp/InterpPaths.ml`, compares the two types with their
  regions erased. It points to `fc321a28` (#1457) for the exception, as for
  `static-str-table`. Neither was bisected; the change of the error rests on
  the controlled comparison.
- `function-pointers`: expected
  `[Error] Invalid input for unop: cast<formal_qualification::function_pointers::halve, fn(u64) -> u64> on formal_qualification::function_pointers::halve`;
  observed
  `[Error] Invalid input for unop: fn_def_to_fn_ptr on formal_qualification::function_pointers::halve`.
  The other 6 diagnostics are unchanged. Charon replaced the cast kind
  `FnPtr(Ty, Ty)`, which its OCaml library prints as `cast<src, tgt>`, with
  `FnDefToFnPtr`, printed as `fn_def_to_fn_ptr`
  (`charon-ml/src/PrintFmt.ml:653` of Charon 0.1.312); Aeneas `34659d2a`
  updated to that Charon (pin `08d7c9d` to `de8736f`).
- `view-map-loop`, `view-index-loop`, `view-borrowed-helper`: expected
  `[Error] Internal error, please file an issue`; observed
  `[Error] Joining region abstractions containing shared loans whose shared value contains borrows is not supported yet`;
  the warning for `add_row`, `sum` or `sum_values` is unchanged. The old
  error is that of the joins of group A, here at the loop of a method or
  function that holds a shared borrow of a view with a `&str` field. The
  check that Aeneas `fc321a28` (#1457) adds
  (`src/interp/InterpReduceCollapse.ml:1373`) names it; at a loop the
  translation cannot duplicate code instead of joining, so it stops there.
- `collection-tree-frame-enum`: expected
  `[Error] Internal error, please file an issue`; observed
  `[Error] Unimplemented: found a loan and its corresponding borrow in the same region abstraction (this can happen in some situations involving the 'static lifetime)`;
  the warnings for `copy_frames` and `equal_pairs` are unchanged. At
  `d119a47` a sanity check that two region abstractions to merge are
  distinct failed (`src/interp/InterpAbs.ml:2188` at `d119a47`). Aeneas
  `21345f80` (#1438) checks the same condition before the merge and reports
  it as this limitation (`src/interp/InterpReduceCollapse.ml:781`).

#### C. `Vec::is_empty` no longer external (5)

`trim-by-index`, `polynomial-interface`, `term-walk`, `carried-term-walk`
and `collection-hand-traits` expected the external function
`alloc::vec::{alloc::vec::Vec<T>}::is_empty`, which the pinned tools do not
report; nothing else changes, and `carried-term-walk` is still rejected
with its diagnostics. Aeneas `27735db2` (#1487) adds the model
`alloc.vec.Vec.is_empty` (`backends/lean/Aeneas/Std/Alloc/Vec.lean:101`)
and maps the Rust function to it (`src/extract/ExtractBuiltinLean.ml:256`),
so the generated code calls the library and no template declares it.

#### D. `Borrow::borrow` no longer external (7)

`ordered-maps`, `coefficient-map`, `map-term-walk`, `view-map-range` (group
A), `view-map-helper`, `monomial-order` and `division-walk` expected the
external function `core::borrow::{impl core::borrow::Borrow<T> for T}::borrow`,
which the pinned tools do not report. Apart from the changes of group A to
`view-map-range`, its `expect` and its diagnostics, nothing else changes,
and the 4 loop sources of `division-walk` are the same. Aeneas `ae18927b`
(#1482) adds the model of the blanket implementation,
`core.borrow.Borrow.Blanket.borrow`
(`backends/lean/Aeneas/Std/Core/Borrow.lean:17`), and maps the Rust function
to it (`src/extract/ExtractBuiltinLean.ml:402`), so the generated code uses
`core.borrow.Borrow.Blanket` from the library.

## Behaviour changes

- 76 kept cases keep the expectation of the CAS project apart from the
  rules above. The other 27 expect what the pinned tools give, which differs
  from what the earlier Charon and Aeneas of the CAS project gave; the
  [revised expectations](#revised-expectations) explain each, and the
  qualification of `cargo xtask formal run` checks them.
- The cases `str_from`, `match-machine-arc` and `term-layout-cut` type-check
  against the krepi definitions in place of the definitions of the CAS
  project. `fromStr` fails with the undefined-behaviour error on bytes that
  are not UTF-8, which no Rust `&str` holds; the comment of the CAS project
  described a deterministic result for such bytes. No kept proof reaches
  either definition.

## Hardware evidence to re-obtain

None: the qualification runs on the host.

## Not carried over

- The 9 cases that reach a `num-*` crate, their modules, the file
  `src/rewrite_value_providers.rs`, the 4 `num-*` dependencies, and the
  directory `verification/externals/Qual/RewriteValues/` of the case
  `rewrite-value-providers`: the crate depends on no crate.
- `src/bin/model_vectors.rs` and `src/bin/provider_vectors/mod.rs`, which
  generated the vectors of the differential checks of models: the gate has
  no such check, and the definitions that the cases use are not models.
- `clippy.toml` of the crate: `cargo xtask check` does not lint the crate,
  whose shapes are inputs of the tools.
- The 15 other proofs of `verification/Casxi/Qualification/`: those of the
  13 kept cases whose `proof` is removed, and `SeriesSummerOwned.lean` and
  `RewriteValues.lean` of removed cases.
- The model definitions of the CAS project that its external declarations
  import: krepi writes its own, as the summary states.
