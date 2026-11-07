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
ones. The kept cases are 67 translated, 28 rejected and 8 ill-typed (5 with
their type errors in `Funs.lean`, 3 in `Types.lean`); 4 have `opaque`, 2
`loop_sources`, 3 `models` and 3 `proof`. The changes to the kept cases are
mechanical and follow from the changes to the crate:

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
| The 103 kept cases of `verification/qualification/cases.json` | The first 103 cases of `verification/qualification/cases.json` | Changed by the rules of the table above only |
| `mul_mod_spec` of `verification/Casxi/Qualification/Arithmetic.lean` | `Krepi.Qualification.Arithmetic.mul_mod_spec` | Unchanged statement |
| `add_within_spec` of `verification/Casxi/Qualification/Checked.lean` | `Krepi.Qualification.Checked.add_within_spec` | Unchanged statement |
| `charge_each_spec` of `verification/Casxi/Qualification/SingleLoop.lean` | `Krepi.Qualification.SingleLoop.charge_each_spec` | Unchanged statement |

## Behaviour changes

- Each kept case keeps the expectation of the CAS project apart from the
  rules above. A case whose conclusion the pinned tools of krepi change is
  explained case by case and reviewed before its expectation changes, and
  this record then lists the change.
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
