---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/lib.rs
  - tools/Cargo.toml
destination:
  - tools/src/lib.rs
  - tools/Cargo.toml
treatment: ported
features: none
---

# Porting record: tools/src/lib.rs

## Summary

The crate root and manifest of the host tooling crate `krepi-tools` at
`tools/`. The crate root declares the ported modules and defines `Failure`,
the error that a check returns with the message that describes it, which the
modules share. The manifest names the crates that provide the general
functions the modules use.

This is the first change that takes code from the legacy tooling crate
`tools/`, so this record classifies that crate by module. Modules and items
that later changes of this crate take are recorded in the records of the
krepi modules that receive them.

| Treatment | Legacy modules | What is taken |
| --- | --- | --- |
| Ported | `elf` in this change; `qemu`, `receipt`, `serial` and `serial_capture` in later changes | The module with its tests, each with its own record |
| Ported in part | The crate root and `report` in this change; `tty`, `json`, `cycles`, `suites/platform/pi5_bundle.rs` and `suites/platform/pi5_kernel.rs` in later changes | The items that the ported modules use, with their tests: `Failure`; the UTC time stamps, with `serde_json` values in place of `Value`; the serial port, receiver and writer of `tty` with its interrupt flag, in a record of its own; the JSON reader of `json`, as test support; `random_hex` of `cycles`; and the path normalization, file error text and directory creation of the two suites, written again for serial capture |
| Not ported | Every other module, listed under [Not carried over](#not-carried-over) | Nothing |

## Changes

- The package is `krepi-tools`, licensed MIT, Rust 2024 with `rust-version`
  1.99, and a Cargo workspace of its own with its own `Cargo.lock`, outside
  the kernel, user-space and xtask workspaces. The format, Clippy and test
  steps of `cargo xtask check` cover it.
- The crate depends on `serde_json` `=1.0.154` without its default features
  and with its `preserve_order` feature, for report values and their text,
  and on `sha2` `=0.11.1` without its default features, for the SHA-256
  digests of the ELF fixture patching; see [dependencies](../../CONTRIBUTING.md#dependencies). Both are
  licensed MIT OR Apache-2.0, and the crates they depend on are licensed
  under MIT, Apache-2.0, Zlib or the Unlicense, one of them with the
  Unicode-3.0 license in addition; each permits its use in this MIT-licensed
  crate. `libc`, pinned to the version of the legacy manifest, is added with
  the first module that calls it.
- The lints `unsafe_op_in_unsafe_fn = "deny"` and
  `clippy::undocumented_unsafe_blocks = "deny"` are kept.
- The crate documentation describes the modules it holds. The documentation
  of `Failure` no longer refers to the messages of the Python runners.
- The test-only module `tools/src/scratch.rs` is new: a directory for the
  files of one unit test, removed with its value. Like the scratch trees of
  the legacy integration tests, it lies below the build directory, so that
  tests never fill the system temporary directory. Unit tests have no
  `CARGO_TARGET_TMPDIR`, so the directory is placed in `scratch` beside the
  `deps` directory that holds the test executable.
- `Failure` had no test; `tests::a_failure_displays_its_message` and
  `tests::an_io_error_becomes_a_failure_with_its_text` check its text and its
  conversion from an I/O error.

## Tests carried over

None; the legacy crate root had no tests. The tests of the legacy SHA
modules are not carried over; see [Not carried over](#not-carried-over).

## Behaviour changes

None.

## Hardware evidence to re-obtain

None. The crate root runs on the host and had no QEMU or board results.

## Not carried over

- `repository_root`, which only legacy tests called, to find build outputs
  of the prototype below its repository root.
- The legacy modules that are not ported, each with the reason:
  - `archive`, the streamed reading of the fixed source archives that only
    the legacy record verifiers read.
  - `cycles`, apart from `random_hex`: the interleaved diagnostic cycle suites
    and layered workloads, which drive the serial-triggered diagnostic
    controllers that are retired.
  - `kernel_elf`, the section and symbol contract of the prototype kernel
    image and its linker script. A kernel image of this repository states its
    own contract.
  - `media`, the VirtIO block fixture of the prototype storage suites.
  - `probe`, the console probes of the retired serial-triggered diagnostic
    controllers.
  - `python_text`, the Python string semantics that the prototype audits
    reproduced; no Python parity is carried over.
  - `records`, the verifiers that bind prototype acceptance records to source
    bytes. Those records are not ported. The tests carried over later use
    equivalents of its JSON loading and canonical JSON, written as test
    support.
  - `rust_lexical`, the lexical masking of Rust sources for the prototype
    audits, which are not ported.
  - `sha1`, `sha256` and `sha512`, hand-written SHA-1, SHA-256 and SHA-512,
    with their tests `tests::known_vectors` and `tests::git_blob_identity`
    of `sha1`, `tests::known_vectors_match` and
    `tests::incremental_updates_match_one_shot` of `sha256`, and
    `tests::known_vectors` and `tests::incremental_updates_match_one_shot`
    of `sha512`. The host tools take hashes from a crate: SHA-256 comes from
    `sha2`, whose own tests cover the function. SHA-1 and SHA-512, which no
    module of this crate calls, are taken from a crate with their first
    caller.
  - `smp`, the shared parts of the prototype multicore suites. Multicore
    support is redesigned.
  - `stats`, statistics with the results of Python's `statistics` module for
    the prototype channel repetition suites.
  - `suites`, apart from the items above: the prototype simulation and board
    suites. krepi suites are written against krepi feature documents.
  - `symbolize`, the resolution of fault addresses to functions and source
    lines on top of the ELF reader. It is left to the change that adds a
    fault-symbolization command.
- The dependencies `bzip2-rs`, `fancy-regex`, `lzma-rs`, `miniz_oxide` and
  `toml`, which only modules that are not ported, or Python-parity parts of
  ported ones, use.
- The crate and package descriptions, which named the prototype system and
  its simulation suites.
