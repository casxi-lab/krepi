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
| Ported | `elf`, `qemu`, `receipt`, `serial` and `serial_capture` | The module with its tests, each with its own record |
| Ported in part | The crate root, `report`, `tty`, `cycles`, `suites/platform/pi5_bundle.rs` and `suites/platform/pi5_kernel.rs` | The items that the ported modules use, with their tests: `Failure`; the UTC time stamps, with `serde_json` values in place of `Value`; the serial port, receiver and writer of `tty` with its interrupt flag, in a record of its own; and `random_hex` of `cycles` and the path normalization, file error text and directory creation of the two suites, written again for the serial capture and recorded with it |
| Not ported | Every other module, listed under [Not carried over](#not-carried-over) | Nothing |

## Changes

- The package is `krepi-tools`, licensed MIT, Rust 2024 with `rust-version`
  1.99, and a Cargo workspace of its own with its own `Cargo.lock`, outside
  the kernel, user-space and xtask workspaces. The format, Clippy and test
  steps of `cargo xtask check` cover it.
- The crate depends on `serde_json` `=1.0.154` without its default features
  and with its `preserve_order` feature, for report values and their text
  and for the messages of Cargo that `qemu_boot` reads, on `sha2` `=0.11.1`
  without its default features, for the SHA-256 digests of the ELF fixture
  patching, of the serial capture, of the QEMU runner and of the QEMU boot
  suite and the build-id of the test image, and on
  `libc` `=0.2.191`, the version of the legacy manifest, without its default
  feature, for the terminal, lock and signal calls of `tty`, the signal
  that `qemu` sends, and the pseudo-terminals, signals, file-size limits and
  child processes of the tests of `tty`, `serial_capture`, `qemu` and
  `qemu_run`; on `clap` `=4.6.7` without its default features and with
  its `std`, `help`, `usage` and `error-context` features, for the command
  lines of `serial_capture`, `qemu_run` and `qemu_boot`; and on `object`
  `=0.40.0` without its default features and with its `write_core` and
  `elf` features, for the ELF writer of `test_elf`; see
  [dependencies](../../CONTRIBUTING.md#dependencies). All five are licensed
  MIT OR Apache-2.0, and the crates they depend on are licensed under MIT,
  Apache-2.0, Zlib or the Unlicense, one of them with the Unicode-3.0
  license in addition; each permits its use in this MIT-licensed crate.
- The crate builds on Unix hosts only, the hosts of development and CI, and
  stops with a compile error elsewhere. The legacy crate kept variants for
  other hosts in two functions of `qemu` alone and called `libc` on Unix
  throughout.
- The lints `unsafe_op_in_unsafe_fn = "deny"` and
  `clippy::undocumented_unsafe_blocks = "deny"` are kept.
- The crate documentation and the package description describe the
  modules that the crate holds. The documentation of `Failure` no longer
  refers to the messages of the Python runners.
- Two modules are new, not taken from the legacy tree.
  `tools/src/qemu_run.rs` is the command `cargo xtask qemu`, which runs an
  image on QEMU virt with the command line, the guarded capture and the
  process helpers of [`qemu`](tools-qemu.md) and writes the serial
  transcript, QEMU's standard error and a receipt into a new run directory;
  [testing](../conventions/testing.md#entry-points) describes it and its
  receipt. Its library entry `run_image_with` also sends input to the guest,
  for the QEMU boot suite of [`qemu_boot`](tools-qemu_boot.md), and
  `run_image_on` runs the guest on the machine with EL2, for a test image
  that enters at EL2.
  `tools/src/test_elf.rs` writes the test image, an AArch64 executable for
  QEMU virt that writes one line to the PL011 UART and powers the machine
  off with PSCI `SYSTEM_OFF` through HVC. Its program is a fixed list of
  instruction words, and the ELF writer of `object` lays out the executable
  around it, so it needs no bare-metal target, assembler or linker; the ELF
  reader of [`elf`](tools-elf.md) reads it in its tests.
- `tools/src/console.rs` holds code of the port of `serial_capture`, the
  terminal of a command, moved out of that module so that both commands
  share it; [`serial_capture`](tools-serial_capture.md#changes) records it.
- The test-only module `tools/src/scratch.rs` is new: a directory for the
  files of one unit test, removed with its value. Like the scratch trees of
  the legacy integration tests, it lies below the build directory, so that
  tests never fill the system temporary directory. Unit tests have no
  `CARGO_TARGET_TMPDIR`, so the directory is placed in `scratch` beside the
  `deps` directory that holds the test executable. It gives the path of the
  directory and of a file in it, writes and reads such a file, and writes a
  shell script, such as a fake QEMU, and waits until it can be run: Linux
  refuses to run a file that a process holds open for writing, as a child
  that another test starts holds a copy of the descriptor until its exec.
- The module `tools/src/timing.rs` is new: `Timing` holds the time slices,
  polling intervals and timeouts of `tty`, `serial_capture`, `serial` and
  `qemu`, which the legacy modules wrote as constants,
  and gives one set for QEMU virt and one for the Pi 5. Both sets hold the
  legacy values; [testing](../conventions/testing.md#determinism-and-time)
  lists them.
- The crate root gives `hex`, the lowercase hexadecimal digits of bytes,
  which `tty` and `serial_capture` share; the legacy modules wrote the
  digits each in place.
- The test-only modules `tools/src/pty.rs` and `tools/src/child.rs`, a
  pseudo-terminal pair and a runner of one test in a child process, are
  recorded with [`tty`](tools-tty.md), whose tests they serve first, and
  with [`serial_capture`](tools-serial_capture.md), whose tests added the
  board scripts and the other parts that they use. The
  crate root defines `TEST_WAIT`, the 60 s for which a test waits for an
  event, which only a failing test reaches.
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
  - `json`, the hand-written JSON reader and writer: `serde_json` writes the
    reports and reads JSON in the tests. The legacy capture tests read their
    receipts with its `parse`, which is recorded with
    [`serial_capture`](tools-serial_capture.md#not-carried-over).
  - `kernel_elf`, the section and symbol contract of the prototype kernel
    image and its linker script. A kernel image of this repository states its
    own contract.
  - `media`, the VirtIO block fixture of the prototype storage suites.
  - `probe`, the console probes of the retired serial-triggered diagnostic
    controllers. The tests of [`qemu`](tools-qemu.md) take its output limit
    and fatal records as constants.
  - `python_text`, the Python string semantics that the prototype audits
    reproduced; no Python parity is carried over.
  - `records`, the verifiers that bind prototype acceptance records to source
    bytes. Those records are not ported. The tests that are carried over
    read JSON with `serde_json` and compare a receipt with the text that
    `report::to_json` writes.
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
    suites. krepi suites are written against krepi feature documents. The
    tests of [`qemu`](tools-qemu.md) take the fatal records of the board
    session of `suites/platform/kernel_serial.rs` as a constant, and the
    QEMU boot suite takes the judgment and the echo challenge of
    `suites/platform/qemu_boot.rs`, recorded in
    [`qemu_boot`](tools-qemu_boot.md).
  - `symbolize`, the resolution of fault addresses to functions and source
    lines on top of the ELF reader. It is left to the change that adds a
    fault-symbolization command.
- The dependencies `bzip2-rs`, `fancy-regex`, `lzma-rs`, `miniz_oxide` and
  `toml`, which only modules that are not ported, or Python-parity parts of
  ported ones, use.
- The crate and package descriptions, which named the prototype system and
  its simulation suites.
