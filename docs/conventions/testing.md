# Testing

Tests and test tooling are written in Rust. So far the repository tasks in
`xtask/` and the host tooling crate in `tools/`, which holds the first test
tools, have host tests; this page states the rules that every test follows,
and its command sections are filled in when the commands work.

## Environments

krepi is tested in three environments, which establish different properties
and are reported separately:

| Environment | What it shows | What it does not show |
| --- | --- | --- |
| Host tests | Logic of kernel and service modules, codecs, tools, invariants over generated inputs | EL0 isolation, exceptions, MMU, caches, interrupts, real concurrency |
| QEMU virt / Cortex-A76 | Boot, exceptions, real EL0 execution, IPC and services on a generic ARM64 machine with one, two or four vCPUs | Pi 5 addresses, firmware, devices and timing; hardware races |
| Raspberry Pi 5 through the HIL bench | Board boot, devices, firmware interaction, four real CPUs | Anything about QEMU or about another firmware version |

A passing simulation is not a board result, and a fixed-instruction-count
QEMU run is a functional reproduction, not evidence about races or timing.
Races are tested with multi-threaded TCG and then on the board.

## Entry points

`cargo xtask check` runs the required host checks from the repository root in
order. It stops at the first failure, exits with a non-zero status and names
the failed step:

1. `toolchain`: the installed rustc, Clang, lld and QEMU have the versions
   that `toolchains.toml` pins for the host (`darwin-arm64` or
   `linux-aarch64`), and every host pins the rustc of `rust-toolchain.toml`;
2. `manifests`: every crate is licensed MIT, both workspace root manifests
   build releases with `overflow-checks = true`, and the dependency rules of
   the [source layout](../architecture.md#source-layout) hold, as far as the
   following checks reach:
   - Cargo resolves the kernel workspace with
     `cargo metadata --locked --offline --all-features`, so a dependency that
     it cannot resolve offline, or a `Cargo.lock` that the manifests no longer
     match, fails the step. In what Cargo reports, the workspace root must be
     `kernel/`; every package must be a member of the kernel workspace, which
     a package from a registry or a Git repository never is; and the
     manifest of every package and the source of every target must lie
     inside `kernel/`. Paths are compared with symbolic links resolved, and
     one that cannot be resolved fails. Every feature of every member is on,
     and every package is a member, so no choice of features adds a package.
   - In the tracked manifests, path dependencies of every kind keep to the
     rules. Below `kernel/`, tracked symbolic links stay inside `kernel/`,
     and so does a string literal that starts the argument of `include!(`,
     `include_bytes!(` or `include_str!(`, or follows `#[path =`, on the
     same line; a path written another way, such as on the next line,
     through `concat!` or in `cfg_attr`, is not seen.
   - Every tracked `.cargo/config.toml` or `.cargo/config` at the repository
     root or in a directory below `kernel/`, whatever the case of its name,
     is a regular file of TOML, and no string in it, split at whitespace,
     has a word that starts with `--extern` or `-L`; a tracked `.cargo`
     entry in those places that is a symbolic link or a submodule fails.
     Cargo reads this configuration when it runs from the repository root,
     as `cargo xtask` does, or from a directory below `kernel/`.
   - These checks catch an external crate added by mistake, not one hidden
     on purpose. The step does not see the environment, such as `RUSTFLAGS`
     or `RUSTC_WRAPPER`, Cargo configuration that is outside the
     repository, untracked or in another directory, or the command line,
     including what an alias runs. Nor does it see other ways to hand rustc
     code from elsewhere: in Cargo configuration, argument files,
     `--sysroot`, a compiler wrapper, an included configuration file or a
     build-script override; in a build script, a library search path it
     prints; and in a procedural macro, files it reads;
3. `fmt`, `clippy` with warnings as errors, and `test`, each in the kernel
   workspace, the user-space workspace, `xtask` and the host tooling crate
   `tools`;
4. `docs`: relative links and anchors in Markdown and the `cargo xtask`
   commands that documents mention;
5. `workflows`: every `.yml` or `.yaml` file below `.github/workflows/` is
   YAML without anchors, aliases, merge keys, repeated keys or characters
   that YAML parsers read differently, and never mentions
   `pull_request_target`, not even in a comment or through an escape; every
   job sets its own `permissions`; and in a workflow that runs on
   `pull_request`, no job requests write access and nothing outside `on`
   references `secrets`.

The checks that `xtask` implements itself read only files that Git tracks,
so a fresh clone and a working copy with build output give the same result;
the Cargo commands, including the resolution in `manifests`, read the
working copy. The proof gate joins the check once the formal tooling
exists.

`cargo xtask check --receipt <path>` also writes a JSON receipt of the run to
`<path>`, whether the check passes or fails. It records the commit, whether
the working tree was clean before and after the run, each step with its
status and duration, the version output of the tools that the toolchain step
found, the runner image (`ImageOS`, `ImageVersion`) and the GitHub Actions
run (`GITHUB_RUN_ID`, `GITHUB_RUN_ATTEMPT`, `GITHUB_EVENT_NAME`, `GITHUB_REF`,
`GITHUB_SHA`); a value the environment does not provide is `null`.

CI runs the check as the job `cargo xtask check` of
`.github/workflows/check.yml` on a GitHub-hosted `ubuntu-24.04-arm` runner,
for the head commit of every pull request to `main` and for every push to
`main`. The job installs `clang-18` and `qemu-system-arm` from the Ubuntu
archive and the toolchain of `rust-toolchain.toml` with rustup, and uploads
the receipt as the artifact `check-receipt-<commit>-<attempt>`.

`cargo xtask serial-capture --port <tty>` records what a board sends over a
serial port, such as the UART of a Pi 5 behind a USB serial adapter, without
evaluating its boot; it is a tool for the bench and is not part of the
check. It opens the port read-only, holds it exclusively with `TIOCEXCL`,
sets raw 115200 8N1 attributes without flow control, sends nothing and
restores the attributes at its end. It receives for `--seconds` (default 30,
greater than 0 and at most 300) or until `--max-bytes` (default 262144, at
most 16777216) have arrived, never reading past that limit, or until the
device ends. It writes three files into the new directory `--output-dir`, by
default `artifacts/hardware-uart/<UTC time>Z-<12 hexadecimal digits>`:
`raw.bin`, the bytes received; `preview.txt`, the first 16 KiB decoded as
UTF-8 with control and other unprintable characters escaped; and
`summary.json`, a receipt with sorted keys. The receipt records the port and
its line settings, the limits, the count and SHA-256 digest of the bytes,
whether the port was held exclusively and its attributes restored, the start
and end times, and the status: `CAPTURED` or `NO_DATA` with the reason
`deadline`, `byte_limit` or `end_of_stream`, `INTERRUPTED`, or `FAIL` with
its `errors`; `boot_acceptance` is always `NOT_EVALUATED`. The command exits
with 0 for `CAPTURED` and `NO_DATA`, 130 for `INTERRUPTED`, 2 for `FAIL`, a
usage error or files that it cannot create or write, and 120 when it cannot
write its own output. From immediately before the port opens, SIGINT,
SIGTERM and SIGHUP end the capture as `INTERRUPTED`, with the port restored
and the receipt written; before that, they end the process by the
dispositions that it started with. `cargo xtask serial-capture --list` prints
the likely USB serial devices below `/dev` without opening them. `clap`
reads the command line: `--help` prints its help with the options and
their defaults on standard output, and a usage error is its error text on
standard error.

QEMU suites and board suites have their own entry points (planned), built on
the serial port transport and the serial link of the host tooling crate and
on the QEMU runner, with its serial capture, and the receipt module, which
are still to be ported from the legacy tooling crate. Each suite writes its
report and the raw serial bytes under `artifacts/`, together with the
identity of the image it ran.

## Evidence and receipts

- Only a receipt that CI or the HIL bench produced, stored where it can be
  retrieved, is acceptance evidence. A local run is a development aid.
- The list of known failures is generated by a tool from the receipts
  (planned) and is not edited by hand. A failure stays on the list until a
  receipt shows the fixed behaviour.
- A receipt records the identity and digest of the image, the toolchain,
  the QEMU version or the board configuration, and the inputs.

## Board runs

Board runs use the HIL bench (planned): a relay powers the board and its state
is read back, the image is published over TFTP, and the run confirms that the
board booted that image over the network, because the firmware falls
back to the SD card without a message when the TFTP server does not answer.
The serial console is captured from power-on. A run never depends on watching
LEDs.

Every board receipt names the entry of the firmware and lab registry
(planned) that describes the firmware, EEPROM and BL31 versions and the bench
configuration. Updating any of them makes earlier board receipts stale for the
affected features until they are obtained again.

## Layout

- Unit tests live in `#[cfg(test)]` modules next to the code they test.
- Integration tests are grouped by documentation area: one module per feature
  document, whose path mirrors the feature ID with hyphens written as
  underscores (`krepi.kernel.endpoint-ipc` maps to a module
  `endpoint_ipc` in the `kernel` area). The crate layout is fixed with the
  first tests.
- Frozen data lives in a data directory per area; each file starts with a
  comment that names its source (hand calculation, manual, construction or
  the legacy tree with commit and path).
- Tests carried over from the legacy tree keep their expected values; a
  changed expectation is a behaviour change and is recorded in the porting
  record.

## Categories

Within a feature module, tests are grouped into submodules by category:

| Category | Content |
| --- | --- |
| `examples` | The numbered examples of the feature document, named `exN_...` |
| `properties` | Invariants that hold over generated or enumerated inputs |
| `boundaries` | Empty, degenerate and invalid inputs, limits, stale handles and rejected authority |
| `resources` | Budgets, deadlines, cancellation, teardown and reclamation |
| `receipts` | Expected fields of a receipt parsed from serial output; incomplete, replayed, weakened or misattributed receipts are rejected |
| `regressions` | Minimal reproductions of fixed defects, named after the defect |

A module may omit categories that do not apply.

## Independent evidence

A test establishes a property through a path independent of the code under
test: receipts parsed from serial output against fixed expected fields,
hand-written fixtures, values from hardware manuals and specifications,
negative mutations of valid inputs, test vectors taken from the legacy tree,
and formal proofs. A test never accepts an output because the code under test
produced it before. Metadata checks are not source checks, source checks are
not execution, and execution on QEMU is not execution on the board.

## Determinism and time

- Tests do not access the network and do not depend on the wall clock.
- Tests do not depend on CPU speed. Time slices, spin limits, timeouts and
  sampling windows are platform parameters with documented values for QEMU
  and for the Pi 5, never constants tuned on one machine.
- A test whose outcome depends on an interleaving drives that interleaving
  explicitly or runs in an environment that produces it; a fixed instruction
  count does not cover interleavings of preemption with system calls.
- Generated inputs use fixed seeds and a fixed number of cases; a failing case
  reports its seed and position, and a case that exposed a defect is added to
  `regressions` as a fixed input.
- Deadlines use generous bounds or an injected clock.

The host tools take their time slices, polling intervals and timeouts from a
`Timing` value of `tools/src/timing.rs`, which a caller chooses for the
platform it talks to; `cargo xtask serial-capture` takes the Pi 5 set. The
values for the Pi 5 are those of the legacy tooling crate, which used the
same values on QEMU and on the board; they have not yet been measured
against a board run of krepi.

| Field | Use | QEMU virt | Pi 5 |
| --- | --- | ---: | ---: |
| `reader_poll` | Longest wait of a serial port's reader thread for input before it looks at its stop flag | 100 ms | 100 ms |
| `request_transmit` | Longest transmission of one request of 1 to 128 bytes to a serial port, within the deadline of its session | 2 s | 2 s |
| `capture_slice` | Longest wait of a serial capture for input before it looks at its interrupt flag | 100 ms | 100 ms |
| `link_slice` | Longest wait of a serial link for output in one look: after its output ended, for the ready line and while it drains | 20 ms | 20 ms |
| `link_drain` | How long a serial link collects the output that follows a failure | 250 ms | 250 ms |
| `link_finish` | Longest final read of a finished serial link, until its output ends | 1 s | 1 s |
| `link_finish_slice` | Longest wait in one look of that final read | 50 ms | 50 ms |
| `stop_grace` | How long a stopped process may take to end after SIGTERM before it is killed | 1 s | 1 s |
| `kill_grace` | How long a killed process may take to end before its status is given up | 1 s | 1 s |
| `reap_poll` | Interval between two looks at whether a process has ended | 10 ms | 10 ms |

The unit tests of these tools wait at most 60 s for an event that they
expect, which only a failing test reaches, and pass sets of their own whose
bounds for an expected event are as long; a capture that a test ends by its
byte limit, the end of its stream or an interrupt has a deadline of 120 s.
No test bounds the time that a step takes.

## Dependencies

The test tooling takes general functionality from crates, as
[contributing](../../CONTRIBUTING.md#dependencies) requires. Each is pinned
to an exact version in the manifest of the crate that uses it:

| Manifest | Dependency | License | Purpose |
| --- | --- | --- | --- |
| `tools/Cargo.toml` | `clap` without default features, with `std`, `help`, `usage` and `error-context` | MIT OR Apache-2.0 | The command line of `cargo xtask serial-capture`, defined with the builder, with its help, usage and error texts, which have no colour and are not wrapped to the terminal |
| `tools/Cargo.toml` | `libc` without default features | MIT OR Apache-2.0 | The terminal, lock and signal calls of the serial port transport, the signal that the process helpers send, and the pseudo-terminals, signals, file-size limits and child processes of the tests of the transport, the serial capture and the process helpers |
| `tools/Cargo.toml` | `serde_json` without default features, with `preserve_order` | MIT OR Apache-2.0 | Report values, whose objects keep the order of their keys, and their JSON text |
| `tools/Cargo.toml` | `sha2` without default features | MIT OR Apache-2.0 | The SHA-256 digests in the report of the ELF fixture patching and in the receipt of the serial capture, and the suffix of the capture's run directory |
| `xtask/Cargo.toml` | `serde_json` without default features, with `preserve_order` | MIT OR Apache-2.0 | The JSON text of the receipt of `cargo xtask check`, and reading the output of `cargo metadata` in the `manifests` step |
| `xtask/Cargo.toml` | `toml` without default features, with `parse` and `serde` | MIT OR Apache-2.0 | Reading the Cargo manifests and configuration files, `toolchains.toml` and `rust-toolchain.toml` |
| `xtask/Cargo.toml` | `yaml-rust2` without default features | MIT OR Apache-2.0 | The YAML event parser of the `workflows` step |

No test has a development dependency yet. Development dependencies are added
only when a test category needs them, are pinned to an exact version and are
listed here with their purpose.
