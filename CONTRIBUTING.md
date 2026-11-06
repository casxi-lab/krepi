# Contributing

## Tooling

The Rust toolchain is pinned in `rust-toolchain.toml`; the exact versions of
rustc, Clang, lld and QEMU for each host are in `toolchains.toml`. Before
proposing a change, enable the commit-message hook once and run the required
host checks from the repository root:

```sh
git config --local core.hooksPath .githooks
cargo xtask check
git diff --check
git diff --cached --check
```

[Testing](docs/conventions/testing.md#entry-points) describes what the check
runs. CI runs the same check on every pull request to `main` and on every
push to `main`. A change that updates a tool version updates
`toolchains.toml` in the same change. The proof tools are pinned separately,
in `verification/toolchain.json`: a change to them runs
`cargo xtask formal toolchain-check` and builds their image in CI, as
[formal verification](docs/formal-verification.md#tool-checks) describes.

`cargo xtask serial-capture` is a tool for the bench, not a check: it
records what a board sends over a serial port into a new directory below
`artifacts/`, with a receipt, and does not evaluate the board's boot.
[Testing](docs/conventions/testing.md#entry-points) describes what it does.

`cargo xtask qemu <ELF>` is a tool as well, not a check: it runs an image on
QEMU virt until the guest powers the machine off or a limit ends the run,
and records the serial output, QEMU's standard error and a receipt in a new
directory below `artifacts/`, without evaluating the output. The tests of the
check run it on the test image of the host tooling crate.
[Testing](docs/conventions/testing.md#entry-points) describes it and its
receipt.

When a command lands, this page and [testing](docs/conventions/testing.md)
describe what it runs. Do not write a command into a document before it works.
A command that does not exist yet, such as `cargo xtask docs check` (planned)
or `cargo xtask formal run` (planned), carries the marker `(planned)` right
after its code span. The documentation check rejects any other mention
of a command that `cargo xtask` does not provide, a mention outside code, and
the marker once the command exists.

## Source and documentation

Use English for documentation, comments, diagnostic text and commit messages.
Feature documents and tests follow the
[documentation](docs/conventions/documentation.md) and
[testing](docs/conventions/testing.md) conventions. Document current
behaviour, interfaces, invariants, limitations and the commands needed to use
or test the software. Keep task tracking, dated work logs, internal
deliberations and implementation chronology out of technical documentation.

Planning identifiers, proposal records with their versions and reviews,
decision records, historical acceptance records and cross-repository
coordination belong in the project's coordination records outside this
repository. No document or code comment here uses
milestone, task, proposal or decision numbers, or capability and interface
codes. Requirement IDs such as `IPC-R01` label requirements within a
component and are not planning identifiers.

Explain the CPU state, address validity, alignment, ownership and exclusion
requirements of unsafe operations. Keep QEMU device constants within QEMU
board support. Application-facing interfaces must not expose internal Rust
layouts or unmanaged pointers.

Inspect the working tree before editing and preserve unrelated changes. Use a
topic branch for changes. Do not modify global Git configuration.

## Dependencies

The host tools (the repository tasks in `xtask/` and the host tooling crate
in `tools/`) do not hand-write general functionality that a mature crate
provides, such as hashes, JSON, compression and regular expressions. They
take it from the crate, pinned to an exact version (`version = "=x.y.z"`),
with only the features they use and under a license that permits its use in
an MIT-licensed project, such as MIT or Apache-2.0. Their tests cover how
krepi uses the crate, not the crate itself.
[Testing](docs/conventions/testing.md#dependencies) lists each dependency
with its purpose.

This rule covers the host tools only. Crates of the kernel workspace use no
external crate at all, whether from a registry, a Git repository or a path
outside `kernel/`: proof extraction and the image take their input from the
kernel workspace's own tracked files, and code from elsewhere would run in
EL1 without a specification or a proof. What the kernel needs, such as a
hash, is written inside the kernel workspace and follows the
[provable Rust subset](docs/conventions/provable-subset.md).

## One image

Each supported board has one system image that serves every product function.
A change must not introduce compile-time profiles that exclude each other,
such as an SMP image without a device driver that another image has. When two
functions cannot yet run together, add a narrow slice of both to the same
image. The default image contains no diagnostic operations or fault probes;
diagnostic operation numbers are separate from production ones, and an ELF
symbol check of the release image confirms that the diagnostics are absent
(planned).

## Formal verification

Develop kernel changes from independent requirements and explicit state,
ownership, error, frame, progress and environment contracts, written in the
component documents below [subject domains](docs/domains/README.md).
Executable specifications, proofs, production-entry mappings and regression
tools belong here; proposals and review policy are kept in the coordination
records. Lean 4 +
Charon/Aeneas is the implementation-refinement toolchain. Follow
[formal verification](docs/formal-verification.md).

Code of the modules that the
[provable Rust subset](docs/conventions/provable-subset.md) lists follows it
from the first change of the module: it avoids the constructs that the
pinned extraction tools reject, leave unproved or fail on in Lean, and it
follows the provable design rules. A helper proof does not close a feature,
and metadata inspection or a successful fixture test is not a proof.

Review specification and theorem changes for weakened requirements, smaller
input domains, missing calls and new trusted assumptions. Classify a failed
proof before changing code: a production defect needs a minimal fix toward the
intended behaviour, a Rust regression test and the affected proofs; a tool
defect needs a qualified tool repair, except that a construct that the
[provable Rust subset](docs/conventions/provable-subset.md) covers is
rewritten into its alternative and any other rejection is handled as that
convention states. Do not edit generated definitions, introduce unproved
wrappers or weaken contracts to hide failures.

Once the required proof gate runs in CI, a kernel change merges only when the
gate passes on its head or a committed waiver record covers the failure. A red
gate is never merged over.

## Porting from the prototype tree

The prototype tree is a frozen earlier implementation of this system. It is
not public, is read-only and is the source for porting. Take one module at a time, carry its
tests over, and add a porting record in the same change; see
[porting](docs/conventions/porting.md). Results obtained with the prototype,
including proofs, QEMU runs and board runs, are not evidence for krepi.

## Evidence

Only receipts that CI or the hardware-in-the-loop (HIL) bench produced, and
that are stored where they can be retrieved, are acceptance evidence. A local
run helps development; it does not accept a change. The list of known
failures is generated by a tool from those receipts (planned), never edited by
hand.

Every Pi 5 receipt names the firmware, EEPROM and BL31 versions and the bench
configuration from the firmware and lab registry (planned). Updating the
firmware or changing the bench makes the affected receipts stale until they
are obtained again.

Tests do not depend on CPU speed, the wall clock or a fixed QEMU instruction
count; time slices, spin limits and timeouts are platform parameters. Host
tests, QEMU execution and board tests cover different environments, and each
is reported separately.

Tests and tools are written in Rust. Python tooling from the prototype is not
ported.

## Commit format

Use Conventional Commits with an English subject of at most 72 characters:

```text
<type>[(scope)][!]: <description>
```

Types: `feat`, `fix`, `docs`, `style`, `refactor`, `perf`, `test`, `build`,
`ci`, `chore` and `revert`. A scope uses lowercase letters, digits, dots,
underscores, slashes or hyphens. Explain relevant behaviour and testing in the
body when useful.

```text
feat(boot): enter EL1 on QEMU virt and echo the serial console
test(fdt): cover the Pi 5 memory banks and reserved ranges
docs(ipc): state the single-winner rule for reply completion
```

The `.githooks/commit-msg` hook checks the header. Enable it with
`git config --local core.hooksPath .githooks` and do not bypass it.

## License

krepi is released under the [MIT License](LICENSE). The copyright holders are
the casξ Authors, listed in [AUTHORS](AUTHORS). Contributions are accepted
under the same license. Creating a tag or a release is a separate authorized
action.
