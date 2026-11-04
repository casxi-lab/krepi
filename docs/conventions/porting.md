# Porting from the legacy tree

krepi starts from an empty tree. Code, tests and design rules that the
prototype established are taken from the legacy tree one module at a time,
with a record of where each piece came from and what changed.

## The legacy tree

The legacy tree, also called the prototype tree, is a frozen earlier
implementation of this system at commit
`ec8305c618a8f4e84e0707fa56beac5673f4675e`. It is not public and accepts no
changes. Every port reads from that commit, never from a branch, so that a
porting record names fixed source bytes. Maintainers with access keep it in a
separate clone; it is never added as a remote of this repository.

Results obtained with the legacy tree are not evidence for krepi. Its proofs
are about its own code, its QEMU and board receipts are about its own images,
and its documents describe a system with different capacities and profiles.
A ported module is tested, and where required proved, again here.

## Classification of the legacy areas

Each area of the legacy `src/` tree is ported, redesigned or retired.

| Treatment | Legacy areas | What is taken |
| --- | --- | --- |
| Ported | `src/arch`, `src/board`, `src/mmu`, `src/fdt`, `src/memory`, `src/loader`, `src/crt`, `src/drivers`, `src/services`, `src/platform` | The code, adapted to the krepi layout and conventions, with its tests |
| Redesigned | `src/objects`, `src/capabilities`, `src/ipc`, `src/waits`, `src/notifications`, `src/scheduler`, `src/execution`, `src/smp`, `src/vm`, `src/abi`, `src/root` | The rules, invariants and tests; the code is written again for the krepi object storage, transaction model and multicore design |
| Retired | The serial-triggered diagnostic controllers below `src/user`, the Cargo feature profiles, the Python tooling | Nothing |

- **Ported** code keeps its behaviour unless the porting record lists a
  change. Board facts that the legacy code encodes, such as Pi 5 entry
  conditions, device-tree limits and PCIe and RP1 bring-up sequences, are
  carried over with the code and its references.
- **Redesigned** areas are rebuilt on a new object storage and transaction
  model. The legacy code has fixed demonstration capacities; the new object
  core takes its capacities from a boot-time configuration, commits
  transactions by write set and is designed for several CPUs. The host tests
  of these areas become test vectors for the new code, and their rules become
  requirements and contract clauses of the new components below
  `docs/domains/`.
- **Retired** items are not ported. The diagnostic controllers ran EL0 work
  only as scripts triggered by single serial bytes, which the resident root
  replaces. The feature profiles (`pi5-kernel`, `smp-kernel`, `pi5-storage`,
  `virtio-block` and the others in the legacy `Cargo.toml`) built images that
  excluded each other, which the single-image rule forbids. Tests and tools
  are written in Rust, so no Python script or Python test is ported.

Legacy areas that this table does not list, and the tooling crates, are
classified in the porting record of the first change that takes code from
them. The QEMU runner, serial, serial capture, receipt, ELF and SHA modules
of the legacy tooling crate `tools/` are ported with their tests.

## Porting records

Every change that takes code, tests or data from the legacy tree adds or
updates a porting record in the same change. A record lives at
`docs/porting/<module>.md`, where `<module>` is the destination module path
below `src/` (or below the tooling crate) with `/` written as `-`, for example
`docs/porting/fdt.md`. One record may cover a module directory and its
children.

A record starts with a metadata block:

| Field | Content |
| --- | --- |
| `source` | `prototype@` followed by the full commit hash, for example `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`; tooling taken from the CAS project uses `cas-project@` and its full commit hash |
| `paths` | Every legacy path taken, file or directory |
| `destination` | The krepi paths that received the code |
| `treatment` | `ported` or `redesigned` |
| `features` | The krepi feature IDs that the code serves, or `none` while no feature document exists |

Its level-two sections are, in this order:

1. `Summary`: what was taken and why this treatment applies.
2. `Changes`: every difference from the legacy code that is not a pure
   rename or move, such as changed bounds, errors, capacities, interfaces,
   per-CPU data, or removed diagnostic paths.
3. `Tests carried over`: the legacy tests that were taken, with their legacy
   path and their krepi path, and any whose expected values changed.
4. `Behaviour changes`: observable differences from the legacy behaviour, each
   with the test that fixes the new behaviour. Behaviour differences that the
   legacy tree itself records, such as the differences between its Rust
   suites and the Python runners they replaced, listed in the module
   documentation of the suites (for example
   `tools/src/suites/platform/pi5_kernel.rs`), each get a test.
5. `Hardware evidence to re-obtain`: the QEMU and board results that the
   legacy code had and that krepi has to obtain again on its own image, with
   the board configuration each needs.
6. `Not carried over`: legacy code, tests or documents in the taken paths that
   were left behind, and why.

A record names legacy code by path and commit only. It contains no planning
identifiers and no legacy acceptance records; see
[planning references](documentation.md#planning-references).

## Licensing of ported code

- Code ported from the prototype tree is released under the MIT License as
  part of krepi.
- The formal-verification tooling ported from the CAS project is released
  under the MIT License as part of krepi.
- Third-party code keeps its own license and notice; the reviewed Aeneas patch
  keeps its Apache-2.0 notice.
- The `vendor/` directory of the prototype tree is not ported.

## Rules for a port

- Take the smallest module that compiles and tests on its own.
- Read the whole legacy file before porting it, including its `unsafe`
  comments and module documentation.
- Bring the code to the krepi conventions in the same change: English
  documentation, feature annotations, the single-image rule, per-CPU
  classification of state, and the provable Rust subset for code that a proof
  target will cover.
- Leave legacy diagnostic hooks, serial-triggered probes and feature-profile
  `cfg` branches out of the port.
- Do not port a legacy document as it is. Write the krepi feature document or
  component document from the code and tests that were ported.
