# Formal verification

Selected kernel functions are to be proved correct in Lean 4. Charon extracts
the actual Rust source of the kernel, Aeneas translates the extraction into
Lean definitions, and handwritten Lean proofs show that those generated
definitions satisfy independently written specifications. The organization
follows the one used for the casξ CAS library, adapted to an
operating-system kernel.

A proof covers exactly the functions and statements registered for it. Code
outside a registered target is unverified, and a theorem says nothing beyond
its statement: the items under [trusted boundary](#trusted-boundary) remain
assumptions, and a refinement proof of Rust code says nothing about timing,
the compiled binary or concurrent execution unless a separate layer proves it.

## Status

The three registries `verification/targets.json`, `verification/models.json`
and `verification/legacy.json` exist and are empty. The pinned tools exist:
the tool manifest `verification/toolchain.json`, the reviewed Aeneas patch,
the recipe of the image that holds the tools, the workflows that build and
publish it, and `cargo xtask formal toolchain-check`, which checks the
manifest against the Aeneas and Charon sources ([tools](#tools)). Everything
else on this page is planned: the Lake project, the `Krepi` Lean modules, the
qualification crate and the other commands of `cargo xtask formal`. They are
set up by porting the tooling of the CAS project and the prototype tree, and
this page changes with them. No target is registered and nothing is proved.

Proofs of the prototype are proofs about that code.
They do not carry over: a module taken into krepi is proved again against the
contract of its component here.

## Proof layers

The final goal is a reproducible argument of functional correctness and
security for a declared configuration of the privileged kernel. The argument
is built in layers, and each layer connects to real objects of the next.

| Layer | What it proves | What it must connect to | What it does not give |
| --- | --- | --- | --- |
| Requirements and security specification | Subjects, rights, objects, observations, budgets, failure and termination | The ABI and service requirements, the threat model and the supported configurations | Adequacy of the specification, which review decides |
| Abstract state machine | Transitions of processes and threads, capabilities, IPC, waits, resources and scheduling | Independently defined state, invariants, permitted actions and environment assumptions | A finite enumeration of states is not a proof over every trace |
| Sequential implementation refinement | The Charon/Aeneas translation of the production Rust refines the state machine | The same production source, machine integers, error paths and failure behaviour | The compiler, unextracted wrappers and concurrent execution |
| Composition | Construction, identity lookup, snapshot and write-back, transaction commit, system-call paths | Real call relations, frame properties, counts and references, global invariants | One module's proof does not order or make atomic a path across modules |
| Concurrency | Per-CPU state, shared transactions, publication, cancellation, invalidation and reclamation | The actual locks, atomics and IRQ paths with their linearization points | A sequential model with exclusive `&mut` access says nothing about weak memory |
| Architecture and binary | `unsafe` boundaries, assembly, context, page tables, caches and TLBs, the delivered image | The fixed CPU, ISA, compiler flags, link layout and the exact binary | QEMU or board runs are not a proof of machine semantics |

The sequential value semantics of Aeneas does not cover atomics, `unsafe`
code or assembly. Those layers need a method chosen for the real primitives,
and every connection that is not proved stays an open obligation. An item is
never moved into the trusted boundary to close a gap.

## Layout

| Path | Content | Status |
| --- | --- | --- |
| `verification/toolchain.json` | The tool manifest: Lean, the Aeneas source commit with its reviewed patch and the Lake lock of its Lean library, Charon, the Rust nightly used by Charon, opam and GMP, with the downloads of each host ([tools](#tool-manifest)) | Present |
| `verification/tooling/` | Reviewed tool patches, named by the manifest, and their license texts | Present |
| `verification/image/` | The recipe of the image that holds the pinned tools, and the list of its third-party notices ([image](#image)) | Present |
| `verification/lakefile.lean`, `lean-toolchain`, `lake-manifest.json` | The Lake project for specifications and proofs | Planned |
| `verification/Krepi/Spec/` | Specifications written from requirements, registered in `targets.json`; a component with a directory below [subject domains](domains/README.md) describes its own in the `specification.md` there | Planned |
| `verification/Krepi/Proofs/` | Refinement proofs of production targets | Planned |
| `verification/Krepi/Models/` | Lean models of items that proofs reach without extracting them, and their differential check | Planned |
| `verification/Krepi/Qualification/` | Proofs about the qualification shapes | Planned |
| `verification/externals/<Module>/` | Reviewed external declarations of a target or a qualification case (`FunsExternal.lean`, `TypesExternal.lean`), named by its `models` field | Planned |
| `verification/targets.json` | The proof target registry | Present, empty |
| `verification/models.json` | The model registry | Present, empty |
| `verification/legacy.json` | Production functions without proofs, recorded when the inventory is adopted | Present, empty |
| `verification/qualification/` | A small crate of code shapes and their expected tool outcomes (`cases.json`) | Planned |
| `xtask/src/formal/` | The commands of `cargo xtask formal` | `toolchain-check` present, the others planned |

Generated Lean, extraction outputs, logs and receipts go to the ignored
`artifacts/formal/` directory, and the Lake build directory
`verification/.lake/` is ignored as well. Generated definitions are never
edited.

## Tools

The proof tools have one set of pinned versions for two hosts:
`linux-aarch64`, where CI runs them in a container image on a GitHub-hosted
`ubuntu-24.04-arm` runner, and `darwin-arm64`, where a local installation
serves development. Only runs in the image produce evidence. Aeneas and
Charon are built from source; their released binaries are not used.

| Tool | Pin |
| --- | --- |
| Lean | A release archive for each host, by SHA-256; it provides `lean`, `lake` and `leanchecker` |
| Aeneas | A source commit, built with the reviewed patch in `verification/tooling/`; its Lean library is built with the Mathlib commit of its Lake lock |
| Charon | The commit that Aeneas names in its `charon-pin` |
| Rust | The nightly that Charon names in its `rust-toolchain`, installed with rustup, with the standard library for `aarch64-unknown-none` beside the host's |
| opam and OCaml | An opam binary for each host, by SHA-256, a commit of the opam package repository and an OCaml compiler package; they build Aeneas |
| GMP | A source archive, by SHA-256, built on each host |

The patch keeps its Apache-2.0 notice; the license text is
`verification/tooling/LICENSE-Apache-2.0`. Any change of a tool version,
patch or pin requires a new image ([changing a tool](#changing-a-tool)) and a
passing qualification.

### Tool manifest

`verification/toolchain.json` has schema version 1. Its sections pin what
both hosts share; `hosts` holds what differs between them.

| Field | Content |
| --- | --- |
| `schema` | `1` |
| `lean` | `toolchain` as `lean-toolchain` files name it, and `version` and `commit` as `lean --version` prints them |
| `aeneas` | `source_url` and `commit`; `patch`, the repository path of the reviewed patch, and its `patch_sha256`; `patch_origin`, the source, SHA-256 and changes of the version the patch was ported from; `lake_manifest_sha256`, the SHA-256 of `backends/lean/lake-manifest.json` at the commit, and `mathlib_commit`, the Mathlib commit that this lock pins |
| `charon` | `source_url`, `commit`, and `version` as `charon version` prints it |
| `rust` | `toolchain`, the rustup name of the nightly; `rustc_commit`; `manifest_url` and `manifest_sha256` of the dated channel manifest; the rustup `components` and the further `targets` to install; `rustup`, the version of rustup, and `rustup_source_url` and `rustup_commit`, the source of that version, from which the image takes rustup's license texts |
| `opam` | `version`; `repository_url` and `repository_commit` of the opam package repository; `compiler`, the compiler package of the switch |
| `gmp` | `version`, and `url` and `sha256` of the source archive |
| `hosts` | One column each for `linux-aarch64` and `darwin-arm64`, described below |

A host column holds:

- `locale`, the locale of the tools;
- `prefix`, the directory of the installation, laid out as the image lays out
  `/opt/krepi-formal`: that path itself on `linux-aarch64`, and on
  `darwin-arm64` `artifacts/formal/tools`, relative to the repository root,
  where a symbolic link may point to an installation outside the checkout;
- `url` and `sha256` of the Lean archive (`lean`), the opam binary (`opam`)
  and `rustup-init` (`rustup_init`);
- on `darwin-arm64` only, `version`, `url` and `sha256` of the pkgconf
  source archive (`pkgconf`), built on that host because its OCaml switch
  needs a `pkg-config`; the image build takes `pkg-config` from the Ubuntu
  archive;
- `switch_export_sha256`, the SHA-256 of what `opam switch export --full`
  writes for the switch built on that host, or `null` until a build on that
  host has produced it.

### Tool checks

`cargo xtask formal toolchain-check --aeneas DIR --charon DIR` checks the
manifest against a checkout of Aeneas, a checkout of Charon and the patch in
the repository, prints one line per check and fails when any check fails:

- each checkout is at its pinned commit;
- the pinned Lean toolchain is the one that Aeneas names in
  `backends/lean/lean-toolchain`, the pinned Charon commit the one in
  Aeneas's `charon-pin`, and the pinned nightly the channel of Charon's
  `charon/rust-toolchain`;
- the pinned Lean toolchain is that of the pinned Lean `version`, and the
  Lean archive of each host belongs to that release, so that the Lean the
  image installs is the Lean that Aeneas names;
- the patch has the pinned SHA-256;
- Aeneas's `backends/lean/lake-manifest.json` has the pinned SHA-256 and
  pins the pinned Mathlib commit;
- the Rust targets include `aarch64-unknown-none`, the triple for which the
  kernel is extracted;
- the manifest has exactly the two host columns, each with a UTF-8 locale, a
  prefix without `.` or `..` components, `/opt/krepi-formal` on
  `linux-aarch64`, and a `switch_export_sha256` that is `null` or a SHA-256
  in lowercase hexadecimal.

The image build runs it before its first expensive step. Its unit tests run
in `cargo xtask check`, together with a test that the committed manifest
passes the checks that need no checkout and that the committed patch has the
pinned SHA-256.

### Image

`verification/image/Dockerfile` builds the image in stages from an Ubuntu
base image pinned by digest; `verification/image/recipe.sh` holds the shell
functions of its steps. Its default build context is `verification/`, and
the named contexts `aeneas-src` and `charon-src` are the checkouts that the
tool checks have accepted, Charon's with its submodules. The steps

- download the Lean archive, `rustup-init`, the channel manifest, the opam
  binary and the GMP source archive over HTTPS and check each against its
  pinned SHA-256, and fetch the opam package repository and rustup's source
  at their pinned commits;
- install the nightly with a rustup whose self-update is turned off, check
  the version and commit that rustup reports, check the SHA-256 of the dated
  channel manifest, and check that the manifest and the installed `rustc -vV`
  name the pinned rustc commit;
- check the SHA-256 of the patch and of the Lake lock of the Aeneas Lean
  library and the Mathlib commit of the lock again, apply the patch, and
  build the library with Mathlib from the Mathlib cache;
- build GMP, the OCaml switch, Aeneas and Charon from source, check that
  Charon's submodules are at the commits that Charon records, check the
  versions that Lean and opam report against the manifest, and, once the
  `linux-aarch64` column pins it, check the SHA-256 of the switch export.

Two kinds of download have no pin of their own. Cargo fetches the crates that
Charon uses from crates.io and Git and checks them against the checksums and
commits of Charon's `Cargo.lock`. `lake exe cache get` takes Mathlib's build
cache, and the `leantar` tool that unpacks it, from Mathlib's cache service
for the Mathlib commit of the pinned Lake lock, and Lake clones the packages
of the lock at the commits that it names.

The final stage holds the tools only, below `/opt/krepi-formal`:

| Path | Content |
| --- | --- |
| `lean/` | The Lean toolchain |
| `bin/` | `aeneas`, `charon` and `charon-driver` |
| `backend/` | The patched Aeneas Lean library, built, with Mathlib and its other Lake packages in `.lake/packages` |
| `rustup/`, `cargo/` | The rustup and Cargo homes with the nightly |
| `versions.json` | What the build observed: `lean` (`version`, `commit`, `sha256`), `aeneas` (`commit`, `patch_sha256`, `version`, `lake_manifest_sha256`, `mathlib_commit`), `charon` (`commit`, `version`, and the commit of each path in `submodules`), `rust` (`toolchain`, `rustc_commit`, `manifest_sha256`, `rustup`, `rustup_commit`, `rustup_init_sha256`, `components`, `targets`), `opam` (`version`, `sha256`, `repository_commit`, `ocaml`, `switch_export_sha256`), `gmp` (`version`, `sha256`), the Ubuntu versions of bubblewrap and Git (`apt`) and the base image (`base_image`) |
| `opam-switch.export` | The switch that built Aeneas, as `opam switch export --full` writes it |
| `notices/` | The third-party license texts that its `README` lists, and the GMP source archive |

GMP's shared library is in `/usr/local/lib`; bubblewrap, Git and `time` come
from the Ubuntu archive. The source trees, the opam switch and the build
directories stay in the build stages. Everything below `/opt/krepi-formal`
belongs to root, and the installed trees and files have no write
permission, so a tool that runs as another user cannot change the
installation.

The build fails when a component that `notices/README` lists has no license
text, and also when one of the packages below has none:

- each crate that Charon links for the host, that is the crates from
  registries and Git repositories that its normal and build dependencies
  reach: the license files of the crate, or for a crate from Git without
  any, of its repository. A crate that ships no license file gets the
  standard texts of the licenses that it declares, which the Rust toolchain
  ships, and a note that says so;
- each submodule of Charon, such as MiniRust;
- each package of the opam switch that has a source: the license files that
  it installs, or else those of its source as `opam source` fetches it. A
  package without a source, such as a `base-` or `conf-` package, holds no
  code;
- each package of the Lake lock of the Aeneas Lean library.

### Environment of tool commands

The proof gate (planned) runs each tool command with an empty environment
and only the variables that `xtask/src/formal/toolchain.rs` gives it:

| Variable | Value | Commands |
| --- | --- | --- |
| `LAKE_ARTIFACT_CACHE` | `false` | All |
| `CARGO_NET_OFFLINE` | `true` | All |
| `CARGO_HOME` | `cargo/` of the installation | All |
| `RUSTUP_HOME` | `rustup/` of the installation | All |
| `RUSTUP_TOOLCHAIN` | The pinned nightly | All |
| `LANG`, `LC_ALL` | The `locale` of the host's column | All |
| `GIT_CONFIG_NOSYSTEM` | `1` | All |
| `GIT_CONFIG_GLOBAL` | `/dev/null` | All |
| `PATH` | `lean/bin`, `bin` and `cargo/bin` of the installation, then `/usr/bin:/bin:/usr/sbin:/sbin` | All |
| `HOME` | A new, empty directory of the run | All |
| `TMPDIR` | A directory of the run | All |
| `CARGO_INCREMENTAL` | `0` | Charon and Aeneas, the extraction |
| `CARGO_TARGET_DIR` | A directory of the run for this extraction alone | Charon and Aeneas, the extraction |

The installation is the `prefix` of the host's column: `/opt/krepi-formal`
in the image, and a directory with the same layout on `darwin-arm64`. The
Lean toolchain comes first in `PATH` because `leanchecker` takes the
toolchain of the `lean` it finds there as its system root. Charon runs Cargo
through `rustup run`, which needs `RUSTUP_HOME` to find the nightly instead
of installing it from the network. The two Cargo build variables go to both
extraction commands; Aeneas runs no Cargo and ignores them.
`LEAN_NUM_THREADS` is not set, so Lean uses every CPU of the host.

### Changing a tool

A change of a tool version, of the patch or of the image recipe takes two
pull requests:

1. The first changes `verification/toolchain.json`, `verification/tooling/`
   or `verification/image/`. The workflow `formal image build` builds the
   image on the pull request without publishing it. Where the change alters
   the opam switch, the `linux-aarch64` column's `switch_export_sha256` is
   `null` for the first build and takes `opam.switch_export_sha256` from the
   `versions.json` that the build uploads; the build that follows checks it.
   After the merge, the workflow `formal image publish` builds the image
   again from `main`, publishes it as
   `ghcr.io/casxi-lab/krepi-formal:<commit>` and prints its digest. It
   refuses to run while `switch_export_sha256` of `linux-aarch64` is `null`.
2. The second pins that digest as the image that the CI jobs of the proof
   gate (planned) pull, and those jobs validate it on its pull request.

Both workflows run only for changes to these paths or to the two workflows.
The publish workflow runs only on pushes to `main`, and its job alone may
write packages; a pull request never publishes an image. Both run every
step with `bash -eo pipefail`. Before the image build, both run the tool
checks and a check that `check_notices` of the recipe fails when any
component that `notices.txt` lists has a missing or empty notice. Both record
the available disk before and after removing preinstalled software from the
runner, sample it together with the size of the Docker data directory every
15 seconds during the build, record Docker's disk use at the end and then
free its build cache, and upload the samples, the build log, the notice
check, the layer sizes, `versions.json` and the switch export as a workflow
artifact.

## Commands

The commands of `cargo xtask formal` follow the CAS project. Only
`cargo xtask formal toolchain-check` exists; the others are planned.

| Command | Purpose |
| --- | --- |
| `cargo xtask formal toolchain-check --aeneas DIR --charon DIR` | Checks Aeneas and Charon checkouts and the Aeneas patch against the tool manifest ([tool checks](#tool-checks)) |
| `cargo xtask formal qualify` (planned) | Tool qualification regression on the code shapes in `verification/qualification` |
| `cargo xtask formal run [--target NAME]...` (planned) | The proof gate: qualification, the specifications and every target (or the named ones) with its mutants |
| `cargo xtask formal check` (planned) | Registry, legacy and inventory metadata only; runs no tool and proves nothing |
| `cargo xtask formal impact --base REV` (planned) | Classifies changed functions since `REV` and reports scope reductions |
| `cargo xtask formal inventory` (planned) | Lists every production function by inventory key |
| `cargo xtask formal editor` (planned) | Prepares `verification/` for interactive editing |

Once the commands exist, `cargo xtask check` runs the proof gate, and CI runs
it on every change. A change merges only when the required gate passes on its
head or a committed waiver record covers the failure.

## Proof targets

Each entry of `targets.json` under `targets` describes one extraction and its
obligations. The fields are those of the CAS project:

| Field | Meaning |
| --- | --- |
| `name`, `module`, `feature` | Target name, generated Lean namespace, feature ID (`krepi.<area>.<feature>`) |
| `description` | What the target proves, in one paragraph |
| `start_from`, `opaque`, `exclude` | Charon roots and cut points |
| `proves` | Inventory keys (`file#Owner::name`) of local functions whose every path the obligations cover |
| `unclosed` | Inventory keys of local functions the extraction reaches, translated or cut, that are not proved |
| `derived` | Reached methods that a `#[derive(..)]` attribute defines; they have no source text and stay unverified |
| `unconstrained` | Rust names of the external functions and types the extraction reaches |
| `models` | Optional directory of reviewed external declarations installed in place of the generated templates |
| `trusted_axioms` | Further axioms the theorems may use, each with a reviewed reason |
| `premises` | Hypotheses that restate, over this target's generated types, a registered theorem of another target about a function this target cuts |
| `proof_modules`, `obligations` | Lean modules, and the statements with the theorems that establish them |
| `mutants` | Source edits, each of which must make a named theorem fail |

A run extracts the target from the current production source and checks the
registry against the translation: every reached local function is in `proves`
or `unclosed`, every external item in `unconstrained`, and no entry is stale.
It builds the generated definitions and the proof modules with warnings as
errors, so `sorry` fails, and audits every registered theorem with
`#print axioms`. Allowed axioms are Lean's `propext`, `Classical.choice` and
`Quot.sound`, the target's unconstrained declarations and its trusted axioms.
Every mutant must make a named theorem fail; a mutant whose failure has
another explanation fails the gate as inconclusive. A tool failure is reported
apart from a proof failure.

A target extracts the production code itself. A hand-written mirror of the
implementation, an unmatched extraction root, an unreviewed rewrite of
execution semantics or an edited generated file is rejected.

## Specifications

A specification is the Lean statement of what a component must do. It is
written from the `requirements.md` and `contract.md` of the component below
[subject domains](domains/README.md) and from its feature documents, before
the implementation is extracted, and never from the implementation. The
component's `specification.md` describes the model and relates each contract
clause and requirement to Lean; its `proof.md` lists the targets, obligations
and trusted items. Specifications live below `verification/Krepi/Spec/` and
are registered in `targets.json` under `specifications`:

| Field | Meaning |
| --- | --- |
| `module`, `feature` | Lean module below `Krepi.Spec`, feature ID |
| `theorems` | Theorems of the module that establish its properties and witness that it is not vacuous |

A specification is pure Lean, so only `propext`, `Classical.choice` and
`Quot.sound` may appear in its audit. It quantifies over every input of the
stated widths and over every sequence of external observations, and states
the results and the error order of each operation, the fields it may change
and the invariants that constructors establish and operations preserve.
Witnesses of success and of every failure are registered as theorems, so an
unsatisfiable specification is caught. Changing a registered specification
changes the meaning of the obligations that refine it and is reviewed as
such.

For kernel state, the specification states identity (pool, slot, generation
and rights together), lifetime (which states are terminal and which
transitions they allow), the frame of each operation for success and for
failure, budget accounting including overshoot that preemption causes, and
reclamation conditions, each tied to a real acknowledgement.

## Models

`verification/Krepi/Models/` states, as executable Lean definitions, the
behaviour of items that proofs reach without extracting them. Each model is
registered in `models.json` with these fields:

| Field | Meaning |
| --- | --- |
| `name`, `lean` | Model name and Lean module |
| `provider` | The library or source that the model describes, with its version |
| `items` | The modelled Rust items |
| `cases` | The case kinds that the qualification compares with the real implementation |
| `axioms` | Model axioms, each reviewed |
| `used_by` | For each target that installs the model, the registered theorems that reach it |

The comparison of a model with the real implementation is evidence for the
model, not a proof; the modelled source remains an assumption.

## Trusted boundary

| Item | Role | How it is checked |
| --- | --- | --- |
| Lean kernel and the three standard axioms | Checks every proof | Axiom audit of every registered theorem |
| Mathlib and the Aeneas Lean library | Mathematical definitions and models of integers, slices, `Option`, `Result` and other core items | Pinned Lake lock; library axioms appear in the audit and must be registered |
| Charon, the Rust nightly and Aeneas with reviewed patches | Translation of the production source into Lean | Pinned sources and binaries; qualification regression; mutants |
| Unconstrained declarations | External functions and types without a model | Theorems hold for every interpretation; listed per target |
| Trusted axioms | Reviewed exceptions | Listed per target with a reason |
| Library models (`models.json`) | Behaviour of items that are not extracted | Compared with the real implementation in every qualification |
| Compiler, linker and the production toolchain | The binary that runs | Not proved; the architecture and binary layer narrows this item |
| Assembly, `unsafe` code, atomics and IRQ paths | Entry, context switch, page-table and cache maintenance, synchronization | Not covered by the sequential refinement; separate obligations |
| Hardware: CPU, MMU, GIC, timers, memory | Behaviour of the machine | Architecture assumptions checked against manuals and tested on boards; the hardware model stays an assumption |
| Firmware entry and the firmware coherence convention | State at kernel entry, and the cache coherence that cache-on entry code relies on beyond its own image range | Listed in the release declaration; board tests |
| DMA drivers without an IOMMU constraint | Device access to memory | Listed in the release declaration; such drivers are part of the trusted base |
| Firmware mailbox services | Services that the firmware provides at run time | Listed in the release declaration |

Each release declaration names its configuration, the privileged entry
points it covers, its open obligations and these trusted items. A result
obtained on a host, on QEMU or on a board, and a proof of an earlier
configuration, is never upgraded by a later theorem.

## Code shapes and the provable subset

`verification/qualification/` holds a small crate of the code shapes that
targets use, with the expected outcome of the tools for each in
`cases.json`. Every qualification re-extracts them, so a tool change that
alters a translation fails before it reaches a target. Some constructs that
the prototype used, such as `Iterator::any` and `flatten`, do not translate
into code that a proof can rely on; the
[provable Rust subset](conventions/provable-subset.md) lists them with the
other constructs that stop extraction or proofs, and the forms to write
instead, for the modules that proofs are to cover.

## Legacy inventory and admission

`cargo xtask formal inventory` (planned) lists every production function by
file, owner and name, found by a conservative lexical scan that skips test
code. `legacy.json` lists the functions that have no proof at the time the
inventory is adopted; its `baseline` is the commit of that adoption and is
`null` until then. An entry leaves the list when a target proves the function
or, with review, when the function is no longer a production function. A
legacy function is never trusted by a proof and appears in a target's
`unclosed` list when reached. `cargo xtask formal check` (planned) reports new
functions that are neither legacy nor proved, and
`cargo xtask formal impact --base REV` (planned) reports a removed target, theorem or
proved function, a new unconstrained item, trusted axiom or premise, and a
removed obligation or mutant, each of which needs independent review.

## Editing proofs

Interactive editing in `verification/` with the Lean 4 extension needs the
generated definitions of a run and a writable clone of the Lean library,
which `cargo xtask formal editor` (planned) prepares. Editor builds are not
formal evidence; only a gate run produces receipts.

## Limitations

- No target is registered; the whole kernel is unverified.
- Proofs cover only registered targets. Code outside them, including code
  ported from the legacy tree, is unverified until a target proves it.
- Sequential refinement does not cover concurrency, weak memory, `unsafe`
  code, assembly, the compiler or the hardware.
- A proof says nothing about time, memory use or the compiled binary unless a
  registered obligation states it.
