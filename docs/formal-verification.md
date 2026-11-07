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

The registries `verification/targets.json`, `verification/models.json` and
`verification/legacy.json` exist, and so do the statement registry
`verification/statements.json`, the registry of library axioms
`verification/axioms.json` and the registry of the trusted base
`verification/tcb.json`: no target, model, statement, library axiom or
trusted item is registered. The pinned tools exist: the tool manifest
`verification/toolchain.json`, the reviewed Aeneas patch, the recipe of the
image that holds the tools, the workflows that build and publish it, and
`cargo xtask formal toolchain-check`, which checks the manifest against the
Aeneas and Charon sources ([tools](#tools)).
`cargo xtask formal run` exists as the proof gate
([gate run](#gate-run)): it takes a snapshot of the gate inputs, exports
them, applies their rules, runs its phases and writes a receipt. Its phases
are the [qualification](#qualification) of the tools on the code shapes of
the qualification crate, with the three proofs about them, and the
[base round](#base-round), which builds, audits and replays krepi's own
Lean: today the qualification proofs and the definitions that they use. On
a pull request, a first phase records the [guard](#guard), which
`cargo xtask formal guard` runs on its own. None of them verifies anything
about the kernel. The qualification rejects 27 of the cases taken from the
CAS project for now: they keep the expectations recorded with the earlier
Charon and Aeneas, which the pinned tools no longer meet, until each change
is explained and reviewed. Everything else on this page is planned:
specifications, statements and targets, the other phases of the gate and
the other commands of `cargo xtask formal`. They are set up by porting the
tooling of the CAS project and the prototype tree, and this page changes
with them. Nothing about the kernel is proved.

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
| `verification/lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | The Lake project of the hand-written Lean and of the generated definitions, with the Lean toolchain and the packages of the Lake lock of the Aeneas Lean library ([qualification](#qualification)), and the library `KrepiRoot` of the root module that the [base round](#base-round) writes | Present |
| `verification/extraction.toml` | How Charon compiles each extracted crate ([extraction](#extraction)) | Present |
| `verification/Krepi/Spec/` | Specifications written from requirements, registered in `targets.json`; a component with a directory below [subject domains](domains/README.md) describes its own in the `specification.md` there | Planned |
| `verification/Krepi/Statements/` | Statements: the propositions that registered theorems prove ([statements and proofs](#statements-and-proofs)) | Planned |
| `verification/Krepi/Proofs/` | Proofs of statements and refinement proofs of production targets; the only directory of the Lake project outside the statement side ([statements and proofs](#statements-and-proofs)) | Planned |
| `verification/Krepi/Models/` | Lean models of items that proofs reach without extracting them, and their differential check | Planned |
| `verification/Krepi/Qualification/` | Proofs about the qualification shapes | Present |
| `verification/Krepi/Qualification/Models/` | Definitions that the reviewed external declarations of three qualification cases use; they are not models ([qualification](#qualification)) | Present |
| `verification/externals/<Module>/` | Reviewed external declarations of a target or a qualification case (`FunsExternal.lean`, `TypesExternal.lean`), named by its `models` field | Present for qualification cases |
| `verification/targets.json` | The proof target registry | Present, empty |
| `verification/models.json` | The model registry | Present, empty |
| `verification/statements.json` | The statement hash, and each statement with its theorem and state ([statements and proofs](#statements-and-proofs)) | Present, empty |
| `verification/axioms.json` | The axioms of the Aeneas Lean library that target theorems may use, each with its source and reason ([base round](#base-round)) | Present, empty |
| `verification/tcb.json` | Items of the trusted base: native decisions and patterns of generated axioms, whose classification comes later ([base round](#base-round)) | Present, empty |
| `verification/legacy.json` | Kept empty: production functions without a proof are to be listed in `open.json` ([legacy inventory and admission](#legacy-inventory-and-admission)) | Present, empty by design |
| `verification/open.json` | Production functions without a proof, generated from the contracts of the components | Planned |
| `verification/qualification/` | A small crate of code shapes and their expected tool outcomes (`cases.json`) | Present |
| `xtask/src/formal/` | The commands of `cargo xtask formal` | `toolchain-check`, `run` and `guard` present, the others planned |

Generated Lean, extraction outputs, logs and receipts go to the ignored
`artifacts/formal/` directory, and the Lake build directory
`verification/.lake/` is ignored as well. Each run of the gate has a
directory `artifacts/formal/runs/<id>/`, where `<id>` is the Unix time of
its start, its process number and a count: `receipt.json`, `logs/` with
the two output files of each command, and `work/` with the export of the
gate inputs, the home and temporary directories of the tools; in
`cases/`, the extraction and the Lake stage of each qualification case; in
`base/`, the stage of the base round with the root module `Krepi.lean` that
the run writes, its audit file `Audit.lean` and its heartbeat copies in
`.heartbeats/`, and `mktree`, the input of `git mktree` for the statement
hash of the round; and `mktree`, the same input for the guard phase. The
root module is written only there, never in the checkout. Generated
definitions are never edited.

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

`cargo xtask formal run` runs each command that it starts, Git and
`cargo metadata` among them, with an empty environment and only the
variables that `xtask/src/formal/toolchain.rs` gives it:

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
| `CARGO_TARGET_DIR` | A directory of the run for this extraction alone, removed when the extraction ends | Charon and Aeneas, the extraction |

The installation is the `prefix` of the host's column: `/opt/krepi-formal`
in the image, and a directory with the same layout on `darwin-arm64`. The
Lean toolchain comes first in `PATH` because `leanchecker` takes the
toolchain of the `lean` it finds there as its system root. Charon runs Cargo
through `rustup run`, which needs `RUSTUP_HOME` to find the nightly instead
of installing it from the network. The two Cargo build variables go to both
extraction commands; Aeneas runs no Cargo and ignores them.
`LEAN_NUM_THREADS` is not set, so Lean uses every CPU of the host. Because
`cargo` too comes from the installation, a local run needs the
`darwin-arm64` installation at `artifacts/formal/tools`.

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

The commands of `cargo xtask formal` follow the design of the gate.
`cargo xtask formal toolchain-check`, `cargo xtask formal run` and
`cargo xtask formal guard` exist; the others are planned.

| Command | Purpose |
| --- | --- |
| `cargo xtask formal toolchain-check --aeneas DIR --charon DIR` | Checks Aeneas and Charon checkouts and the Aeneas patch against the tool manifest ([tool checks](#tool-checks)) |
| `cargo xtask formal run [--target NAME]...` | The proof gate on a snapshot of the gate inputs, with its receipt ([gate run](#gate-run)); `--target` runs only the named targets. Its phases are, on a pull request, the [guard](#guard), which records its rules; the [qualification](#qualification) and the [base round](#base-round), which every run has; and, planned, every target (or the named ones) with its mutants |
| `cargo xtask formal guard --event PATH` | Checks a pull request, given by the JSON of its `pull_request` event, against the rules for changes of statements, proofs and sources ([guard](#guard)) |
| `cargo xtask formal check` (planned) | Registry metadata and the coverage ratchet against `open.json`; runs no tool and proves nothing |
| `cargo xtask formal receipt [--require-fresh]` (planned) | Says whether a receipt is current for the checkout: the same gate inputs and image, one conclusion for each unit, complete and `VERIFIED`; `--require-fresh` also requires a run of the whole gate from a clean checkout without planned statements |
| `cargo xtask formal vectors COMPONENT` (planned) | Replays the test vectors of a component's contract through its specification and compares the results with those of the Rust host tests |
| `cargo xtask formal mutants TARGET` (planned) | Generates the source mutants of a target and records the survivors with their classification |
| `cargo xtask formal impact --base REV` (planned) | Lists the targets that a change since `REV` affects |
| `cargo xtask formal merge` (planned) | Combines the receipts of the shards of a run and of its qualification into the conclusion of the whole gate |

`cargo xtask check` does not run the gate, which needs the pinned tools.
CI is to run the gate in a job of its own on every change, and a change is
to merge only when the required gate passes on its head or a committed
waiver record covers the failure; both are planned.

## Gate run

`cargo xtask formal run` runs the gate on the commit checked out, the
snapshot commit, and writes a receipt of the run, whether it passes, fails
or stops on an internal error. Its code is in `xtask/src/formal/`: the gate
inputs in `paths.rs`, the commands in `process.rs`, their classes and the
statuses in `outcome.rs`, the receipt in `receipt.rs`, the extraction in
`extract.rs`, the Lake stages, the source rules and the allowlist in
`lean.rs`, the qualification in `qualify.rs`, the base round in `base.rs`,
the statement side and the guard in `guard.rs`, and the run in `run.rs`.

### Gate inputs and snapshot

The gate inputs are defined once, in `paths.rs`: the inputs of extraction,
which are the kernel workspace `kernel/`, the qualification crate
`verification/qualification/` and `.cargo/config.toml`, which Cargo reads
in the repository; and `verification/`, `xtask/`, `.github/workflows/`,
`rust-toolchain.toml` and `toolchains.toml`. A run

1. takes the snapshot: the commit checked out, its root tree, and the Git
   object of each gate input at that commit (`git ls-tree`), or none for a
   gate input that the commit does not have;
2. stops unless the gate inputs are clean: `git status` lists no staged or
   unstaged change and no untracked file below them. Ignored files, such as
   Lake's build directory, are allowed;
3. exports the gate inputs of the snapshot commit with `git archive`, whose
   output is kept in `logs/` as that of any command, into `work/source` of
   the run directory, and checks that the export holds every file of the
   commit, with the same mode (a file, an executable file, a symbolic link)
   and the same object name, which Git computes from the export without
   filters. Attributes such as `export-ignore` or `export-subst`, or
   line-ending conversions, therefore cannot change what the run reads; any
   difference is a tool failure. The tool manifest of the export must also
   be the file that the run read from the checkout at its start, for the
   environment of its commands, and the target registry of the export,
   `verification/targets.json`, must register every name given with
   `--target`;
4. rejects the run when a gate input is a Python source, a file whose name
   ends in `.py` in any case, a Lean file below `verification/KrepiGen/`,
   the directory of the generated definitions, which only stages of the run
   hold, or a Cargo configuration below the root, a `.cargo/config.toml` or
   `.cargo/config` in any directory but the root
   ([Cargo configuration](#cargo-configuration));
5. fails when Cargo would read a Cargo configuration in the export that is
   not the snapshot's ([Cargo configuration](#cargo-configuration)), and
   rejects the run when a manifest of the exported kernel workspace has a
   path dependency outside `kernel/`, as the `manifests` step of
   `cargo xtask check` does for the checkout, whether or not the export
   holds the path; either way Cargo then does not run;
6. resolves the exported kernel workspace with
   `cargo metadata --format-version 1 --locked --offline --all-features --manifest-path kernel/Cargo.toml`
   and rejects the run unless the workspace root is `kernel/` and every
   package is a member of it, with its manifest and the sources of its
   targets inside `kernel/` once symbolic links are resolved, as the
   `manifests` step requires of the checkout. A failure of Cargo itself is
   a tool failure.

A tool failure in one of these steps ends them: the later steps do not run.
A rule that rejects the run in step 4 does not. Every later step reads the
gate inputs from the export, never from the checkout. After a clean start,
the run takes the objects of the gate inputs again at the end, at the
commit checked out then, and runs `git status` again: when an object
differs, or the gate inputs are not clean at the end, the run is `STALE`,
with one failure that names the gate inputs whose objects differ and the
records of `git status`.

### Cargo configuration

Cargo reads the `.cargo/config.toml` or `.cargo/config` of the directory
where it runs and of each directory above it, up to the root of the file
system, and the configuration of its Cargo home. The gate runs Cargo in the
export and in directories below it, such as the qualification crate, so a
gate input that holds either file in a directory other than the root
rejects the run. Before the run starts Cargo in the export, it looks for
both files in the export and in every directory above it, with symbolic
links resolved. Only the snapshot's own
are allowed: `.cargo/config.toml` of the export when the snapshot holds it
as a file, not as a symbolic link, and that of the checkout root when it
has the bytes of the snapshot's. Any other, such as a file below the
ignored `artifacts/`, a `.cargo/config` in the checkout root or a Cargo
configuration above the repository, fails the run as a tool failure that
names the file, without a conclusion about the code; Cargo then does not
run. When the checkout root's file is allowed, Cargo reads the snapshot's
configuration twice: values that Cargo joins across files, such as
arrays, appear twice, and a relative path in the root's copy resolves in
the checkout, not in the export.

The Cargo home is `cargo/` of the tool installation. Its configuration is
part of the installation, trusted as the tools are, and the run does not
look for it: in the image it is what the recipe installs, and on
`darwin-arm64` what the developer installed.

### Deadlines and processes

Each command runs in a process group of its own, with the environment
above, its input from a file or from nothing, and its standard output and
standard error each written to a file of `logs/`, so that what a killed
command wrote is kept. Its limit is the smallest of:

- the cap of its call site: 1,800 s for Charon, 3,600 s for Aeneas, 7,200 s
  for each `lake build` and 1,800 s for each `lake env lean`; `leanchecker`,
  the comparator, Git and `cargo metadata` have none;
- the rest of the budget of its phase;
- the rest of the budget of the gate, 7,200 s from the start of the run.

The steps after the phases, the second snapshot and the receipt, have 300 s
beyond the gate's budget. A command whose limit is used up, 0 s as the
receipt writes it, does not start and is `NOT_RUN`. When a command reaches
its limit, or ends by itself, the run kills its process group, collects the
command and waits up to 60 s, beyond the command's limit, until no process
of the group is left; a process that is still there makes the command a
tool failure. The run restores the default disposition of `SIGCHLD` when it
starts, without which the system could collect an ended command before the
kill. Each command is printed when it ends.

A signal from the terminal does not reach a running tool, whose group is
its own. SIGINT and SIGTERM stop the run instead, also when they were
ignored when it started, and so does SIGHUP unless it was ignored then, as
`nohup` leaves it: the run kills the group of the command that is running,
collects the command, waits for its group as above, and ends by the same
signal, without a receipt. A signal that comes
between two commands takes effect before the next command starts or before
the receipt is written.

### Extraction

An extraction, in `extract.rs`, translates the Rust items that it starts
from into Lean. It needs at least one root, and a work directory that no
extraction has used: a request without a root, or a work directory that
already holds `extract.llbc`, `aeneas/` or `target/`, is an internal error,
and nothing runs. It runs two commands of its unit:

- Charon, in the package that it extracts:
  `charon cargo --preset=aeneas --sysroot default --start-from <roots separated by commas> [--opaque <pattern>]... --dest-file <work>/extract.llbc -- --lib --locked`;
- Aeneas, in the work directory:
  `aeneas -backend lean -namespace KrepiGen.<module> -split-files -subdir KrepiGen/<module path> -emit-json -no-progress-bar -sequential -dest <work>/aeneas <work>/extract.llbc`.

Aeneas starts only when Charon passed and wrote `extract.llbc`; otherwise
it is `NOT_RUN` (see [results](#results)). Aeneas runs on one thread,
because its pool of threads takes a time that varies with the load of the
machine and, after an internal exception, can go on to report errors in
other functions. Both commands have `<work>/target` as their Cargo target
directory, which is removed when they have ended; one that cannot be
removed is an internal error. Before Aeneas is classified, the gate reads
`translation.json` and the Lean files in
`<work>/aeneas/KrepiGen/<module path>`, and takes the SHA-256 of each; a
file that cannot be read, a `translation.json` that is not one, and a
missing `translation.json` after Aeneas exited with 0 make Aeneas a tool
failure. Aeneas writes `translation.json` at the end of every run; after
any other exit, a missing one is no translation. Of `translation.json` the
gate reads `rust_name`, `lean_name`, `lean_file`, `is_local`, `is_opaque`,
`source.file` and `loop.is_body` of each function, and `rust_name` and
`lean_file` of each type; every one of them but `loop` must be there, and
other fields are not read.

What the extraction gives:

| Item | Content |
| --- | --- |
| Complete | Aeneas exited with 0, reported no `[Error]` and wrote at least one Lean file |
| Diagnostics | The `[Error]` and `[Warn ]` messages of Aeneas and the lines of Charon that start with `error:` or `error[`, with terminal escapes removed |
| External functions | The Rust names of the functions translated without a body whose Lean file is `FunsExternal_Template.lean`, local ones among them |
| External types | The Rust names of the types whose Lean file is `TypesExternal_Template.lean` |
| Loops | Each local function with a body whose `loop` record is not a body, as its Lean name below the namespace of the extraction and its source file |
| Local functions | The Rust name, source file and Lean name of each function of the crate, with a body or without one |

`verification/extraction.toml`, schema 1, states how Charon compiles each
crate that the gate extracts. Its section `qualification` gives the triple of
each host of the tool manifest, `aarch64-unknown-linux-gnu` and
`aarch64-apple-darwin`, and empty `features` and `cfg`: Charon is given no
`--target` and adds the host's triple itself, and the gate passes no
features and no `cfg` settings. Its section `kernel` gives the triple of the
production kernel, `aarch64-unknown-none`, and the features and `cfg`
settings of its release profile, which has none; nothing is extracted from
the kernel while no target is registered. The qualification stops when the
file of the export does not have exactly these hosts, names features or
`cfg` settings for the qualification crate, or gives the kernel another
triple. The triples of the qualification crate record what Charon chooses
on each host; nothing passes them to Charon, and the gate does not check
their values.

### Qualification

The qualification phase, in `qualify.rs`, checks the pinned tools against
the code shapes of the qualification crate before anything relies on them.
Every run has it, a run of named targets as well, with a budget of 3,600 s.

The crate `verification/qualification/` holds one module per shape. It is a
workspace of its own with its own `Cargo.lock` and depends on no crate, so
that Charon compiles it alone, offline and `--locked`. Its manifest may hold
only `[package]` with `name`, `version`, `edition`, `license`, `publish` and
`description`, an empty `[workspace]`, `[lib]` with `path`, and
`[lints]` with `rust`, and the package has no `build.rs`: dependencies,
features, a build script, profiles and patches would change what Cargo
compiles, and Charon reads `[package.metadata.charon]` in addition to its
arguments. The phase stops when the crate in the export is otherwise. The
cases are in `verification/qualification/cases.json`, schema 1, in the
order in which they run:

| Field | Meaning |
| --- | --- |
| `name` | The case, a word of ASCII letters, digits, `-` and `_`, given once |
| `module` | The module path of its translation below `KrepiGen`, such as `Qual.Arithmetic` |
| `start_from` | The roots of its extraction; empty for a case with `parts` |
| `parts` | Optional. Modules below the case's, each with its own `start_from`, which are extracted one by one and imported together |
| `opaque` | Optional. Patterns of items that the extraction translates without their bodies |
| `expect` | `translated`, `ill-typed` or `rejected` |
| `type_errors_in` | For an ill-typed case alone: the file of the case's directory of generated modules in which every type error lies, such as `Funs.lean` |
| `models` | Optional. A directory below `verification/externals/` with the reviewed external declarations that replace the templates of the case |
| `diagnostics`, `external_functions`, `external_types` | The exact [diagnostics and external items](#extraction) of the extraction |
| `loop_sources` | Optional. The exact loops of the extraction with their source files |
| `proof` | Optional, for a translated case: `module`, a module below `Krepi.Qualification`, and `theorems`, the theorems below that module that it proves about the translation |

A field that is not in this table, and a case that does not follow it,
stop the phase. The phase reads `cases.json` from the checkout at the start
of the run, to register its units, and stops when the export's file is not
the same. Its units are each case, `qualification/<case>`, and each theorem
of a case, `qualification/<case>/<theorem>`.

Each case runs in a new directory of the run, `work/cases/<case>/`:

1. The [extraction](#extraction) of the case in that directory, or of each
   of its parts in `parts/<n>/`, from the crate of the export. Each
   extraction's Cargo target directory is removed when it ends; its LLBC
   file and the output of Aeneas stay with the run directory.
2. The comparison of the extraction with the case: whether it is complete,
   with a complete translation expected for `translated` and `ill-typed`
   and a rejection for `rejected`, and the sets of diagnostics, external
   functions, external types and, when the case records them, loops. Each
   item that is missing or extra is a difference, so a shape that starts to
   translate after a tool change is one too.
3. For a case that expects a translation and whose extraction is complete,
   the stage `stage/`: the project files of `verification/` of the export,
   the Lean files that Aeneas wrote, with the templates of external items
   renamed to `FunsExternal.lean` and `TypesExternal.lean`, and two links
   below `artifacts/formal/lake` to the Aeneas Lean library of the
   installation and to its packages, which are read in place and never
   copied. A case with `models` gets its reviewed declarations in place of
   the templates, and the definitions of
   `verification/Krepi/Qualification/Models/`. A reviewed file may declare
   with `axiom`, after any attributes and modifiers such as `public`, only
   what its template declares, and may not use `sorry`; otherwise it is not
   installed, which is a difference. A case with parts
   gets the module `KrepiGen.<module>.Check`, written by the gate, which
   imports the `Funs` module of each part.
4. The build of the stage with
   `lake build --no-cache --wfail KrepiGen.<module>.Funs`, or the `Check`
   module of a case with parts, at the call site of the qualification
   builds, or of the ill-typed builds for an ill-typed case. A translated
   case must build. An ill-typed case must exit with 1 with at least one
   error in the files directly in its directory of generated modules, every
   one of them in the file that it records, and every `error:` and
   `warning:` line of the log must name that file, apart from Lake's closing
   lines; a build that passes, or an error elsewhere, is a difference.
   Nothing of a case that expects a rejection is built, and when the
   extraction of a case that expects a translation is not complete, the
   build is `NOT_RUN`.
5. For a case with `proof`, when its generated code built: the build of the
   proof module, copied from the export, with
   `lake build --no-cache --wfail`, and its audit, a file `Audit.lean` that
   is not a module, imports the proof module and has one `#print axioms`
   line for each theorem, checked with `lake env lean Audit.lean` at the
   call site of the case audits. Otherwise both are `NOT_RUN`.

A case is `VERIFIED` without a difference and `REJECTED` with its
differences. A theorem is `REJECTED` when its case is not as expected, its
case did not build its generated code, its proof does not build, the audit
does not report it, reports a theorem that was not requested or exits with a
status other than 0, or the theorem depends on an axiom other than
`propext`, `Classical.choice`, `Quot.sound` and the axioms that the
templates of its own case declare; each extraction owns its external
declarations, so a case's theorems are audited in its own Lean environment.
Otherwise it is `VERIFIED`. The build and the audit of a proof are commands
of its case, so a tool failure among the commands of a case decides the
case and each of its theorems. A stage or a file of the run that cannot be
created or written is an internal error, which stops the phase; the cases
after it are then `NOT_RUN`.

The proofs `Krepi.Qualification.Arithmetic`, `Checked` and `SingleLoop` are
module files that import the generated definitions of their case. The
reviewed external declarations of the cases `str_from`, `match-machine-arc`
and `term-layout-cut` in `verification/externals/Qual/` use definitions in
`verification/Krepi/Qualification/Models/`, namespace
`Krepi.Qualification.Models`: the structure `alloc.sync.Arc` with `clone`
and `deref`, and the decoding of a `&str` into a `String`. They are written
from the types that those declarations need and from the documentation of
the Rust standard library, declare no axiom, and serve only the type
checking of these cases: they are not [models](#models), are not
registered in `models.json`, are not compared with the standard library,
and enter neither a proof target nor the [trusted boundary](#trusted-boundary).

An expectation records what the pinned tools give. When a tool change
changes the conclusion of a case, its new expectation is explained case by
case, with an independent review of the explanations, before the case is
changed. The cases taken from the CAS project still record what its
earlier Charon and Aeneas gave; those that the pinned tools change are
rejected until that review.

### Base round

The base round, in `base.rs`, builds, audits and replays the hand-written
Lean of the snapshot with the generated modules of the proof cases of the
qualification. Every run has it after the qualification, a run of named
targets as well, with a budget of 3,600 s. Its units are `base` and
`base/<theorem>` for each statement that `statements.json` registers as
proved; the phase reads that file from the checkout at the start of the
run, to register its units, and stops when the export's file is not the
same. A planned statement has no unit. Other theorems that the audit
lists, such as the qualification theorems and unregistered ones, are
judged within `base`.

The round reads `statements.json`, `axioms.json` and `tcb.json` of the
export; a file that cannot be read, or does not follow its schema, stops
the phase. Then it

1. computes the statement hash of the snapshot commit
   ([statements and proofs](#statements-and-proofs)) and rejects the round
   when `statements.json` records another;
2. lists the `.lean` files below `verification/` of the snapshot commit with
   `git ls-tree`, and rejects the round for a symbolic link, for a file
   below neither `verification/Krepi/` nor `verification/externals/`, such
   as `verification/Krepi.lean`, for a file whose path does not name a
   Lean module, and for a file that breaks a
   [source rule](#source-rules);
3. creates the stage `work/base/stage/` as the qualification creates the
   stage of a case: the project files of the export, its module files below
   `verification/Krepi/` whose paths name modules, so that no file that
   step 2 rejects for its form reaches the root, the two links to the
   installation, and, for each
   qualification case with a proof whose generated code built, the
   generated modules as the case installed them, the reviewed external
   declarations of a case with `models` among them. When the generated code
   of such a case did not build, nothing is built, audited or replayed:
   `base` and each of its theorems are concluded from the commands of the
   case, so that a tool failure there forces them, and they are `REJECTED`
   otherwise;
4. writes the root module `Krepi`, a module file with a `public import` of
   each module below `Krepi` and `KrepiGen` in the stage, sorted, so that a
   module that nothing imports is built, audited and replayed as well. The
   library `KrepiRoot` of `lakefile.toml` builds it as `+Krepi`; the
   library `Krepi` takes only the modules below the root, so that a stage
   without the root, such as that of a qualification case, still builds by
   default. The round rejects a planned statement whose module has no file.

No problem of these steps stops the commands, so that the audit and
`leanchecker` judge what they find themselves. The commands run in the
stage's `verification/`, in this order:

| Command | Call site | Cap |
| --- | --- | --- |
| `lake build --no-cache --wfail +Krepi`; with planned statements, `+M` for each module that is neither the root nor the module of a planned statement | Base build | 7,200 s |
| With planned statements, `lake build --no-cache +Krepi` | Base build | 7,200 s |
| `lake env lean Audit.lean` | Axiom audit | 1,800 s |
| `lake env leanchecker Krepi`, then `lake env leanchecker KrepiGen` | `leanchecker` | None |
| `lean --version` | `leanchecker` | None |
| `lake env lean --json .heartbeats/<file>`, for each own file with theorems | Axiom audit | 1,800 s |

After a command that was a tool failure or met a budget, no later command
starts. The audit and `leanchecker` start only after the builds passed; a
proof failure of the audit does not stop `leanchecker`, whose result does
not depend on it.

**Builds.** The statement side and the proof files without planned
theorems build with `--wfail`, so that any warning fails the build,
``declaration uses `sorry` `` included, also when Lake replays it from a
dependency: a proved file that imports a planned file fails. The second
build, of the root without `--wfail`, adds the planned modules, and each
line of its log that starts with `warning: ` or `error: ` must be the
warning ``declaration uses `sorry` `` in the file of a planned module; any
other rejects the round. krepi's own modules are every module below `Krepi` but
the root, and the reviewed external declarations installed for
qualification cases, `KrepiGen.<module>.FunsExternal` and
`TypesExternal`. A failed build is a proof failure when its log has an
error or a warning whose line names the file of an own module, and a tool
failure otherwise ([results](#results)).

**Audit.** `Audit.lean` is not a module. It imports the root, sets
`pp.privateNames`, states `example : S := t` for the theorem `t` of each
proved statement `S`, and runs a program that, for each own module, prints
a marker, runs `#print axioms` on each theorem constant of the module that
is not private, not an internal detail and not the theorem of a planned
statement, prints the module that declares each of its native-decision
axioms, and prints the line at which each theorem's declaration range
starts; it then prints, for each proved statement, the module that defines
`S` and whether the type of `t` in the environment is the constant `S`
itself. The `example` alone would not show that: elaborating `t` against
`S` may insert a coercion, apply an instance or fill an argument that the
proofs declare.
The list of theorems is Lean's, so it holds the theorems that Lean
generates, such as `injEq` and `congr_eq` lemmas, and theorems that a
metaprogram adds. The round rejects

- an axiom of a theorem that the allowlist does not allow for its kind;
- a registered proved theorem that the audit does not report in its
  registered module, or whose type is not the statement constant itself,
  without arguments, whether or not its `example` checks;
- a statement that is not defined in an own module outside `Krepi.Proofs`;
- an own module without its marker, and an error at another line of the
  audit file.

The allowlist is one table of data in `lean.rs`, by the kind of the
theorem's module. Besides `propext`, `Classical.choice` and `Quot.sound`,
it allows:

| Kind | Modules | Also allowed |
| --- | --- | --- |
| Specification | Own modules below `Krepi` outside `Krepi.Proofs` that are not the proof module of a qualification case | Nothing |
| Qualification | The proof module of a qualification case, and the reviewed external declarations installed for the case | The axioms that the case's generated files declare |
| Target | Modules below `Krepi.Proofs` | The names in `axioms.json`; the axioms of the native decisions of a declaration that a `native-decision` item of `tcb.json` names, declared in the module of the item's `file`; and an axiom that a generated or reviewed external file of the stage declares and whose name starts with the `prefix` of an `axiom-pattern` item, in whole components |

`sorryAx` is in no row. The case audits of the qualification use the same
table with the qualification kind. The `unconstrained` and `opaque`
declarations of a target come with targets. Lean 4.35.0 gives each native
decision an axiom of its own, `<declaration>._native.<tactic>.ax_<i>_<j>`,
where the tactic is `native_decide`, `decide` or `bv_decide`, with
`_private.<module>.0.` before it in a module file. A name with a component
`_native` is such an axiom: only a `native-decision` item allows it, for a
target theorem, and `axioms.json` refuses such names. Any module could
declare an axiom of such a name without the kernel, so the item allows it
only when the audit finds it declared in the module of the item's `file`.
Changes of `tcb.json` itself are not guarded yet: the rules of the guard
for the registries are planned.

`verification/axioms.json` has schema 1 and a list `axioms`, each with
`name`, `source`, the module of the Aeneas Lean library that declares the
axiom, and `reason`. `verification/tcb.json` has schema 1 and a list
`items`, each with the `kind` `native-decision`, with `file`, a tracked
hand-written file, `declaration` and `reason`, or `axiom-pattern`, with
`prefix` and `reason`. Other kinds are refused until the trusted base is
classified, and unknown fields are refused in both files.

**Replay.** `leanchecker` checks again in the kernel every declaration of
the modules that its prefix selects: `Krepi` selects the root and every
module below it, `KrepiGen` the generated ones, by whole name components.
The stage's build directory is new in every run, so that no earlier output
is replayed. An exit with 0 passes. Another exit is a proof failure, which
rejects the round with the lines that name the module and the declaration,
when the output has the line `leanchecker found a problem in <module>` and
a kernel message about something other than a deterministic timeout,
excessive memory, deep recursion or an interruption; otherwise, such as
when `leanchecker` finds no built modules, it is a tool failure.
`leanchecker` has no version option. The receipt records the output of
`lean --version`, which must exit with 0 and print a line that starts with
`Lean (version `, else it is a tool failure, and the SHA-256 of the
`leanchecker` of the installation, which `lake env` finds first on `PATH`.
That program loads the kernel from the Lean shared library, so the
checker is identified by the download digest of the Lean archive in the
tool manifest and, in CI, by the digest of the image.

**Heartbeats.** Only theorems with a declaration range are counted. For
each own file with such theorems, the round writes a copy below
`.heartbeats/` with Mathlib's `#count_heartbeats in` inserted before each
of them, at the line at which its declaration range starts when a
declaration command starts there, and reads the counts that
`lake env lean --json` prints for the copy. A theorem whose range starts
inside another command, such as a `where` clause, has no count, nor have
the theorems of a file whose command ends by itself with a status other
than 0; the receipt records why. A theorem without a declaration range,
such as one that Lean generates for a structure or a `match`, has no count
and no such record. `#count_heartbeats` is Mathlib's, so a file that
imports neither Mathlib nor the Aeneas Lean library, which imports it,
gets no counts either. A count is that of elaborating the declaration
synchronously without a limit. In every measurement it was above the
smallest `maxHeartbeats` with which the declaration elaborates with
`Elab.async` off: on the qualification proofs by at most 2 % of that limit
plus 50, and on a small `ring` proof of the test fixtures by 59 over a
limit of 313. Counts decide nothing, but a heartbeat command that is a
tool failure or meets a budget forces `base` as any command of a unit
does.

**Installation.** The qualification and the base round list the Aeneas
Lean library of the installation, with its packages, and the Lean
toolchain, at their start and at their end, without following symbolic
links below them: the path, mode, size, modification and change times and
link target of each entry. Any difference stops the phase as a tool
failure that names up to 20 paths, so that a tool that writes to the
installation is a tool failure of the run. In the image, the installation
belongs to root and has no write permission.

**Conclusions.** `base` is `VERIFIED` when the round has no problem and no
command forced it, and `REJECTED` with its problems otherwise: the
statement hash, the file and source rules, the modules of planned
statements, a build that failed with messages in own modules, messages of
the planned build other than the `sorry` warning, the axioms of
unregistered theorems, missing markers, errors in the audit file and the
kernel reports of `leanchecker`. Each `base/<theorem>` is `REJECTED` with
its own problems, and when the build failed or `leanchecker` reported a
declaration that the kernel rejects, and `VERIFIED` otherwise; the other
audited theorems get their status in the receipt the same way. A tool
failure among the round's commands forces `base` and each of its
theorems.

### Source rules

The `lean` step of `cargo xtask check` reads each tracked `.lean` file
below `verification/`, which must be a UTF-8 regular file, and
`verification/tcb.json`, and the base round each such file of the
snapshot, with the same rules. They read Lean's tokens: comments, string
literals, raw string literals and character literals are skipped, but the
`{}` parts of a string are read as code, as an interpolated string reads
them, and a string that ends elsewhere when it is read as an interpolated
string than when it is read as a plain one breaks a rule:

- the file lies below `verification/Krepi/` or `verification/externals/`
  and is a module file: its header starts with `module`;
- `native_decide`, `bv_decide`, and the name `native`, which `decide`
  takes as an option, such as in `decide +native` or
  `decide (native := true)`, appear only in a file that a
  `native-decision` item of `verification/tcb.json` names;
- `axiom` appears only below `verification/externals/`;
- a file of the statement side imports neither the root module `Krepi` nor
  a module below `Krepi.Proofs`
  ([statements and proofs](#statements-and-proofs)).

The rules are a lexical check, made before any build. They do not read
generated files, which exist only in stages, and do not expand tactics or
run metaprograms: a tactic that wraps a native decision, such as Aeneas's
`bv_tac`, passes them, and so does an axiom that a metaprogram adds with
`addDecl`. The audit is the check of the axioms: it rejects the axiom of
such a decision and any other axiom that no row allows. The Aeneas Lean
library itself declares the native-decision axioms of some of its lemmas,
among them those behind `bv_tac`; no registry admits them yet, so a target
theorem that depends on them fails the audit.

### Guard

`cargo xtask formal guard --event PATH`, in `guard.rs`, checks a pull
request against the rules for changes of statements, proofs and sources.
`PATH` is the JSON of a `pull_request` event as GitHub writes it, the file
of `GITHUB_EVENT_PATH`; the guard reads `pull_request.base.sha`,
`pull_request.head.sha`, the names of `pull_request.labels`, and
`pull_request.body`, which may be absent or `null`, and fails on an event
without the two commits and the labels. It runs Git itself in the
repository root, with literal pathspecs and without optional locks, in an
environment of the caller's `PATH` alone with `GIT_CONFIG_NOSYSTEM=1` and
`GIT_CONFIG_GLOBAL=/dev/null`, so that variables such as `GIT_DIR` and
`GIT_INDEX_FILE` and the caller's configuration cannot change what it
reads. The repository must hold both commits and their history. The
command prints `PASSED <rule>` or `FAILED <rule>: <why>` for each rule,
the labels and the statement hash of the head, and exits with 0 when every
rule holds and with 1 when a rule fails or an input cannot be read.
Computing the statement hash writes tree objects into the repository,
through a directory below `artifacts/formal/guard/` that the command
removes.

From Git alone, the guard finds

- the merge base of the two commits, and the paths that changed from it to
  the head, with `git diff --name-status --no-renames`, so that a renamed
  file counts at its old and at its new path;
- among those paths, the statement side, the proof files, which are the
  `.lean` files below `verification/Krepi/Proofs/`, and the sources, which
  are the `.rs` files below `kernel/` and `user/`, `build.rs` included;
- the statements no longer proved: each `name` that `statements.json`
  registers as proved at the merge base and not at the head, because the
  statement became planned, was removed or was renamed;
- the new raised heartbeat limits: in each changed file of the statement
  side or proof file, each text `maxHeartbeats` with the value after it,
  across white space, line breaks, quotes, `»` and `=`, unless the value is
  a number from 1 to Lean's default of 200000, or of 20000 when a namespace
  such as `synthInstance.` comes before the name. Lean takes the option's
  name in `«»` and its value after a line break or a comment, and a value
  of 0 or of another base removes or hides the limit, so any other value,
  a comment before it, or a mention without a value, counts as a raise.
  Each is keyed by its lines, with white space collapsed, and the next line
  that is not blank, and is new when the file at the merge base does not
  have its key. Moving a raise to another declaration is therefore a new
  raise, and lowering a limit is none. A new file of reviewed external
  declarations that keeps the line `set_option maxHeartbeats 1000000` of
  the Aeneas templates raises the limit: its reviewer gives a
  `Heartbeats-Review` or removes the line. A limit that a metaprogram sets
  without the text `maxHeartbeats` is outside this rule;
- the statement hash of the head.

The description of the pull request gives these fields, each on a line of
its own as `Name: value`, with spaces around the value allowed. A field
given twice, or with a value of another form, counts as missing. The ids
are opaque; the records that they name are kept outside this repository.

| Field | Value |
| --- | --- |
| `Review` | The id of the review of a statement change: 1 to 64 ASCII letters and digits |
| `Approval` | The id of the owner's approval of the change, in the same form |
| `Approved-Statement-Hash` | The statement hash that was approved, 40 lowercase hexadecimal digits |
| `Heartbeats-Review` | The id of the review of a raised heartbeat limit, in the same form as `Review` |

The labels are `spec` for a change of statements, `proof` for a change of
proofs, and `ai-proof` for a pull request with proofs that an AI system
wrote, which the guard records and never judges. Other labels are recorded
and ignored. The rules are rows of one table, to which later checks add
theirs:

| Rule | Fails when |
| --- | --- |
| `statement-change-needs-spec` | A path of the statement side changed, or a statement is no longer proved, and the label `spec` is missing |
| `spec-approval` | The label `spec` is present and `Review`, `Approval` or `Approved-Statement-Hash` is missing, or the approved hash is not the statement hash of the head |
| `no-sources-with-proofs-or-statements` | A source changed together with the label `proof`, a changed proof file or a changed path of the statement side |
| `heartbeats-need-review` | A heartbeat limit is newly raised and `Heartbeats-Review` is missing |

On a pull request, when `GITHUB_EVENT_NAME` is `pull_request` and
`GITHUB_EVENT_PATH` names the event, `cargo xtask formal run` runs the same
check through the gate's Git in a first phase, `guard`, with a budget of
300 s, and records what it found in the receipt. The phase has no unit: a
failing rule does not change the status of the run, which is about the
proofs, and the standalone command decides. An event that cannot be read,
or a failed Git command, stops the run as an internal error. Without a
pull request event the run has no guard phase.

### Results

Every command gets one class from one function, `outcome::classify`, which
every call site uses: `PASSED`, `PROOF_FAILURE`, `TOOL_FAILURE` or
`NOT_RUN`, and `BUDGET`, a tool failure at the limit of a phase or of the
gate rather than at the cap of the call site. A tool failure is never a
statement about the code. The conventions:

| Result of the command | Call sites | Class |
| --- | --- | --- |
| Ran until its cap | All | `TOOL_FAILURE` |
| Ran until the rest of a budget | All | `BUDGET` |
| Ended by a signal | All | `TOOL_FAILURE` |
| Exited with a status above 128 | All | `TOOL_FAILURE` |
| `lake build` prints `error: Lean exited with code N` with `N` above 128 | The three builds | `TOOL_FAILURE` |
| Charon exits with 255 | Charon | `TOOL_FAILURE` |
| Cargo reports a process ended by a signal, as in `(signal: 9, SIGKILL: kill)` | Charon | `TOOL_FAILURE` |
| Could not start or could not keep its output | All | `TOOL_FAILURE` |
| Ended by itself, and an output file that the gate reads, `translation.json` or a generated Lean file, cannot be read or is not what the tool writes, or `translation.json` is missing after an exit with 0 | Aeneas | `TOOL_FAILURE` |
| The base build fails with errors in krepi's own modules | The base build | `PROOF_FAILURE` |
| The base build fails with warnings only in krepi's own modules | The base build | `PROOF_FAILURE` |
| The base build fails without an error or a warning in krepi's own modules | The base build | `TOOL_FAILURE` |
| The comparator exits with 1 and prints a line that starts with `error: Child exited with ` | The comparator | `TOOL_FAILURE` |
| The comparator exits with 1 otherwise | The comparator | `PROOF_FAILURE` |

A process of the group that survives the kill is a tool failure as well, and
so is any failure of Git or `cargo metadata`, which the gate runs itself,
and any status of the comparator but 0 and 1. Any other non-zero status of
a tool is a `PROOF_FAILURE`, which its call site compares with what it
expects. The call sites are Charon and Aeneas, the qualification builds,
the ill-typed builds and the case audits of the qualification, the base
build, the axiom audit and `leanchecker` of the [base round](#base-round),
and, planned, the comparator.

krepi's own modules, in the rows of the base build, are every module below
`Krepi` but the root module, and the reviewed external declarations
installed for qualification cases. A message counts for them when its
`error:` or `warning:` line names the file of one of them; a message in a
generated file, Lake's own `error: build failed`, a `trace:` line and a
message without a position do not. The base round also reads what
`leanchecker` and `lean --version` print before they are classified: a
`leanchecker` that exits with a status other than 0 without reporting a
kernel problem in a module, and a `lean --version` that does not exit with
0 and print the version, are tool failures, never proof failures. A
heartbeat command that ends by itself with another status is a proof
failure by these conventions, but it decides nothing about the round.

A command that does not start because the command before it did not write
what it needs, such as Aeneas after a Charon that failed, is `NOT_RUN`
with the reason `not started:` and the limit that it would have had. It
decides nothing: the command before it does. When the limit is used up as
well, it is `NOT_RUN` for the budget, as any command whose limit is used
up.

A unit is a registered piece of work that gets exactly one conclusion: a
qualification case, an audited theorem, the base round. A phase is a part
of the pipeline with a budget of its own, such as the qualification. A unit
with a command that was a tool failure is concluded `TOOL_FAILURE`, and one
with a command that met a budget, or did not start because its limit was
used up, `BUDGET`, whatever its phase concludes.

The status of a run is the first of these that applies: `TOOL_FAILURE`,
`BUDGET`, `STALE`, `REJECTED`, from its failures and the conclusions of its
units; `TOOL_FAILURE` when a unit was `NOT_RUN` without another failure;
`SCOPED` for a run of named targets; and `VERIFIED`. The run is a tool
failure, and not complete, after an internal error, such as a host other
than `linux-aarch64` or `darwin-arm64`, a tool manifest or a target
registry that cannot be read, a tool manifest that is not the snapshot's,
a failed Git command, a failed export, a phase that returns an error or
panics, or a panic of the run itself. After an error of the export or of
its checks, or of a phase, the closing steps still run; an error of the
start ends the run without the second snapshot, and a panic of the run
outside a phase ends it without any later command. The receipt is written in every case. It
is a tool failure as well when the gate inputs are not clean at the start,
when a name given with `--target` is not in `verification/targets.json`,
and when a registered unit has no conclusion or more than one, or a
conclusion is given for a unit that is not registered. After any failure
before the phases, no phase runs, and after a phase stops no later phase
runs; every registered unit without a conclusion is then `NOT_RUN`. A run
of named targets is `SCOPED` and is never complete. A run of the whole
gate is complete when its only failures are `STALE` and no unit is
`NOT_RUN` or `BUDGET`.

The command exits with 0 for `VERIFIED` and `SCOPED` and 1 for any other
status, and prints each failure on standard error. It exits with 2 on a
usage error, and by the signal after a stop signal, without a receipt in
both cases. When the run directory or the receipt cannot be written, it
writes the receipt to standard error and exits with 120.

### Receipt

`receipt.json` has schema 1. It is the pretty form of `serde_json`, with
the fields in the order of the tables below and every map sorted by its
keys; times are seconds, rounded to milliseconds.

| Field | Content |
| --- | --- |
| `schema` | `1` |
| `command` | `cargo xtask formal run` |
| `status` | `VERIFIED`, `REJECTED`, `STALE`, `TOOL_FAILURE`, `BUDGET` or `SCOPED` |
| `complete` | Whether the run is complete, as defined above |
| `trigger` | `mode`, `MANUAL` for a run of the whole gate and `SCOPED` for a run of named targets, with `REQUIRED`, `FORCED_FULL` and `WEEKLY` kept for the jobs of CI; `event`, `ref`, `run_id` and `attempt`, from `GITHUB_EVENT_NAME`, `GITHUB_REF`, `GITHUB_RUN_ID` and `GITHUB_RUN_ATTEMPT`, or `null` |
| `targets` | The names given with `--target`, sorted; empty for a run of the whole gate |
| `host` | `linux-aarch64` or `darwin-arm64`, or `null` on another host |
| `run`, `directory` | The identifier of the run, and its directory relative to the repository root |
| `started`, `seconds` | The Unix time in seconds at which the run started, and how long it took |
| `commit`, `tree` | The snapshot commit and its root tree, or `null` |
| `inputs` | `before` and `after`, the object of each gate input (`mode`, `type`, `oid`, or `null` when the commit does not have it) at the start and at the end, or `null` when they were not taken; `clean_after`, whether the gate inputs were clean at the end, or `null` |
| `budgets` | `gate_seconds`, 7200, and `receipt_margin_seconds`, 300 |
| `phases` | For each phase, `budget_seconds`, `seconds` and `ran` |
| `units` | For each unit, its `phase`, its `status` and the `reason` for it, or `null` |
| `qualification` | What the qualification found, below, or `null` when it did not start |
| `base` | What the base round found, below, or `null` when the round stopped before it recorded it |
| `guard` | What the guard found on a pull request, below, or `null` without a pull request event or when its phase did not finish |
| `commands` | Every command, in the order in which they ran |
| `failures` | Every failure that is not the conclusion of a unit, with its `status` and `message` |

Each command has these fields:

| Field | Content |
| --- | --- |
| `sequence` | The number of the command in the run, from 1 |
| `phase`, `unit` | The phase and the unit of the command, or `null` for the commands of the gate itself |
| `site` | `charon`, `aeneas`, `qualification-build`, `ill-typed-build`, `case-audit`, `base-build`, `axiom-audit`, `leanchecker`, `comparator`, `git` or `cargo-metadata` |
| `argv` | The program and its arguments |
| `cwd` | The working directory, relative to the repository root |
| `class`, `reason` | The class of the result, and the reason for any class but `PASSED`, or `null` |
| `exit_code`, `signal`, `timed_out` | The exit status or the signal that ended the command, each `null` otherwise, and whether it ran until its limit |
| `limit_seconds`, `limit` | The limit of the command, and what set it: `cap`, `phase` or `gate` |
| `seconds` | How long the command ran |
| `group_survived` | Whether processes of its group were still there after the kill |
| `stdout`, `stderr` | `path` relative to the run directory, `bytes` and `sha256` of each output file, or `null` for a command that did not start |

The `qualification` record has `cases_sha256` and `extraction_sha256`, the
SHA-256 of `verification/qualification/cases.json` and
`verification/extraction.toml` of the export, and these maps, which hold
what the phase reached before it ended or stopped:

| Field | Content |
| --- | --- |
| `cases` | For each case: `unit`, `module`, `parts`, `expect` and `models` as `cases.json` gives them; `observed`, what the extraction gave (`complete`, `diagnostics`, `external_functions`, `external_types`, `loop_sources`); `type_errors`, for an ill-typed case whose generated code was built, the recorded `file` and the number of type errors in the case's files (`errors`) and in that file (`in_file`), or `null`; `differences`; `generated`, the SHA-256 of each Lean file that Aeneas wrote, by its path below the output of Aeneas; and `declarations`, the axioms of the templates of a case with a proof |
| `theorems` | For each theorem: its `case`, its `unit`, and the `axioms` that the audit reported for it, or `null` |

The `base` record has these fields:

| Field | Content |
| --- | --- |
| `statements_sha256`, `axioms_sha256`, `tcb_sha256` | The SHA-256 of `verification/statements.json`, `verification/axioms.json` and `verification/tcb.json` of the export |
| `statement_hash` | `recorded`, the hash that `statements.json` records, and `computed`, the statement hash of the snapshot commit |
| `modules` | The modules that the root module imports |
| `own` | krepi's own modules, whose messages decide a failed build |
| `planned` | The modules of planned statements, built without `--wfail` |
| `theorems` | For each theorem that the audit reported or `statements.json` registers: its `module`; its `kind`, `specification`, `qualification` or `target`; its `state` in `statements.json`, `proved` or `planned`, or `null` for a theorem that is not registered; the `axioms` that the audit reported, or `null`; its `status`; and its `problems`. The status of a registered proved theorem is that of its unit, that of a planned one `NOT_RUN`, and that of any other `VERIFIED` without problems, `REJECTED` with them, or the status that forced `base` |
| `leanchecker` | `version`, the version line of `lean --version`, or `null`; `sha256`, of the `leanchecker` program; `mode`, `prefix`; and `prefixes`, `Krepi` and `KrepiGen` |
| `heartbeats` | `method`, `count_heartbeats`; `counts`, the heartbeats of each theorem with a declaration range; and `missing`, why such a theorem, by its name, or a file, by its path, has none |
| `problems` | The problems that reject `base` |

The `guard` record has these fields:

| Field | Content |
| --- | --- |
| `base`, `head` | The base and head commits of the pull request |
| `merge_base` | Their merge base |
| `labels` | The labels of the pull request, sorted |
| `ai_proof` | Whether it has the label `ai-proof` |
| `statement_hash` | The statement hash of the head |
| `statement_side`, `proofs`, `sources` | The paths of the statement side, the proof files and the sources that changed since the merge base |
| `demoted` | The statements proved at the merge base and not at the head |
| `raised` | The files with a new raised heartbeat limit |
| `rules` | Each rule, with why it fails, or `null` when it holds |

Fields are only added to schema 1 while the gate's phases are added, until
CI keeps receipts; after that, any change of a field takes a new schema.
Receipts come from two hosts. CI is to run the gate on `linux-aarch64` in
the image, as a user that cannot write to its read-only installation (the
job is planned). Local runs on `darwin-arm64`, with the installation at
`artifacts/formal/tools`, serve development; there the gate only detects
writes to the installation. Only receipts of CI runs are evidence.

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
`#print axioms`. The axioms that its theorems may use are those of the
target row of the allowlist of the [base round](#base-round): Lean's
`propext`, `Classical.choice` and `Quot.sound`, the library axioms of
`verification/axioms.json`, the items of `verification/tcb.json`, and the
target's unconstrained and opaque declarations.
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

## Statements and proofs

A statement is a proposition on the statement side, and a theorem in a
proof file proves it. The statement side is the hand-written part of the
Lake project that decides what the statements mean:

- every tracked hand-written `.lean` file below `verification/` outside
  `verification/Krepi/Proofs/`: the specifications below `Krepi/Spec`, the
  statements below `Krepi/Statements`, the models, the qualification proofs
  with their definitions, and the reviewed external declarations below
  `externals/`;
- the registry of library axioms, `verification/axioms.json`;
- the Lake project files `verification/lakefile.*`, `lean-toolchain` and
  `lake-manifest.json`.

Generated modules and the root module exist only in the stages of a run.
`verification/tcb.json` is not on the statement side; changes of it are to
be reviewed through the registry rules of the [guard](#guard) (planned).
Nor are the pins of the tools: `verification/toolchain.json` and the patch
of the Aeneas Lean library in `verification/tooling/` also decide what the
definitions of that library mean, but a change of them changes no
statement hash and needs no label `spec`; such a change is checked by
`cargo xtask formal toolchain-check` and the image build ([tool
checks](#tool-checks)).

Statements, and the definitions that they use, are written as
`@[expose] public def`, such as `@[expose] public def S : Prop := ...` in a
module below `Krepi.Statements`, and the theorem that proves a statement as
`public theorem t : S` in a module below `Krepi.Proofs`, whose proof body
is private to the module. Every hand-written file is a module file. A
minimal example on Lean 4.35.0 showed that

- the statement and the theorem build with `lake build --wfail`, and the
  audit reports the axioms of the proof;
- the Git tree of the statement side stays the same when only a proof
  changes, and changes with a definition that a statement uses, also when
  the file of the statement itself does not change;
- Lean rejects only cyclic imports, so a statement-side file that imports a
  proof builds, and the import rule below is needed to reject it.

A statement file is not itself the challenge that the comparator checks:
the comparator needs each of its theorem names to be a theorem of the
challenge, and the statement file has only the definition `S`. The gate is
to generate the challenge from `statements.json` (planned): a module that
imports the statement side and states `public theorem t : S := sorry` for
each proved statement.

**Statement hash.** The statement hash of a commit is the Git tree object
that holds exactly the commit's paths of the statement side, at their
repository paths. `verification/statements.json` records it, and it is not
on the statement side itself. With Git alone, in a checkout of the commit,
these commands print it, through an index of their own in a subshell, so
that later Git commands of the shell use the repository's index again:

```sh
(
  export GIT_INDEX_FILE="$(mktemp -d)/index"
  git read-tree HEAD
  git rm -r --cached --quiet -- . \
    ':(exclude,glob)verification/**/*.lean' \
    ':(exclude)verification/axioms.json' \
    ':(exclude,glob)verification/lakefile.*' \
    ':(exclude)verification/lean-toolchain' \
    ':(exclude)verification/lake-manifest.json'
  git rm -r --cached --quiet --ignore-unmatch -- verification/Krepi/Proofs
  git write-tree
)
```

The gate writes the same tree with `git ls-tree` and one `git mktree` for
each directory with files of the statement side, from the deepest up. Like
`git write-tree`, this writes tree objects into the repository, and no
reference or index. A change of the statement side therefore changes the
hash: the base round rejects a snapshot whose `statements.json` records
another, and the guard requires the label `spec` and an approval of the new
hash.

**Import rule.** A file of the statement side imports neither the root
module `Krepi` nor a module equal to or below `Krepi.Proofs`. Its header
is read as Lean 4.35.0 reads it: after white space, line comments and
nested block comments, an optional `module`, an optional `prelude`, and
then imports of the form `[public] [meta] import [all] <name>`, each of
one name, whose components may be written as `«...»`. A doc comment or any
other token ends the header, so an import in a comment is no import.

**`statements.json`**, schema 1:

| Field | Content |
| --- | --- |
| `schema` | `1` |
| `hash` | The statement hash, 40 lowercase hexadecimal digits |
| `statements` | Each statement: `name`, the proposition on the statement side, which identifies the statement; `theorem`, the theorem that proves it; `module`, the module below `Krepi.Proofs` that holds the theorem; and `state`, `planned` or `proved` |

Names are Lean names of ASCII components. Each `name` and each `theorem`
appears once, and `name` lies outside `Krepi.Proofs`; unknown fields are
refused. A planned statement is merged with its proof pending: its module
builds without `--wfail` and may warn only ``declaration uses `sorry` ``,
its theorem is not audited, and the comparator is to get no challenge for
it. A proof pull request changes a statement from planned to proved, or
moves its proof to another theorem or module; a statement that becomes
planned again, is removed or is renamed is a statement change
([guard](#guard)).

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
model, not a proof; the modelled source remains an assumption. The
definitions in `verification/Krepi/Qualification/Models/` are not models:
they serve only the type checking of three qualification cases
([qualification](#qualification)).

## Trusted boundary

| Item | Role | How it is checked |
| --- | --- | --- |
| Lean kernel and the three standard axioms | Checks every proof | Axiom audit of every registered theorem |
| Mathlib and the Aeneas Lean library | Mathematical definitions and models of integers, slices, `Option`, `Result` and other core items | Pinned Lake lock; library axioms appear in the audit and must be registered in `verification/axioms.json` |
| Charon, the Rust nightly and Aeneas with reviewed patches | Translation of the production source into Lean | Pinned sources and binaries; qualification regression; mutants |
| Unconstrained declarations | External functions and types without a model | Theorems hold for every interpretation; listed per target |
| Trusted axioms | Reviewed exceptions | Items of `verification/tcb.json`, each with a reason |
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
`cases.json`. Every run of the gate extracts them again
([qualification](#qualification)), so a tool change that alters a
translation fails before it reaches a target. Besides the shapes taken from
the CAS project, cases record a body chosen by `cfg` (`cfg-shape`), a const
generic parameter (`const-generic`) and each construct R1 to R7 of the
provable subset (`r1-function-item-value` to `r7-private-enum`), with what
the pinned tools give them. Some constructs that
the prototype used, such as `Iterator::any` and `flatten`, do not translate
into code that a proof can rely on; the
[provable Rust subset](conventions/provable-subset.md) lists them with the
other constructs that stop extraction or proofs, and the forms to write
instead, for the modules that proofs are to cover.

## Legacy inventory and admission

`verification/legacy.json` is empty by design and stays so: no production
function is admitted without a proof as a legacy function. Production
functions without a proof are to be listed in `verification/open.json`
(planned), which is generated from the OPEN tables of the `contract.md` of
the components, each entry with the later task or stage that takes it over;
an `unsafe` entry also says whether it reads or writes verified state.
`cargo xtask formal check` (planned) fails on a production function that is
in no target's `proves` or `unclosed` list and not in `open.json`, and on
an `open.json` that differs from what the contracts give. The removal of a
target, a theorem or a proved function, and any widening of the trusted
base, are reviewed through the registry rules of the [guard](#guard)
(planned), and `cargo xtask formal impact --base REV` (planned) lists the
targets that a change affects. A function without a proof is never trusted
by a proof and appears in a target's `unclosed` list when reached.

## Editing proofs

A run keeps its directory. A proof is edited in the stage of the base round
of a run, `artifacts/formal/runs/<id>/work/base/stage/verification`, or in
the stage of a qualification case, with the Lean 4 extension: a stage holds
the generated modules and the links to the installation that a checkout
lacks, and a change is then copied back to the checkout. Builds there and
in a checkout are not evidence; only a run of the gate produces receipts.

## Limitations

- No specification, statement or target is registered; the whole kernel is
  unverified, and the base round checks only the qualification proofs and
  the definitions that they use.
- Proofs cover only registered targets. Code outside them, including code
  ported from the legacy tree, is unverified until a target proves it.
- Sequential refinement does not cover concurrency, weak memory, `unsafe`
  code, assembly, the compiler or the hardware.
- A proof says nothing about time, memory use or the compiled binary unless a
  registered obligation states it.
- The audit program runs in the Lean environment of the code that it
  audits, so a krepi module could in principle change what `#print axioms`
  or the program reports; `leanchecker` replays the declarations, and the
  comparator (planned) is to check the axioms of the export independently.
