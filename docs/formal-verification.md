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
manifest against the Aeneas and Charon sources ([tools](#tools)).
`cargo xtask formal run` exists as the frame of the proof gate
([gate run](#gate-run)): it takes a snapshot of the gate inputs, exports
them, applies their rules and writes a receipt. Its pipeline has no phases
yet, with no extraction, qualification or Lean build, so its receipt
verifies nothing about the code. Everything else on this page is planned:
the Lake project, the `Krepi` Lean modules, the qualification crate, the
phases of the gate and the other commands of `cargo xtask formal`. They are
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
| `xtask/src/formal/` | The commands of `cargo xtask formal` | `toolchain-check` and `run` present, the others planned |

Generated Lean, extraction outputs, logs and receipts go to the ignored
`artifacts/formal/` directory, and the Lake build directory
`verification/.lake/` is ignored as well. Each run of the gate has a
directory `artifacts/formal/runs/<id>/`, where `<id>` is the Unix time of
its start, its process number and a count: `receipt.json`, `logs/` with
the two output files of each command, and `work/` with the export of the
gate inputs and the home and temporary directories of the tools.
Generated definitions are never edited.

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
| `CARGO_TARGET_DIR` | A directory of the run for this extraction alone | Charon and Aeneas, the extraction |

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

The commands of `cargo xtask formal` follow the CAS project.
`cargo xtask formal toolchain-check` and `cargo xtask formal run` exist; the
others are planned.

| Command | Purpose |
| --- | --- |
| `cargo xtask formal toolchain-check --aeneas DIR --charon DIR` | Checks Aeneas and Charon checkouts and the Aeneas patch against the tool manifest ([tool checks](#tool-checks)) |
| `cargo xtask formal qualify` (planned) | Tool qualification regression on the code shapes in `verification/qualification` |
| `cargo xtask formal run [--target NAME]...` | The proof gate on a snapshot of the gate inputs, with its receipt ([gate run](#gate-run)); `--target` runs only the named targets. Its phases, which are planned, are the qualification, the specifications and every target (or the named ones) with its mutants |
| `cargo xtask formal check` (planned) | Registry, legacy and inventory metadata only; runs no tool and proves nothing |
| `cargo xtask formal impact --base REV` (planned) | Classifies changed functions since `REV` and reports scope reductions |
| `cargo xtask formal inventory` (planned) | Lists every production function by inventory key |
| `cargo xtask formal editor` (planned) | Prepares `verification/` for interactive editing |

Once the gate checks the qualification and the specifications,
`cargo xtask check` runs it, and CI runs it on every change. A change merges
only when the required gate passes on its head or a committed waiver record
covers the failure.

## Gate run

`cargo xtask formal run` runs the gate on the commit checked out, the
snapshot commit, and writes a receipt of the run, whether it passes, fails
or stops on an internal error. Its code is in `xtask/src/formal/`: the gate
inputs in `paths.rs`, the commands in `process.rs`, their classes and the
statuses in `outcome.rs`, the receipt in `receipt.rs` and the run in
`run.rs`.

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
   ends in `.py` in any case;
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
system, and the configuration of its Cargo home. Before the run starts
Cargo in the export, it looks for both files in the export and in every
directory above it, with symbolic links resolved. Only the snapshot's own
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
beyond the gate's budget. A command whose limit is used up does not start
and is `NOT_RUN`. When a command reaches its limit, or ends by itself, the
run kills its process group, collects the command and waits up to 60 s,
beyond the command's limit, until no process of the group is left; a
process that is still there makes the command a tool failure. The run
restores the default disposition of `SIGCHLD` when it starts, without which
the system could collect an ended command before the kill. Each command is
printed when it ends.

A signal from the terminal does not reach a running tool, whose group is
its own. SIGINT and SIGTERM stop the run instead, also when they were
ignored when it started, and so does SIGHUP unless it was ignored then, as
`nohup` leaves it: the run kills the group of the command that is running,
collects the command, waits for its group as above, and ends by the same
signal, without a receipt. A signal that comes
between two commands takes effect before the next command starts or before
the receipt is written.

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
| The base build fails with errors in krepi's own modules | The base build | `PROOF_FAILURE` |
| The base build fails with warnings only in krepi's own modules | The base build | `PROOF_FAILURE` |
| The base build fails without an error or a warning in krepi's own modules | The base build | `TOOL_FAILURE` |
| The comparator exits with 1 and prints a line that starts with `error: Child exited with ` | The comparator | `TOOL_FAILURE` |
| The comparator exits with 1 otherwise | The comparator | `PROOF_FAILURE` |

A process of the group that survives the kill is a tool failure as well, and
so is any failure of Git or `cargo metadata`, which the gate runs itself,
and any status of the comparator but 0 and 1. Any other non-zero status of
a tool is a `PROOF_FAILURE`, which its call site compares with what it
expects. The call sites are the extraction, the qualification builds and
audits, the base build, the axiom audit, `leanchecker` and the comparator,
all planned.

A unit is a registered piece of work that gets exactly one conclusion: a
qualification case, an audited theorem, the base round. A phase is a part
of the pipeline with a budget of its own, such as the qualification. A unit
with a command that was a tool failure is concluded `TOOL_FAILURE`, and one
with a command that met a budget `BUDGET`, whatever its phase concludes.

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

Fields are only added to schema 1 while the gate's phases are added, until
CI keeps receipts; after that, any change of a field takes a new schema.
CI is to run the gate on `linux-aarch64` in the image, and local runs on
`darwin-arm64` serve development; only receipts of CI runs are evidence.

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
