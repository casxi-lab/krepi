# Formal verification

Selected kernel functions are to be proved correct in Lean 4. Charon extracts
the actual Rust source of the kernel, Aeneas translates the extraction into
Lean definitions, and handwritten Lean proofs show that those generated
definitions satisfy independently written specifications. The organization
follows the one used for the CAS project, adapted to an operating-system
kernel.

A proof covers exactly the functions and statements registered for it. Code
outside a registered target is unverified, and a theorem says nothing beyond
its statement: the items under [trusted boundary](#trusted-boundary) remain
assumptions, and a refinement proof of Rust code says nothing about timing,
the compiled binary or concurrent execution unless a separate layer proves it.

## Status

The registries `verification/targets.json`, `verification/models.json` and
`verification/legacy.json` exist, and so do the open obligations
`verification/open.json`, the statement registry
`verification/statements.json`, the registry of library axioms
`verification/axioms.json` and the registry of the trusted base
`verification/tcb.json`: no target, model, statement, library axiom or
trusted item is registered. The pinned tools exist: the tool manifest
`verification/toolchain.json`, the reviewed Aeneas patch, the recipe of the
image that holds the tools, the workflows that build and publish it, the
pin of the published image, `verification/image-pin.json`, and
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
`cargo xtask formal guard` runs on its own. `cargo xtask formal check`
holds the inventory of the production functions of the kernel workspace
against the targets and the open obligations
([legacy inventory and admission](#legacy-inventory-and-admission)), and
`cargo xtask formal vectors` compares a component's frozen test vectors
through its specification with the results of its host tests
([test vectors](#test-vectors)), though no contract names vectors yet. A
weekly toolchain canary runs the gate with the tools of Aeneas main through
the steps of `cargo xtask formal canary` and records what they would break
([toolchain canary](#toolchain-canary)). None of them verifies anything
about the kernel. The cases taken from the CAS project expect what the
pinned tools give; for 27 of them this differs from the expectation
recorded with the earlier Charon and Aeneas, and each such change is
explained ([qualification](#qualification)). CI runs the gate in the
pinned image on every pull request to `main` and every push to `main`, in
a job that is not required ([CI job](#ci-job)). Everything else
on this page is planned: specifications, statements and targets, the other
phases of the gate, the required gate and the other commands of
`cargo xtask formal`. They are set up by porting the tooling of the CAS
project and the prototype tree, and this page changes with them. Nothing
about the kernel is proved.

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
| `verification/image/` | The recipe of the image that holds the pinned tools, the list of its third-party notices, and the check of the built image as a user other than root ([image](#image)) | Present |
| `verification/image-pin.json` | The published image that the CI jobs of the gate run, by its digest ([image pin](#image-pin)) | Present |
| `verification/lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | The Lake project of the hand-written Lean and of the generated definitions, with the Lean toolchain and the packages of the Lake lock of the Aeneas Lean library ([qualification](#qualification)), and the library `KrepiRoot` of the root module that the [base round](#base-round) writes | Present |
| `verification/extraction.toml` | How Charon compiles each extracted crate ([extraction](#extraction)) | Present |
| `verification/Krepi/Spec/` | Specifications written from requirements, registered in `targets.json`; a component with a directory below [subject domains](domains/README.md) describes its own in the `specification.md` there, where it has one | Planned |
| `verification/Krepi/Statements/` | Statements: the propositions that registered theorems prove ([statements and proofs](#statements-and-proofs)) | Planned |
| `verification/Krepi/Proofs/` | Proofs of statements and refinement proofs of production targets; the only directory of the Lake project outside the statement side ([statements and proofs](#statements-and-proofs)) | Planned |
| `verification/Krepi/Models/` | Lean models of items that proofs reach without extracting them, and their differential check | Planned |
| `verification/Krepi/Qualification/` | Proofs about the qualification shapes | Present |
| `verification/Krepi/Qualification/Models/` | Definitions that the reviewed external declarations of three qualification cases use; they are not models ([qualification](#qualification)) | Present |
| `verification/externals/<Module>/` | Reviewed external declarations of a target or a qualification case (`FunsExternal.lean`, `TypesExternal.lean`), named by its `models` field | Present for qualification cases |
| `verification/targets.json` | The proof target registry | Present, empty |
| `verification/models.json` | The model registry ([models](#models)); `cargo xtask formal check` refuses a registered model | Present, empty |
| `verification/statements.json` | The statement hash, and each statement with its theorem and state ([statements and proofs](#statements-and-proofs)) | Present, empty |
| `verification/axioms.json` | The axioms of the Aeneas Lean library that target theorems may use, each with its source and reason ([base round](#base-round)) | Present, empty |
| `verification/tcb.json` | Items of the trusted base: native decisions and patterns of generated axioms, whose classification comes later ([base round](#base-round)) | Present, empty |
| `verification/legacy.json` | Kept empty: production functions without a proof are listed in `open.json` ([legacy inventory and admission](#legacy-inventory-and-admission)) | Present, empty by design |
| `verification/open.json` | The open obligations of the production code, generated from the `Open obligations` tables of the contracts of the components ([legacy inventory and admission](#legacy-inventory-and-admission)) | Present |
| `verification/qualification/` | A small crate of code shapes and their expected tool outcomes (`cases.json`) | Present |
| `xtask/src/formal/` | The commands of `cargo xtask formal` | `toolchain-check`, `run`, `guard`, `check`, `vectors` and `canary` present, the others planned |

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
definitions are never edited. A comparison of `cargo xtask formal vectors`
has a run directory too, without a receipt: `logs/`, and in `work/` the
home and temporary directories, its stage, the vector file `vectors` and
the result file `results` of the replay; the host tests write their result
files below `artifacts/formal/vectors/` ([test vectors](#test-vectors)).
The job of the toolchain canary keeps its trees, downloads and records
below `artifacts/canary/`, and its image build, as the image workflows do,
below `artifacts/image/` ([toolchain canary](#toolchain-canary)).

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
- the Rust targets include `aarch64-unknown-none`, the extraction triple of
  the kernel, which is not the target of the kernel images
  ([extraction](#extraction));
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
belongs to root; every user can read it and search its directories, and no
user but root can write it. The stage that installs a tree or a file makes
it readable by all and writable by none (`chmod -R a+rX,a-w`, or
`install -m 0555` for the programs in `bin/`); this also covers the build
outputs of Mathlib and of the packages it depends on, which
`lake exe cache get` unpacks readable by their owner only. The directories
that hold the trees can be written by root alone. So the tools run as any
other user, and that user cannot change the installation. The image sets no
user: whoever runs it chooses one. CI runs every container of the gate as
the runner's own user, which is not root, without capabilities, new
privileges or a network, with an init process, on a read-only root file
system with a temporary `/tmp`, and with the checkout mounted at its path
on the runner ([CI job](#ci-job)).

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

### Image pin

`verification/image-pin.json` names the published image that the CI jobs of
the gate run ([CI job](#ci-job)). It has schema 1:

| Field | Content |
| --- | --- |
| `schema` | `1` |
| `repository` | The repository of the image in the registry, without a tag or a digest |
| `digest` | The digest of the image: `sha256:` and 64 lowercase hexadecimal digits |
| `revision` | The commit of `main` from which `formal image publish` built and published the image, for readers; nothing checks it |

The file lies outside `verification/image/` and the other paths that start
the image workflows, so changing it builds and publishes no image, and the
image does not contain it. It has three readers:

- `.github/workflows/formal.yml` names the image as
  `<repository>@<digest>` in its variable `IMAGE`, which every container of
  the workflow runs, after a pull that takes the image by that digest.
- The `workflows` step of `cargo xtask check` reads the pin from the tracked
  files and fails unless a workflow that runs on `pull_request` names that
  reference and every mention of the repository in such a workflow,
  comments included, is the reference itself. A tag, another digest and the
  bare repository each fail with their line. A workflow that does not run
  on `pull_request`, such as `formal image publish`, which tags what it
  publishes, is not checked. The check is in `toolchain.rs`;
  `workflows.rs` only tells which workflows run on `pull_request`, as its
  third rule does.
- `cargo xtask formal run` on `linux-aarch64` checks the image that it runs
  in, after the export of the snapshot and before Cargo or any phase runs.
  It stops the run as a tool failure, with one failure that starts with
  `image:` and names each problem, when the job names an image in
  `KREPI_FORMAL_IMAGE` that is not the reference of the export's pin; when
  `versions.json` of the installation cannot be read; when an item that
  both it and the tool manifest pin differs; or when the user of the run is
  root, owns the directory of the installation, or could write it through
  the write permission of its group or of others, whatever groups the user
  is in. Such a user could change the modes of the installation, so the
  gate does not run as one. Without `KREPI_FORMAL_IMAGE` the receipt
  records no reference.

The compared items, each as a JSON value: `schema`, the schema of the
image's own file, which must be 1; of `lean`, `version`, `commit` and
`sha256`, the digest of the Lean archive of the `linux-aarch64` column; of
`aeneas`, `commit`, `patch_sha256`,
`lake_manifest_sha256`, `mathlib_commit`, and `version`, which must be
`aeneas <the first 7 digits of the commit>+patch-<the first 8 of
patch_sha256>`; of `charon`, `commit`, and `version`, which must be the
manifest's `version` followed by the commit in parentheses; of `rust`,
`toolchain`, `rustc_commit`, `manifest_sha256`, `rustup`, `rustup_commit`
and `rustup_init_sha256`, the digest of the column's `rustup-init`; of
`opam`, `version`, `repository_commit`, `sha256` and
`switch_export_sha256`, the last two from the column, and `ocaml`, the
version of the manifest's compiler package; and of `gmp`, `version` and
`sha256`. The image's Rust `targets` and `components` must hold those of
the manifest, where a component counts bare or with the suffix
`-aarch64-unknown-linux-gnu`. What the manifest does not pin, such as the
Ubuntu versions of bubblewrap and Git and the base image, is only recorded,
with the whole file, in the receipt. A unit test runs the check on the
`versions.json` of the pinned image, which `xtask/src/formal/fixtures/image/`
keeps, against the committed manifest.

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
| `GIT_CONFIG_COUNT` | `1` | All |
| `GIT_CONFIG_KEY_0` | `safe.directory` | All |
| `GIT_CONFIG_VALUE_0` | `*` | All |
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

Lake runs Git in each package of the Lake lock whenever it loads the
workspace, for every build and every `lake env`. In the image those
packages belong to root, and Git works in a repository of another user only
when `safe.directory` allows it in the system, global or command
configuration. The first two are turned off, so `GIT_CONFIG_COUNT`,
`GIT_CONFIG_KEY_0` and `GIT_CONFIG_VALUE_0` set `safe.directory` to `*` for
the command, which makes every repository safe: the repositories that the
tools meet are the packages of the installation, which they cannot write,
and the checkout and the directories of the run, which belong to the user
that runs the gate. On `darwin-arm64` that user owns the installation too,
and the variables change nothing.
`verification/image/non-root-check.sh` runs its tools with the same
variables; a test keeps the two lists equal.

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
2. The second pins that digest: it sets `digest` and `revision` of
   `verification/image-pin.json` and the reference in `IMAGE` of
   `.github/workflows/formal.yml` together, as the `workflows` step requires
   ([image pin](#image-pin)), and starts no image workflow. The CI job of
   the gate on its pull request is the first run of the new image
   ([CI job](#ci-job)).

When the first changes a version or digest that the gate compares with the
image ([image pin](#image-pin)), the CI job of the gate still runs the image
of the old pin, so the gate stops as a tool failure on that pull request and
on every push to `main` until the second is merged. Once the second is
merged, a pull request runs the workflow of its merge with `main`, and so
the new image, while the gate compares that image with the pin of the pull
request's head: on every open pull request that does not yet contain the
second, the gate stops as a tool failure, `image: the snapshot pins no
image or another than the job's`, until the pull request is updated from
`main`. The same failure names a pin that is missing or cannot be read.

The two image workflows run only for changes to these paths or to the two
workflows.
The publish workflow runs only on pushes to `main`, and its job alone may
write packages; a pull request never publishes an image. Both run every
step with `bash -eo pipefail`. Before the image build, both run the tool
checks and a check that `check_notices` of the recipe fails when any
component that `notices.txt` lists has a missing or empty notice. After the
build, both run `verification/image/non-root-check.sh` in the image as the
runner's user, without network and capabilities, with the variables that
tool commands get. It fails when an entry below `/opt/krepi-formal` cannot
be read or can be written, or is a directory that cannot be searched, when a
Mathlib build output cannot be read, when `lake env lean` cannot check a
file that imports Aeneas in a Lake project laid out as the gate lays out its
stages, when `git status` fails in the Mathlib package, when Cargo and rustc
through the rustup proxies, Charon or Aeneas cannot print their versions, or
when Charon and Aeneas cannot translate a crate of one function. It also
records Git's refusal without the `safe.directory` variables, the time of
`git status` there with and without `core.checkStat=minimal`, and whether
Lake finds the installed library up to date. The publish workflow publishes
only an image that passed the check. A test keeps the check's variables
equal to those of tool commands, so a change of those variables also
changes the check: its pull request builds the image, and its merge
publishes one. Both record the available disk before and after removing
preinstalled software from the runner, sample it together with the size of
the Docker data directory every 15 seconds during the build, record Docker's
disk use at the end and then free its build cache, and upload the samples,
the build log, the notice check, the layer sizes, `versions.json`, the
switch export and the output of the image check as a workflow artifact.

A change of the tools belongs to a formal upgrade, a separate task with
the requalification and the repair of the proofs that the new tools break;
[formal upgrade](formal-upgrade.md) is its manual. The [toolchain
canary](#toolchain-canary) shows each week what an upgrade to the tools of
Aeneas main would break.

### Toolchain canary

The workflow `formal canary`, `.github/workflows/formal-canary.yml`, runs
the gate once a week, on Saturdays at 09:17 UTC, and on a manual run of
`main`; a manual run of another branch skips the job. It runs the gate with
the tools that the pins follow upstream: the head of Aeneas's `main`, the
Lean release that its `backends/lean/lean-toolchain` names, the Charon
commit of its `charon-pin` and the Rust nightly of that Charon's
`charon/rust-toolchain`, each resolved when the job runs. It records what
an upgrade to them would break, and changes nothing: it is not a required
check, runs on no pull request and blocks no merge. Its one job,
`toolchain canary`, runs on a GitHub-hosted `ubuntu-24.04-arm` runner, may
only read the repository's contents, logs in to no registry, publishes no
image and pushes nothing. The job has 240 minutes, and every step a limit
of its own; the limits add up to 234 minutes, so a step's limit, never the
job's, ends a long step, and the steps that record the run always run.

These steps end the job at the first that fails, each by its id:

1. `runner`, `disk`, `sampler` and `xtask`: record the runner and refuse a
   root user or a checkout of another owner, record the disk, remove
   preinstalled software and sample the disk every 15 seconds as the image
   workflows do, here until the end of the gate, and build xtask;
2. `resolve`: fetch the head of Aeneas's `main`, which `git ls-remote`
   gives, into `artifacts/canary/aeneas/`, and, when its `charon-pin` has
   one line that is not a comment, that Charon commit, without submodules,
   into `artifacts/canary/charon/`;
   `cargo xtask formal canary resolve` reads the trees and names the
   downloads, and the step downloads both Lean archives of the release and
   the channel manifest of the nightly into `artifacts/canary/`, unpacks
   the `linux-aarch64` archive and keeps what its `lean --version` prints
   in `lean-version.txt`;
3. `derive`: `cargo xtask formal canary derive` writes the manifest of the
   build into `verification/toolchain.json`, and the Lake project files
   that Aeneas main changes, below, and prints each derived field with its
   committed and its derived value;
4. `fetch` and `toolchain-check`: fetch the derived Aeneas and Charon
   commits into `artifacts/image/`, Charon with its submodules, and run
   `cargo xtask formal toolchain-check` on them, as the image workflows do;
5. `patch`: `cargo xtask formal canary patch` runs `git apply --check`
   with the reviewed patch on that Aeneas tree; a patch that does not apply
   is one breakage, and the job ends there;
6. `build` and `record`: build the image with the committed recipe and the
   derived manifest, as the first build of [changing a
   tool](#changing-a-tool) does, under `timeout` with a limit of 52
   minutes, tag it locally, and record it as the image workflows do;
7. `fill`: commit the derived files in the job's checkout;
   `cargo xtask formal canary fill` sets the switch export of
   `linux-aarch64` to the `opam.switch_export_sha256` of the image and
   writes the statement hash of that commit into
   `verification/statements.json` where it differs, and a second commit
   holds both. The commits are local and never pushed;
8. `probe` and `gate`: probe a container of the image and run
   `cargo xtask formal run` in it as the [CI job](#ci-job) does, with its
   flags and variables but without `KREPI_FORMAL_IMAGE`.

The derived fields, each of the manifest of the build:

| Field | From | When it cannot be read |
| --- | --- | --- |
| `aeneas.commit` | The commit of the Aeneas tree | A failure of the run |
| `aeneas.lake_manifest_sha256`, `aeneas.mathlib_commit` | The SHA-256 of its `backends/lean/lake-manifest.json`, and the revision of its one package `mathlib` | For a missing lock, a failure of the run; for a lock without one package `mathlib`, a breakage |
| `lean.toolchain`, `lean.version` | Its `backends/lean/lean-toolchain`, which must name a release, `leanprover/lean4:v<version>` | A breakage |
| `lean.commit` | The commit that `lean --version` of the `linux-aarch64` archive reports for that version | A defect |
| `url` and `sha256` of `lean` in both host columns | The committed URL with its release replaced, and the SHA-256 of the download | For a URL that does not hold the committed release once, a defect; for a missing download, a failure of the run |
| `charon.commit` | The one line of `charon-pin` that is not a comment, the commit at which the Charon tree must be | For a `charon-pin` with more or fewer such lines, a breakage; for a missing one, or a line that Git cannot fetch, a failure of the run; for a tree at another commit than that line, a defect |
| `charon.version` | `package.version` of the Charon tree's `charon/Cargo.toml` | A defect |
| `rust.toolchain` | The channel of its `charon/rust-toolchain`, which must be a dated nightly, `nightly-YYYY-MM-DD` | A breakage |
| `rust.manifest_url`, `rust.manifest_sha256`, `rust.rustc_commit` | The committed URL with its date replaced, the SHA-256 of the download and its `pkg.rustc.git_commit_hash`; the manifest's `date` must be the nightly's | A defect |

`switch_export_sha256` of `linux-aarch64` is `null` for the build, as for
a first build, and `fill` sets it for the gate. Every other field keeps
its committed value: the patch and its origin, opam, OCaml and GMP,
rustup, the Rust components and targets, the prefixes and the switch
export of `darwin-arm64`. The written manifest has the layout of
`serde_json`. When Aeneas's Lake lock or Lean toolchain differs from the
committed ones, `derive` also writes `verification/lake-manifest.json`,
the committed lock with its path package `aeneas` followed by each package
of Aeneas's lock, inherited, and copies Aeneas's `lean-toolchain` to
`verification/lean-toolchain`. These files are on the statement side,
which is why `fill` computes the statement hash. A lock of another Lake
manifest version than the committed one is a defect: the canary does not
guess a layout of the lock that Lake may refuse.

Each step of `cargo xtask formal canary` writes
`artifacts/canary/<step>.json`, with `verdict`, `detail` and `data`, and
exits with 0 only when its verdict is `PASSED`. The step `verdict` reads
the outcome of every step of the job and gives the run the finding of the
first that did not pass, or else that of the gate, with the step and the
commit of `main` in its detail; the job passes only on `PASSED`:

| Finding | When |
| --- | --- |
| `PASSED` | Every step passed, and the gate exited with 0 and left one complete `VERIFIED` receipt |
| `BROKEN` | The patch does not apply; Aeneas main has a form that the committed checks refuse too; the build failed in a stage of the tools, `aeneas-source`, `lean`, `rust-toolchain`, `charon-build`, `aeneas-build` or `backend`; or the gate exited with 1 and left one receipt that is `REJECTED`, `TOOL_FAILURE`, `BUDGET` or `STALE`; each without a text of the two rows below |
| `DEFECT` | The tool checks fail on the derived manifest; a field cannot be derived; or the error or the output of the step that the failure block of the build log shows, or a failure or the reason of a unit that is not `VERIFIED` in the receipt, holds a check of what was installed against a pin, such as `lean reports` or `the switch export has SHA-256` of the recipe, a failure of the gate that starts with `image:`, or a statement hash that the snapshot does not have |
| `FAILED` | A step was cancelled or skipped, has no outcome, or succeeded without a record that passed; any other step failed; the build reached its limit, or the runner ended it, or it failed in another stage or without a BuildKit failure block after its first error; the text holds a full disk, a network error or a cancelled build, or a check of the gate's own inputs; or the gate wrote no exit status, left no single receipt that can be read, or exited with another status, which is an error of the run and not a verdict |

A text of an unknown shape is never a breakage: a breakage needs a failed
stage of the tools without the text of a defect or a failure, or a verdict
of the gate on a receipt that can be read. A text of a defect counts before
one of a failure. Of the build log, the error line and the output lines of
the failure block are read; only the script that the error line of a failed
process quotes, which the first line of the block also names, is left out,
since it holds the recipe's own texts. The summary of the workflow run and
one annotation give the finding, and the artifact
`formal-canary-<run>-<attempt>` holds, from `artifacts/canary/`, the
records, the outputs of `resolve`, `derive` and `toolchain-check`, the
manifest of the build and that of the gate, the diff of the derived files
and the exit statuses of the build and the gate; from `artifacts/image/`,
the build log, `versions.json`, the switch export, the layers and the disk
measurement, whose least available space and largest Docker root, which its
summary calls those of the build, cover the probe and the gate too; and the
record of the job, the event, the receipt and the logs of the gate.

The canary leaves out the notice check of the image workflows, which does
not depend on the tools, and `verification/image/non-root-check.sh`,
which is written for the committed nightly; the probe and the gate's check
of the image cover what the gate needs. The build takes Mathlib's build
cache for the Mathlib commit of the new lock; without one, it builds
Mathlib from source and reaches its limit, which fails the run. The
receipt of the canary has the mode `MANUAL`, the event `schedule` or
`workflow_dispatch` and no image reference, and the gate compares the
image with the derived manifest. It is no evidence about krepi, which
only the gate in the pinned image gives. [Formal
upgrade](formal-upgrade.md#canary-verdicts) says what follows each
finding.

## Commands

The commands of `cargo xtask formal` follow the design of the gate.
`cargo xtask formal toolchain-check`, `cargo xtask formal run`,
`cargo xtask formal guard`, `cargo xtask formal check`,
`cargo xtask formal vectors` and `cargo xtask formal canary` exist; the
others are planned.

| Command | Purpose |
| --- | --- |
| `cargo xtask formal toolchain-check --aeneas DIR --charon DIR` | Checks Aeneas and Charon checkouts and the Aeneas patch against the tool manifest ([tool checks](#tool-checks)) |
| `cargo xtask formal run [--target NAME]...` | The proof gate on a snapshot of the gate inputs, with its receipt ([gate run](#gate-run)); `--target` runs only the named targets. Its phases are, on a pull request, the [guard](#guard), which records its rules; the [qualification](#qualification) and the [base round](#base-round), which every run has; and, planned, every target (or the named ones) with its mutants |
| `cargo xtask formal guard --event PATH` | Checks a pull request, given by the JSON of its `pull_request` event, against the rules for changes of statements, proofs and sources ([guard](#guard)) |
| `cargo xtask formal check [--write]` | The inventory of the production functions against the `proves` and `unclosed` lists of the targets and against `open.json`, which it compares with what the contracts give, the rules of the registry ([proof targets](#proof-targets)) and the refusal of what the gate does not support yet ([legacy inventory and admission](#legacy-inventory-and-admission)); `--write` first writes `open.json`. It runs no tool and proves nothing |
| `cargo xtask formal receipt [--require-fresh]` (planned) | Says whether a receipt is current for the checkout: the same gate inputs and image, one conclusion for each unit, complete and `VERIFIED`; `--require-fresh` also requires a run of the whole gate from a clean checkout without planned statements |
| `cargo xtask formal vectors [DOMAIN/COMPONENT]` | Replays the test vectors of a component's contract, or of each component whose contract names a replay, through its specification with the pinned Lean and compares the results line by line with those that its Rust host tests wrote ([test vectors](#test-vectors)). It writes no receipt and proves nothing |
| `cargo xtask formal canary STEP [--outcomes TEXT]` | Runs one step of the toolchain canary on what its job fetched and built: `resolve` and `derive` the tool manifest of Aeneas main, check that the `patch` applies, `fill` the switch export and the statement hash, or conclude the run with its `verdict` from the outcomes of the steps of the job ([toolchain canary](#toolchain-canary)). It fetches nothing and proves nothing |
| `cargo xtask formal mutants TARGET` (planned) | Generates the source mutants of a target and records the survivors with their classification |
| `cargo xtask formal impact --base REV` (planned) | Lists the targets that a change since `REV` affects |
| `cargo xtask formal merge` (planned) | Combines the receipts of the shards of a run and of its qualification into the conclusion of the whole gate |

`cargo xtask check` does not run the gate, which needs the pinned tools.
CI runs the gate in a job of its own on every pull request to `main` and
every push to `main` ([CI job](#ci-job)). That job is not required: a
change is to merge only when a required gate passes on its head or a
committed waiver record covers the failure, and both are planned.

## Gate run

`cargo xtask formal run` runs the gate on the commit checked out, the
snapshot commit, and writes a receipt of the run, whether it passes, fails
or stops on an internal error. Its code is in `xtask/src/formal/`: the gate
inputs in `paths.rs`, the commands in `process.rs`, their classes and the
statuses in `outcome.rs`, the receipt in `receipt.rs`, the extraction in
`extract.rs`, the Lake stages, the source rules and the allowlist in
`lean.rs`, the qualification in `qualify.rs`, the base round in `base.rs`,
the statement side and the guard in `guard.rs`, the registry and its rules
in `registry.rs`, the check of a target's registration against its
extraction in `classify.rs`, and the run in `run.rs`.

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
   environment of its commands. On `linux-aarch64` the run then checks the
   image that it runs in against the tool manifest and the export's image
   pin, and the user it runs as ([image pin](#image-pin)). The target
   registry of the export, `verification/targets.json`, must register every
   name given with `--target`;
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
   targets inside `kernel/` once symbolic links are resolved, and the root
   manifest `kernel/Cargo.toml` has the shape of the
   [source layout](architecture.md#source-layout), as the `manifests` step
   requires of the checkout. A failure of Cargo itself is a tool failure.
   The run is also rejected when it extracts kernel targets and
   `kernel/Cargo.toml` has no `[package]` named `krepi-kernel`, the root
   package that kernel targets are extracted from: a whole run extracts
   every formal target of the registry, a run with `--target` the targets
   that it names, planned ones included. A run whose registry has no formal
   target, or that names none, only qualifies the tools and runs the base
   round, and the workspace may then have no root package.

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
features and no `cfg` settings. Its section `kernel` gives the extraction
triple, `aarch64-unknown-none`, and the features and `cfg` settings of the
release profile of the kernel, which has none; nothing is extracted from
the kernel while no target is registered. The qualification stops when the
file of the export does not have exactly these hosts, names features or
`cfg` settings for the qualification crate, or gives the kernel another
triple. The triples of the qualification crate record what Charon chooses
on each host; nothing passes them to Charon, and the gate does not check
their values.

The extraction triple is a pin of the gate, whose standard library the
image that holds the tools installs ([tool checks](#tool-checks)). It is
not the target of the kernel images, `aarch64-unknown-none-softfloat`,
whose soft-float ABI keeps compiled kernel code off the FP/SIMD registers
at EL1, where FP/SIMD instructions trap
([floating-point state](architecture.md#floating-point-state)). The two
triples have the same architecture, OS and data layout and differ in the
floating-point ABI, the target feature `neon` and linker arguments. The
kernel crates use no floating point and no `cfg` condition on the ABI or
on a target feature, so Charon translates the same source for both
triples.

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
changed. The cases taken from the CAS project were recorded with its
earlier Charon and Aeneas; the 27 whose conclusion the pinned tools change
record what the pinned tools give, and the
[porting record](porting/verification-qualification.md#revised-expectations)
explains each with its evidence.

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
belongs to root, every user can read it and none but root can write it. CI
runs the gate there as the runner's user, on a read-only root file system
([CI job](#ci-job)), and the gate refuses to run as root or as the owner of
the installation ([image pin](#image-pin)).

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
- the statements restated: each `name` that `statements.json` registers at
  only one of the merge base and the head, that is, a statement added,
  removed or renamed. A registered statement may change its `theorem`, its
  `module` or its `state` without being restated. A pull request that does
  not change `statements.json` restates none;
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
The pull request template, `.github/pull_request_template.md`, ends with
the six fields, empty, and explains them and the label `ai-proof` in a
comment, where no line starts with the name of a field.

| Field | Value |
| --- | --- |
| `Review` | The id of the review of a statement change: 1 to 64 ASCII letters and digits |
| `Approval` | The id of the owner's approval of the change, in the same form |
| `Approved-Statement-Hash` | The statement hash that was approved, 40 lowercase hexadecimal digits |
| `Heartbeats-Review` | The id of the review of a raised heartbeat limit, in the same form as `Review` |
| `Phase` | The phase of the proof work that the pull request belongs to: `statement`, `proof` or `rewrite` |
| `Author` | The opaque id of the author of the pull request, in the same form as `Review` |

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
| `phase-and-author` | The label `spec` or `proof` is present and `Phase` or `Author` is missing, or `Phase` is not `statement`, `proof` or `rewrite` |
| `proof-of-registered-statements` | A statement is restated and the label `spec` is missing: a proof may only prove a statement that the merge base registers |

`proof-of-registered-statements` judges every pull request, whatever its
labels: adding, removing or renaming a statement needs the label `spec`,
and with it the fields that `spec-approval` checks.

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

`receipt.json` has schema 2. It is the pretty form of `serde_json`, with
the fields in the order of the tables below and every map sorted by its
keys; times are seconds, rounded to milliseconds.

| Field | Content |
| --- | --- |
| `schema` | `2` |
| `command` | `cargo xtask formal run` |
| `status` | `VERIFIED`, `REJECTED`, `STALE`, `TOOL_FAILURE`, `BUDGET` or `SCOPED` |
| `complete` | Whether the run is complete, as defined above |
| `trigger` | `mode`, `MANUAL` for a run of the whole gate and `SCOPED` for a run of named targets, with `REQUIRED`, `FORCED_FULL` and `WEEKLY` kept for the jobs of CI; `event`, `ref`, `run_id` and `attempt`, from `GITHUB_EVENT_NAME`, `GITHUB_REF`, `GITHUB_RUN_ID` and `GITHUB_RUN_ATTEMPT`, or `null` |
| `targets` | The names given with `--target`, sorted; empty for a run of the whole gate |
| `host` | `linux-aarch64` or `darwin-arm64`, or `null` on another host |
| `image` | The image of a run on `linux-aarch64`, below, or `null` on another host |
| `run`, `directory` | The identifier of the run, and its directory relative to the repository root |
| `started`, `seconds` | The Unix time in seconds at which the run started, and how long it took |
| `commit`, `tree` | The snapshot commit and its root tree, or `null` |
| `inputs` | `before` and `after`, the object of each gate input (`mode`, `type`, `oid`, or `null` when the commit does not have it) at the start and at the end, or `null` when they were not taken; `clean_after`, whether the gate inputs were clean at the end, or `null` |
| `budgets` | `gate_seconds`, 7200, and `receipt_margin_seconds`, 300 |
| `resources` | What the run used of the host, below |
| `phases` | For each phase, `budget_seconds`, `seconds` and `ran` |
| `units` | For each unit, its `phase`, its `status` and the `reason` for it, or `null` |
| `qualification` | What the qualification found, below, or `null` when it did not start |
| `base` | What the base round found, below, or `null` when the round stopped before it recorded it |
| `guard` | What the guard found on a pull request, below, or `null` without a pull request event or when its phase did not finish |
| `commands` | Every command, in the order in which they ran |
| `failures` | Every failure that is not the conclusion of a unit, with its `status` and `message` |

The `image` record has these fields:

| Field | Content |
| --- | --- |
| `reference` | The image that the job named in `KREPI_FORMAL_IMAGE`, `<repository>@<digest>`, or `null` without the variable |
| `uid` | The effective user ID of the run |
| `writable` | Whether that user could write the directory of the installation, as the [image pin](#image-pin) describes, or `null` when the run stopped before the check |
| `versions_sha256` | The SHA-256 of `versions.json` of the installation, or `null` when it could not be read |
| `versions` | The whole text of that file, or `null` |
| `os_release` | The whole text of `/etc/os-release`, or `null` |

The manifest and `/etc/os-release` are kept as text, as the image wrote
them, so that the receipt holds the image's own record without a parser
and without a map in the order of a JSON object.

The `resources` record has these fields, each `null` when the host does not
report it:

| Field | Content |
| --- | --- |
| `disk_available_at_start` | The bytes available to users other than root on the file system of the run directory when the run started |
| `disk_least_available` | The least of those bytes at the start and after each command |
| `largest_process_max_rss` | The largest maximum resident set of a single process that the run collected, or that such a process collected, in bytes: the largest one process, not the sum of processes that ran side by side |
| `cgroup_memory_peak` | `memory.peak` of the run's cgroup under cgroup version 2, in bytes: in CI the container's. It counts the page cache too, such as the build outputs of Mathlib that Lean maps, so it bounds from above what the container held and does not say what the processes needed |

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
| `restated` | The statements registered at only one of the merge base and the head: added, removed or renamed |
| `raised` | The files with a new raised heartbeat limit |
| `rules` | Each rule, with why it fails, or `null` when it holds |

CI keeps the receipts of its runs, so any change of a field takes a new
schema. Receipts come from two hosts. CI runs the gate on `linux-aarch64`
in the pinned image, as the runner's user, which cannot write the image's
installation, and records the image ([CI job](#ci-job)). Local runs on
`darwin-arm64`, with the installation at `artifacts/formal/tools`, serve
development; there the user owns the installation, the receipt records no
image, and the gate only detects writes to the installation. Only receipts
of CI runs are evidence.

### CI job

The workflow `formal`, `.github/workflows/formal.yml`, runs the gate in CI.
Its job `formal run` runs on every push to `main` and on every pull request
to `main` when it is opened, reopened or updated, when a label is added or
removed, and when its description is edited, since the guard reads the
labels and the description. It is not a required check. A newer event of
the same pull request cancels a run of the job that has not ended. The job
runs on a GitHub-hosted `ubuntu-24.04-arm` runner, may only read the
repository's contents, uses no stored credentials, and runs actions pinned
to full commit SHAs. Its steps:

1. check out the head of the pull request, or the pushed commit, with its
   whole history, which the guard needs for the merge base;
2. record the runner (its user, processors, memory, disk, kernel, and
   Docker's cgroup version and security options), and fail when the
   runner's user is root or does not own the checkout; pull the image by
   the digest of `IMAGE` ([image pin](#image-pin)) and record its digests
   and size; copy the event to `artifacts/formal/event.json`, inside the
   checkout;
3. build xtask on the runner with the Rust toolchain of
   `rust-toolchain.toml`;
4. probe a container of the image with the flags of the gate: the step
   fails unless the user is not root, the root file system is read-only, no
   capability is left in the bounding set, new privileges are off, `lo` is
   the only network interface, every attempt to create a file in or change
   the mode of `lean/`, `backend/`, `bin/`, `rustup/` and `cargo/` of the
   installation fails, and xtask starts in the image;
5. on a pull request, run `cargo xtask formal guard` with the copied event,
   as the binary of step 3 on the runner; its failure fails the job, and the
   gate still runs;
6. on a pull request that changes `kernel/`, `user/`, `verification/`,
   `docs/domains/`, `xtask/` or `.github/workflows/formal.yml` since the
   merge base, compare the test vectors ([vectors in CI](#vectors-in-ci)):
   build the test executable of xtask and run its ignored replay of the
   fixture in a container of the image, run the host tests of the kernel and
   user-space workspaces with `KREPI_VECTOR_RESULTS` set, and run
   `cargo xtask formal vectors` in another container. Each container has the
   flags, the user and the mounted checkout of the gate's and is removed
   when it ends. Under `timeout`, the build of the test executable has 5
   minutes, the fixture replay 6, the host tests of each workspace 5 and the
   comparison 31, and each container a minute more for its kill, so that
   none outlives the step's 55 minutes. Its failure fails the job, and the
   gate still runs;
7. run `cargo xtask formal run`, as the same binary, in a container of the
   image, as the runner's user and group, with
   `--pull never --init --read-only --tmpfs /tmp --cap-drop ALL --security-opt no-new-privileges --network none`,
   the checkout mounted at its own path as the working directory, and the
   variables `GITHUB_EVENT_NAME`, `GITHUB_REF`, `GITHUB_RUN_ID` and
   `GITHUB_RUN_ATTEMPT` of the run, `GITHUB_EVENT_PATH` naming the copied
   event, and `KREPI_FORMAL_IMAGE` naming the image of `IMAGE`;
8. always, remove the container of the gate if a cancelled step left it;
9. always, write a summary of the receipt to the summary of the workflow
   run: the status, whether the run is complete, its time and that of each
   phase, the number of units of each status, the image, the resources, the
   rules of the guard, every unit that is not `VERIFIED` and every failure.
   The step fails when the gate's step ran and left no receipt;
10. always, upload `job.txt`, the record of steps 2 to 4 and of the start
    and end of the gate, the output of the guard, the output of the vectors
    step with that of the fixture replay, the path of its test executable
    and the host results, the event, and the receipt and the logs of the run
    as the artifact `formal-receipt-<commit>-<attempt>`.

xtask finds the repository through the path at which it was compiled, so
the checkout is mounted at that path; the runner and the image are the same
Ubuntu release, so xtask, built on the runner, runs in the image, as the
probe checks. The runner's user owns the checkout, so
the run directory is its own and Git works in the checkout, while Lake's
Git works in the packages of the installation through `safe.directory`
([environment of tool commands](#environment-of-tool-commands)). The init
process collects processes that leave their group, which the gate as
process 1 would not, and `--pull never` makes a missing image an error
instead of a pull.

The job may take 195 minutes: 15 for the steps before the vectors step (2
to check out, 8 to record the runner and pull, 3 to build xtask, 1 for the
probe and 1 for the guard), the 55 of the vectors step, and the gate's own
7,200 s with the 300 s of its receipt.
The gate's step has a limit of 126 minutes, a backstop one minute after the
gate's own end. When the steps before the gate and the gate use all their
time, the steps after it have almost none, and the limit of the job may cut
the upload; the receipt is still written in the checkout. When the gate's
step is cancelled or reaches its limit, the step after it removes the
container, and the gate writes no receipt.

The gate's step fails whenever the gate does not exit with 0, `REJECTED`
included, and nothing marks a failure as expected. While the qualification
rejects the cases kept from the CAS project, every run of the job fails, and
the summary shows whether exactly those units are rejected.

The measurement jobs `leanchecker fresh`, `leanchecker prefix` and
`lake comparator` run on a manual run of the workflow (`workflow_dispatch`,
which runs the workflow of the branch it is started on) and on a pull
request that has the label `formal-measure`, when it is opened, reopened or
updated and when that label is added, but not when its description is
edited or another label changes; the job `formal run` does not run on a
manual run. Each waits for an earlier run of itself on the same pull request
or commit instead of cancelling it.

- `leanchecker fresh` and `leanchecker prefix`, 120 minutes each, prepare
  and run the gate as `formal run` does, without the probe and the guard
  step; a gate that exits with 1 passes there, and any other status but 0
  fails. The gate's step has 75 minutes there, which hold a qualification
  that uses its whole budget and a base round of the expected length. Then
  they drop the page cache of the runner and run, in the stage of the base
  round, in a container with the flags of the gate,
  `lake env /usr/bin/time -v leanchecker --fresh Krepi`, or
  `leanchecker Krepi` and then `leanchecker KrepiGen` in the same way, each
  with the variables of tool commands, which a test keeps equal to those of
  the gate but for the home and temporary directories. This step has no
  limit of its own, so only the job's limit bounds it. It fails when the
  base round did not build its stage or `leanchecker` does not exit with 0.
  The summary gives the time from the start of the job, which the runner's
  worker process gives, to the end of the build of xtask; the time of the
  extraction of the three qualification cases with proofs and that of the
  base round without its audits and `leanchecker`, both from the receipt;
  the wall time of the measured `leanchecker` calls; and their sum, an
  estimate of the time of a job that does only what `leanchecker --fresh`
  needs, composed of these parts. The extraction and the base round run
  after the qualification, so on a warm page cache, and `/usr/bin/time`
  inside `lake env` leaves out Lake's loading of the workspace. As context,
  the summary also gives how long the container of each call ran, until it
  was removed when the job's limit cut the call, and the time from the start
  of the job to the end of the last call and to the summary. The output and
  the `/usr/bin/time` record of each call, the times and the receipt with
  its logs are uploaded as `formal-leanchecker-<mode>-<commit>-<attempt>`.
- `lake comparator`, 30 minutes, writes a Lake project from the counter
  fixtures of `xtask/src/formal/fixtures/base/counter/`, with two
  handwritten challenges, and runs `lake comparator` on three
  configurations: a challenge that the solution proves, the statement
  module as the challenge, and a challenge that the solution proves only in
  a weaker form. It runs each, in a new copy of the project, in these
  container settings in turn: Docker's defaults, as root; those with seccomp
  and AppArmor unconfined; the container of the gate; and, after
  `kernel.apparmor_restrict_unprivileged_userns` is set to 0 on the runner,
  the second setting and the gate's container again, and both once more
  with an empty `/run`, where bubblewrap creates `/run/user`, the gate's
  container then also with seccomp and AppArmor unconfined. It records the
  kernel, the settings of user namespaces, Docker's security options and
  the version of bubblewrap in the image, and the exit status and output of
  each run, and uploads them as `formal-comparator-<commit>-<attempt>`. A
  result of the comparator never fails the job; an error of Docker, exit
  status 125 to 127, or of the runner does.

## Proof targets

`targets.json` has schema 2. Each entry under `targets` describes one
extraction and its obligations. The fields are those of the CAS project,
with the state and the budget of a target added and a cut point written as
an object; a field that the table does not list is refused:

| Field | Meaning |
| --- | --- |
| `name`, `module`, `feature` | Target name, generated Lean namespace, feature ID (`krepi.<area>.<feature>`) |
| `state` | `formal`, the default, for a target that the gate verifies, or `planned` for one that it only extracts and type-checks; a run of the whole gate selects the formal targets, and a planned one runs when `--target` names it |
| `budget` | The seconds that the unit of the target may take, 1,800 when the field is left out |
| `description` | What the target proves, in one paragraph |
| `start_from`, `exclude` | Charon roots and cut points by exclusion; `cargo xtask formal check` refuses `exclude`, which the gate does not support |
| `opaque` | The cut points: items translated without their bodies, each an object with the Charon `pattern`, the `source` where the items are and the `reason`. A cut item is modelled as a deterministic function of its arguments, so the reason states that no statement depends on two calls with the same arguments agreeing, as a function that reads hardware or global state would not |
| `proves` | Inventory keys (`file#Owner::name`) of local functions whose every path the obligations cover |
| `unclosed` | Inventory keys of local functions the extraction reaches, translated or cut, that are not proved |
| `derived` | Reached methods that a `#[derive(..)]` attribute defines; they have no source text and stay unverified |
| `unconstrained` | Rust names of the external functions and types the extraction reaches |
| `models` | Optional directory of reviewed external declarations installed in place of the generated templates |
| `trusted_axioms` | Further axioms the theorems may use, each with a reviewed reason |
| `premises` | Hypotheses that restate, over this target's generated types, a registered theorem of another target about a function this target cuts; `cargo xtask formal check` refuses non-empty `premises`, which the gate does not check yet |
| `proof_modules`, `obligations` | Lean modules, and the statements, each with its `id`, `statement` and the `theorems` that establish it |
| `mutants` | Source edits, each with its `name`, the `file`, the text `find`, which occurs once in the file, its `replace` and the theorems `fails`, one of which the edit must make fail |

`cargo xtask formal check` applies the rules of the registry without running
a tool, and each broken rule is a problem:

- no two targets have the same name or module, and no theorem is registered
  twice, by the obligations of one target or of two, or by a target and a
  specification;
- a formal target has at least one obligation and at least one mutant, and
  every obligation has at least one theorem; a planned target needs neither
  an obligation nor a mutant;
- every mutant names at least one theorem in `fails`, each a theorem of an
  obligation of its own target, and no target registers more than 30
  mutants;
- no key is in two of `proves`, `unclosed` and `derived`;
- every cut point and every axiom of `verification/axioms.json` has a
  `source` and a `reason` that are not blank;
- every key of `proves` and `unclosed` is a production function of the
  [inventory](#legacy-inventory-and-admission), and every entry of
  `derived` is a key `file#Type::method` of a method that a
  `#[derive(..)]` of a production type in the file defines, not a
  production function.

A run extracts the target from the current production source and checks the
registry against the translation (planned): every reached local function is
in `proves`, `unclosed` or `derived`, every cut local item in `unclosed`, and
the reached external items are exactly those of `unconstrained`; every entry
of these lists is still reached, and a `derived` entry is reached as a method
of a derived implementation of a standard trait, under one Rust name. A Rust
name maps to the inventory key of its function: the path below the module
of its source file, `krepi_kernel::m::inner::f` in the file of `m` for
`inner::f`, gives the inline modules; the self type of an implementation,
`{impl Trait for krepi_kernel::m::Type}`, the owner; and the loops of a
function, whose Rust name is that of the function, map to its key, as the
default method of a trait and its loops map to `Trait::method`. A reached
function that maps to no function of the inventory is not registered, so the
run fails: the body of a closure, which has a function of its own (rule R4 of
the [provable subset](conventions/provable-subset.md)), a loop that the tools
place in a file outside the package, such as that of a macro, a function in
the body of another, and a method of a trait implementation whose key the
inventory numbers, as `#2`, which its Rust name cannot tell apart from the
others of its key.
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
such. The frozen test vectors of a component are also replayed through its
specification and compared with its host tests
([test vectors](#test-vectors)).

For kernel state, the specification states identity (pool, slot, generation
and rights together), lifetime (which states are terminal and which
transitions they allow), the frame of each operation for success and for
failure, budget accounting including overshoot that preemption causes, and
reclamation conditions, each tied to a real acknowledgement.

## Test vectors

`cargo xtask formal vectors [DOMAIN/COMPONENT]` replays the frozen test
vectors of a component through its specification with the pinned Lean and
compares the results, line by line, with those that the component's Rust
host tests wrote. The two sides are independent: the host tests run the
code, the replay runs the specification, and both answer the vectors that
the legacy tree froze
([independent evidence](conventions/testing.md#independent-evidence)). No
contract names vectors yet.

### Contract block

The `Legacy test vectors` section of a component's `contract.md` names its
files in one fenced block that opens with the line ```` ```vectors ```` and
ends at the line ```` ``` ````, with white space allowed around either. It
is the only fenced block of the section: any other line of the section that
starts with three backticks or tildes, such as another info string, a tilde
or longer fence, a second block, or a block that is not closed, fails the
command, so that a misspelt block is not passed over. A block in another
section is not read, and a section without a block names no vectors. The
body is TOML with these keys and no others:

| Key | Value |
| --- | --- |
| `vectors` | Required: the repository path of the vector file, a tracked UTF-8 file at any path, such as a data directory of the component's workspace |
| `replay` | The Lean module of the replay; named once the module exists and the host tests write their results |

A contract that is not tracked, a body that is not TOML and a missing or
unknown key fail as well.

### Vector and result files

A vector file is UTF-8 with LF line ends. Its first line is a `#` comment
that names its source, as for all frozen data
([layout](conventions/testing.md#layout)), and lines that start with `#`
are comments. Every other line is one vector: an id, the input and the
expected output, separated by tabs. An id is not empty and is not given
twice, no field holds a tab, and a blank line is malformed. The file holds
at least one vector, so that a comparison cannot pass on nothing.
`cargo xtask formal vectors` reads only the ids and the number of fields,
and the replay gets only the input.

Inputs and outputs use the notation that the contract states, and an
expected output is in its canonical form, since outputs are compared as
text. Bytes are written as lowercase hexadecimal digits, two for each byte
and nothing between them; a structured value is written as `key=value`
fields separated by single spaces, in the order that the contract gives;
no field holds a tab or a line break. Whether these forms hold every
vector of the legacy tree is checked with the first contracts that name
vectors.

The replay and the host tests write result files of one form: UTF-8 with
LF line ends, where lines that start with `#` are comments; every other line
is the id of a vector, a tab and the output, in the order of the vector
file.

### Host results

When `KREPI_VECTOR_RESULTS` names a directory, the host tests of a component
write `$KREPI_VECTOR_RESULTS/<domain>/<component>.results` and create the
directories that they need. They still assert each output against the
expected output of its vector; the result file only carries the outputs to
the comparison. Kernel tests write the lines with the standard library
alone. The command reads `artifacts/formal/vectors/<domain>/<component>.results`
below the repository root, so a local comparison runs the host tests first
with the variable set to `artifacts/formal/vectors` of the checkout; a
result file left by an earlier run may be stale. Result files are not
committed.

### Replay module

The replay of a component is a module below `verification/Krepi/` and
outside `verification/Krepi/Proofs/`, by convention `Krepi.SpecTests.<...>`.
It defines `public def replay (input : String) : String` in the namespace of
its module name, with Lean core and the statement side only. It is a test,
not a theorem: `#guard` is allowed, it builds with `--wfail`, and the
[source rules](#source-rules) apply to it, so `native_decide` is refused. It
defines no `main`, which would clash with others in the root module, and
writes nothing to standard error. It lies on the statement side, so a pull
request that changes it carries the `spec` label ([guard](#guard)).

### Run

The command compares the named component or, without one, every component
whose block names `replay`; then a block that cannot be read in any contract
fails the command. For each component it first reads the inputs: the block;
the replay module, which must be a module name below `Krepi` and outside
`Krepi.Proofs`, on the statement side, whose file is tracked; the vector
file; and the host results. A problem with any of them fails the component
before a tool runs; the comparison, after the replay, checks the form of the
vector file's lines. It then takes the installation of the host's column of
the tool manifest and creates a run directory, where it lays out a stage of
the Lake project as the gate does, with every tracked file below
`verification/Krepi/`, writes the driver into the project of the stage as
`Vectors.lean` and the vector file as `work/vectors`. The driver,
`xtask/src/formal/vectors/Driver.lean`, is a plain Lean file with the name
of the replay module in place of `KrepiVectorsReplay`: for each vector it
writes the id, a tab and the output of `replay` for the input to
`work/results`, and for a line that is not an id, an input and an output an
empty line, so that the comparison names that vector. It is not a module,
since `lean --run` of a module file fails with
`Could not find native implementation`.

Two commands run as the gate runs its commands
([deadlines and processes](#deadlines-and-processes)), each in a process
group of its own, with the [environment](#environment-of-tool-commands) of
`lake env lean` and its output in `logs/0001-build.*` and
`logs/0002-replay.*`:

1. `lake build --no-cache --wfail +<module>`, with the cap of 7,200 s of a
   `lake build`;
2. `lake env lean --run Vectors.lean <work/vectors> <work/results>`, with
   the cap of 1,800 s of a `lake env lean`.

The commands of one `cargo xtask formal vectors` share a budget of 1,800 s.
The limit of a command is the smaller of its cap and what is left of the
budget, and a command that is left no time does not start: the component
fails with `the budget was used up`. A command that reaches the end of the
budget is reported, in the words of the gate, as stopped at the rest of the
budget of the gate. A command fails the component as it fails the gate:
when it could not start or was stopped, when a signal ended it or a Lean
process that it ran, when processes of its group outlived it, and when it
did not exit with 0. The replay also fails it when it wrote anything to
standard error, since a Lean `panic!` prints `PANIC` there and goes on with
a default value. The reason names the log directory.

### Comparison and output

Comment lines are dropped, and the lines of the vector file and of the two
result files are then compared position by position, up to the longest:

- a vector line that is not an id, an input and an output gives
  `vector N: not an id, input and output`, and one whose id an earlier
  vector has gives `vector N: an id given twice`;
- a result after the last vector gives `result N: of no vector`;
- otherwise the line of the replay must be the id of the vector and an
  output, with the same bytes as the line of the host tests, or the
  problem is `<id>: the replay gives "<line>", the host tests "<line>"`,
  with `nothing` for a missing line.

A vector file without a vector, or whose first line names no source, gives
one problem more. Outputs are never parsed, so `1` and `1.0` differ and a
number above `u64::MAX` keeps its digits. Every vector of the file is
compared: a vector that the specification or the host tests cannot run
stays out of the file, the contract lists it with its reason, and review
checks that the vectors of the file and those listed make up the frozen
count.

The command prints the host and the prefix of the installation, a line
`compared <component>` for each component that it compares, a line
`FAILED <component>: <problem>` for each problem, a line
`not compared <component>: it names no replay` for each component whose
block names no replay, and `<n> components, <m> problems`. A problem before
any comparison, such as a block that cannot be read, is then the only line
before the counts, a `FAILED` line without a component, and the host line
is not printed. It exits with 1 when there is a problem and with 2 for a
usage error. It writes no receipt and does not check the image: in CI, the
gate of the same job checks it ([image pin](#image-pin)).

### Vectors in CI

On a pull request, step 6 of the [CI job](#ci-job) compares the vectors when
the pull request changes `kernel/`, `user/`, `verification/`,
`docs/domains/`, `xtask/` or `.github/workflows/formal.yml` since the merge
base, and otherwise prints that it compares 0 components. Every
specification module lies below `verification/`, every source below
`kernel/` or `user/` and every contract below `docs/domains/`, so the rule
selects every component whose specification or sources changed, and more; a
vector file outside these paths, such as one below `tools/`, is compared
only when one of them changes too. `xtask/` and the workflow are in the list
so that a change of the comparison runs it too. The step runs the fixture
replay below, then the host tests of the kernel and user-space workspaces
with `KREPI_VECTOR_RESULTS` set, and then `cargo xtask formal vectors`
without a component in a container of the image. It does not block a merge,
since the job is not required. Selecting the components one by one, a
receipt of the comparison and a check of the image are planned.

### Fixture

The fixture component of the tests lies in
`xtask/src/formal/fixtures/vectors/`: `sum.vectors`, three vectors of the
sum of two natural numbers as `a=<m> b=<n>`, one of them above `u64::MAX`;
`Sum.lean`, its replay, with Lean core only; and `sum.results`, its host
results. The unit tests write it into Git repositories, with a Lake
stand-in in place of the pinned Lean. The ignored test
`formal::vectors::tests::the_fixture_replays_with_the_pinned_lean` replays
it with the pinned Lean in a stage of the Lake project of the repository,
which links the Aeneas library and Mathlib but builds neither, and checks
that equal results pass and that results with one item that differs give
exactly that problem, within 300 s. Step 6 of the CI job runs it in the
image, and a local run needs the `darwin-arm64` installation at
`artifacts/formal/tools`:

```sh
cargo test --manifest-path xtask/Cargo.toml --bin xtask -- --ignored --exact \
  formal::vectors::tests::the_fixture_replays_with_the_pinned_lean
```

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
it. A proof pull request, with the label `proof`, proves statements that
the merge base registers: it may take a statement from planned to proved
or move its proof to another theorem or module. Adding, removing or
renaming a statement restates it and needs the label `spec`
([guard](#guard)). A statement that becomes planned again, is removed or
is renamed is also a statement change.

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
model, not a proof; the modelled source remains an assumption. Until the
gate compares models with their implementations, `cargo xtask formal check`
refuses a registered model. The
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
function is admitted without a proof as a legacy function. Every production
function of the kernel workspace is instead in the `proves` or `unclosed`
list of a target or covered by an open obligation that the contract of its
component lists, and `cargo xtask formal check` holds the inventory of
these functions against both. It runs no tool and proves nothing.

The inventory reads every tracked `.rs` file below `kernel/`, build
scripts included, and parses it with `syn`. Its roots are the sources of
the targets that `cargo metadata` reports for the kernel workspace, with
the command of the `manifests` step: those of library, binary and
procedural-macro targets are production roots; those of tests, examples,
benchmarks and build scripts are not. From the roots it follows `mod`
declarations by the rules of rustc, `#[path]` and inline modules included,
only to find the files that production code reaches; a file that two
declarations load is followed from both:

- A test module file, the file of `#[cfg(test)] mod x;` or of a `mod`
  declared in an inline `#[cfg(test)]` module, is test code, and so is
  every file that only test code, a root that is not a production root or
  a build script reaches. A file that production code reaches as well is
  production code. Only `#[cfg(test)]` in exactly this form marks test
  code; `#[cfg(all(test, unix))]` and other forms do not.
- A file fails the check when it is not a regular file of UTF-8 text, when
  it does not parse, when the identifier `include`, raw or not, appears in
  it at any depth of its tokens, or when it is no root and no `mod`
  declaration reaches it. Every way to call `include!`, through a path, an
  import that renames it or a macro that is given its name, writes that
  identifier, so no other use of the name is allowed either; `include_str!`
  and `include_bytes!` do not count. A `mod` declaration that names no
  tracked file, or both `x.rs` and `x/mod.rs`, fails as well.
- The production functions are the functions with a body in production
  files, outside items marked `#[cfg(test)]` and outside function bodies,
  including those in the initializers of constants and statics. Functions
  that a macro generates cannot be seen before expansion, so a production
  `macro_rules!` macro whose body holds the keyword `fn` fails the check.
  The key of a function is
  `<path>#[<inline module>::]...[<Owner>::]<name>`: the owner of a method is
  the last path segment of the self type of its implementation, under `&`,
  `*` and parentheses, or the name of its trait for a default method. When
  methods of trait implementations in one file share a key, the second
  takes `#2`, the third `#3` and so on, in source order; any other repeated
  key fails the check, and so does a method whose self type has no path,
  such as a tuple.
- The methods that a `#[derive(..)]` of a production type defines, `clone`,
  `fmt`, `eq`, `assert_fields_are_eq`, `partial_cmp`, `cmp`, `hash` and
  `default`, are recorded with the same keys for the `derived` list of a
  target. They have no source text, and the check does not count them.

`verification/open.json` is generated from the `Open obligations` tables of
the `contract.md` of the components below `docs/domains/`, whose columns
the [component documents](conventions/documentation.md#component-documents)
fix. Each entry has the `item`, a function key or the path of a file or
directory below `kernel/`, which covers every function in it; the `kind`;
the `verified_state`, one of `reads`, `writes`, `reads and writes` and
`neither`, or `null` when the row does not say; the `carrier`, a neutral
description of the planned target and obligation that close the entry or
of the condition that lifts it; the `stage`, the release by which it is to
be closed or lifted; and the `contract`. The entries are sorted by item.
`cargo xtask formal check --write` writes the file first, unless a table
is malformed, and the check compares the committed file byte for byte with
what the contracts give.

`cargo xtask formal check` reports every problem and exits with 1 when
there is any:

- a problem of the inventory;
- a production function that is in no `proves` or `unclosed` list, is not
  the item of an entry of `open.json` and is not inside one whose item is a
  path;
- a malformed table, a row whose cells are more or fewer than those of the
  header, an item that two rows list, an entry whose stage is later than
  `0.2`, compared as numbers, so that `0.10` is later, and an `unsafe`
  entry that does not say whether it reads or writes verified state. The
  latest stage is the release after the one in work, and it rises by one
  release when work on the next release begins;
- a committed `open.json` that differs from what the contracts give;
- a broken rule of the registry ([proof targets](#proof-targets)), such as
  a key of a target that is no production function of the inventory;
- what the gate does not support yet: non-empty `premises` of a target, an
  `exclude` cut point and a model in `verification/models.json`.

No CI job runs it yet, nor does `cargo xtask check`: run it before
proposing a change to the kernel workspace, a contract or the registries.
The removal of a target, a theorem or a proved function, and any widening
of the trusted base, are reviewed through the registry rules of the
[guard](#guard) (planned), and `cargo xtask formal impact --base REV`
(planned) lists the targets that a change affects. A function without a
proof is never trusted by a proof and appears in a target's `unclosed` list
when reached.

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
