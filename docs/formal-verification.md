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
`verification/axioms.json`, the registry of the trusted base
`verification/tcb.json` and the waiver record `verification/waivers.json`
([waivers](#waivers)). Two specifications are registered, those of the
device-tree and page-tables components, each with its planned statements
and a planned target whose code does not exist yet
([specifications](#specifications)); no formal target, model, library
axiom, trusted item or waiver is registered. The pinned tools exist: the tool manifest
`verification/toolchain.json`, the reviewed Aeneas patch, the recipe of the
image that holds the tools, the workflows that build and publish it, the
pin of the published image, `verification/image-pin.json`, and
`cargo xtask formal toolchain-check`, which checks the manifest against the
Aeneas and Charon sources ([tools](#tools)).
`cargo xtask formal run` exists as the proof gate
([gate run](#gate-run)): it takes a snapshot of the gate inputs, exports
them, applies their rules, runs its phases and writes a receipt. Its phases
are the [qualification](#qualification) of the tools on the code shapes of
the qualification crate, with the three proofs about them; the extraction
of the [proof targets](#proof-targets), of which only two planned ones are
registered, which a whole run extracts only when a hand-written module
imports their generated modules, as none does yet; the
[base round](#base-round), which builds, audits and replays krepi's own
Lean, divided between the qualification job and the [lanes](#lanes): today
the qualification proofs and the definitions that they use, and the
specifications of the device tree and of the page tables with their
properties, their tests and the theorems that witness them, where the
theorems of planned statements are built but not audited; and the targets,
which build and audit the proofs of each target in a stage of its own and
then build each of its registered [mutants](#mutants) in a stage of its
own, which its proofs must reject. On a pull request, a first phase
records the [guard](#guard), which `cargo xtask formal guard` runs on its
own. With `--shard`, `cargo xtask formal run` runs one part of the gate,
the qualification job, a lane, whose base run `--comparator` follows with
its [comparator](#comparator), or the part of one formal target, and
`cargo xtask formal merge` combines the receipts of the parts of a commit
into the conclusion of the whole gate and of its three hard gates, the
axiom audits, the replay of `leanchecker` and the comparator, with the
[waivers](#waivers) that hold ([shards and merge](#shards-and-merge)); CI
runs the gate as these parts and merges them ([CI job](#ci-job)). `cargo
xtask formal receipt` says whether the record of a merge is current for
the checkout, and whether it is fresh ([current and fresh
records](#current-and-fresh-records)). The [calibration
target](#calibration-target), a crate with the shapes of the first kernel
targets and its proofs, runs through the same phases with `cargo xtask
formal run --calibration`, in the workflow `formal calibration` too.
`cargo xtask formal mutants` generates the source mutants of a target and
writes the list of those that survive ([source mutants and
survivors](#source-mutants-and-survivors)). `cargo xtask formal check`
holds the inventory of the production functions of the kernel workspace
against the targets and the open obligations ([legacy inventory and
admission](#legacy-inventory-and-admission)), and `cargo xtask formal
vectors` compares a component's frozen test vectors through its
specification with the results of its host tests ([test
vectors](#test-vectors)); the formal step of `cargo xtask check` runs
both, the second in the pinned image ([vectors in CI](#vectors-in-ci)).
`cargo xtask formal impact` lists the targets that a change affects
([commands](#commands)). A weekly toolchain canary runs the gate with the
tools of Aeneas main through the steps of `cargo xtask formal canary` and
records what they would break ([toolchain canary](#toolchain-canary)).
None of them verifies anything about the kernel. The cases taken from the
CAS project expect what the pinned tools give; for 27 of them this differs
from the expectation recorded with the earlier Charon and Aeneas, and each
such change is explained ([qualification](#qualification)). CI runs the
gate in the pinned image when the label `full-check` is added to a pull
request to `main` whose change affects it, on a manual run of `main` and
once a week, as the qualification job, a job for each lane, a part for
each formal target and their merge; four jobs judge the conclusion and
each hard gate in the record of the merge, and with `formal fast` and
`formal guard` they are the six checks of the gate, which the rules of
`main` require. On a push to `main`, a job reviews the record of the
merged head ([CI job](#ci-job)). Everything else on this page is planned:
the proofs of the registered statements, the formal targets of the kernel,
further specifications and the other commands of `cargo xtask formal`.
They are set up by porting the tooling of the CAS project and the
prototype tree, and this page changes with them. Nothing about the kernel
is proved.

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
| `verification/image-pin.json` | The published image that the CI jobs of the gate and the formal step of `cargo xtask check` run, by its digest ([image pin](#image-pin)) | Present |
| `verification/lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | The Lake project of the hand-written Lean and of the generated definitions, with the Lean toolchain and the packages of the Lake lock of the Aeneas Lean library ([qualification](#qualification)), and the library `KrepiRoot` of the root module that the [base round](#base-round) writes | Present |
| `verification/extraction.toml` | How Charon compiles each extracted crate ([extraction](#extraction)) | Present |
| `verification/Krepi/Spec/` | Specifications written from requirements, registered in `targets.json`; a component with a directory below [subject domains](domains/README.md) describes its own in the `specification.md` there, where it has one | Present |
| `verification/Krepi/SpecProperties/` | The invariants and the cross-cutting properties of the specifications, stated on them as statements ([specifications](#specifications)) | Present |
| `verification/Krepi/SpecTests/` | The specification tests, stated as statements, the builders of their inputs and the replay of the frozen test vectors of each component ([test vectors](#test-vectors)) | Present |
| `verification/Krepi/Statements/` | Statements: the propositions that registered theorems prove ([statements and proofs](#statements-and-proofs)) | Present |
| `verification/Krepi/Proofs/` | Proofs of statements and refinement proofs of production targets; the only directory of the Lake project outside the statement side ([statements and proofs](#statements-and-proofs)) | Present |
| `verification/Krepi/Models/` | Lean models of items that proofs reach without extracting them, and their differential check | Planned |
| `verification/Krepi/Qualification/` | Proofs about the qualification shapes | Present |
| `verification/Krepi/Qualification/Models/` | Definitions that the reviewed external declarations of three qualification cases use; they are not models ([qualification](#qualification)) | Present |
| `verification/externals/<Module>/` | Reviewed external declarations of a target or a qualification case (`FunsExternal.lean`, `TypesExternal.lean`), named by its `models` field | Present for qualification cases |
| `verification/targets.json` | The proof target registry | Present |
| `verification/shards.json` | The shard plan: for the qualification and for each target, the disk peak, the seconds and the cgroup memory peak that a run of CI measured, with the run and its commit; the disk guard of a run reads it ([shard plan and disk guard](#shard-plan-and-disk-guard)) | Present |
| `verification/lanes.json` | The lanes: the components and the shared hand-written modules of each lane of the base round, with its registered budget ([lanes](#lanes)) | Present |
| `verification/models.json` | The model registry ([models](#models)); `cargo xtask formal check` refuses a registered model | Present, empty |
| `verification/statements.json` | The statement hash, and each statement with its theorem and state ([statements and proofs](#statements-and-proofs)) | Present |
| `verification/axioms.json` | The axioms of the Aeneas Lean library that target theorems may use, each with its source and reason ([base round](#base-round)) | Present, empty |
| `verification/tcb.json` | Items of the trusted base: native decisions and patterns of generated axioms, whose classification comes later ([base round](#base-round)) | Present, empty |
| `verification/waivers.json` | The waiver record: each waiver of registered targets with its reason, scope, expiry and author ([waivers](#waivers)) | Present, empty |
| `verification/legacy.json` | Kept empty: production functions without a proof are listed in `open.json` ([legacy inventory and admission](#legacy-inventory-and-admission)) | Present, empty by design |
| `verification/open.json` | The open obligations of the production code, generated from the `Open obligations` tables of the contracts of the components ([legacy inventory and admission](#legacy-inventory-and-admission)) | Present |
| `verification/qualification/` | A small crate of code shapes and their expected tool outcomes (`cases.json`) | Present |
| `verification/qualification/calibration/` | The [calibration target](#calibration-target): a workspace with a root package and a member, its Lake project with its statements and proofs, its registries, shard plan and lanes, and the lists of survivors of its source mutants in `mutants/` | Present |
| `verification/mutants/` | The list of survivors of the source mutants of each target that has one, `<target>.json` ([source mutants and survivors](#source-mutants-and-survivors)) | Absent until a list is written |
| `verification/vectors/` | The frozen test vectors of the components whose contracts name them, one file for each component ([test vectors](#test-vectors)) | Present |
| `xtask/src/formal/` | The commands of `cargo xtask formal` | `toolchain-check`, `run`, `guard`, `check`, `mutants`, `vectors`, `canary`, `impact`, `merge` and `receipt` present, the others planned |

Generated Lean, extraction outputs, logs and receipts go to the ignored
`artifacts/formal/` directory, and the Lake build directory
`verification/.lake/` is ignored as well. Each run of the gate has a
directory `artifacts/formal/runs/<id>/`, where `<id>` is the Unix time of
its start, its process number and a count: `receipt.json`, or
`base.json` for the base run of a lane
([shards and merge](#shards-and-merge)), `logs/` with
the two output files of each command, and `work/` with the export of the
gate inputs, the home and temporary directories of the tools; in
`cases/`, the extraction and the Lake stage of each qualification case; in
`targets/<name>/`, the extraction of each target that the run extracts
in `extract/` and its stage in `stage/`, with the root module, the audit
file and the range printer `Ranges.lean` of a selected formal target, and
the copied package, the extraction, the stage and the home and temporary
directories of each registered mutant in `mutants/<mutant>/`; in
`mutants/<target>/`, those of each source
mutant of a run of `formal mutants`, removed once it is judged; in `base/`, the stage of the base
round with the root module `Krepi.lean` that the run writes, its audit
file `Audit.lean` and its heartbeat copies in `.heartbeats/`, and
`mktree`, the input of
`git mktree` for the statement hash of the round; and `mktree`, the same
input for the guard phase. The
root module is written only there, never in the checkout. Generated
definitions are never edited.

At its end, after the second snapshot, a run of `cargo xtask formal run` or
`cargo xtask formal mutants` removes `work/`, so that its directory keeps
its receipt and `logs/`; with `--keep` it keeps `work/`, as
[editing proofs](#editing-proofs) needs. A work directory that cannot be
removed, or whose removal ends after the deadline of the closing steps, is
a tool failure of the run. A stop signal ends a run without a receipt and
with its work directory, unless the signal arrives once the run has
started to remove it. During a run, the Cargo target directory of each
extraction is removed when the extraction ends, and the LLBC file and the
output of Aeneas of a qualification case, also those of each of its
parts, once the case is concluded, unless the run keeps its work
directory.

A comparison of `cargo xtask formal vectors` has a run directory too,
without a receipt, and keeps all of it: `logs/`, and in `work/` the
home and temporary directories, its stage, the vector file `vectors` and
the result file `results` of the replay; the host tests write their result
files below `artifacts/formal/vectors/` ([test vectors](#test-vectors)).
The jobs of the toolchain canary keep their trees, downloads and records
below `artifacts/canary/`, the parts that its verdict reads below
`artifacts/canary/parts/`, and their image builds, as the image workflows
do, below `artifacts/image/` ([toolchain canary](#toolchain-canary)).
`cargo xtask formal merge` writes its record and summary to
`artifacts/formal/merge/` ([shards and merge](#shards-and-merge)), where
`cargo xtask formal receipt` reads the record by default
([current and fresh records](#current-and-fresh-records)). In CI,
the jobs of the gate pack the `logs/` of their runs into
`artifacts/formal/logs.tar.gz`, and the merge job downloads the artifacts
of the parts below `artifacts/formal/parts/`: a single artifact into that
directory itself, several each into a directory of its own.

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
the gate ([CI job](#ci-job)) and the formal step of `cargo xtask check` run.
It has schema 1:

| Field | Content |
| --- | --- |
| `schema` | `1` |
| `repository` | The repository of the image in the registry, without a tag or a digest |
| `digest` | The digest of the image: `sha256:` and 64 lowercase hexadecimal digits |
| `revision` | The commit of `main` from which `formal image publish` built and published the image, for readers; nothing checks it |

The file lies outside `verification/image/` and the other paths that start
the image workflows, so changing it builds and publishes no image, and the
image does not contain it. It has these readers:

- `.github/workflows/formal.yml`, `formal-measure.yml` and
  `formal-calibration.yml` name the image as `<repository>@<digest>` in
  their variable `IMAGE`, which every container of these workflows runs,
  after a pull that takes the image by that digest.
- The formal step of `cargo xtask check` reads the pin of the checkout,
  fails unless it has schema 1, a repository without a tag or a digest, a
  digest and a revision, and runs its containers on
  `<repository>@<digest>` with `--pull never`
  ([vectors in CI](#vectors-in-ci)). Each job that runs the check, in
  `check.yml`, `full.yml`, `nightly.yml` and `cache.yml`, first pulls that
  reference, which it reads from the pin with `jq`.
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
| `HOME` | A new, empty directory of the run, or of the mutant whose command it is | All |
| `TMPDIR` | A directory of the run, or of the mutant whose command it is | All |
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
   the gate on its pull request, which the label `full-check` starts, is
   the first run of the new image ([CI job](#ci-job)).

When the first changes a version or digest that the gate compares with the
image ([image pin](#image-pin)), the CI job of the gate still runs the image
of the old pin, so the gate stops as a tool failure on that pull request and
on every run of `main` until the second is merged. Once the second is
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
`main`; a manual run of another branch skips its jobs. It runs the gate with
the tools that the pins follow upstream: the head of Aeneas's `main`, the
Lean release that its `backends/lean/lean-toolchain` names, the Charon
commit of its `charon-pin` and the Rust nightly of that Charon's
`charon/rust-toolchain`, each resolved when the run starts. It records what
an upgrade to them would break, and changes nothing: it is not a required
check, runs on no pull request and blocks no merge. It runs the gate in
the parts of the [CI job](#ci-job) ([shards and merge](#shards-and-merge)),
in jobs on GitHub-hosted `ubuntu-24.04-arm` runners, which may only read
the repository's contents, log in to no registry, publish no image and
push nothing:

- `canary limits` resolves the head of Aeneas's `main` once, with
  `git ls-remote`, and `cargo xtask formal canary limits` gives the rows of
  the run from `verification/targets.json` and `verification/lanes.json`:
  the qualification row, the row of each lane, with its registered budget,
  and the row of the part of each formal target, by its part, with the
  budget of the part; planned targets have none. The steps of a lane and
  of a part have the limits that the job `formal limits` of the CI job
  gives them, and every job the limits of the steps that it runs and 5
  minutes, so a step's limit, never the job's, ends a long step, and the
  steps that record a part always run. A row whose job would need more
  than the 360 minutes of a hosted runner fails the step.
- `toolchain canary <part>`, one job for each row, builds the image and
  runs its part in the steps below, and uploads what it leaves as the
  artifact `formal-canary-part-<part>-<run>-<attempt>`, with `-` for `/`.
- `toolchain canary verdict` concludes the run from those artifacts after
  the rows, also when one of them failed.

The steps of a row end its job at the first that fails, each by its id:

1. `runner`, `disk`, `sampler`, `xtask` and `copy`: record the runner and
   refuse a root user or a checkout of another owner, record the disk,
   remove preinstalled software and sample the disk every 15 seconds as the
   image workflows do, here until the end of the part, build xtask and copy
   it for the comparator of a lane as the job `formal lane` does;
2. `resolve`: fetch the head of Aeneas's `main` that `canary limits`
   resolved into `artifacts/canary/aeneas/`, and, when its `charon-pin` has
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
   tool](#changing-a-tool) does, under `.github/scripts/deadline.sh` with
   a deadline of 52 minutes, which writes its exit status for the verdict,
   tag it locally, and record it as the image workflows do;
7. `fill`: commit the derived files in the job's checkout;
   `cargo xtask formal canary fill` sets the switch export of
   `linux-aarch64` to the `opam.switch_export_sha256` of the image and
   writes the statement hash of that commit into
   `verification/statements.json` where it differs, and a second commit
   holds both. Both commits have the identity of the canary and the commit
   time of `main`, so rows whose images give the same switch export make
   the same commits. The commits are local and never pushed;
8. `probe` and the part: probe a container of the image and run the part
   in it with the flags, variables and deadlines of the CI job, but
   without `KREPI_FORMAL_IMAGE` and without a trigger, under `deadline.sh`,
   which writes its exit status for the verdict as well. The qualification
   row runs `gate`, the qualification job, `cargo xtask formal run --shard
   qualification`, as the job `formal run` does; the row of a lane runs
   `lane`, its base run, `cargo xtask formal run --shard lane/<name>
   --keep`, and then `comparator`, its [comparator](#comparator), on the
   stage that the base run kept, in a container of its own, as the job
   `formal lane <name>` does, also when the base run failed; and the row of
   a part of a formal target runs `shard`, its part, as the job
   `formal shard <name>/<i>` does. The comparator runs `lake comparator` only
   on the units whose statements the base round verified and audited, and
   records each other unit as `NOT_RUN` ([formal
   upgrade](formal-upgrade.md#canary-verdicts)).

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
exits with 0 only when its verdict is `PASSED`. A row writes the outcome
of each of its steps into `artifacts/canary/part.json`. The step `verdict`
reads what the rows of the attempt uploaded itself, not through
`cargo xtask formal merge`, as the receipts of the canary name no image:
the qualification job, each lane and the part of each formal target of
the registry are its parts, and each row must have left one record and
each part one receipt, which for a lane its comparator writes; the step
`lane` is judged by the base record that the base run of the lane left.
Receipts of more than one commit, tree, run or attempt are a defect of the
canary. Otherwise the run gets the finding of the first part that did not
pass, in that order with the lanes and the parts each by name, at the
first step of its row that did not pass, or else that of the part, with
the step, after the part for a lane and the part of a target, and the
commit of `main` in its detail. The detail starts instead with `limits` when the job `canary
limits` did not succeed, with `parts` when the registry cannot be read,
the receipts disagree or the run passed, and with the part of the row,
without a step, when a row left no record or more than one. The job passes
only on `PASSED`. A run is repeated whole, never by its failed jobs alone,
so that its parts are of one attempt:

| Finding | When |
| --- | --- |
| `PASSED` | Every step of every row passed, and each part exited with 0 and left one complete `VERIFIED` receipt |
| `BROKEN` | The patch does not apply; Aeneas main has a form that the committed checks refuse too; the build failed in a stage of the tools, `aeneas-source`, `lean`, `rust-toolchain`, `charon-build`, `aeneas-build` or `backend`; or a part exited with 1 and left one receipt that is `REJECTED`, `TOOL_FAILURE`, `BUDGET` or `STALE`; each without a text of the two rows below |
| `DEFECT` | The receipts of the parts are not of one commit, tree, run and attempt; the tool checks fail on the derived manifest; a field cannot be derived; or the error or the output of the step that the failure block of the build log shows, or a failure or the reason of a unit that is not `VERIFIED` in a receipt, holds a check of what was installed against a pin, such as `lean reports` or `the switch export has SHA-256` of the recipe, a failure of the gate that starts with `image:`, or a statement hash that the snapshot does not have |
| `FAILED` | The job `canary limits` did not succeed, or a row left no record or more than one; a step was cancelled or skipped, has no outcome, or succeeded without a record that passed; any other step failed; the build reached its limit, or the runner ended it, or it failed in another stage or without a BuildKit failure block after its first error; the text holds a full disk, a network error or a cancelled build, or a check of the gate's own inputs; or a part wrote no exit status, left no single receipt that can be read, exited with 1 and left a receipt that is `NOT_RUN`, which the [disk guard](#shard-plan-and-disk-guard) refused, or exited with another status, which is an error of the run and not a verdict |

A text of an unknown shape is never a breakage: a breakage needs a failed
stage of the tools without the text of a defect or a failure, or a verdict
of the gate on a receipt that can be read. A text of a defect counts before
one of a failure. Of the build log, the error line and the output lines of
the failure block are read; only the script that the error line of a failed
process quotes, which the first line of the block also names, is left out,
since it holds the recipe's own texts. The summary of the workflow run and
one annotation give the finding, and the artifact
`formal-canary-<run>-<attempt>` holds `verdict.json`. The artifact of each
part holds, from `artifacts/canary/`, the records, the outputs of
`resolve`, `derive` and `toolchain-check`, the manifest of the build and
that of the gate, the diff of the derived files, the two commits and the
exit statuses of the build and of its parts; from `artifacts/image/`, the
build log, `versions.json`, the switch export, the layers and the disk
measurement, whose least available space and largest Docker root, which its
summary calls those of the build, cover the probe and the parts too; and
the record of the job, the event, the receipts and the logs of its parts.

The canary leaves out the notice check of the image workflows, which does
not depend on the tools, and `verification/image/non-root-check.sh`,
which is written for the committed nightly; the probe and the gate's check
of the image cover what the gate needs. The build takes Mathlib's build
cache for the Mathlib commit of the new lock; without one, it builds
Mathlib from source and reaches its limit, which fails the run. Each row
builds the image itself, as the image is not passed between jobs. The
receipts of the canary have the mode `MANUAL` and no image reference, and
the gate compares the image with the derived manifest. They are no
evidence about krepi, which only the gate in the pinned image gives. [Formal
upgrade](formal-upgrade.md#canary-verdicts) says what follows each
finding.

## Commands

The commands of `cargo xtask formal` follow the design of the gate.
`cargo xtask formal toolchain-check`, `cargo xtask formal run`,
`cargo xtask formal guard`, `cargo xtask formal check`,
`cargo xtask formal mutants`, `cargo xtask formal vectors`,
`cargo xtask formal canary`, `cargo xtask formal impact`,
`cargo xtask formal merge` and `cargo xtask formal receipt` exist; the
others are planned.

| Command | Purpose |
| --- | --- |
| `cargo xtask formal toolchain-check --aeneas DIR --charon DIR` | Checks Aeneas and Charon checkouts and the Aeneas patch against the tool manifest ([tool checks](#tool-checks)) |
| `cargo xtask formal run [--target NAME]... [--shard NAME [--comparator]] [--calibration] [--keep]` | The proof gate on a snapshot of the gate inputs, with its receipt ([gate run](#gate-run)); `--target` runs only the part of the named targets, their extraction and the phase `targets`, `--shard` only the qualification job, the base run of a lane, whose [comparator](#comparator) `--comparator` runs after it, or the part of a formal target ([shards and merge](#shards-and-merge)), `--calibration` runs in the layout of the [calibration target](#calibration-target), and `--keep` keeps the work directory of the run ([layout](#layout)). Its phases are, on a pull request, the [guard](#guard), which records its rules; then the [qualification](#qualification), the extraction of the selected and the formal targets, the [base round](#base-round) and the selected [targets](#proof-targets) with their [mutants](#mutants), which every run of the whole gate has |
| `cargo xtask formal guard --event PATH` | Checks a pull request, given by the JSON of its `pull_request` event, against the rules for changes of statements, proofs, sources and registries ([guard](#guard)) |
| `cargo xtask formal check [--write] [--calibration]` | The inventory of the production functions against the `proves` and `unclosed` lists of the targets and against `open.json`, which it compares with what the contracts give, the rules of the registry ([proof targets](#proof-targets)) and of the waiver record ([waivers](#waivers)), the lists of survivors ([source mutants and survivors](#source-mutants-and-survivors)), the shard plan and the budget of each shard ([shard plan and disk guard](#shard-plan-and-disk-guard)), the lanes ([lanes](#lanes)) and the refusal of what the gate does not support yet ([legacy inventory and admission](#legacy-inventory-and-admission)); `--write` first writes `open.json`, and `--calibration` checks the calibration target, which no contract describes. It runs no tool and proves nothing |
| `cargo xtask formal vectors [DOMAIN/COMPONENT]` | Replays the test vectors of a component's contract, or of each component whose contract names a replay, through its specification with the pinned Lean and compares the results line by line with those that its Rust host tests wrote ([test vectors](#test-vectors)). It writes no receipt and proves nothing |
| `cargo xtask formal canary STEP [--outcomes TEXT]` | Runs one step of the toolchain canary on what its jobs fetched and built: give the rows of the run and their `limits` from the registry, `resolve` and `derive` the tool manifest of Aeneas main, check that the `patch` applies, `fill` the switch export and the statement hash, or conclude the run with its `verdict` from what its parts left and, with `--outcomes`, the result of the job `canary limits` ([toolchain canary](#toolchain-canary)). It fetches nothing and proves nothing |
| `cargo xtask formal mutants TARGET [--operator NAME]... [--calibration] [--keep]` | Generates the source mutants of a formal target with every operator, or those named, runs each through a run of the gate on the target and writes the list of its survivors ([source mutants and survivors](#source-mutants-and-survivors)); `--calibration` takes a target of the calibration, and `--keep` keeps the work directory of the run, as for `run` |
| `cargo xtask formal impact --base REV` | Lists, one item per line, the merge base of `REV` and `HEAD`, each path changed since with its Git status, without rename detection, the decision, `unaffected` when no changed path lies within a [gate input](#gate-inputs-and-snapshot) and `affected` otherwise, and the registered targets that the change affects, with their states: every target when an input of extraction changed, and otherwise each whose entry in `verification/targets.json` changed and each with a changed file of its `proof_modules`. A registry that cannot be read at the merge base, as after a change of its schema, counts as one without targets, so that every target is listed, after a line `unreadable verification/targets.json at the merge base: <why>`. Paths, names and that reason are printed escaped, so that none splits a line. It decides nothing, and exits with 1 only on a base that is not a revision or when Git or the registry at the head cannot be read |
| `cargo xtask formal merge [--calibration] RECEIPT...` | Combines the receipts of the qualification job, of each lane and of the part of each formal target of the commit checked out into the conclusion of the whole gate, which passes when every unit and part outside the [waivers](#waivers) that hold is `VERIFIED`, and of its three hard gates, the axiom audits, the replays of `leanchecker` and the comparator, with its record and summary ([shards and merge](#shards-and-merge)); `--calibration` merges those of the calibration target |
| `cargo xtask formal receipt [--require-fresh] [RECORD]` | Judges the record of a merge, by default `artifacts/formal/merge/record.json`, against the checkout ([current and fresh records](#current-and-fresh-records)): `CURRENT` when it has the gate inputs of the clean checkout, the pinned image and one conclusion for each registered unit and is complete, `VERIFIED` and passing, and `WAIVED` when it passes only within waivers that still hold; `--require-fresh` also requires the trigger of a run of CI, no planned statement and no waiver. It exits with 0 when the record is current, and fresh when asked, 3 when it is waived, 1 otherwise and 2 on a usage error. It runs no tool and proves nothing |

`cargo xtask check` does not run the gate, which needs the pinned tools;
its formal step runs `cargo xtask formal check` and
`cargo xtask formal vectors` ([vectors in CI](#vectors-in-ci)).
CI runs the gate as its parts and their merge when the label `full-check`
is added to a pull request to `main` whose change affects it, on a manual
run of `main` and once a week, and four jobs judge the record of the merge
([CI job](#ci-job)): `formal merge` its conclusion, which passes a failure
that a committed [waiver](#waivers) covers, and `formal axioms`,
`formal leanchecker` and `formal comparator` its hard gates. On a pull
request, the jobs `formal fast` and `formal guard` run
`cargo xtask formal impact` and `cargo xtask formal guard`. The rules of
`main` require these six jobs, so a pull request merges only when they
pass on its head ([CI job](#ci-job)). On a push to `main`, the job
`formal receipt review` judges the record of the merged head with
`cargo xtask formal receipt`.

## Gate run

`cargo xtask formal run` runs the gate on the commit checked out, the
snapshot commit, and writes a receipt of the run, whether it passes, fails
or stops on an internal error. Its code is in `xtask/src/formal/`: the gate
inputs, the change since a merge base and the targets that it affects in
`paths.rs`, the commands in `process.rs`, their classes and the
statuses in `outcome.rs`, the receipt in `receipt.rs`, the extraction in
`extract.rs`, the Lake stages, the source rules and the allowlist in
`lean.rs`, the qualification in `qualify.rs`, the base round in `base.rs`,
the statement side and the guard in `guard.rs`, the registry and its rules
in `registry.rs`, the check of a target's registration against its
extraction in `classify.rs`, the [comparator](#comparator) in
`comparator.rs`, the installation of its generated files and
reviewed external declarations in `externals.rs`, the shard plan, the
disk guard and the removals in `storage.rs`, the lanes and their rules in
`lanes.rs`, the shard limit, the parts
of the gate and their merge in `merge.rs`, and the run, with the phases of
the targets, in `run.rs`.

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
   name given with `--target`, and the target of the part of a target as a
   formal target, and the lanes of the export the lane of a run of a lane
   ([shards and merge](#shards-and-merge));
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
   The run is also rejected when it is to extract kernel targets and
   `kernel/Cargo.toml` has no `[package]` named `krepi-kernel`, the root
   package that kernel targets are extracted from. The targets that a run
   selects are every formal target of the registry for a whole run, and
   those that `--target` names, planned ones included, for a run with
   `--target`; a whole run extracts these and, for the base
   round, the formal targets that it does not select and the planned
   targets whose generated modules a hand-written module imports
   ([proof targets](#proof-targets)), so a whole run extracts no other
   planned target, and a run of
   `cargo xtask formal run --target` extracts the named targets alone.
   The qualification job selects and extracts no target; the base run of
   a lane selects none and extracts the targets of the lane for its base
   round but the formal ones of the waivers that hold
   ([waivers](#waivers), [base round](#base-round)); the part of a
   target selects its target and extracts no other. A whole run whose
   registry has no formal target and no such planned target selects and
   extracts none, and the workspace may then have no root package.
   When the run selects targets, it takes the inventory of
   the exported workspace for their registration checks
   ([legacy inventory and admission](#legacy-inventory-and-admission));
7. when no earlier step has failed or rejected the run, refuses it unless
   its file system had 1.5 times the disk peak of its parts free at its
   start ([shard plan and disk guard](#shard-plan-and-disk-guard)), and
   then lists the Aeneas Lean library of the installation and Lean as the
   [base round](#base-round) does, before the first phase.

A tool failure in one of these steps ends them: the later steps do not run.
A rule that rejects the run in step 4 does not. Every later step reads the
gate inputs from the export, never from the checkout. After a clean start,
the run takes the objects of the gate inputs again at the end, at the
commit checked out then, and runs `git status` again: when an object
differs, or the gate inputs are not clean at the end, the run is `STALE`,
with one failure that names the gate inputs whose objects differ and the
records of `git status`. Before that, after the last phase, also when a
phase stopped, the run lists the installation again; a difference is a
tool failure of the run that names up to 20 paths, so that a command of
the extraction, of a target or of a mutant that writes the installation
fails the run as one of the qualification or the base round does, and so
is a listing that cannot be taken then.

`paths.rs` also gives the change between two commits, which the
[guard](#guard) and `cargo xtask formal impact` share: their merge base and
the paths changed from it to the second commit, each with its Git status,
from `git diff --name-status --no-renames` with `--` after the two commits,
so that a moved file counts as the deletion of its old path and the addition
of its new one, and a file named as a revision, such as `HEAD`, is a path. A
change leaves the gate unaffected when none of its paths is a gate input or
lies below one, compared by whole path components, so that `kernelx/a.rs`
does not lie below `kernel/`; otherwise it affects the gate.

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
- the rest of the budget of the gate, 7,200 s from the start of the run
  and the budget of each target that the run selects; 7,200 s for the
  qualification job; 300 s, the registered budget of the lane and 600 s
  for the runs of a lane, whose comparator run ends by the deadline of its
  base run; and 300 s and the budgets of its targets for the part of a
  target and for a run of `cargo xtask formal run --target`
  ([shards and merge](#shards-and-merge));
- for a command of the unit of a target, the rest of the budget of the
  target: the budget less the time during which a command of the unit or
  of a unit of its mutants has run so far, whichever phase ran it
  ([proof targets](#proof-targets)).

The steps after the phases, the second snapshot, the removal of the work
directory and the receipt, have 300 s beyond the gate's budget. A command
whose limit is used up, 0 s as the receipt writes it, does not start and is
`NOT_RUN`. When a command reaches its limit, or ends by itself, the run
kills its process group, collects the command and waits up to 60 s, beyond
the command's limit, until no process of the group is left; a process that
is still there makes the command a tool failure. The run restores the
default disposition of `SIGCHLD` when it starts, without which the system
could collect an ended command before the kill. Each command is printed
when it ends.

A signal from the terminal does not reach a running tool, whose group is
its own. SIGINT and SIGTERM stop the run instead, also when they were
ignored when it started, and so does SIGHUP unless it was ignored then, as
`nohup` leaves it: the run kills the group of each command that is
running, collects one of these commands, waits for its group as above,
and ends by the same signal, without a receipt. A signal that comes
between two commands takes effect before the next command starts or before
the receipt is written.

### Shard plan and disk guard

The shard plan is `verification/shards.json`, and
`verification/qualification/calibration/shards.json` for the
[calibration target](#calibration-target). It has schema 1 and `parts`, an
array with one entry for each part of the gate that a run of CI has
measured: `qualification`, `lane/<name>` for a lane of the
[lanes](#lanes), or `target/<name>/<i>` for a part of a registered target,
each named as its receipt names its part. It is written by hand from the
receipts of runs on a standard `ubuntu-24.04-arm` runner, never by a run.
The entries are those of the runs that measured the parts:
`verification/shards.json` has `qualification`, `lane/fdt` and
`lane/page-tables`, and the plan of the calibration target has
`qualification` and `target/calibration/1`, the part that once held every
mutant of its target. Each entry has these fields:

| Field | Content |
| --- | --- |
| `part` | `qualification`, `lane/<name>` or `target/<name>/<i>` |
| `disk_peak` | The disk peak of the part in bytes: `disk_available_at_start` less `disk_least_available` of the measuring receipt ([receipt](#receipt)) |
| `seconds` | The `seconds` of the measuring receipt |
| `cgroup_memory_peak` | The `cgroup_memory_peak` of the measuring receipt, in bytes |
| `run_id` | The identifier of the workflow run that measured it |
| `commit` | The commit that it ran on |

For example, with values that are only an illustration:

```json
{
  "schema": 1,
  "parts": [
    {
      "part": "qualification",
      "disk_peak": 600000000,
      "seconds": 1100.0,
      "cgroup_memory_peak": 10000000000,
      "run_id": "1234567890",
      "commit": "0123456789abcdef0123456789abcdef01234567"
    }
  ]
}
```

`cargo xtask formal check` refuses a plan that does not parse, of another
schema or with a field that it does not know, a part listed twice, and a
part that is neither `qualification`, a lane of the lanes nor a part of a
registered target; it lists the parts of the formal targets that the plan
has no entry for, which is not a problem, as a part is measured once it
runs.

Every formal target has its parts, `target/<name>/<i>` from 1: those that
the registry gives it, at most 4, or else one
([proof targets](#proof-targets)); a planned target has none. The shard
limit is 3,300 s: the wall-clock limit of the gate, 3,600 s, less the time
of the merge, 300 s. `cargo xtask formal check` refuses a part of a target
whose registered budget is more than the shard limit, whatever the workers
of the part, in either layout ([proof targets](#proof-targets)): the
budget counts the time during which a command of its target runs,
whichever worker runs it, and the run of the part has a deadline of 300 s
and that budget from its start. Two workers build the mutants of a part
side by side, each in a stage of its own that starts from the build of its
target ([registered mutants](#registered-mutants)). On a standard
`ubuntu-24.04-arm` runner the one part of the calibration target, with its
30 mutants built one after another, took about 400 s, against its
registered budget of 3,000 s, and the parts of the gate stayed well within
the wall-clock limit, the memory and the disk of the runner.

The disk guard of a run, after the steps of the gate inputs and before the
first phase, reads the plan of the export. A run of a part counts that
part alone: the qualification job `qualification`, both runs of a lane
`lane/<name>` and a part of a target `target/<name>/<i>`. Any other run
counts `qualification` and the parts of each target that it selects: a
whole run sums the qualification and every part of every formal target,
and a run with `--target` or of `formal mutants` the qualification and the
parts of the named targets. A part
without an entry counts 8 GiB, 8,589,934,592 bytes, and a part listed
twice its largest peak. When the bytes available on the file system of the
run directory at the start are less than 1.5 times the sum of the disk
peaks of its parts, the guard refuses the run: no phase runs, the run has
one failure `NOT_RUN` that gives both numbers, every registered unit is
`NOT_RUN`, and the run is `NOT_RUN` and not complete, and exits with 1. A
reading of the free space at the start that cannot be taken, or a plan
that cannot be read, is a tool failure of the run before its phases.

From its start until its phases and its second snapshot have ended, a
thread of the run reads the bytes available on the file system of the run
directory every second and skips a reading that cannot be taken;
`disk_least_available` of the receipt is the least of these readings and
the one at the start. A thread that cannot be started, or whose reading
panics, is a tool failure of the run.

### Lanes

The lanes are `verification/lanes.json`, and
`verification/qualification/calibration/lanes.json` for the
[calibration target](#calibration-target). They divide the hand-written
modules of the Lake project, its Lean files below `Krepi/`, between the
qualification job and the lanes of the base round, each with a registered
budget, and the gate runs each lane as a part of its own
([shards and merge](#shards-and-merge), [base round](#base-round));
`cargo xtask formal check` and the job `formal limits` of the
[CI job](#ci-job) check them. They have
schema 1 and `lanes`, an array with one entry for each lane, with these
fields; a field that the table does not list is refused:

| Field | Content |
| --- | --- |
| `name` | The name of the lane, of lowercase letters, digits and hyphens, starting with a letter or a digit |
| `components` | The components of the lane, each the name of its directories `Krepi/<layer>/<component>/` in the layers `Spec`, `SpecProperties`, `SpecTests`, `Statements` and `Proofs`, which is the `module` of its targets ([proof targets](#proof-targets)) |
| `modules` | The shared modules of the lane, by name, none when the field is left out |
| `budget` | The registered budget of the lane in seconds, 2,400 when the field is left out |

Each hand-written module belongs by its file to the qualification job when
it lies below `Krepi/Qualification/`, to the lane of its component when it
lies in the directory of a component, and otherwise it is a shared module,
which belongs to the lane that lists it. The shared modules count as one
component, so one lane lists them all.
`verification/lanes.json` has the lane `fdt`, with the component `Fdt` and
the shared module `Krepi.Statements.Basic`, and the lane `page-tables`, with
the component `PageTables`. The Lake project of the calibration target has
no directory of a component: its lanes have the lane `calibration`, with
the component `Calibration` of its formal target and the shared modules
`Krepi.Calibration.Statements` and `Krepi.Proofs.Calibration`. Each lane has
the budget 2,400 s.

`cargo xtask formal check` refuses, in either layout, lanes that do not
parse, of another schema or with a field that it does not know, and:

- a lane name that is not of lowercase letters, digits and hyphens starting
  with a letter or a digit, or that another lane has;
- a component, or a listed module, in two lanes or twice in one, and a
  listed module that is no shared module;
- a lane whose registered budget and the 600 s for the extraction of its
  targets, the extraction margin, are more than the shard limit of 3,300 s
  ([shard plan and disk guard](#shard-plan-and-disk-guard)), so that a lane
  has at most 2,700 s;
- a component of a hand-written module that no lane holds, a shared module
  that no lane lists, and shared modules in two lanes;
- a formal target whose `module` is no component of a lane; a planned
  target needs no lane, and a component of a lane needs no hand-written
  module.

The lanes are neither a registry nor on the statement side, so the
[guard](#guard) requires no label for a change of them. The job
`formal limits` fails on a lane name that is not of these characters or
that another lane has, on a component in two lanes, and on a lane whose
budget and the extraction margin are more than the shard limit, as the
check does ([CI job](#ci-job)); the other rules are the check's alone. The
merge checks that the base rounds of the qualification job and of the
lanes held the modules that the lanes give them
([shards and merge](#shards-and-merge)).

### Shards and merge

The gate runs as parts of one commit: the qualification job,
`cargo xtask formal run --shard qualification`; each lane of the
[lanes](#lanes), in two runs, its base run,
`cargo xtask formal run --shard lane/<name> --keep`, and then its
comparator run, `cargo xtask formal run --shard lane/<name> --comparator`;
and each part of each formal target of the registry,
`cargo xtask formal run --shard target/<name>/<i>`
([proof targets](#proof-targets)). `cargo xtask formal merge` combines
their receipts into the
conclusion of the whole gate. A run without `--shard` and `--target` has
every phase in one process, with one base round over every hand-written
module; local runs, the measurement jobs of the workflow `formal measure`
such as `leanchecker fresh` ([CI job](#ci-job)) and `formal mutants` use
it, and its receipt is no part of a merge. `--shard` cannot be given with
`--target`, and `--comparator` only with `--shard lane/<name>`: otherwise
the command exits with 2 before a run starts.
In CI the jobs `formal run`, `formal lane <name>`, which runs the
comparator run of its lane after its base run, `formal shard <name>/<i>` and
`formal parts` of the workflow `formal` run these parts and their merge,
and the workflow `formal calibration` runs those of the calibration
([CI job](#ci-job), [calibration target](#calibration-target)); the
[toolchain canary](#toolchain-canary) runs the parts without a merge. These parts
and their merge are the default way of running the gate in CI, and the
jobs `formal merge`, `formal axioms`, `formal leanchecker` and
`formal comparator` of the workflow `formal`, which judge the record of
the merge, are among the required checks of `main`.

- **The qualification job** has the [guard](#guard) on a pull request, the
  [qualification](#qualification) and its [base round](#base-round): that
  of the modules below `Krepi/Qualification/`, with the generated modules
  of the proof cases of the qualification, and the checks of every
  hand-written module, the statement hash, the file and source rules, the
  list of the modules with the part that holds each, and what the
  [waivers](#waivers) that hold leave out of them. It extracts no target
  and runs none. Its budget is the gate's 7,200 s, and its disk guard
  counts `qualification` alone.
- **The base run of a lane** has the extraction of the targets of the
  lane, whose commands are those of the unit `base/lane/<name>` of its
  round, and the base round of the lane: its own hand-written modules,
  with the generated modules of its targets, built, audited and replayed
  from a root module of their own. Its deadline is 300 s for its start and
  its closing steps, the registered budget of the lane and 600 s, the
  extraction margin, which the phase `extraction` has: at most the shard
  limit of 3,300 s ([lanes](#lanes)). It writes its receipt in its run
  directory as the base record of the lane, `base.json` with schema 1, in
  place of `receipt.json`, and keeps its stage with `--keep` for the
  comparator run. Its disk guard counts the lane.
- **The comparator run of a lane** has the phase `comparator` alone
  ([comparator](#comparator)): it takes the one base record of the lane of
  the same commit, tree, image and run of CI below the runs directory,
  continues the deadline of that base run, checks the proved statements of
  the lane in the stage that the base run kept, and writes the receipt of
  the lane, below. Its phase has at most 1,800 s, and its disk guard counts
  the lane.
- **A part of a target**, `target/<name>/<i>` of the `k` parts of its
  target, has the extraction of that formal target, whose commands are
  those of its unit, and the phase `targets` for it: its build, the seed,
  type check, audit, declaration ranges and the registered
  [mutants](#mutants) of the part. Only the first part judges the target,
  its build, type check, audit and declaration range, and concludes its
  unit; each other part builds the seed alone, without judging it, and
  runs its mutants on it ([proof targets](#proof-targets)). It has no
  guard, qualification or base round, and lists the hand-written Lean
  modules of the snapshot as the base round does, without building or
  auditing them, which the lanes do. Its budget is 300 s for its start and
  its closing steps and the registered budget of the part, which its
  extraction shares. Its disk guard counts its part alone. A part of a
  planned or unknown target, or one that its target does not have, is a
  tool failure before the phases. Its receipt records the part and its
  seed in `part` ([receipt](#receipt)).
- **A run of `cargo xtask formal run --target NAME...`** runs the named
  targets in the same way, each whole, its unit and every mutant of its
  parts: their extraction, planned targets included, and the phase
  `targets` for the formal ones, without the guard, the qualification and
  the base round, which a run of `cargo xtask formal mutants` keeps. Its
  budget is 300 s and the registered budgets of its targets, each the sum
  of those of its parts. Its receipt is `SCOPED` and no part of a merge.
- **The receipt of a part** names its part in `shard` and has the mode
  that `KREPI_FORMAL_TRIGGER` gives ([receipt](#receipt)), `MANUAL`
  without it, never `SCOPED`; it is complete by the rule of a run of the
  whole gate over its own units ([results](#results)).

The receipt of a lane is that of its comparator run, which reads the base
record again as it ends: a record whose SHA-256 is not the one that the
run took at its start is a tool failure of the run. Otherwise the receipt
holds the phases, units, failures, extracted targets, base round and lane
record of the base run with its own; the commands of the base run, with
the paths of their logs from the run directory of the comparator run,
`../<run>/logs/...`, and then its own, numbered after them and timed from
the start of the base run; the start and the budgets of the base run, the
sum of the seconds of both runs, the larger memory peaks and the least
free disk of both and the free disk at the start of the base run; and
`base_record`, the SHA-256 of the base record, the run, start and seconds
of the base run, and the start and seconds of the comparator run
([receipt](#receipt)). When the comparator run finds no base record of the
lane, or more than one, its receipt has its own units alone, `NOT_RUN`,
and is a tool failure ([comparator](#comparator)).

`cargo xtask formal merge [--calibration] RECEIPT...` runs on the host in a
checkout of the commit of the receipts; it pulls no image and runs no proof
tool. It reads the registry, `statements.json`, the qualification cases,
the lanes and the waiver record of the checkout, those of the calibration
target, which has no waiver record, with `--calibration`, and judges the
[waivers](#waivers) on the UTC date of the clock of its host.
Where it is given the receipts of several attempts of one part, only that
of the latest attempt counts and the others are listed as superseded; a
receipt without a numeric attempt counts as the earliest, and two receipts
of one part and one attempt are two receipts of the part. It gives the
conclusion of the whole gate only when:

1. every receipt can be read and parses, has schema 7 and a part, and its
   commit and tree are those of the checkout, whose gate inputs are clean,
   whose registry, `statements.json`, qualification cases and lanes can be
   read and keep their rules and whose waiver record, where it can be read,
   keeps its rules (a missing or unreadable record has no
   [waivers](#waivers)), and the clock of the host gives a date from
   1970-01-01 to 9999-12-31;
2. each receipt of the commit started from the gate inputs of the
   checkout, its `inputs.before` ([receipt](#receipt)), which its commit
   and tree imply, so that this only guards against a receipt without them;
3. every receipt names one and the same image;
4. every receipt has one and the same trigger: the mode, `ref` and
   `run_id` of its `trigger`, whatever its event and attempt;
5. one receipt is of the qualification job, one of each lane of the
   checkout and one of each part of each formal target, and none is of
   another part;
6. each unit that the checkout registers, of the qualification and of the
   base round of the qualification job, of the base round and of the
   comparator of each lane, and of each formal target with its registered
   mutants, has exactly one conclusion among the receipts, which the
   receipt of the part that holds the unit gives: the unit of a target its
   first part, and the unit of a registered mutant the part that the
   registry gives it; and no receipt concludes another unit;
7. the receipt of the qualification job lists the hand-written modules,
   and the checks below find nothing.

The first four checks judge what the base rounds of the qualification job
and of the lanes held, from `handwritten`, `left_out` and `lane` of their
receipts, and the last the seeds of the parts of the targets, from their
`part` ([receipt](#receipt)). Each is `true` in `checks` of the record
when it finds nothing, and each finding is a problem:

- **`coverage`**: each hand-written module that the qualification job
  lists is held by exactly one of the job and the lanes, and each module
  that they hold is in that list;
- **`names`**: no public constant that the audit of a base round reports
  for the modules of its root, below, is declared by two parts, but a
  theorem that each part declares with the same fingerprint, the hash of
  its type and its universe parameters, as Lean declares the `congr_eq`
  equations that it generates for a `match` in each module that uses
  them. The check lets through only such a theorem and reports every other
  pair of constants of one name: a theorem and a definition, two theorems
  of different types or universe parameters, and also a theorem and an
  axiom of one type, which Lean 4.35.0 imports together. Lean also
  requires two theorems of one name to have the same `all`, the names of
  their mutual block, which the check does not compare;
- **`waivers`**: each lane leaves out of its round exactly those of its
  modules that the qualification job lists in `left_out`, the closure of
  what the waivers that held for it leave out;
- **`extraction`**: the lane of each formal target outside the waivers
  that hold on the date of the merge, the lane of its `module`, extracted
  it;
- **`seeds`**: the receipt of each part of a formal target records its
  part, and the parts of one target took the same seed: the same tree of
  the extracted workspace, image and SHA-256 of each file that Aeneas
  wrote, and each built it, or none did, as where the proofs of the target
  do not build and its first part rejects it. The build products are not
  compared, since the build of a seed is not shown to be reproducible to
  the byte.

Without the receipt of the qualification job, which is a problem already,
the first four checks are `false`.

When a condition fails, the merge gives no conclusion: it is `TOOL_FAILURE`
and not complete, with each problem. Otherwise its status is that of a run
of the whole gate with the failures of the receipts and the merged units,
`SCOPED` in place of `VERIFIED` when a unit is `SCOPED`, and it is complete
when every receipt is: a target that the proofs reject, whose mutants did
not run, makes it `REJECTED` and not complete, and a part that the disk
guard refused makes it `TOOL_FAILURE` and not complete, where that run
itself is `NOT_RUN`. With no formal target in the registry, the receipts of
the qualification job and of the lanes alone are merged. Each run
whose job names its image compares that reference with the pin of its
snapshot, so the merge records the image that the receipts name and does
not compare it with the pin.

The units of the targets of the waivers that hold on the date of the merge,
with their registered mutants and the `base/<theorem>` of each statement
in a proof module of these targets that the base round leaves out, and the
parts of these targets are recorded and not required. A
statement in a module that the base round leaves out only because the
module imports what a waiver leaves out stays required: its `SCOPED`
`base/<theorem>` fails the merge ([waivers](#waivers)). The merge passes
when it has no problem, every other unit is `VERIFIED` and no other part
has a failure. A waiver is used when a unit of its targets is not
`VERIFIED` or a part of them has a failure, and a merge that passes with a
used waiver is `REJECTED`: a waiver only lets the merge pass. A merge
whose units are all `VERIFIED` and whose parts have no failure is
`VERIFIED`, with its waivers unused. A merge without a waiver that holds
passes only when every unit is `VERIFIED` and no part has a failure. A
waiver that expires after the base run of a lane and before the merge
leaves a target out of the lane that no waiver covers at the merge: the
check `extraction` fails and the merge gives no conclusion; running the
merge again does not help, the gate must run again.

The merge also judges three hard gates, each from its own entries among the
kept receipts and over the same waivers: an entry holds when it passed or
is `VERIFIED`, or when it is of a target of a waiver that holds, as above.
Every gate fails when the merge has a problem.

- **`axioms`** passes when each receipt with a base round, of the
  qualification job and of each lane, has an audit, a command of its round
  that checks `Audit.lean` (the runs that count heartbeats are no audit),
  each audit of the receipts, those of the parts of the targets included,
  holds, and each unit `base`, `base/lane/<name>`, `base/<theorem>` and
  `target/<name>`, without the units of mutants, holds.
- **`leanchecker`** passes when each receipt with a base round has exactly
  one replay with `leanchecker`, that of its round with `--fresh` of its
  root module `Krepi`, and it passed; no waiver covers it.
- **`comparator`** passes when each unit `comparator/lane/<name>`,
  `comparator/<target>` and `comparator` holds, and so without such a unit.

A gate that passes says only that its own entries hold: a merge whose
other units or parts fail does not pass, whatever its gates.

Each part runs in a job of its own: the qualification job in `formal run`,
the two runs of a lane in `formal lane <name>`, and each part of a target
in `formal shard <name>/<i>`, so that the job of a lane takes the `seconds` of
both its runs, which its receipt sums. The synthetic wall clock is the
longest chain of these jobs that their `needs` in the workflow `formal`
give, each job after those that it needs, by the sum of their `seconds`,
and the seconds of the merge, from the start of its job, which the job
gives in `KREPI_FORMAL_MERGE_STARTED` as Unix seconds (the merge jobs of CI
take the start of the runner's worker process, else that of their first
step), to the end of the command; it is the command's own seconds without
that variable or with one that is not a Unix time before the command. The
jobs of the parts need only `formal limits`, so the chain is the slowest
job; the merge keeps their `needs` in a table that a test holds equal to
the workflow. The `seconds` of a part do not count the pull of the image
and the build of xtask in its job. The gate's wall-clock limit is 3,600 s,
300 s of which are the merge's, so the registered budget of a part of a
target, and that of a lane with the extraction margin, is at most 3,300 s
([shard plan and disk guard](#shard-plan-and-disk-guard), [lanes](#lanes)).
A synthetic wall clock above 2,880 s, 80% of the limit, is flagged in the
record and the summary, and so is each job whose `seconds` are above
2,880 s, and each part whose cgroup memory peak is above
13,372,738,764 B, 80% of the 16,715,923,456 B of memory of the runner of
CI. The flags change no conclusion.

The merge writes `artifacts/formal/merge/record.json` and its summary
`summary.md`, prints the summary, and exits with 0 when it passes and 1
otherwise, with 2 on a usage error, or with 120 when it cannot write them,
the record then on standard error. The summary has the conclusion and the
synthetic wall clock, the trigger, a line
`- checks: axioms pass, leanchecker pass, comparator pass` with `fail` for
each hard gate that fails, that the merge passes when it is not
`VERIFIED`, each waiver that holds, each flag and each problem; the
trigger, the jobs, the parts, the waivers and the problems are escaped, so
that none splits a line. The record has schema 4 and the form of a receipt
([receipt](#receipt)):

| Field | Content |
| --- | --- |
| `schema` | `4` |
| `status`, `complete` | The conclusion, as above |
| `passes` | Whether the merge passes, as above |
| `gates` | Whether each hard gate passes: `axioms`, `leanchecker` and `comparator`, as above |
| `commit`, `tree` | Those of the checkout, or `null` when they cannot be read |
| `inputs` | The object of each gate input of the checkout, as `inputs.before` of a receipt, or `null` when it cannot be read |
| `image` | The one image that the receipts name, or `null` |
| `trigger`, `ref`, `run_id` | The one mode, `ref` and `run_id` of the triggers of the receipts, or `null` |
| `planned_statements` | The number of planned statements of `statements.json`, or `null` when it cannot be read |
| `waiver_date` | The UTC date on which the merge judged the waivers, or `null` when the clock gives none |
| `waivers` | Each waiver that holds on that date: `waiver`, its entry of the waiver record, and `used`, whether the merge used it |
| `parts` | Each receipt given, in order: `receipt`, its path; `sha256`, of its bytes, or `null`; and when it parses, `shard`, `job`, the job that runs its part, `run_id`, `attempt`, `superseded`, `status`, `complete`, `seconds` and the `cgroup_memory_peak` of its `resources`; `over_seconds`, whether the `seconds` of its job are above 2,880 s, as above; and `over_memory`, whether its peak is above 13,372,738,764 B, or `null` without a peak |
| `units` | Each registered unit with its phase, status and reason |
| `axioms` | Each theorem that the base rounds of the qualification job and of the lanes audited, with the axioms that the audit reported for it, the report of the gate `axioms` |
| `checks` | Whether each check found nothing: `coverage`, `names`, `waivers`, `extraction` and `seeds`, as above |
| `jobs` | Each job of the parts that the merge kept, by its name: `seconds`, the sum of the `seconds` of its receipts; `over_seconds`, whether these are above 2,880 s; and `cgroup_memory_peak`, the largest of its receipts, with `over_memory`, as for a part |
| `chain`, `chain_seconds`, `merge_seconds`, `merge_from`, `wall_clock_seconds`, `over_80_percent` | The synthetic wall clock: the longest chain of jobs, the first first, and the sum of their seconds, the merge from its `job` or its `command`, the sum of both and whether it is above 2,880 s |
| `problems` | Each condition that fails |

For example, with values that are only an illustration:

```json
{
  "schema": 4,
  "status": "VERIFIED",
  "complete": true,
  "passes": true,
  "gates": {
    "axioms": true,
    "leanchecker": true,
    "comparator": true
  },
  "commit": "cccccccccccccccccccccccccccccccccccccccc",
  "tree": "dddddddddddddddddddddddddddddddddddddddd",
  "inputs": {
    "kernel": {
      "mode": "040000",
      "type": "tree",
      "oid": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    },
    "xtask": null
  },
  "image": "ghcr.io/o/r@sha256:9999999999999999999999999999999999999999999999999999999999999999",
  "trigger": "REQUIRED",
  "ref": "refs/pull/7/merge",
  "run_id": "123",
  "planned_statements": 0,
  "waiver_date": "2026-11-13",
  "waivers": [
    {
      "waiver": {
        "reason": "The proofs wait for a fix of the tool.",
        "scope": [
          "t"
        ],
        "expires": "2026-12-01",
        "author": "someone"
      },
      "used": false
    }
  ],
  "parts": [
    {
      "receipt": "artifacts/parts/qualification/receipt.json",
      "sha256": "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
      "shard": "qualification",
      "job": "formal run",
      "run_id": "123",
      "attempt": "1",
      "superseded": false,
      "status": "VERIFIED",
      "complete": true,
      "seconds": 1095.7,
      "cgroup_memory_peak": 10429386752,
      "over_seconds": false,
      "over_memory": false
    }
  ],
  "units": {
    "base": {
      "phase": "base",
      "status": "VERIFIED",
      "reason": null
    }
  },
  "axioms": {
    "Krepi.Proofs.Counter.t": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ]
  },
  "checks": {
    "coverage": true,
    "names": true,
    "waivers": true,
    "extraction": true,
    "seeds": true
  },
  "jobs": {
    "formal run": {
      "seconds": 1095.7,
      "over_seconds": false,
      "cgroup_memory_peak": 10429386752,
      "over_memory": false
    }
  },
  "chain": [
    "formal run"
  ],
  "chain_seconds": 1095.7,
  "merge_seconds": 62.0,
  "merge_from": "job",
  "wall_clock_seconds": 1157.7,
  "over_80_percent": false,
  "problems": []
}
```

`cargo xtask formal receipt` judges a record against a checkout
([current and fresh records](#current-and-fresh-records)).

### Waivers

`verification/waivers.json`, the waiver record, is a gate input with
schema 1 and a list `waivers`, and is committed empty. Each waiver has

- `reason`, why the targets that it covers may stay unverified;
- `scope`, the names of the registered targets that it covers;
- `expires`, the last UTC date on which it holds, as `YYYY-MM-DD`;
- `author`, the author of the pull request that adds it.

A waiver holds on each date up to its expiry, that date included; dates
in this form sort as text in the order of the calendar.
`cargo xtask formal check` refuses a record of another schema or with an
unknown field, and a waiver with a blank reason or author, an empty scope,
a name in it that `verification/targets.json` does not register, or an
expiry that is not a date of the calendar in that form. A planned target
may be named, and a name may repeat. A record that is missing or cannot
be read has no waivers, and the layout of the
[calibration target](#calibration-target) has no record.

The qualification job reads the record of its export when its
[base round](#base-round) starts, and the base run of a lane when its
extraction starts, each with the UTC date of the clock of its host; a
lane leaves the formal targets of the waivers that hold then out of its
extraction, and both leave what these waivers leave out out of their base
round. A record that breaks its rules, or a clock that reads before
1970-01-01 or after 9999-12-31, stops the phase as a tool failure. The
base round leaves out the proof modules of those targets that no other
formal target lists, and every hand-written module that imports a module
left out, or a generated module of such a target,
`KrepiGen.<module>.<file>`, unless a formal target outside the waivers
lists it: such a module of a target fails the build, as the import of any
missing module does. The qualification job records what is left out of
all the hand-written modules, with the target of each, in `left_out` of
its receipt, and each lane, in its lane record, what it left out of its
own modules; the merge requires the two to agree
([shards and merge](#shards-and-merge)). The round neither builds nor
checks a statement whose module is left out: its `base/<theorem>` is
`SCOPED`, with the reason that the waiver of the target leaves the module
out of the base round, and is a unit of that target when the module is one
of its proof modules. A waiver of a target that proves a registered
statement in one of its proof modules that the round leaves out is
therefore always used: the round leaves the statement unchecked, so a
merge that passes is `REJECTED`, never `VERIFIED`, and `cargo xtask formal
receipt` calls its record `WAIVED` at best, not `CURRENT`, even when the
part of the target is `VERIFIED`; once the waiver has expired, the record
is not current ([current and fresh records](#current-and-fresh-records)).
The [source rules](#source-rules) still apply to every tracked Lean file,
those left out included, in the qualification job. The part of a waived
target runs as any other. A run without `--shard`, the part of a target
and the comparator run of a lane do not read the record, and the layout of
the calibration target has none.

`cargo xtask formal merge` reads the record of the checkout and judges it
on the UTC date of the clock of its host; a record that breaks its rules,
or a clock that gives no date, leaves the merge without a conclusion
([shards and merge](#shards-and-merge)). The units of the targets of the
waivers that hold then, the `comparator/<target>` of each among them,
their parts and the `base/<theorem>` of each statement in a proof module
of theirs that the base round leaves out are recorded and not required:
the merge passes over their failures, records
each waiver that holds and whether it used it, and stays `REJECTED` when
it used one. A waiver covers no unit of the qualification, not the unit
`base`, and no `base/<theorem>` of a module that the base round leaves
out only because the module imports what a waiver leaves out: that unit
is `SCOPED` and fails the merge. Nor does a waiver cover the unit
`comparator/lane/<name>` of a lane, which holds the statements of its
modules that no formal target or two formal targets list: a waiver of one
of two such targets leaves such a module in the base round, where it is
checked, and waivers of all of them leave it out, which makes the unit
`SCOPED` and fails the merge. The hard gates of the merge pass over the
commands and units of the same targets in the same way, so the merge and
its three gates can pass while the record is `REJECTED`; the replays of
`leanchecker`, commands of the units of the base rounds, are never covered
([shards and merge](#shards-and-merge)).

`cargo xtask formal receipt` calls a record that passes with a used waiver
`WAIVED`, not `CURRENT`, and only while each waiver that it used holds on
the UTC date of the clock of its host; with `--require-fresh` it refuses
every record that holds a waiver, used or not, even one that has expired
since ([current and fresh records](#current-and-fresh-records)).

### Current and fresh records

`cargo xtask formal receipt [--require-fresh] [RECORD]` judges the record
of a merge, by default `artifacts/formal/merge/record.json`, against the
checkout, in the production layout. It runs no tool and proves nothing. A
record that cannot be read, that does not parse or whose `schema` is not 3
([shards and merge](#shards-and-merge)), such as a record of schema 2,
which has no hard gates, is not current. A record is
`CURRENT` when

1. its `inputs` are the objects of the gate inputs of the commit checked
   out ([gate inputs and snapshot](#gate-inputs-and-snapshot)), and the
   gate inputs of the checkout are clean. The commit and the tree are not
   compared, so the record of a head is current for every commit with the
   same gate inputs, such as the merge of its pull request into `main`; a
   change outside the gate inputs, such as below `tools/` or
   `.github/scripts/`, leaves the record current;
2. its `image` is the reference that the image pin of the checkout names
   ([image pin](#image-pin));
3. each unit that the checkout registers, of the qualification, of the
   base round, of the comparator and of each formal target with its
   registered mutants, has
   exactly one conclusion among its `units`, and it concludes no other
   unit;
4. it has no problem, is `VERIFIED` and complete, and passes.

A record that fails only the last condition, because it is not `VERIFIED`
or not complete, and passes with a waiver that it used, passed the merge
only through its waivers ([waivers](#waivers)). It is `WAIVED` when each
waiver that it used still holds on the UTC date of the clock of the host,
and not current otherwise, or when the clock gives no date.

With `--require-fresh`, a current record must also be fresh: its trigger
is `REQUIRED`, `FORCED_FULL` or `WEEKLY` with a `run_id`, the mode of a run
of CI, so that neither a run of named targets, which is `SCOPED`, nor a run
without `KREPI_FORMAL_TRIGGER`, which is `MANUAL`, is fresh; its
`planned_statements` are 0; and it holds no waiver. A run of the gate
starts only from clean gate inputs ([gate run](#gate-run)), so a
`VERIFIED` record is of a run from a clean checkout. With
`--require-fresh` no record is `WAIVED`.

The command prints `formal receipt:` and the verdict, `CURRENT`,
`CURRENT and fresh`, `WAIVED`, `CURRENT, not fresh` or `not CURRENT`; a
line `commit` with the commit of the record; a line `trigger` with its
mode, `ref` and `run_id`, `none` for each that it lacks; a line for each
waiver that the record holds, as the summary of the merge writes it; and a
line for each reason against the record, each condition that fails. The
values of the record and the reasons are escaped, so that none splits a
line. It exits with 0 when the record is current, and fresh when
`--require-fresh` is given, with 3 when it is waived, with 1 otherwise and
with 2 on a usage error. In CI, the job `formal merge` reads the record
of a manual or scheduled run of `main` back with `--require-fresh`, which
changes no verdict, and the job `formal receipt review` judges the record
of the head of a pull request merged into `main` whose change affects the
gate ([CI job](#ci-job)).

### Extraction

An extraction, in `extract.rs`, translates the Rust items that it starts
from into Lean. It needs at least one root, and a work directory that no
extraction has used: a request without a root, or a work directory that
already holds `extract.llbc`, `aeneas/` or `target/`, is an internal error,
and nothing runs. It runs two commands of its unit:

- Charon, in the package that it extracts:
  `charon cargo --preset=aeneas --sysroot default --start-from <roots separated by commas> [--opaque <pattern>]... --dest-file <work>/extract.llbc -- --lib --locked`,
  followed by `--target aarch64-unknown-none` for a kernel target;
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
`source.file` and `loop.is_body` of each function, and `rust_name`,
`lean_name` and `lean_file` of each type; every one of them but `loop` must
be there, and other fields are not read.

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
triple, `aarch64-unknown-none`, for which the gate has Cargo compile the
root package of the kernel workspace, from which every kernel target is
extracted without `-p`, and empty `features` and `cfg`, since the gate
passes neither. The qualification stops when the file of the export does
not have exactly these hosts, names features or `cfg` settings, or gives
the kernel another triple.

Charon builds the package that it extracts with `cargo build` without
`--release`, in the dev profile. The root manifest of the kernel workspace
may not have a `[profile.dev]` ([source layout](architecture.md#source-layout)),
and the Cargo configuration of the repository sets none, so the extraction
sees Cargo's dev profile, with `debug-assertions` and `overflow-checks` on,
while the images are built in the release profile, with `overflow-checks`
on and `debug-assertions` off. A `debug_assert!` is therefore checked only
in what the gate extracts, and `cfg!(debug_assertions)` has another value
in the extraction than in the images; only review keeps such code out of
what is proved
([rule 7](conventions/provable-subset.md#7-no-shape-changing-cfg)). The triples of the qualification crate record what Charon chooses
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
The qualification job and a run without `--shard` and `--target` have
it, with a budget of 3,600 s; the runs of a lane, the part of a target and
a run of `cargo xtask formal run --target` do not.

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
   file and the output of Aeneas, also those of each part, are removed
   once the case is concluded, which for a case with a stage is after its
   generated files are installed there, unless the run keeps its work
   directory ([layout](#layout)).
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

The base round, in `base.rs`, builds, audits and replays hand-written
Lean of the snapshot with the generated modules of the proof cases of the
qualification and of the targets that the run extracted, with a budget of
3,600 s. It runs over a part of the hand-written modules, as the
[lanes](#lanes) divide them: in the qualification job, after the
qualification, over the modules below `Krepi/Qualification/`, with the
proof cases; in the base run of a lane, after the
extraction of its targets, over its own modules, those of its components
and the shared modules that it lists, with the generated modules of its
targets; and in a run without `--shard` and `--target`, after the
qualification and the extraction, over all of them. A module of no lane is
in no part, so that the merge finds it held by none. The qualification job
of the [calibration target](#calibration-target) has no module and no
proof case, so its root imports no module; its round builds, audits and
replays that root all the same, as the hard gates of the merge require of
each base round. The part of a target,
the comparator run of a lane and a run of
`cargo xtask formal run --target` have no base round. Its units are
`base`, or `base/lane/<name>` in a lane, and `base/<theorem>` for each
statement that `statements.json` registers as proved in a module of its
part; the phase reads that file and the lanes from the checkout at the
start of the run, to register its units, and stops when one cannot be
read or the export's `statements.json` is not the same. A planned
statement has no unit. Other theorems that the audit lists, such as the
qualification theorems and unregistered ones, are judged within the unit
of the round, which the rest of this section calls `base`.

A lane extracts the formal targets of its components, as the `module` of a
target names its component, the planned targets of its components whose
generated modules its own modules import, and every other target whose
generated modules the hand-written modules that its own modules reach
import, which it extracts for the stage alone; the lane record of its
receipt gives each with its role, `formal`, `planned` or `cone`
([receipt](#receipt)). The qualification job extracts no target.

The round reads `statements.json`, `axioms.json` and `tcb.json` of the
export; a file that cannot be read, or does not follow its schema, stops
the phase. Then it

1. computes the statement hash of the snapshot commit
   ([statements and proofs](#statements-and-proofs)) and rejects the round
   when `statements.json` records another;
2. lists the `.lean` files below `verification/` of the snapshot commit with
   `git ls-tree`, but those of the calibration project, which are in its
   own layout, and rejects the round for a symbolic link, for a file
   below neither `verification/Krepi/` nor `verification/externals/`, such
   as `verification/Krepi.lean`, for a file whose path does not name a
   Lean module, and for a file that breaks a
   [source rule](#source-rules). A lane leaves step 1 and these rules to the
   qualification job: it lists the files in the same way and rejects its
   round only for a file below neither directory, and its
   `statement_hash` holds two empty strings;
3. creates the stage `work/base/stage/` as the qualification creates the
   stage of a case: the project files of the export, its module files below
   `verification/Krepi/` whose paths name modules but those that the
   [waivers](#waivers) leave out, so that no file that
   step 2 rejects for its form reaches the root, the two links to the
   installation, and, for each
   qualification case with a proof whose generated code built, the
   generated modules as the case installed them, the reviewed external
   declarations of a case with `models` among them, in the qualification
   job and a run without a part, and, for each target that the run
   extracted, its generated modules as its stage holds them.
   When the generated code of such a case did not build, or the generated
   definitions of a target do not type-check, nothing is built, audited or
   replayed: `base` and each of its theorems are concluded from the
   commands of the case or of the target, so that a tool failure there
   forces them, and they are `REJECTED` otherwise. In the layout of the
   [calibration target](#calibration-target), the qualification proofs are
   in another Lake project, and the round has no proof case;
4. writes the root module `Krepi`, a module file with a `public import` of
   each module of its part in the stage, sorted: the hand-written modules
   of the part and the generated modules of the proof cases and of the
   targets that the run extracted, in a lane but those of the targets that
   it extracted for the stage alone, so that a module of the part that
   nothing imports is built, audited and replayed as well; in a run without
   a part these are all the modules below `Krepi` and `KrepiGen` in the
   stage. The other modules of the stage are built only as far as the root
   imports them. The library `KrepiRoot` of `lakefile.toml` builds it as
   `+Krepi`; the library `Krepi` takes only the modules below the root, so
   that a stage without the root, such as that of a qualification case,
   still builds by default; the [comparator](#comparator) of a lane gives
   it the root alone. In the qualification job and a run without a
   part, the round rejects a planned statement whose module has no file.

No problem of these steps stops the commands, so that the audit and
`leanchecker` judge what they find themselves. The commands run in the
stage's `verification/`, in this order:

| Command | Call site | Cap |
| --- | --- | --- |
| `lake build --no-cache --wfail +Krepi`; with planned statements, `+M` for each module that the root imports that is not the module of a planned statement | Base build | 7,200 s |
| With planned statements, `lake build --no-cache +Krepi` | Base build | 7,200 s |
| `lake env lean Audit.lean` | Axiom audit | 1,800 s |
| `lake env leanchecker --fresh Krepi` | `leanchecker` | None |
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
other rejects the round. krepi's own modules are every module below `Krepi` in
the stage but the root, and the reviewed external declarations installed for
qualification cases, `KrepiGen.<module>.FunsExternal` and
`TypesExternal`. A failed build is a proof failure when its log has an
error or a warning whose line names the file of an own module, and a tool
failure otherwise ([results](#results)).

**Audit.** `Audit.lean` is not a module. It imports `Lean`, whose
elaborator its programs use also when the root imports no module, and the
root, sets `pp.privateNames`, states `example : S := t` for the theorem
`t` of each proved statement `S` of a module of the part in the stage, and
runs a program that, for each own module that the root imports, prints a
marker, runs `#print axioms` on each theorem constant of the module that
is not private, not an internal detail and not the theorem of a planned
statement, prints the module that declares each of its native-decision
axioms, and prints the line at which each theorem's declaration range
starts; it then prints, for each proved statement, the module that defines
`S` and whether the type of `t` in the environment is the constant `S`
itself. The `example` alone would not show that: elaborating `t` against
`S` may insert a coercion, apply an instance or fill an argument that the
proofs declare. A second program prints
`krepi-name <constant> <kind> <fingerprint>` for each constant of each
module that the root imports that is neither private nor an internal
detail, as that module declares it: its kind, `theorem` or `other`, and
the fingerprint `<hash>[<parameters>]`: the hash of its type, which Lean
computes from the structure of the type alone, so that it is the same in
every environment for the same type, and its universe parameters,
separated by commas. These are the public constants of the round, which
its lane record lists for the check `names` of the merge ([shards
and merge](#shards-and-merge)). The hash is Lean's 32-bit structural hash
of the type (`Expr.hash`), not a cryptographic one, and the fingerprint
leaves out `all`, the names of the mutual block of a theorem: two theorems
of one name whose types have the same hash, or that differ in `all` alone,
pass the check `names`. That weakens only the check that stands in for
importing every hand-written module together; no conclusion rests on it,
since each part builds, audits, replays and compares its own theorems.
The list of theorems is Lean's, so it
holds the theorems that Lean generates, such as `injEq` and `congr_eq`
lemmas, and theorems that a metaprogram adds; Lean generates the
`congr_eq` equations of a `match` in each module that uses them, so two
parts may declare the same theorem, which the check admits. A constant
that is an internal detail is not in the list, so the check does not see
two such constants of one name, which Lean would not import together. The
round rejects

- an axiom of a theorem that the allowlist does not allow for its kind;
- a registered proved theorem that the audit does not report in its
  registered module, or whose type is not the statement constant itself,
  without arguments, whether or not its `example` checks;
- a statement that is not defined in an own module outside `Krepi.Proofs`;
- an own module that the root imports without its marker, and an error
  at another line of the audit file.

The allowlist is one table of data in `lean.rs`, by the kind of the
theorem's module. Besides `propext`, `Classical.choice` and `Quot.sound`,
it allows:

| Kind | Modules | Also allowed |
| --- | --- | --- |
| Specification | Own modules below `Krepi` outside `Krepi.Proofs` that are not the proof module of a qualification case | Nothing |
| Qualification | The proof module of a qualification case, and the reviewed external declarations installed for the case | The axioms that the case's generated files declare |
| Target | Modules below `Krepi.Proofs` | The names in `axioms.json`; the axioms of the native decisions of a declaration that a `native-decision` item of `tcb.json` names, declared in the module of the item's `file`; the axioms of the native decisions of a lemma of the Aeneas Lean library that a `library-native-decision` item names, `_private.<source>.0.<declaration>._native.<tactic>.ax_<i>_<j>` declared in the item's `source`; and an axiom that a generated or reviewed external file of the stage declares and whose name starts with the `prefix` of an `axiom-pattern` item, in whole components |

`sorryAx` is in no row. The case audits of the qualification use the same
table with the qualification kind. A theorem of a proof module of a target
may also use the declarations that the templates of the target keep, its
unconstrained and cut items, and the `trusted_axioms` of the target, in
the audit of the base round as in that of the
[target](#proof-targets). In the base round, a module below
`Krepi.Proofs` that no formal target lists belongs to a planned target
that the run extracted when its imports, directly or through hand-written
modules, reach the generated modules of that target and of no other, and
its theorems may then use the same; a module that reaches those of two
or more targets, such as a composition proof, belongs to none.
Lean 4.35.0 gives each native
decision an axiom of its own, `<declaration>._native.<tactic>.ax_<i>_<j>`,
where the tactic is `native_decide`, `decide` or `bv_decide`, with
`_private.<module>.0.` before it in a module file. A name with a component
`_native` is such an axiom: only a `native-decision` or a
`library-native-decision` item allows it, for a target theorem, and
`axioms.json` refuses such names. Any module could declare an axiom of
such a name without the kernel, so the item allows it only when the audit
finds it declared in the module of the item's `file`, or, for a
`library-native-decision` item, in its `source`; such an item allows
the axioms of its lemma alone, not those of another lemma of the module.
A pull request that adds an item to `tcb.json` or changes the reason of
one needs the label `spec`, by the registry rules of the [guard](#guard).

`verification/axioms.json` has schema 1 and a list `axioms`, each with
`name`, `source`, the module of the Aeneas Lean library that declares the
axiom, and `reason`. `verification/tcb.json` has schema 1 and a list
`items`, each with the `kind` `native-decision`, with `file`, a tracked
hand-written file, `declaration` and `reason`, or `axiom-pattern`, with
`prefix` and `reason`, or `library-native-decision`, with `source`, the
module of the Aeneas Lean library that declares a lemma proved by a
native decision, `declaration`, the lemma, and `reason`; a `source` that
does not start with `Aeneas.` is refused. Other kinds are refused until
the trusted base is classified, and unknown fields are refused in both
files.

**Replay.** `leanchecker --fresh Krepi` imports the root module and checks
again in the kernel, starting from an empty environment, every declaration
that the import brings in but unsafe and partial ones: those of every
module of the stage that the root imports, directly or through others,
krepi's own and the generated ones, and those of Lean, the Aeneas Lean
library and its packages that they import. A declaration of a module of
another lane that no module of the part imports is replayed in that lane
alone. The stage's
build directory is new in every run, so that no earlier output is
replayed. An exit with 0 passes. Another exit is a proof failure, which
rejects the round with the output, whose lines name the declaration but
not its module, when the output has a kernel message about something other
than a deterministic timeout, excessive memory, deep recursion or an
interruption; otherwise, such as when `leanchecker` finds no built root
module, it is a tool failure.
`leanchecker` has no version option. The receipt records the output of
`lean --version`, which must exit with 0 and print a line that starts with
`Lean (version `, else it is a tool failure, and the SHA-256 of the
`leanchecker` of the installation, which `lake env` finds first on `PATH`.
That program loads the kernel from the Lean shared library, so the
checker is identified by the download digest of the Lean archive in the
tool manifest and, in CI, by the digest of the image. The receipt also
records the module of the replay, its seconds, and the largest maximum
resident set of a process that the run had collected when it ended, with
whether that grew during the replay, so that it is then the replay's own
and otherwise bounds it from above.

**Heartbeats.** Only theorems with a declaration range are counted. For
each own file with such theorems, the round writes a copy below
`.heartbeats/` with Mathlib's `#count_heartbeats in` inserted before each
of them, at the line at which its declaration range starts when a
declaration command starts there, and reads the counts that
`lake env lean --json` prints for the copy. A declaration command starts
at a line whose first token is a doc comment, an attribute, one of the
modifiers `public`, `private`, `protected` and `nonrec`, `theorem` or
`lemma`, unless the line lies in the header of a command before which a
count is inserted on an earlier line, up to the line of its keyword, the
first name outside the brackets of its attributes that is no modifier. A theorem whose range
starts inside another command, such as a `where` clause, or the theorem
`<name>.mvcgen_spec` that `@[step]` adds at its attribute after the doc
comment of a theorem on an earlier line, has no count, nor have
the theorems of a file whose command ends by itself with a status other
than 0; the receipt records why. A theorem that an attribute adds in the
header of a declaration of another kind, such as `@[ext]` after the doc
comment of a structure, gets a line inserted there, so the copy does not
parse and the theorems of its file have no counts. A theorem without a declaration range,
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
installation is a tool failure of the run. The run lists them as well
before its first phase and after its last, also when a phase stopped, so
that a command of the extraction, of a target or of a mutant that writes
them is a tool failure of the run too. In the image, the installation
belongs to root, every user can read it and none but root can write it. CI
runs the gate there as the runner's user, on a read-only root file system
([CI job](#ci-job)), and the gate refuses to run as root or as the owner of
the installation ([image pin](#image-pin)).

**Conclusions.** `base`, or `base/lane/<name>`, is `VERIFIED` when the
round has no problem and no command forced it, and `REJECTED` with its
problems otherwise: the statement hash, the file and source rules, the
modules of planned statements, a build that failed with messages in own
modules, messages of the planned build other than the `sorry` warning, the
axioms of unregistered theorems, missing markers, errors in the audit file
and the kernel reports of `leanchecker`. Each `base/<theorem>` is
`REJECTED` with its own problems, and when the build failed or
`leanchecker` reported a declaration that the kernel rejects, and
`VERIFIED` otherwise; the other audited theorems get their status in the
receipt the same way. A tool failure among the round's commands forces
`base` and each of its theorems. A `base/<theorem>` whose module a waiver
leaves out is `SCOPED` ([waivers](#waivers)).

### Source rules

The `lean` step of `cargo xtask check` reads each tracked `.lean` file
below `verification/`, which must be a UTF-8 regular file, with the
`tcb.json` of its Lake project: `verification/tcb.json`, or for a file of
the Lake project of the [calibration target](#calibration-target), that
project's own. The base round reads each such file of the snapshot in the
Lake project of its layout, with the same rules. They read Lean's tokens:
comments, string literals, raw string literals and character literals are
skipped, but the `{}` parts of a string are read as code, as an
interpolated string reads them, and a string that ends elsewhere when it
is read as an interpolated string than when it is read as a plain one
breaks a rule:

- the file lies below `Krepi/` of its Lake project, `verification/Krepi/`
  or that of the calibration target, or below `verification/externals/`,
  and is a module file: its header starts with `module`;
- `native_decide`, `bv_decide`, and the name `native`, which `decide`
  takes as an option, such as in `decide +native` or
  `decide (native := true)`, appear only in a file that a
  `native-decision` item of the `tcb.json` of its project names;
- `axiom` appears only below `verification/externals/`;
- a file of the statement side imports neither the root module `Krepi` nor
  a module below `Krepi.Proofs`
  ([statements and proofs](#statements-and-proofs)).

The rules are a lexical check, made before any build. They do not read
generated files, which exist only in stages, and do not expand tactics or
run metaprograms: a tactic that wraps a native decision, such as Aeneas's
`bv_tac`, passes them, and so does an axiom that a metaprogram adds with
`addDecl`. The audit is the check of the axioms: it rejects the axiom of
such a decision and any other axiom that no row allows. The
[comparator](#comparator) never permits an axiom private to a proof
module, so it rejects a theorem whose proof makes a native decision in a
proof module, even when a `native-decision` item admits the axiom in the
audit. The Aeneas Lean
library itself declares the native-decision axioms of some of its lemmas,
among them the `bv_mod_size` lemmas that `bv_tac` uses; a target theorem
that depends on one of them fails the audit unless an item of `tcb.json`
admits the axiom, which for such a lemma is its `library-native-decision`
item, and the comparator then permits it. The audit takes the `file` of
a `native-decision` item for the module that declares the axiom when its
path ends with the file of that module, and the gate does not check that
the file is hand-written: the review that the label `spec` requires
checks that each item names what its kind is for.

### Comparator

The comparator of a lane, in `comparator.rs`, checks the theorem of each
proved statement of the lane once more, apart from the audit: Lake's
`lake comparator` builds a challenge, which declares the theorem with the
type of its statement and `sorry` for its proof, and the root module
`Krepi` of the stage of the [base round](#base-round) of the lane, exports
both and requires the theorem of the solution to have exactly the type
that the challenge gives it and to depend on no axiom outside the
permitted list, which it checks on the export of the solution.
`cargo xtask formal run --shard lane/<name> --comparator`, the comparator
run of the lane, runs it after the base run of the lane of the same
commit, on the stage of the base round that the base run kept with
`--keep`, and writes the receipt of the lane
([shards and merge](#shards-and-merge)).

A proved statement belongs to the lane that holds its module
([lanes](#lanes)). The units of a lane are `comparator/<target>` for each
formal target that alone lists the module of a proved statement of the
lane in its `proof_modules`, with those statements, and
`comparator/lane/<name>` with its other proved statements, among them
those of a module that two formal targets list or none; a planned
statement has none. A proved statement of a module that no lane holds is
in the unit `comparator`, which no part concludes, so that the merge gives
no conclusion. A unit of a target thus holds only statements whose
modules a [waiver](#waivers) of the target leaves out of the base round,
and the waiver covers no result of the comparator on a statement that the
round checked. The phase reads them from `statements.json`, the registry
and the lanes of the checkout when the run starts, and stops when it
cannot read them. It

1. reads the base records below the runs directory,
   `artifacts/formal/runs/`, or the directory that `KREPI_FORMAL_RUNS`
   names, and takes the one base record of the same lane, commit, tree,
   image and `run_id` of the trigger; when there is none or more than one,
   as when a build below that directory wrote another, the phase stops, so
   that the units are `NOT_RUN` and the run is a tool failure. The run then
   takes the deadline of the base run, from its start and its budget; the
   commands of the run before its phase, such as those of its export, have
   the deadline that its own start and the same budget give.
   Without a unit, it runs no command, and the
   receipt of the lane has the units of the base run alone; with one, a
   base record without a base round stops the phase as well;
2. adds the Lean library `KrepiChallenge` to the `lakefile.toml` of the
   stage of that round, once however often the comparator runs on it, and
   gives the library `Krepi` of that file the root alone,
   `globs = ["Krepi"]` for `globs = ["Krepi.+"]`. Lake takes the name of
   the solution, `Krepi`, for that library before the root module, and the
   stage of a lane holds the hand-written modules of every part but only
   the generated modules of the targets that the lane extracted, so that a
   build of every module below `Krepi` fails on those of the other parts.
   The build of the solution is thus that of the root and of what it
   imports, which the base round built, and no other module of the stage is
   built;
3. concludes each unit:
   - `SCOPED` when the base round left the statement of one of its
     theorems out under a [waiver](#waivers), which makes
     `comparator/<target>` a unit of the waived target, while no waiver
     covers `comparator`;
   - `NOT_RUN` when the base round did not verify one of its theorems with
     the axioms that the audit reported: the record of the round has no
     entry for it, an entry that is not `VERIFIED`, as after a failed base
     build, an axiom that the allowlist refused or a tool failure, or one
     without axioms. The reason names the theorem and its status there.
     `NOT_RUN` ranks below `REJECTED` ([results](#results)), so that the
     merge keeps the `REJECTED` of the base round;
   - otherwise by `lake comparator --config KrepiChallenge.C<i>.json`,
     run in the stage, where `i` counts the units in the order of their
     names from 0. The challenge `KrepiChallenge.C<i>` imports every
     module that the root of the round imports but the proof modules,
     `Krepi.Proofs`, the modules below it and the proof modules of the
     targets that the base run extracted, and declares each theorem of the
     unit as `public theorem <theorem> : <statement> := sorry`. The
     configuration names the challenge, the solution module `Krepi`, the
     theorems and the permitted axioms. Exit 0 is `VERIFIED`, and exit 1
     `REJECTED`, with the lines of the comparator that hold `error:`,
     unless a line starts with `error: Child exited with `: a build or an
     export in its sandbox did not finish, as for a name that the
     challenge lacks, which is a `TOOL_FAILURE`, as is any other status
     ([results](#results)).

The permitted axioms of a unit are the axioms that the audit of the base
round reported for its theorems, which the round verified, so that the
allowlist admitted each with the sources of its theorem, and `propext`,
`Classical.choice` and `Quot.sound`, without `sorryAx` and without a name
`_private.<module>.0.<name>` of a proof module, sorted. They are part of
what the allowlist admits for the target. No registry and no declaration
of the stage adds to them: an axiom that no theorem of the unit uses is not
permitted, whether `axioms.json`, a trusted axiom of the target or a
template declaration names it, and neither is `sorryAx`, even when a
trusted axiom admits it. The standard axioms are always permitted, since
the walk of the comparator over the axioms of a theorem also follows the
constructors and the recursor rules of the inductive types that it uses,
which `#print axioms` does not. So:

- a native decision in a proof module, which `native_decide`,
  `decide +native` and `bv_decide` make, and Aeneas's `bv_tac` when its
  goal reaches the stage of its SAT solver, adds an axiom private to that
  module, which is never permitted: the comparator reports
  `Illegal axiom detected` and the unit is `REJECTED`, even when a
  `native-decision` item admits the axiom in the audit;
- an axiom of a native decision that is not private, and an axiom of
  `axioms.json` or a trusted axiom that a theorem uses and that only
  modules outside the imports of the challenge declare, are permitted but
  missing from the challenge: the comparator cannot export them, and the
  unit is a `TOOL_FAILURE`, with the name in the comparator's standard
  error;
- a native decision of a library that the challenge imports, such as those
  of the Aeneas Lean library behind `bv_tac`, is permitted when the audit
  admitted it.

`lake comparator` builds and exports in a sandbox of bubblewrap, which
clears the environment, sees the file system read-only and lays empty
directories over `/home`, `/root`, `/run/user` and `/tmp`, into which it
binds back only the Lake project, Lean and Lake's home, with the build
directory `.lake` writable. The stage reaches the Aeneas Lean library and
its packages through links outside its Lake project, so the runs
directory must lie outside those directories: in CI, the comparator run
reads it through a second mount at `/krepi-runs`, which
`KREPI_FORMAL_RUNS` names.
Git in the sandbox reads only the system's configuration, `/etc/gitconfig`,
which CI provides to mark every directory as safe, since the packages of
the installation belong to root
([environment of tool commands](#environment-of-tool-commands),
[CI job](#ci-job)). In CI the comparator run runs a copy of xtask that its
job made outside the checkout before the base run, mounted read-only at
`/krepi-xtask`, so that what the base build writes in the checkout does
not change the program that concludes the lane; the stage that it checks
is still the output of that build ([limitations](#limitations)).

In the layout of the [calibration target](#calibration-target), the
comparator runs two more challenges after its first unit when that unit has two
statements A and B, which conclude no unit: `KrepiChallenge.Statement`,
the command of `comparator-negative/statement`, declares the theorem of A
with the statement of B, with the permitted axioms of the unit, and
`KrepiChallenge.Axiom`, that of `comparator-negative/axiom`, declares the
theorem of A with its own statement, with the permitted axioms of the unit
but `propext`. The comparator must reject both: the first because the
statements differ, the second because of `propext`, which every theorem of
the calibration uses. Their classes and logs in the receipt show whether
it did. A first unit that is not checked, or has fewer than two
statements, runs neither.

### Guard

`cargo xtask formal guard --event PATH`, in `guard.rs`, checks a pull
request against the rules for changes of statements, proofs, sources and
registries.
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
  file counts at its old and at its new path
  ([gate inputs and snapshot](#gate-inputs-and-snapshot));
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
- what the registry rules below find in `verification/targets.json`,
  `verification/models.json` and `verification/tcb.json`, when the pull
  request changes them: each is read at the merge base and at the head as
  the gate reads it, a side without the file as an empty registry, and
  their targets, mutants and items are compared as values, so that another
  order of the entries, of the theorems of an obligation or of the fields,
  other white space and a default written out change nothing. A registry
  that cannot be read on one side is compared on neither side;
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

The labels are `spec` for a change of statements and for the registry
changes below, `proof` for a change of proofs, and `ai-proof` for a pull
request with proofs that an AI system wrote, which the guard records and
never judges. Other labels are recorded and ignored. The rules are rows of
one table, to which later checks add theirs; each rule from
`registry-target-removed` on fails when it finds something and the label
`spec` is missing:

| Rule | Fails when |
| --- | --- |
| `statement-change-needs-spec` | A path of the statement side changed, or a statement is no longer proved, and the label `spec` is missing |
| `spec-approval` | The label `spec` is present and `Review`, `Approval` or `Approved-Statement-Hash` is missing, or the approved hash is not the statement hash of the head |
| `no-sources-with-proofs-or-statements` | A source changed together with the label `proof`, a changed proof file or a changed path of the statement side |
| `heartbeats-need-review` | A heartbeat limit is newly raised and `Heartbeats-Review` is missing |
| `phase-and-author` | The label `spec` or `proof` is present and `Phase` or `Author` is missing, or `Phase` is not `statement`, `proof` or `rewrite` |
| `proof-of-registered-statements` | A statement is restated and the label `spec` is missing: a proof may only prove a statement that the merge base registers |
| `registry-target-removed` | A target of the merge base is not registered at the head |
| `registry-theorem-removed` | A theorem of an obligation of a target of the merge base is not one of that target at the head |
| `registry-mutant-removed` | A mutant of a target of the merge base is not one of that target at the head |
| `registry-proves-narrowed` | A key of `proves` of a target of the merge base is not in that of the target at the head |
| `registry-formal-made-planned` | A formal target of the merge base is planned at the head |
| `registry-unconstrained-added` | A target of the head lists a function in `unconstrained` that it does not list at the merge base |
| `registry-opaque-added` | A target of the head has a cut point, by its pattern, that it does not have at the merge base |
| `registry-trusted-axiom-added` | A target of the head has a trusted axiom, by its name, that it does not have at the merge base, or `tcb.json` has an item, by its kind and its file and declaration, its source and declaration or its prefix, that it does not have there |
| `registry-model-added` | `models.json` has a model, by its name, an item of a model or a target in the `used_by` of a model that it does not have at the merge base, or a target of the head names a `models` directory that it does not name there |
| `registry-obligation-changed` | A target of both commits has other obligations, compared by `id`, `statement` and the set of their theorems |
| `registry-start-from-changed` | A target of both commits has another set of roots in `start_from` |
| `registry-mutant-file-changed` | A mutant of a target of both commits, by its name, has another `file` |
| `registry-mutant-find-changed` | A mutant of a target of both commits, by its name, has another `find` |
| `registry-mutant-replace-changed` | A mutant of a target of both commits, by its name, has another `replace` |
| `registry-mutant-renamed` | A mutant of a target of both commits is missing at the head, where the target has a new mutant with the same `file`, `find` and `replace` |
| `registry-mutant-fails-grown` | A mutant of a target of both commits lists a theorem in `fails` that it does not list at the merge base |
| `registry-trusted-reason-changed` | A trusted axiom or a cut point of a target, or an item of `tcb.json`, that both commits have, has another reason |
| `registry-unreadable` | A changed registry cannot be read at the merge base or at the head |

`proof-of-registered-statements` judges every pull request, whatever its
labels: adding, removing or renaming a statement needs the label `spec`,
and with it the fields that `spec-approval` checks.

The rules of removals compare the targets of the merge base, so a target new
at the head removes nothing; the rules of additions, which widen the trusted
base or the models, compare the head, so a target new at the head adds all
that it has; and the rules of changes compare only the targets and mutants
that both commits have, where a target that gains its first obligation or
root in `start_from` changes them. Removing a theorem of an obligation also
changes the obligation, and renaming a mutant also removes its old name, so
both rules fail. Tightening a registry, such as making a planned target
formal, removing a trusted axiom, an unconstrained function, a cut point or
an item of the trusted base, or adding a key to `proves`, fails no rule. The
reason of a registry rule starts with what it found, such as
`it removes the targets slots in targets.json`, with each item as
`<value> in <target>` or `<target>/<mutant>`, an item of a model as
`<item> in <model> in models.json` and a target that a model is for as
`<model> for <target> in models.json`, and ends with
`without the label spec`; with the label, `spec-approval` requires the
review and the approval as for a statement change. The approved hash is the
statement hash, which does not cover `targets.json`, `models.json` or
`tcb.json`: a registry changed after the approval leaves the approval valid,
so the reviewer checks the registries of the head that carries the label.
Each item of a reason, a path or a value of a registry, is printed escaped,
as `cargo xtask formal impact` prints paths, so that none splits a line.
`cargo xtask formal guard` compares the registries of the production layout,
so a change of those of the [calibration target](#calibration-target) fails
no registry rule.

On a pull request, when `GITHUB_EVENT_NAME` is `pull_request` and
`GITHUB_EVENT_PATH` names the event, `cargo xtask formal run` runs the same
check through the gate's Git in a first phase, `guard`, with a budget of
300 s, and records what it found in the receipt. The phase has no unit: a
failing rule does not change the status of the run, which is about the
proofs, and the standalone command decides. An event that cannot be read,
or a failed Git command, stops the run as an internal error; a registry
that cannot be read does not, as `registry-unreadable` names it. Without a
pull request event, in the runs of a lane, in the part of a target and in
a run of `cargo xtask formal run --target`, the run has no guard phase.

### Results

Every command gets one class from one function, `outcome::classify`, which
every call site uses: `PASSED`, `PROOF_FAILURE`, `TOOL_FAILURE` or
`NOT_RUN`, and `BUDGET`, a tool failure at the limit of a phase, of the
gate or of a target rather than at the cap of the call site. A tool failure is never a
statement about the code. The conventions:

| Result of the command | Call sites | Class |
| --- | --- | --- |
| Ran until its cap | All | `TOOL_FAILURE` |
| Ran until the rest of a budget | All | `BUDGET` |
| Ended by a signal | All | `TOOL_FAILURE` |
| Exited with a status above 128 | All | `TOOL_FAILURE` |
| `lake build` prints `error: Lean exited with code N` with `N` above 128 | The four builds | `TOOL_FAILURE` |
| Charon exits with 255 | Charon | `TOOL_FAILURE` |
| Cargo reports a process ended by a signal, as in `(signal: 9, SIGKILL: kill)` | Charon | `TOOL_FAILURE` |
| Could not start or could not keep its output | All | `TOOL_FAILURE` |
| Ended by itself, and an output file that the gate reads, `translation.json` or a generated Lean file, cannot be read or is not what the tool writes, or `translation.json` is missing after an exit with 0 | Aeneas | `TOOL_FAILURE` |
| The base build fails with errors in krepi's own modules | The base build | `PROOF_FAILURE` |
| The base build fails with warnings only in krepi's own modules | The base build | `PROOF_FAILURE` |
| The base build fails without an error or a warning in krepi's own modules | The base build | `TOOL_FAILURE` |
| The comparator exits with 1 and prints a line that starts with `error: Child exited with ` | The comparator | `TOOL_FAILURE` |
| The comparator exits with 1 otherwise | The comparator | `PROOF_FAILURE` |
| The range printer exits with another status than 0 | Declaration ranges | `TOOL_FAILURE` |

A process of the group that survives the kill is a tool failure as well, and
so is any failure of Git or `cargo metadata`, which the gate runs itself,
and any status of the comparator but 0 and 1. Any other non-zero status of
a tool is a `PROOF_FAILURE`, which its call site compares with what it
expects. The call sites are Charon and Aeneas, the qualification builds,
the ill-typed builds and the case audits of the qualification, the base
build, the axiom audit and `leanchecker` of the [base round](#base-round),
the target builds of the [targets](#proof-targets) and their
[mutants](#mutants), whose audits are axiom audits, the declaration ranges
of a target, `lake env lean Ranges.lean` with a cap of 1,800 s, the
`cargo check` of a source mutant, with a cap of 1,800 s, and the
comparator of the [comparator](#comparator) part.

krepi's own modules, in the rows of the base build, are every module below
`Krepi` but the root module, and the reviewed external declarations
installed for qualification cases. A message counts for them when its
`error:` or `warning:` line names the file of one of them; a message in a
generated file, Lake's own `error: build failed`, a `trace:` line and a
message without a position do not. The base round also reads what
`leanchecker` and `lean --version` print before they are classified: a
`leanchecker` that exits with a status other than 0 without reporting a
kernel problem, and a `lean --version` that does not exit with
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
qualification case, an audited theorem, the base round, a target, a
registered mutant of a target, the source mutants of a run of
`formal mutants`. A phase is a part
of the pipeline with a budget of its own, such as the qualification. A unit
with a command that was a tool failure is concluded `TOOL_FAILURE`, and one
with a command that met a budget, or did not start because its limit was
used up, `BUDGET`, whatever its phase concludes.

The status of a run that the [disk guard](#shard-plan-and-disk-guard)
refused is `NOT_RUN`; otherwise it is the first of these that applies:
`TOOL_FAILURE`, `BUDGET`, `STALE`, `REJECTED`, from its failures and the
conclusions of its units; `TOOL_FAILURE` when a unit was `NOT_RUN`
without another failure; `SCOPED` for a run of named targets; and
`VERIFIED`. The run is a tool failure, and not complete, after an
internal error, such as a host other than `linux-aarch64` or
`darwin-arm64`, a tool manifest or a target registry that cannot be read,
a tool manifest that is not the snapshot's, a failed Git command, a failed
export, a shard plan or a reading of the free space at the start that
cannot be read, a reading of the free space during the run that cannot be
started or panics, a listing of the installation that cannot be taken
before the first phase or after the last or that differs after the last, a
phase that returns an error or panics, a work directory that cannot be
removed or whose removal ends after the deadline of the closing steps, or
a panic of the run itself. After an error of the export or of
its checks, or of a phase, the closing steps still run; an error of the
start ends the run without the second snapshot, and a panic of the run
outside a phase ends it without any later command. The receipt is written in every case. It
is a tool failure as well when the gate inputs are not clean at the start,
when `KREPI_FORMAL_TRIGGER` names no mode of a job of CI
([receipt](#receipt)), when a name given with `--target` is not in
`verification/targets.json` or the target of a shard is not a formal
target of it, and when a registered unit has no conclusion or more than
one, or a conclusion is given for a unit that is not registered. After any
failure before the phases, the refusal of the disk guard included, no phase
runs, and after a phase stops no later phase runs; every registered unit
without a conclusion is then `NOT_RUN`. A run of named targets is
`SCOPED` and is never complete. A run of the whole gate, or of a part
([shards and merge](#shards-and-merge)), is complete when its only failures
are `STALE` and none of its units is `NOT_RUN` or `BUDGET`, so a run that
the disk guard refused is not complete.

The command exits with 0 for `VERIFIED` and `SCOPED` and 1 for any other
status, `NOT_RUN` included, and prints each failure on standard error. It
exits with 2 on a usage error, and by the signal after a stop signal,
without a receipt in both cases; a run that a stop signal ends keeps its
work directory unless the signal arrives once the run has started to
remove it. When the run directory or the receipt cannot be written, it
writes the receipt to standard error and exits with 120.

### Receipt

`receipt.json` has schema 7. It is the pretty form of `serde_json`, with
the fields in the order of the tables below and every map sorted by its
keys; times are seconds, rounded to milliseconds. The base record of a
lane, `base.json`, which its base run writes in place of `receipt.json`,
has the same fields with schema 1, and `base_record` `null`
([shards and merge](#shards-and-merge)).

| Field | Content |
| --- | --- |
| `schema` | `7` |
| `command` | `cargo xtask formal run` |
| `status` | `VERIFIED`, `REJECTED`, `STALE`, `TOOL_FAILURE`, `BUDGET`, `NOT_RUN` or `SCOPED` |
| `complete` | Whether the run is complete, as defined above |
| `trigger` | `mode`: `SCOPED` for a run of named targets; for a run of the whole gate or of a part, the mode that `KREPI_FORMAL_TRIGGER`, the variable through which a job of CI gives the trigger of its run, names, `REQUIRED`, `FORCED_FULL` or `WEEKLY`, and `MANUAL` when it is unset or empty, or when it holds any other value, `SCOPED` and `MANUAL` included, which is a tool failure before the phases ([results](#results)); `event`, `ref`, `run_id` and `attempt`, from `GITHUB_EVENT_NAME`, `GITHUB_REF`, `GITHUB_RUN_ID` and `GITHUB_RUN_ATTEMPT`, or `null` |
| `targets` | The names given with `--target`, sorted, or the target of a part of a target; empty for a run of the whole gate, for the qualification job and for the runs of a lane |
| `shard` | The part of a run with `--shard`, `qualification`, `lane/<name>` or `target/<name>/<i>`, or `null` |
| `host` | `linux-aarch64` or `darwin-arm64`, or `null` on another host |
| `image` | The image of a run on `linux-aarch64`, below, or `null` on another host |
| `run`, `directory` | The identifier of the run, and its directory relative to the repository root |
| `started`, `seconds` | The Unix time in seconds at which the run started, and how long it took |
| `commit`, `tree` | The snapshot commit and its root tree, or `null` |
| `inputs` | `before` and `after`, the object of each gate input (`mode`, `type`, `oid`, or `null` when the commit does not have it) at the start and at the end, or `null` when they were not taken; `clean_after`, whether the gate inputs were clean at the end, or `null` |
| `budgets` | `gate_seconds`, 7200 and the budget of each target that the run selects, 7,200 for the qualification job, 300, the registered budget of the lane and 600 for a lane, the budget of its base run, 300 and the budget of the part for a part of a target, 300 and the budgets of its targets for a run of `cargo xtask formal run --target`, or 14,400 for a run of `cargo xtask formal mutants`, whatever the budgets of its targets ([source mutants and survivors](#source-mutants-and-survivors)), and `receipt_margin_seconds`, 300 |
| `resources` | What the run used of the host, below |
| `phases` | For each phase, `budget_seconds`, `seconds` and `ran` |
| `units` | For each unit, its `phase`, its `status` and the `reason` for it, or `null` |
| `qualification` | What the qualification found, below, or `null` when it did not start |
| `base` | What the base round found, below, or `null` when the round stopped before it recorded it |
| `base_record` | For the receipt of a lane, the base record that its comparator run read: `sha256`, of its bytes; `run`, `started` and `seconds`, of the base run; and `comparator_started` and `comparator_seconds`, of the comparator run; or `null` |
| `lane` | For the qualification job and a lane, what its base round held, below, or `null` |
| `handwritten` | For the qualification job, each hand-written module of the Lake project by name, with where its file lies by the [lanes](#lanes): its component, `qualification` or `shared`; or `null` |
| `left_out` | For the qualification job, each hand-written module that the [waivers](#waivers) that hold leave out of the base round, with the target of the waiver; or `null` |
| `part` | For a part of a target, the part and its seed, below, or `null` |
| `proof_targets` | What the run found for each target that the phase `extraction` took, below, by its name: those that it selects and the formal ones, or in the part of a target and in a run of `cargo xtask formal run --target` those that it selects alone, in a lane the targets of the lane, also one that it did not extract since it registers more than 30 mutants or its module is not a Lean module path |
| `guard` | What the guard found on a pull request, below, or `null` without a pull request event or when its phase did not finish |
| `commands` | Every command, in the order of its `sequence` |
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
| `disk_least_available` | The least of those bytes during the run: the run reads them at its start and then every second until its phases and its second snapshot have ended; `disk_available_at_start` less this is the disk peak of the run ([shard plan and disk guard](#shard-plan-and-disk-guard)) |
| `largest_process_max_rss` | The largest maximum resident set of a single process that the run collected, or that such a process collected, in bytes: the largest one process, not the sum of processes that ran side by side |
| `cgroup_memory_peak` | `memory.peak` of the run's cgroup under cgroup version 2, in bytes: in CI the container's. It counts the page cache too, such as the build outputs of Mathlib that Lean maps, so it bounds from above what the container held and does not say what the processes needed |

Each command has these fields:

| Field | Content |
| --- | --- |
| `sequence` | The number of the command in the run, from 1, in the order in which the commands started |
| `started` | When the command started, or was found not to start, in seconds from the start of the run |
| `phase`, `unit` | The phase and the unit of the command, or `null` for the commands of the gate itself |
| `site` | `charon`, `aeneas`, `qualification-build`, `ill-typed-build`, `case-audit`, `base-build`, `target-build`, `axiom-audit`, `leanchecker`, `comparator`, `git` or `cargo-metadata` |
| `argv` | The program and its arguments |
| `cwd` | The working directory, relative to the repository root |
| `class`, `reason` | The class of the result, and the reason for any class but `PASSED`, or `null` |
| `exit_code`, `signal`, `timed_out` | The exit status or the signal that ended the command, each `null` otherwise, and whether it ran until its limit |
| `limit_seconds`, `limit` | The limit of the command, and what set it: `cap`, `phase`, `gate` or `target` |
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
| `statement_hash` | `recorded`, the hash that `statements.json` records, and `computed`, the statement hash of the snapshot commit; two empty strings in a lane |
| `modules` | The modules that the root module imports |
| `own` | krepi's own modules in the stage, whose messages decide a failed build |
| `planned` | The modules of planned statements, built without `--wfail` |
| `theorems` | For each theorem that the audit reported or `statements.json` registers: its `module`; its `kind`, `specification`, `qualification` or `target`; its `state` in `statements.json`, `proved` or `planned`, or `null` for a theorem that is not registered; the `axioms` that the audit reported, or `null`; its `status`; and its `problems`. The status of a registered proved theorem is that of its unit, that of a planned one `NOT_RUN`, and that of any other `VERIFIED` without problems, `REJECTED` with them, or the status that forced `base` |
| `leanchecker` | `version`, the version line of `lean --version`, or `null`; `sha256`, of the `leanchecker` program; `mode`, `fresh`; `prefixes`, the module that it replays, `Krepi`; `module`, the root module that it imports, `Krepi`; `seconds`, of the replay; `max_rss`, the largest maximum resident set of a process that the run had collected when the replay ended, in bytes, or `null`, an upper bound of the largest resident set of the replay; and `max_rss_own`, whether that grew during the replay, so that it is the replay's own, while otherwise it is that of an earlier process |
| `heartbeats` | `method`, `count_heartbeats`; `counts`, the heartbeats of each theorem with a declaration range; and `missing`, why such a theorem, by its name, or a file, by its path, has none |
| `problems` | The problems that reject `base` |

The `lane` record has these fields:

| Field | Content |
| --- | --- |
| `name` | The name of the lane, or `qualification` |
| `components` | The components of the lane, as the lanes give them |
| `modules` | The hand-written modules of the part, those left out included |
| `left_out` | Those of them that the waivers leave out, with the target of the waiver |
| `constants` | The public constants of the modules that the root imports, as the audit printed them, each `<name> <kind> <fingerprint>`, sorted ([base round](#base-round)); one theorem may be in two parts ([shards and merge](#shards-and-merge)) |
| `targets` | Each target that a lane extracted, with its role: `formal`, a formal target of its components; `planned`, a planned one of them that its own modules import; or `cone`, one that the modules that they reach import, for the stage alone |

The `part` record has these fields:

| Field | Content |
| --- | --- |
| `target`, `i`, `k` | The target, the number of the part, from 1, and the number of the parts of the target |
| `budget_seconds` | The registered budget of the part |
| `judges` | Whether the part judges the target and concludes its unit: the first part alone |
| `source_tree` | The object ID of the tree of the workspace that the target is extracted from, as `inputs.before` gives it, or `null` |
| `image` | The reference of the image, as `image`, or `null` |
| `generated` | The SHA-256 of each Lean file that Aeneas wrote for the target, by its path below the output of Aeneas |
| `seed_built` | Whether the build of the proofs of the target, which seeds its mutants, passed |

Each record of `proof_targets` has these fields:

| Field | Content |
| --- | --- |
| `unit` | The unit of the target, `target/<name>`, or `null` for a target that the run did not select and extracted for the base round alone |
| `state` | `formal` or `planned`, as the registry gives it |
| `budget_seconds`, `seconds` | The budget of the target, in a part of a target that of the part, and the seconds during which a command of its unit or of the units of its registered mutants ran, the length of the union of their intervals, each from its `started` for its `seconds`, or 0 without a unit |
| `observed` | What the extraction gave, as for a qualification case |
| `generated` | The SHA-256 of each Lean file that Aeneas wrote, by its path below the output of Aeneas |
| `declarations` | The declarations of its templates that stay axioms once its reviewed external declarations are installed |
| `proof_modules` | Its proof modules, as the registry gives them |
| `typed` | Whether its generated definitions type-check with warnings as errors |
| `mutants` | The seconds of the commands of each registered mutant that the run ran, by its name, which run one after another; their intervals count in `seconds`, so these may add up to more than it |
| `problems` | The problems that reject the target |

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
schema. Schema 7 alone is extended in place, with `part` and with the
record of the qualification receipt that a run of source mutants reads
(planned), so a receipt of schema 7 written before a field was added has
no such field and reads it as `null`, and a merge reads the receipts of
one run only.
Receipts come from two hosts. CI runs the gate on `linux-aarch64`
in the pinned image, as the runner's user, which cannot write the image's
installation, and records the image ([CI job](#ci-job)). Local runs on
`darwin-arm64`, with the installation at `artifacts/formal/tools`, serve
development; there the user owns the installation, the receipt records no
image, and the gate only detects writes to the installation. Only receipts
of CI runs are evidence.

### CI job

The workflow `formal`, `.github/workflows/formal.yml`, runs the gate in CI
as its parts ([shards and merge](#shards-and-merge)) and judges the record
of their merge. It runs on every pull request to `main` when it is opened,
reopened or updated, when a label is added or removed, and when its
description is edited, since the guard reads the labels and the
description; on every push to `main`; on a manual run, whose input `mode`
is `full` or `weekly`, and whose inputs `mutants` and `operators` may ask
for the source mutants of a target; and once a week, on Tuesdays at
12:37 UTC. The runs
of one pull request share a concurrency group, and a newer run cancels an
older one with all its jobs, also those that wait for others, so that no
older run concludes after a newer event; any other run has a group of its
own. A re-run of a run of a pull request keeps the event of that run, so
the first step of each of the six checks below fails on an attempt after
the first unless the run is the newest run of `formal` on a pull request
with the same head, which it asks the API of the workflow runs with the
token of the run: a re-run of an older run fails, though it still joins
the group and cancels a newer run that is in progress, which must then be
re-run by hand. The variable `KREPI_FORMAL_TRIGGER` of the workflow gives the parts
the mode of their trigger ([receipt](#receipt)): `REQUIRED` on a pull
request, `FORCED_FULL` on a manual run `full`, `WEEKLY` on a manual run
`weekly` and on the schedule, and none on a push. The jobs run on a
GitHub-hosted `ubuntu-24.04-arm` runner, may only read the repository's
contents, the six checks and the review below also its workflow runs, use
no stored credentials, and run actions pinned to full commit SHAs.

The gate runs when the label `full-check` is added to a pull request whose
change affects it, by the decision of the job `formal fast` below, and on
a manual or scheduled run of `main`, whatever the decision; on no other
event. Then the job `formal limits` computes the lanes and the limits of
the parts; the job `formal run` runs the qualification job; beside it, the
job `formal lane <name>` runs each lane of `verification/lanes.json`, its
base run and then its comparator run, the job `formal shard <name>/<i>`
each part of each formal target of the head's registry, and the job
`formal scoped <name>` each planned target that the pull request affects,
alone; and the job `formal parts` merges the receipts of the parts. Every
job of the workflow that needs another has a condition that starts with
`!cancelled()`, so that it runs unless the run was cancelled, also when a
job that it needs failed or was skipped, as `formal fast` is on a run of
`main`, and its condition decides the rest.

Six jobs are the checks of the gate: `formal fast` and `formal guard`, and
the four verdicts, `formal merge`, `formal axioms`, `formal leanchecker`
and `formal comparator`, which judge the record of `formal parts`. They
are jobs of the workflow `formal` alone, named as written, without a
matrix, and no other job of the formal workflows has a name that starts
as one of theirs. They are skipped only on `main`: `formal fast` and
`formal guard` on every run of `main` that is not of a pull request, and
the verdicts on a push to `main`, where the job `formal receipt review`
judges the merged head instead. On any other event or ref that they do
not judge, such as a manual run of another branch, each fails, so that no
such run leaves them passed or skipped.

The rules of `main`, a ruleset of the repository, require checks of the
app GitHub Actions to pass on the head of a pull request before it merges.
The required checks are `cargo xtask check`, `check summary`,
`formal fast`, `formal guard`, `formal merge`, `formal axioms`,
`formal leanchecker` and `formal comparator`. Each counts with its newest
run on the head, so an event after the gate ran that fails the verdicts,
such as an edit of the description, blocks the merge until the label
`full-check` is added again. The head must contain `main`, so after `main`
moves a pull request is updated before it merges, and one whose change
affects the gate runs the gate again. Merging with GitHub and pushing a
merge made locally to `main` are both refused until the checks pass. The
ruleset has no bypass list, so the rules bind administrators too, though
an administrator can change them; deleting `main` or pushing to it other
than as a fast-forward is refused. A merge of a head that contains `main` has
the tree of that head, so `main` then has the tree that the checks judged.
The rules require no approving review, and the checks run the workflows
and the xtask of the head: a pull request that changes them is judged by
its own version, so only review catches a change that weakens them
([limitations](#limitations)).

The steps of the job `formal run`, the qualification job:

1. check out the head of the pull request, or the commit of the run, with
   its whole history, which the guard phase of the gate needs for the
   merge base;
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
5. run `cargo xtask formal run --shard qualification`, as the binary of
   step 3, in a container of the image, as the runner's user and group, with
   `--pull never --init --read-only --tmpfs /tmp --cap-drop ALL --security-opt no-new-privileges --network none`,
   the checkout mounted at its own path as the working directory, and the
   variables `GITHUB_EVENT_NAME`, `GITHUB_REF`, `GITHUB_RUN_ID`,
   `GITHUB_RUN_ATTEMPT` and `KREPI_FORMAL_TRIGGER` of the run,
   `GITHUB_EVENT_PATH` naming the copied event, and `KREPI_FORMAL_IMAGE`
   naming the image of `IMAGE`, under
   `.github/scripts/deadline.sh --stop-commands`;
6. always, remove the container of the gate if a cancelled step left it;
7. always, with workflow commands turned off, write a summary of the
   receipt to the summary of the workflow run: the status, whether the run
   is complete, its time and that of each phase, the number of units of
   each status, the image, the resources, the rules of the guard, every
   unit that is not `VERIFIED` and every failure. The step fails when the
   gate's step ran and the job left no receipt;
8. always, write `summary.md` (the status, phases, units, resources and
   failures of the receipt, with its SHA-256), and pack the `logs/` of
   the run into `logs.tar.gz`;
9. always, upload the summary, the archive, `job.txt`, the record of
   steps 2 to 4 and of the start of the gate, the event and the receipt
   as the artifact `formal-part-qualification-<commit>-<attempt>`. The
   logs of the run are uploaded only in the archive.

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

The job `formal run` has 145 minutes, whatever the registry and the
lanes: 15 for the steps before the gate's step, whose own limits add up to
14 (2 to check out, 8 to record the runner and pull, 3 to build xtask and 1
for the probe), 127 for the gate's step and 3 for the steps after it.
`deadline.sh` stops the gate at the deadline of the qualification job, its
7,200 s, and the 300 s of its receipt, 125 minutes, and kills it a minute
later, a minute before the limit of its step. So its receipt is written
before its step ends. When the steps use all their time, the limit of the job may
cut the upload; the receipts are still written in the checkout. When the
step of a part is cancelled or reaches its limit, the step after it removes
the container, and the part writes no receipt.

The gate's step fails whenever the gate does not exit with 0, `REJECTED`
included, and so does each step that runs a part in the jobs of the lanes
and of the parts of the targets; nothing marks a failure as expected.

The job `formal limits`, before the parts, checks out the head and
computes from the head's `verification/lanes.json` the jobs of the lanes,
one for each lane, and from its `verification/targets.json` the parts of
the targets, one for each part of each formal target with the budget of
the part, and the jobs of `formal scoped`, one for each planned target
that `formal fast` lists, with the budgets of its parts added; the parts
that the registry gives a target, or one with the budget of the target,
1,800 s unless the registry gives another ([proof
targets](#proof-targets)). The deadline of a part of a target and of a job
of `formal scoped` is 300 s and that budget, and each has the 300 s of its
receipt; the step that runs one has the minutes of its deadline and
receipt, rounded up, and two more, as `deadline.sh` kills its command a
minute after its deadline, and its job 15 minutes before that step, the
step and 3 minutes after it. The deadline of a lane is 300 s, its
registered budget, 2,400 s unless the lanes give another, and the
extraction margin of 600 s; its base step has the minutes of that deadline
and the 300 s of its receipt, rounded up, and two more, 62 for the default
budget, and its job 15 minutes before that step, the step, the 37 minutes
of its comparator's step and 3 minutes after them, 117 for the default
budget. So the receipt of each part is written before its step ends,
however many lanes and formal targets there are. A part of a target whose
registered budget is more than the shard limit of 3,300 s fails the job,
as does a target of more than 4 parts or whose parts have budgets of more
than 7,200 s in all, as `cargo xtask formal check` refuses them ([shards
and merge](#shards-and-merge)), so the job of a part has at most 85
minutes and a job of `formal scoped` at most 150. A job of a hosted runner
ends after 360 minutes; when the budget of a planned target needs a longer
job, or a target name is not of lowercase letters, digits and hyphens, the
job `formal limits` fails, the jobs of the parts and of `formal scoped` do
not run, and the verdicts fail. So it does when the name of a lane is not
of these characters or another lane has it, when a component is in two
lanes, or when the registered budget of a lane and the extraction margin
are more than the shard limit, as `cargo xtask formal check` refuses them
([lanes](#lanes)), so the job of a lane has at most 122 minutes. The
limits of the jobs of the lanes, of the parts and of `formal scoped` are
expressions of their matrix, so each such job writes its limit as
`::notice title=timeout-minutes::<minutes>`, from which the record of the
run takes it ([testing](conventions/testing.md#entry-points)); every other
job of the workflow has a limit written in it.

Each job `formal lane <name>`, beside `formal run`, runs one lane. It is
prepared as `formal run` is, with the shorter probe of `formal scoped` and
without the event, and in a step of its own after the build copies xtask
to `$RUNNER_TEMP/xtask`, outside the checkout, and records its SHA-256.
Its steps then

1. run the base run of the lane, `cargo xtask formal run --shard
   lane/<name> --keep`, which keeps the stage of its base round for the
   comparator, in a container of the image with the flags of the gate and
   the variables `GITHUB_REF`, `GITHUB_RUN_ID`, `GITHUB_RUN_ATTEMPT`,
   `KREPI_FORMAL_TRIGGER` and `KREPI_FORMAL_IMAGE`, under
   `.github/scripts/deadline.sh --stop-commands` with the minutes of its
   deadline and receipt and a minute for its kill;
2. always, remove the container of the base run if a cancelled step left
   it;
3. unless the run was cancelled or the probe failed, also when the base
   run failed, run the comparator run of the lane, `cargo xtask formal run
   --shard lane/<name> --comparator`, in a container of its own
   ([comparator](#comparator)). Its sandbox needs unprivileged user
   namespaces, so the step allows them on the runner, setting
   `kernel.apparmor_restrict_unprivileged_userns` to 0, and the container
   has, besides the flags and the user of the gate, seccomp and AppArmor
   unconfined, an empty `/run/user` and Docker's masked and read-only
   system paths unconfined. A probe of that container first fails the step
   unless the user is not root, the root file system is read-only, no
   capability is left in the bounding set, new privileges are off and `lo`
   is the only network interface. The run then has the checkout mounted as
   for the base run, the runs directory of the checkout mounted a second
   time at `/krepi-runs`, which `KREPI_FORMAL_RUNS` names, a file that sets
   `safe.directory` to `*` mounted read-only at `/etc/gitconfig`, and the
   variables of the base run, under `deadline.sh --stop-commands` with the
   1,800 s of its phase and the 300 s of its receipt, 35 minutes, and a
   minute for its kill, in a step of 37 minutes; it runs the copy of
   xtask, mounted read-only at `/krepi-xtask`, which the container of the
   base run does not mount, and ends by the deadline of the base run;
4. always, remove the container of the comparator if a cancelled step left
   it, within a minute;
5. always, with workflow commands turned off, write a summary of the base
   record and of the receipt of the lane, with the outcome of both steps,
   the seconds of the replay, the upper bound `max_rss` of its largest
   resident set with `max_rss_own`, whether it is the replay's own
   ([receipt](#receipt)), and the resources, to
   the summary of the workflow run and `summary.md`, and pack the `logs/`
   of both runs into `logs.tar.gz`. The step fails when the comparator's
   step ran and the job left no receipt;
6. always, upload the summary, the archive, `job.txt`, the base record and
   the receipt as `formal-part-lane-<name>-<commit>-<attempt>`.

The failure of one lane cancels no other, and without a lane the job does
not run.

Each job `formal shard <name>/<i>`, beside `formal run`, runs a part of one
formal target. It is prepared as `formal run` is, with the shorter probe of
`formal scoped`, and without the event. Its main command,
`cargo xtask formal run --shard target/<name>/<i>` in a container of the image
with the flags of the gate and the variables `GITHUB_REF`, `GITHUB_RUN_ID`,
`GITHUB_RUN_ATTEMPT`, `KREPI_FORMAL_TRIGGER` and `KREPI_FORMAL_IMAGE`, runs
under `.github/scripts/deadline.sh --stop-commands` with the minutes of its
deadline and receipt and a minute for its kill. The job summarizes the
receipt with workflow commands turned off, writes `summary.md` and
`logs.tar.gz`, and uploads them with `job.txt` and the receipt as
`formal-part-target-<name>-1-<commit>-<attempt>`. The failure of one part
cancels no other, and without a formal target in the registry the job does
not run.

Each job `formal scoped <name>`, beside `formal run`, runs alone a planned
target that the pull request affects, which a whole run does not select:
`cargo xtask formal run --target <name>`, which runs only the part of the
target and concludes it as `SCOPED` ([shards and merge](#shards-and-merge)),
with the steps of the shard job and without a trigger. Its main command
runs under `.github/scripts/deadline.sh --stop-commands` in the same way.
The job summarizes the receipt, with workflow commands turned off, and
uploads the receipt, the summary, `job.txt` and the logs packed into
`logs.tar.gz` as `formal-scoped-<name>-<commit>-<attempt>`. Its receipt is
no part of the merge, and the job is no check of the gate. On a run of
`main`, and without an affected planned target, it does not run; until a
planned target is registered in `verification/targets.json`, it never
runs.

The job `formal parts` runs after `formal run`, the lanes and the parts of
the targets unless the run was cancelled or `formal run` was skipped, also
when a part failed or did not run. It runs on the runner without the
image, and its steps:

1. record the start of the job, that of the runner's worker process or
   else that of the step, in `KREPI_FORMAL_MERGE_STARTED`;
2. check out the head;
3. build xtask on the runner, and record the disk and memory in `job.txt`;
4. download every artifact `formal-part-*-<commit>-*` of the run, of any
   attempt, below `artifacts/formal/parts/`: a single artifact into that
   directory itself, several each into a directory of its own;
5. run `cargo xtask formal merge` with every receipt found there, at any
   depth, under `.github/scripts/deadline.sh --stop-commands` with 2
   minutes and 30 s for its kill and, where the runner has
   `/usr/bin/time`, under `/usr/bin/time -v`, whose record goes to
   `job.txt`, else a line there says that it has none. With `time` in
   front, a SIGTERM, at the deadline or from the runner on a cancellation,
   can end the step before the command has ended, and no SIGKILL follows,
   since `time` ends on it and `timeout` waits for `time` alone;
6. always, record the disk and memory again, and write the summary of the
   merge with workflow commands turned off;
7. always, upload `record.json`, `summary.md` and `job.txt` as
   `formal-merge-<commit>-<attempt>`, the name that the job gives the
   verdicts as its output.

A part without a receipt (cancelled, stopped, or whose upload failed)
makes the merge `TOOL_FAILURE`; a part's own conclusion carries into the
merge as in a run of the whole gate ([shards and merge](#shards-and-merge)).
With no receipt at all, the step fails before the command.

On every event of a pull request, two jobs of the workflow run on the
runner without the image. `formal fast` runs
`cargo xtask formal impact --base` with the base of the pull request, which
lists the merge base, the paths changed since, whether they affect the gate
inputs and the registered targets that they affect, and fails only when it
cannot list them; from the list it gives the decision, `affected` or
`unaffected`, and the planned targets that it lists, by names that the
rule of the registry allows, as its outputs, and it uploads the list as
`formal-impact-<commit>-<attempt>`. `formal guard` runs
`cargo xtask formal guard` with the event of the run ([guard](#guard)), and
its failure fails the job. Each first fails on any event but a pull
request and on a re-run of an older run, as above, then checks out the head
with its history, builds xtask, runs its command under
`.github/scripts/deadline.sh --stop-commands` with 1 minute and 30 s for
its kill, and writes what the command printed into the summary of the
workflow run, with each carriage return escaped and indented as code; each
has 10 minutes.

The four verdicts run after `formal fast` and `formal parts`, on the
runner without the image, with 15 minutes for `formal merge` and 6 for the
others. Their first step, the same in all four, judges the event:

- on a pull request, it fails unless `formal fast` succeeded; a change
  that does not affect the gate passes without a record, and one that
  affects it needs the event that runs the gate, the label `full-check`
  added, and fails on any other with `the change affects the gate, which
  did not run on this event`; without a decision the step fails;
- on a manual or scheduled run, the gate ran when the run is of `main`,
  and the step fails otherwise;
- on any other event the step fails;
- on a re-run of an older run of a pull request, as above, it fails
  first;
- when the gate ran, the step fails unless `formal parts` succeeded or
  failed, so that it ran to its end.

A later event of a pull request whose change affects the gate, such as a
push or an edit of its description, therefore makes the verdicts fail
until the label `full-check` is added again on that head. When the gate
ran, each verdict downloads the record from the artifact that
`formal parts` names and requires its `schema` to be 4, its `run_id` that
of the run, its `commit` the head and its `trigger` the mode of the run,
and then `passes` for `formal merge`, and `gates.axioms`,
`gates.leanchecker` or `gates.comparator` for the other three
([shards and merge](#shards-and-merge)). With workflow commands turned off
where they print text of the head, `formal merge` then writes the summary
of the merge into the summary of the workflow run, or the paths of a
change that does not affect the gate; `formal axioms` whether its gate
passes, the axioms of each audited theorem of the record, or that there is
no audited theorem, and each target of a waiver of the record, whose proof
modules that no other formal target lists the base audits leave out and
whose part audits them when its proofs build, each name of the record as
a JSON string in code, with `\u0060` for each backtick; `formal
leanchecker` whether its gate passes; and `formal comparator` whether its
gate passes and the status of each unit of the comparator, or that there
is no proved statement. For a change that does not affect the gate, the
three verdicts of the hard gates write
`unaffected: the change does not affect the gate`.

On a manual or scheduled run of `main`, which has no `formal fast`,
`formal merge` also checks out the commit, builds xtask, runs
`cargo xtask formal impact` on the commit itself under `deadline.sh` and
writes its decision into the summary, which changes nothing: such a run
runs the gate whatever the decision. After a record that passes, it reads
the record back with `cargo xtask formal receipt --require-fresh` under
`deadline.sh --stop-commands`, whatever the command concludes, so that its
log holds `formal receipt: CURRENT and fresh` for a fresh record of `main`
([current and fresh records](#current-and-fresh-records)); the readback
changes no verdict.

The job `formal receipt review` runs on a push to `main` alone, the merge
of a pull request, with 15 minutes, read access to the contents and the
workflow runs of the repository and the token of the run. It checks out
the merge with its history, builds xtask, and fails unless the merge has a
second parent, the merged head, whose tree the merge keeps. It runs
`cargo xtask formal impact --base HEAD^1` under `deadline.sh`, which with
the same trees decides on the head against the first parent. A change that
does not affect the gate passes, with `unaffected: not evidence of
CURRENT`. Otherwise the job takes the newest run of `formal` on a pull
request with that head whose latest jobs `formal run` succeeded or failed
and `formal merge` succeeded, downloads its merge record of the highest
attempt that has not expired with `gh run download`, and judges it with
`cargo xtask formal receipt` under `deadline.sh --stop-commands`: `CURRENT`
passes, and so does `WAIVED`, whose waivers hold on the UTC date of the
review; anything else fails, and so does a missing run or record
([current and fresh records](#current-and-fresh-records)).

The job `formal mutants` runs on a manual run of `main` whose input
`mutants` names a target, beside the gate. It fails unless the target is
a formal target of the registry and each word of the input `operators` is
an operator of `cargo xtask formal mutants`, and then runs, in the pinned
image with the flags of the gate,
`cargo xtask formal mutants <target>` with an `--operator` for each word,
or every operator when there is none, under `deadline.sh --stop-commands`
with the 14,400 s of the command and the 300 s of its receipt, 245
minutes; its step has two minutes more, and the job 20 more than its
step, 267. It summarizes the receipt with workflow commands turned off and
uploads the receipt, the summary, the record of the runner and the logs in
`logs.tar.gz`, and the list of survivors of a run that passed, as the job
of the mutants of the [calibration target](#calibration-target) does, as
`formal-mutants-<commit>-<attempt>`.

The measurement jobs `leanchecker fresh`, `leanchecker prefix` and
`lake comparator` are in the workflow `formal measure`,
`.github/workflows/formal-measure.yml`, which has the variables `IMAGE` and
`GATE_FLAGS` of the workflow `formal`. They run on a manual run of that
workflow on `main` (`workflow_dispatch`) and when the label `formal-measure`
is added to a pull request to `main`, and on no other event. Each waits for
an earlier run of itself on the same pull request or commit instead of
cancelling it. The main command of each of their long steps runs under
`.github/scripts/deadline.sh --stop-commands` with a deadline two minutes
before the step's limit and a minute for its kill; a body of shell code
runs there as a script with the flags of the runner's shell,
`-eo pipefail`, so that a failed command in it fails the step.

- `leanchecker fresh` and `leanchecker prefix`, 120 minutes each, prepare
  as the job `formal run` does and run the whole gate, without `--shard`,
  without the probe and with `--keep`, which keeps the stage of the base
  round; a gate that exits with 1 passes there, and any other status but 0
  fails. The gate's step has 75 minutes there, which hold a qualification
  that uses its whole budget and a base round, with its replay, of the
  expected length. Then they drop the page cache of the runner and run, in
  the stage of the base round, in a container with the flags of the gate,
  `lake env /usr/bin/time -v leanchecker --fresh Krepi`, or
  `leanchecker Krepi` and then `leanchecker KrepiGen` in the same way, each
  with the variables of tool commands, which a test keeps equal to those of
  the gate but for the home and temporary directories. This step has 30
  minutes, and fails when the base round did not build its stage or
  `leanchecker` does not exit with 0.
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
  was removed when the deadline cut the call, and the time from the start
  of the job to the end of the last call and to the summary. The output and
  the `/usr/bin/time` record of each call, the times and the receipt with
  its logs are uploaded as `formal-leanchecker-<mode>-<commit>-<attempt>`.
- `lake comparator`, 45 minutes, writes a Lake project from the counter
  fixtures of `xtask/src/formal/fixtures/base/counter/`, with two
  handwritten challenges, and three configurations: a challenge that the
  solution proves, the statement module as the challenge, and a challenge
  that the solution proves only in a weaker form. It records the kernel, the
  settings of user namespaces, Docker's security options, and the version of
  bubblewrap and the executables of the toolchain in the image, and fails
  when the image has no `leanexport`, the exporter that the comparator runs.
  In a copy of the project, in a container with the flags of the gate whose
  home and temporary directory are its `/tmp`, Lake builds the solution, and
  for each configuration `leanexport` exports from the module `Krepi` what
  the comparator exports of a solution: `Quot`, `Quot.mk`, `Quot.lift` and
  `Quot.ind` when `Quot.sound` is permitted, the theorems, the permitted
  axioms and the constants that the kernel builds in; an export that fails
  is removed; that step has 5 minutes. In a step of 25 minutes, it then
  runs `lake comparator` on each configuration, in a new copy of the
  project, in two modes, `plain`, where the comparator builds
  and exports the solution itself, and `export`, where it judges the export
  with `--solution-from-export`, and in four container settings in turn:
  `gate`, the container of the gate; and, after
  `kernel.apparmor_restrict_unprivileged_userns` is set to 0 on the runner,
  `gate-userns`, the container of the gate again, `relaxed`, that container
  with seccomp and AppArmor unconfined and an empty `/run/user`, which
  bubblewrap needs as a mount point, and `relaxed-systempaths`, that with
  Docker's masked and read-only system paths unconfined as well. It records
  the exit status and output of each export and each run, which it prints
  with workflow commands turned off, summarizes them by setting, mode and
  configuration, and uploads them with the project as
  `formal-comparator-<commit>-<attempt>`. A result of an export or of the
  comparator never fails the job; an error of Docker, exit status 125 to
  127, a failed sysctl or an image without `leanexport` does.

## Proof targets

`targets.json` has schema 3. Each entry under `targets` describes one
extraction and its obligations. The fields are those of the CAS project,
with the state, the budget and the parts of a target added and a cut point
written as an object; a field that the table does not list is refused:

| Field | Meaning |
| --- | --- |
| `name`, `module`, `feature` | Target name, generated Lean namespace, feature ID (`krepi.<area>.<feature>`) |
| `state` | `formal`, the default, for a target that the gate verifies, or `planned` for one that it only extracts and type-checks; a run of the whole gate selects the formal targets, a planned one runs when `--target` names it, and a run with a base round extracts, for that round, each planned one whose generated modules a hand-written module imports |
| `budget` | The seconds that the unit of the target and its mutants may take, 1,800 when the field is left out, of a target without `parts` |
| `parts` | The parts of the target, from 1 to at most 4, each a job of the gate of its own ([shards and merge](#shards-and-merge)): each an object with its `budget`, 1,800 when the field is left out, and its `mutants`, the names of the registered mutants that it runs. Left out or empty, the target is one part with its `budget` and every mutant |
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
- a target name is made of lowercase letters, digits and hyphens and
  starts with a letter or a digit;
- a target with a `module` has at least one root in `start_from`;
- a formal target has at least one obligation and at least one mutant, and
  every obligation has at least one theorem; a planned target needs neither
  an obligation nor a mutant;
- every mutant names at least one theorem in `fails`, each a theorem of an
  obligation of its own target, and no target registers more than 30
  mutants, however many parts hold them;
- a target with `parts` has no `budget` of its own and at most 4 parts,
  whose budgets add up to at most 7,200 s; each of its registered mutants
  is in exactly one part, and a part names only mutants of the target;
- no key is in two of `proves`, `unclosed` and `derived`;
- every cut point and every axiom of `verification/axioms.json` has a
  `source` and a `reason` that are not blank;
- every key of `proves` and `unclosed` is a production function of the
  [inventory](#legacy-inventory-and-admission), and every entry of
  `derived` is a key `file#Type::method` of a method that a
  `#[derive(..)]` of a production type in the file defines, not a
  production function;
- the registered budget of each part of each formal target, whatever its
  workers, is at most the shard limit of 3,300 s
  ([shard plan and disk guard](#shard-plan-and-disk-guard)).

`cargo xtask formal check` also checks the shard plan
([shard plan and disk guard](#shard-plan-and-disk-guard)) and the lanes,
which hold the module of every formal target as a component
([lanes](#lanes)).

The job `formal limits` of the workflow `formal` ([CI job](#ci-job)) also
fails on another target name before the names reach a gate, on a target of
more than 4 parts or whose parts have budgets of more than 7,200 s in all,
on a part of a target whose registered budget is more than the shard
limit, and on
a lane whose name is not of lowercase letters, digits and hyphens or that
another lane has, a component in two lanes, and a lane whose budget and
the extraction margin are more than the shard limit.

The targets of the registry run in two phases of the gate. The phase
`extraction`, before the base round, extracts the targets that the run
selects and, in a whole run, every formal target, since the base round
builds every proof and so needs the generated definitions of each formal
target; in a whole run, it also extracts each planned target whose generated
modules, `KrepiGen.<module>.<file>`, the header of a Lean file below
`verification/Krepi/` imports, read as the
[import rule](#statements-and-proofs) reads it, so that the round builds,
audits and replays the statements and the proofs that use them. The
selected targets have a unit of their own, `target/<name>`, and the
others are extracted as commands of the unit of the base round. Such a
planned target is neither checked against its registration nor
concluded, runs no mutant and has no unit and no part of its own; its
record in the receipt has no unit. A planned target that the run does not
select and no hand-written module imports is not extracted. The phase
reads the imports from the checkout when the run starts and stops when
those of the export are other ones. A part of a target extracts its
target alone, the qualification job none, and the base run of a lane the
targets of the lane but the formal ones of the [waivers](#waivers) that
hold, which leave out no planned target, as commands of
`base/lane/<name>` ([base round](#base-round),
[shards and merge](#shards-and-merge)). The phase has the budgets of the
targets that it extracts, a part of a target that of the part, or the
extraction margin of 600 s in a lane, and the gate's budget grows by those
of the selected targets alone. For
each target, in `work/targets/<name>/`, it

1. extracts the target from the root package of the exported workspace,
   for the extraction triple, with its `start_from` roots and the patterns
   of its cut points ([extraction](#extraction));
2. creates its stage from the Lake project and installs what Aeneas
   generated, with the reviewed external declarations of its `models`
   directory in place of the templates: a reviewed file may only turn
   declarations of its template into definitions, each of a Rust item
   that a model of `models.json` lists among its `items` with the target
   among its users, and may not add an axiom or use `sorry`. A reviewed
   file that is missing or does not fit rejects the target, and a file
   that cannot be read or written is a tool failure;
3. type-checks the generated definitions with
   `lake build --no-cache --wfail KrepiGen.<module>.Funs`, at the call site
   of the target builds, with a cap of 7,200 s; the declarations of the
   templates stay declarations, also those of external functions without a
   model;
4. for a selected formal target, checks its registration against the
   translation and the inventory of the export.

A selected planned target is then concluded: `SCOPED` without a problem,
and `REJECTED` with one, unless a command forces its conclusion. A target
that registers more than 30 mutants in all its parts is not extracted,
also in the run of one of its parts, and a selected one is `BUDGET`.
The base round builds the generated modules of each target
whose definitions type-check; for one whose definitions do not, nothing is
built and the round is rejected, as for a qualification case whose code
does not build. The phase `targets`, after the base round, takes each
selected formal target in its stage: it copies the hand-written module
files that the base round found, or in the part of a target those that
the same listing of the snapshot finds without the base round, writes the
root module `Krepi` that imports the target's proof modules, builds it with
`lake build --no-cache --wfail +Krepi`, the seed of its mutants, runs the
audit of the base round
on the proof modules with `lake env lean Audit.lean`, and rejects the
target unless the audit reports each theorem of its obligations in one of
its proof modules with only the axioms that the target row of the
allowlist admits, its `trusted_axioms` and the declarations that its
templates keep, and unless its registration, its installation and its
type check had no problem. A formal target whose obligations name no
theorem is rejected. A build of the proofs that fails without an error or a
warning in a proof module is a tool failure of the target, generated or
model code that did not build. Once the target is verified, each of its
registered [mutants](#mutants) runs in a unit of its own. A target has
its unit in its first part alone: each other part extracts the target,
installs and type-checks it and builds its proofs, the seed, in the same
way, but does not audit or conclude it, and runs its own mutants on that
seed once it built, whether or not the first part verifies the target;
without a seed, its mutants are `NOT_RUN`, unless a command of the target's
unit forces them, as a budget used up forces `BUDGET`
([registered mutants](#registered-mutants)). A run of the whole target,
with `--target`, has its unit and every mutant in one run.

The commands of the unit of a target and of the units of its registered
mutants share its budget, the sum of the budgets of its parts, in a part
the budget of the part, which counts the time during which at least one
of them runs, in either phase: the length of the union of their
intervals. Commands that run one
after another count their seconds, commands that run side by side count
the time that they share once, and the base round between them, or any
other time when none of them runs, does not count. A command that starts
when these units have used `c` seconds runs for at most the budget less
`c`, so commands that run side by side reach that limit together. A
command that meets it concludes its own unit `BUDGET`: the unit of the
target while the target is extracted, built and checked, or that of a
mutant, which leaves the target as it was concluded. A command that would
start once the budget is used up does not start, is `NOT_RUN` and
concludes its unit `BUDGET` too; the run is `BUDGET` either way. In a part
that does not conclude the unit of the target, a command of the seed that
meets the budget makes the mutants of the part `BUDGET`. The calibration
target registers three parts of 1,000 s, each within the shard limit
([calibration target](#calibration-target)); a target of the kernel keeps
the default.

The checks of the registration: every reached local function is
in `proves`, `unclosed` or `derived`, every cut local item in `unclosed`,
where a cut derived method may be in `derived` instead, and the reached
external items are exactly those of `unconstrained`; every entry of these
lists is still reached, and a `derived` entry is reached as a method of a
derived implementation of a standard trait, under one Rust name. A Rust name
maps to the inventory key of its function: the path below the module of its
source file, `krepi_kernel::m::inner::f` in the file of `m` for `inner::f`,
gives the inline modules; the self type of an implementation,
`{impl Trait for krepi_kernel::m::Type}`, the owner; and the loops of a
function, whose Rust name is that of the function, map to its key, as the
default method of a trait and its loops map to `Trait::method`. A reached
function that maps to no function of the inventory is not registered, so the
run fails: the body of a closure, which has a function of its own (rule R4 of
the [provable subset](conventions/provable-subset.md)), a loop that the tools
place in a file outside the package, such as that of a macro, a function in
the body of another, and a method whose key is both that of a function of
the inventory and that of a derived method, as the `eq` of a type that
derives `PartialEq` and also implements `PartialEq<u32>` by hand, which the
key cannot tell apart. A key that the inventory numbers, as `#2` and `#3`
for the second and third method of trait implementations with one key in a
file, is ambiguous too: a Rust name does not say which number is its own,
so every reached method of that key fails as not registered, even where
only one of them is reached.

A target extracts the production code itself. A hand-written mirror of the
implementation, an unmatched extraction root, an unreviewed rewrite of
execution semantics or an edited generated file is rejected.

## Mutants

A mutant is an edit of the source of a target that its proofs are to
reject: the proof of a theorem of the target fails on the mutant. A formal
target registers its mutants in `targets.json`, each in one of its parts
([proof targets](#proof-targets)), and
`cargo xtask formal mutants` generates more
([source mutants and survivors](#source-mutants-and-survivors)); both are
built and judged the same way.

### Registered mutants

Once the phase `targets` has verified a formal target, the run prints the
declaration ranges of its proof modules in its stage, as a command of the
target's unit, and takes each of its registered mutants in a unit of its
own, `target/<name>/mutant/<mutant>`, whose commands share the budget of
the target. A part of a target takes the mutants of the part alone, with
the budget of the part; a part other than the first does so once the
build of its proofs, its seed, passed, without judging the target, and
the merge requires the parts of a target to have taken one seed
([shards and merge](#shards-and-merge)). Two workers take them in turn,
the first the first, the
third and so on, and the second the second, the fourth and so on, each in
the order of the registry. Each worker prepares its next mutant, steps 1
to 5, while it builds the one before, step 6, and a mutant that a step
before the build concludes is not built. So up to four mutants of a part
are prepared or built at once, each in its own work directory, with its
own home and temporary directories, stage and Cargo target directory. A
worker that stops at an error, or panics, stops the other before its next
mutant, and the phase stops, a tool failure of the run: the mutants
concluded so far keep their conclusions, and the others are `NOT_RUN`.
For each mutant:

1. a mutant whose `fails` names a theorem that the ranges do not give as a
   top-level theorem of the proof modules is rejected, without a command;
2. its `find` must occur exactly once in its `file`, which is relative to
   the package of the target, in the export; otherwise it is rejected;
3. the package is copied from the export, with the Cargo configuration of
   the export, into `source/` of its work directory and edited there,
   `find` replaced with `replace`;
4. the copy is extracted as the target is, with the extraction triple, its
   roots and its cut points, and what the tools generated is installed in a
   new stage of its own; an extraction that is not complete and generated
   files that cannot be installed make the mutant inconclusive;
5. the build directory of the stage of the target, `.lake/build` below its
   Lake project, is copied into the new stage: Lake replays a module whose
   source and imported modules are those of the build of the target, such
   as a module of the specification or a generated module that the edit
   leaves as it was, and builds again every other one, since it reads
   each source to decide;
6. the proofs are built there as those of the target, with the hand-written
   Lean of the export, the root module of its proof modules and
   `lake build --no-cache --wfail +Krepi`, at the call site of the target
   builds, and the build is judged.

The mutant is `VERIFIED` when its build is rejected, `REJECTED` when it is
accepted, with the reason `the mutant was not rejected by` and its `fails`,
when it is inconclusive, with a reason that starts with `inconclusive`, and
in the two cases before its build; a build that Lake or a Lean process it
ran did not finish makes it `TOOL_FAILURE`. Each of them but `VERIFIED`
fails the run. In a run that judges a target, its mutants are `NOT_RUN`
when it is not verified; a part that does not judge it runs its mutants
once its seed built, whatever the first part concludes, and leaves them
`NOT_RUN` when the seed did not build; in both cases unless a command of
the target's unit forces them.
When the ranges make no table, the target is a tool failure and its mutants
are inconclusive. The run lists the build directory of the stage of the
target, as it lists the installation, before the first mutant and after
the last; a change of it makes the target a tool failure, which fails the
run whatever its mutants concluded.

### Judging the build of a mutant

A build that passes is accepted. A build whose Lake or a Lean process that
it ran was killed or ran out of time tells nothing. Otherwise the log of
the failed build is read; it is confined to the proof modules when all of
these rules hold, and the mutant is inconclusive, with the rules that do
not, otherwise:

1. Lake exits with 1;
2. no line is `error: Lean exited with code <n>`, which Lean 4.35.0 prints
   only when Lean ends otherwise than with 1 after an error;
3. no line is `info: stdout:`, `info: stderr:` or `info: stdout/stderr:`,
   output of a process besides its messages, such as a panic;
4. every `error:` and `warning:` message with a position is in the source
   file of a proof module;
5. no job line of another module is marked `⚠` or `✖`;
6. each `✖` job of a proof module has an error in its own file after its
   job line and before the next one;
7. no other `error:` or `warning:` line appears than the last
   `error: build failed`;
8. the log has the failure summary `Some required targets logged
   failures:`;
9. the summary lists proof modules alone;
10. each module that it lists has a `⚠` job, or a `✖` job with an error in
    its file.

A job line is `<mark> [<i>/<n>] <verb> <module> (<time>)`; `trace:` lines,
other `info:` lines and the continuation lines of a message do not count.

The errors of a confined log are placed by the declaration ranges of the
build of the target. Its stage prints them with
`lake env lean Ranges.lean`, at the call site `declaration-ranges`: for
each proof module, the range that Lean stored for each of its
declarations, a private one by its name without the private prefix, and
their count. The file of the printer is not a module file, so its imports
bring the private declarations of the proof modules, which are module
files. By the ranges:

1. an error counts against the top-level declaration whose range holds its
   position, both ends included; the range of a declaration command runs
   from its documentation comment, attributes and modifiers to its last
   token, so a failed attribute, which Lean reports at the start of the
   command, counts against the declaration;
2. a nested declaration, such as a constructor, a field of a structure, a
   `where` function or a derived instance in its structure, and a range
   that starts where the one around it starts, count with the declaration
   around them;
3. the names of one range count together, such as a derived instance and
   its method, whose range is the name of the class;
4. an error in no top-level range, as in the prefix `omit … in`, a
   `variable`, an `example`, the module documentation, a namespace or its
   `end`, counts against no declaration and is listed by its position;
5. only a top-level `theorem` is a theorem: errors in a `def`, an
   `abbrev`, an instance or a structure alone reject no mutant.

The build is rejected when an error counts against a theorem of `fails`,
and accepted otherwise. The ranges make no table when

6. a proof module is not counted exactly once, or its count differs from
   the ranges read for it;
7. the printer reports a module that it does not import;
8. a line is malformed or names a module that was not asked for;
9. two ranges overlap without one holding the other;
10. the printer did not exit with 0 by itself; its output is then not read.

### Source mutants and survivors

`cargo xtask formal mutants TARGET [--operator NAME]... [--calibration] [--keep]`
is a run of the gate with `--target TARGET`, `SCOPED` and never complete as
any run of named targets, with a budget of 14,400 s in place of the gate's
7,200 s and those of its targets. Once the phase `targets` has verified the
target, the run generates its source mutants from the export instead of
running its registered ones, and runs each in the unit
`mutants/<target>`, with the theorems of all the obligations of the target
as its `fails`.

The points of the mutants are in the bodies of the functions of `proves`
and `unclosed`, which the extraction reaches from the roots; `derived`
methods have no source, and test code is not edited. The parser of the
inventory finds the bodies, and the positions of their tokens give the
points. Nothing is edited in a pattern, such as the arms of a `match` or
an `if let`, a type, an attribute, a macro call, a nested item such as a
`const`, the length of an array or a generic argument. The operators are
all of these, or those that `--operator` names:

| Operator | Change |
| --- | --- |
| `ordering` | `<` to `<=`, `<=` to `<`, `>` to `>=`, `>=` to `>` |
| `equality` | `==` to `!=`, `!=` to `==` |
| `arithmetic` | `+` to `-`, `-` to `+`, `*` to `+`, `/` to `*`, `%` to `/`, and the same for compound assignments |
| `bitwise` | `&` to `\|`, `\|` to `&`, `^` to `\|`, `<<` to `>>`, `>>` to `<<`, and the same for compound assignments |
| `logical` | `&&` to `\|\|`, `\|\|` to `&&` |
| `negation` | A unary `!` removed |
| `literal` | An integer literal `0` to `1`, `1` to `0` and any other `n` to `n + 1`, with its suffix |
| `condition` | The condition of an `if`, not of an `if let`, to `true` and to `false`, two mutants; conditions of `while` and guards of `match` stay |
| `method` | `checked_add` and `checked_sub`, `wrapping_add` and `wrapping_sub`, `saturating_add` and `saturating_sub`, `min` and `max`, each to the other |

Each keeps the types of the code. The `find` of a mutant is the shortest
text of its file that holds its point, lies within its lines, cuts no word
and occurs once in the file, and its `replace` is that text edited; a
point without such a text is not generated and is counted. Each mutant is
copied, edited and checked with
`cargo check --lib --locked --quiet --target aarch64-unknown-none` at the
call site `cargo-check`, in the environment of Charon, then extracted,
staged, built and judged as a registered mutant, on two workers as those
are, in the order of their points. A mutant that
`cargo check` does not build is not run and is counted. A mutant whose
build is rejected is killed, and one whose build is accepted survives. An
inconclusive mutant, and one with a command that fails as a tool or meets
the budget, conclude the unit otherwise than `VERIFIED`, and the command
then writes no list and exits with 1. So does a run that is not `SCOPED`
for another reason, such as a unit of the qualification or of the base
round that is not `VERIFIED`. A theorem of the obligations that is not a
top-level theorem of the proof modules, against which no error could
count, concludes the unit `REJECTED` before any mutant is generated.

The run writes the list of survivors of the target,
`verification/mutants/<target>.json`, or that of the calibration below
`verification/qualification/calibration/mutants/`, and prints its counts.
Its fields:

| Field | Meaning |
| --- | --- |
| `schema` | 1 |
| `target` | The target |
| `commit` | The commit of the run |
| `operators` | The operators of the run |
| `run`, `run_id`, `receipt_sha256` | The run directory of the run, the ID of the CI run, if any, and the SHA-256 of its receipt |
| `generated`, `killed`, `unbuildable`, `not_unique` | The numbers of mutants generated, killed and not built by `cargo check`, and of points without a text that occurs once |
| `survivors` | Each survivor: its `point`, `<file>:<line>:<column>`, its `operator`, `find` and `replace`, the inventory key of the `function` that it edits, and the `class` and the `reason` that a reviewer gives it |

A reviewer gives every survivor a class, `missing-lemma` for a property
that the proofs lack, `no-theorem` for a function that no theorem covers,
or `equivalent` for a mutant with the meaning of the source, and a reason
that is not blank. A survivor in a function of `unclosed`, which no
theorem is about, is written with the class `no-theorem` and keeps it.
`cargo xtask formal check` fails on a survivor without a class or a
reason, on one in a function of `unclosed` of another class, and on a
list that does not parse or is not that of a registered target at its
path; it names the functions of the survivors of
class `no-theorem` in its report
([legacy inventory and admission](#legacy-inventory-and-admission)). A
refinement task names the operators that it uses; an operator is added to
this command, not by the task that uses it. In CI, the job
`formal mutants` runs the command on a target of production on a manual
run of `main` ([CI job](#ci-job)).

## Calibration target

The calibration target is krepi's own target of the gate, on which the
checks of a target are tried before the kernel registers one. It lies in
`verification/qualification/calibration/`, which no part of krepi uses and
no image holds:

- a Cargo workspace with its own `Cargo.lock`, in the shape of the kernel
  workspace ([source layout](architecture.md#source-layout)): the root
  package `formal-calibration`, `no_std`, with unsafe code forbidden and
  no dependency, whose modules `handle`, `arith` and `table` have the
  shapes of the first kernel targets, a handle in bit fields, checked
  arithmetic, a table of slots whose capacity is fixed when it is made,
  with a generation for each slot, writes after a check and a bounded
  loop; and one member, `formal-calibration-member`, which the root
  package does not depend on;
- its Lake project, with the libraries of that of `verification/`: its
  `lakefile.toml`, the statements in `Krepi/Calibration/Statements.lean`
  and their proofs in `Krepi/Proofs/Calibration.lean`. It has no
  `lean-toolchain` and no `lake-manifest.json`: the gate writes those of
  `verification/` into each of its stages, the lock with the name of this
  project, so the two projects pin the same Lean and the same packages,
  and a change of the tools changes the files of `verification/` alone;
- its registries: `targets.json`, `statements.json`, and `models.json`,
  `axioms.json` and `tcb.json`, which are empty; its shard plan
  `shards.json`, with the entries `qualification` and
  `target/calibration/1`
  ([shard plan and disk guard](#shard-plan-and-disk-guard)); and its lanes
  `lanes.json`, with the lane `calibration` ([lanes](#lanes)).

`targets.json` registers two targets. `calibration` is formal: twelve
roots in `start_from`, one obligation with one theorem for each, thirty
mutants, each of which fails the proof of the theorem that it names alone,
and three parts of 1,000 s, each with ten of the mutants in the order of
the registry, so that the first part concludes the target and its ten
mutants, eleven units, and each other part builds the seed and runs its
ten; the three add up to 3,000 s, more than the default for one target,
since each mutant is built again in a stage of its own.
`calibration-planned` is planned: it reaches
`core::num::{u32}::count_ones`, which the pinned Aeneas does not model, and
whose generated declaration stays a declaration.

`cargo xtask formal run --calibration` runs the gate in the layout of the
calibration target: the gate inputs and the qualification of the tools,
whose cases build in the Lake project of `verification/`, are those of
every run, and the extraction, the base round and the targets take the
workspace, the Lake project and the registries of the calibration. With
`--target calibration-planned` it extracts and concludes the planned target
alone, without the qualification and the base round. With
`--shard qualification`, `--shard lane/calibration`, with `--keep` and then
`--comparator`, and `--shard target/calibration/<i>` for `i` from 1 to 3
it runs the parts of the calibration, and
`cargo xtask formal merge --calibration` merges
their receipts ([shards and merge](#shards-and-merge)). Neither
target is in `verification/targets.json` or among the declared targets: a
run in the production layout cannot name them and records none, and
`cargo xtask formal check` reads the registry of production alone. Its
Lean is on neither the statement side nor the source rules of the
production project ([statements and proofs](#statements-and-proofs)).
`cargo xtask formal check --calibration` checks it as the production
layout is checked, without contracts and open obligations, which describe
the kernel alone, and `cargo xtask formal mutants calibration --calibration`
writes the list of survivors of its source mutants in
`verification/qualification/calibration/mutants/`.

The workflow `formal calibration`, `.github/workflows/formal-calibration.yml`,
runs it in the pinned image: once a week, on Wednesdays at 13:23 UTC, on a
manual run, and on a pull request to `main` that carries the label
`formal-calibration`, when it is opened, reopened or updated and when that
label is added. It is not a required check, and it is not on the path of
the required gate. Its jobs run on GitHub-hosted `ubuntu-24.04-arm`
runners, may only read the repository's contents, use no stored
credentials and run actions pinned to full commit SHAs:

- `calibration run`, the qualification job of the calibration, checks out
  the head, pulls the image, builds xtask, probes a container of the
  gate, runs `cargo xtask formal check --calibration` on the runner, and
  records the bytes available before it and, where the runner has
  `/usr/bin/time`, its record, else a line that it has none, in `job.txt`;
  then it runs
  `cargo xtask formal run --calibration --shard qualification` in
  a container of the image, with the flags, the user and the mounted
  checkout of the job `formal run` ([CI job](#ci-job)), and the variables
  `GITHUB_REF`, `GITHUB_RUN_ID`, `GITHUB_RUN_ATTEMPT`,
  `KREPI_FORMAL_TRIGGER` and `KREPI_FORMAL_IMAGE`, but no event, so that
  the guard does not run;
- `calibration lane <name>`, beside it, one for each lane of the
  calibration, which the workflow writes out and a unit test keeps equal to
  its lanes, runs the steps of the lane job of `formal`, which a unit test
  keeps equal but for `--calibration` and the prefix of the artifact: the
  base run, `cargo xtask formal run --calibration --shard lane/<name>
  --keep`, and then its comparator run, `cargo xtask formal run
  --calibration --shard lane/<name> --comparator`, in a container of its
  own on the stage that the base run kept, with the copy of xtask.
  A step after it, of one minute, fails unless the comparator left one
  receipt of the lane in which the unit `comparator/calibration` is
  `VERIFIED` and the
  commands of the two challenges that the comparator must reject
  ([comparator](#comparator)) are those of the units
  `comparator-negative/statement` and `comparator-negative/axiom` alone,
  each a `PROOF_FAILURE` whose error log holds Lake's message for it,
  `Challenge and solution theorem statement do not match` and
  `Illegal axiom detected: 'propext'`; it writes each class and the line
  that it found to the log and the summary of the run;
- `planned example`, beside it, runs
  `cargo xtask formal run --calibration --target calibration-planned` in
  the same way;
- `calibration shard <name>/<i>`, beside them, one for each part of each
  formal target of the calibration registry, which the workflow writes out
  and a unit test keeps equal to that registry, runs the steps of the shard
  job of `formal` with `cargo xtask formal run --calibration --shard
  target/<name>/<i>`;
- `calibration merge` runs the steps of the merge job of `formal` with
  `cargo xtask formal merge --calibration` on the downloaded
  `calibration-formal-part-*` artifacts. It runs when the jobs above ran,
  unless the run was cancelled, and it waits for the planned example as
  well, since both run in one matrix job;
- `calibration mutants`, on a manual run whose input `mutants` asks for it
  and on a pull request with the label, runs
  `cargo xtask formal mutants calibration --calibration`.

The parts of the calibration have the trigger `WEEKLY` on the schedule
and none, so `MANUAL`, on the other events ([receipt](#receipt)). Each
main command runs under `.github/scripts/deadline.sh --stop-commands`,
which passes a cancellation on to it and turns workflow commands off while
it prints. With `/usr/bin/time` in front, as for the check and the merge,
a SIGTERM, at the deadline or from the runner on a cancellation, can end
the step before the command has ended, and no SIGKILL follows. The
deadline of the qualification job of the calibration is
the gate's 7,200 s, that of the base run of its lane 300 s, the 2,400 s of
the lane and 600 s for its extraction, that of its comparator the 1,800 s
of its phase, that of the planned example, which runs the part of its
target alone, 300 s and the 1,800 s of its planned target, that of each
part of `calibration` 300 s and its 1,000 s, and that of the mutants the
14,400 s of `formal mutants`; with the 300 s of the receipt, 125, 60, 35,
40, 27 and 245 minutes. Each step has two minutes more than its deadline.
The jobs of the qualification and of the planned example have 23 minutes
more than their step, 150 and 65; that of the lane has 15 minutes before
its base step, the 37 of its comparator's step and 3 after them, 117; that
of a part has 15 minutes before its step and 3 after it, 47, and that of
the mutants 20 more than its step, 267; the merge has 15. The limits of
the jobs `calibration run` and `planned example` and those of the lane
and shard jobs are an expression of their matrix, so each such job writes
its limit in a notice, from which the record of the run takes it, as the
jobs `formal lane`, `formal shard` and `formal scoped` do. A newer event
of the same pull request cancels a job of the parts, of the planned
example or of the mutants that has not ended; the merge of an older run
whose parts it cancelled still runs and fails, and only the latest run of
a pull request counts. Each job summarizes its receipt, and the merge its
record, with workflow commands turned off, since the receipt holds text of
Lean and Lake: the run and shard jobs list the budget and the seconds of
each target, and every summary gives the SHA-256 of the receipts. The jobs
`calibration run` and `planned example` upload the receipt, the summary,
and the record of the runner and the logs of the gate compressed into
`logs.tar.gz`, which for `calibration run` also holds the output of the
check; a lane job uploads `job.txt` and the base record beside them, a
shard job `job.txt`, and the merge its record, its summary and `job.txt`.
The artifacts are
`calibration-formal-part-qualification-<commit>-<attempt>` of the job
`calibration run`,
`calibration-formal-part-lane-<name>-<commit>-<attempt>`,
`calibration-formal-part-target-<name>-1-<commit>-<attempt>`,
`formal-calibration-planned-<commit>-<attempt>`,
`formal-calibration-merge-<commit>-<attempt>` and
`formal-calibration-mutants-<commit>-<attempt>`. The job of the mutants
uploads the list of survivors as well, from `artifacts/formal/mutants/`
and only when its run passed: a run that fails writes no list, and the
checkout may hold the list of an earlier run.

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
([independent evidence](conventions/testing.md#independent-evidence)). The
contracts of the device-tree and page-tables components name their vector
files and their replay modules.

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
usage error. It writes no receipt and does not check the image: the formal
step of `cargo xtask check` runs it in the image that the pin names by its
digest ([vectors in CI](#vectors-in-ci)).

### Vectors in CI

The formal step of `cargo xtask check`
([testing](conventions/testing.md#entry-points)) compares the vectors on
every run of the check, after `cargo xtask formal check`. In containers of
the pinned image ([image pin](#image-pin)), with the flags of the gate, as
the owner of the checkout, which they mount at its path, it replays the
[fixture](#fixture) with `--exact --ignored --nocapture` and requires a line
that starts with `test result: ok. 1 passed; 0 failed`, since an exact
filter that matches no test passes as well. It then empties
`artifacts/formal/vectors`, runs the host tests of the kernel and
user-space workspaces with `KREPI_VECTOR_RESULTS` set to that directory, and
runs `cargo xtask formal vectors` without a component in a container. Each
container is named after the process of the check and its part and is
removed before and after it runs, also when the check stops, which kills
only the Docker client. The image runs executables built on the host, so the
step needs a linux-aarch64 host with Docker and the pinned image: without
one of them, or without Lake in the image, it ends as a tool failure, which
fails the check like a failed step. `--skip-formal` records the step as not
run; no workflow passes it, and the workflows that run the check pull the
pinned image before it and require the step to have passed in its receipt.
Since the check is required, a failed comparison blocks a merge. Selecting
the components one by one and a receipt of the comparison are planned.

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
exactly that problem, within 300 s. The formal step of `cargo xtask check`
runs it in the image ([vectors in CI](#vectors-in-ci)), and a local run
needs the `darwin-arm64` installation at
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
  `verification/Krepi/Proofs/` and the calibration project: the
  specifications below `Krepi/Spec`, their properties and tests below
  `Krepi/SpecProperties` and `Krepi/SpecTests`, the statements below
  `Krepi/Statements`, the models, the qualification proofs with their
  definitions, and the reviewed external declarations below `externals/`;
- the registry of library axioms, `verification/axioms.json`;
- the Lake project files `verification/lakefile.*`, `lean-toolchain` and
  `lake-manifest.json`.

The [calibration target](#calibration-target) has a Lake project of its
own, `verification/qualification/calibration/`, which is on neither the
statement side nor the source rules of this project. Its statement side,
in its own layout, is the same rule applied to that project: its
hand-written `.lean` files outside its `Krepi/Proofs/`, its `axioms.json`
and its `lakefile.toml`, with the hash in its own `statements.json`. It is
not a declared target, so a change of it is not a change of a statement
and needs no label `spec`; its paths are gate inputs, so a change of them
runs the gate.

Generated modules and the root module exist only in the stages of a run.
`verification/tcb.json` is not on the statement side; the registry rules
of the [guard](#guard) review its changes.
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
challenge, and the statement file has only the definition `S`. The
[comparator](#comparator) part generates the challenge from
`statements.json`: a module that imports the stage of the base round but
its proof modules and states `public theorem t : S := sorry` for each
proved statement of a unit.

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
  git rm -r --cached --quiet --ignore-unmatch -- verification/Krepi/Proofs \
    verification/qualification/calibration
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
its theorem is not audited, and the comparator gets no challenge for it.
A proof pull request, with the label `proof`, proves statements that
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
| Mathlib and the Aeneas Lean library | Mathematical definitions and models of integers, slices, `Option`, `Result` and other core items | Pinned Lake lock; library axioms appear in the audit and must be registered in `verification/axioms.json`, but for the native decisions of library lemmas, which `library-native-decision` items of `verification/tcb.json` admit |
| Charon, the Rust nightly and Aeneas with reviewed patches | Translation of the production source into Lean | Pinned sources and binaries; qualification regression; mutants |
| Unconstrained declarations | External functions and types without a model | Theorems hold for every interpretation; listed per target |
| Cut points (`opaque`) | Items translated without their bodies, modelled as deterministic functions of their arguments | Each cut point has a source and a reason, which states that no statement depends on two calls with the same arguments agreeing; review checks this for a function that reads hardware or global state |
| Trusted axioms | Reviewed exceptions, among them the native decisions of lemmas of the Aeneas Lean library | Items of `verification/tcb.json`, each with a reason; an item of a library lemma admits the axioms of that lemma alone, private to the library module that declares it |
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
- a list of survivors that does not parse, is not that of a registered
  target at its path, or has a survivor without a class or a reason
  ([source mutants and survivors](#source-mutants-and-survivors));
- what the gate does not support yet: non-empty `premises` of a target, an
  `exclude` cut point and a model in `verification/models.json`.

Its last line counts the files, functions, derived methods and open
obligations of the inventory and, after them, names the function of each
survivor of class `no-theorem`, which no theorem covers yet. The formal
step of `cargo xtask check` runs it in the production layout first, in
every job of CI that runs the check; `--skip-formal` skips it with the
rest of the step, so with that option run it before proposing a change to
the kernel workspace, a contract or the registries.
The job `calibration run` of the workflow `formal calibration` runs it in
the layout of the calibration.
The removal of a target, a theorem or a proved function, and any widening
of the trusted base, are reviewed through the registry rules of the
[guard](#guard), and `cargo xtask formal impact --base REV` lists the
targets that a change affects. A function without a
proof is never trusted by a proof and appears in a target's `unclosed` list
when reached.

## Editing proofs

A run removes its work directory at its end, so a proof is edited after a
run with `--keep`, a whole run or the base run of a lane: in the stage of
the base round of the run,
`artifacts/formal/runs/<id>/work/base/stage/verification`, or in the
stage of a qualification case, with the Lean 4 extension: a stage holds
the generated modules and the links to the installation that a checkout
lacks, and a change is then copied back to the checkout. Builds there and
in a checkout are not evidence; only a run of the gate produces receipts.

## Limitations

- No formal target is registered: the two specifications, those of the
  device-tree and page-tables components, each have a planned target and
  planned statements, so the whole kernel is unverified, and the base round
  checks the qualification proofs, the definitions that they use and those
  specifications with the theorems that witness them.
- Proofs cover only registered targets. Code outside them, including code
  ported from the legacy tree, is unverified until a target proves it.
- Sequential refinement does not cover concurrency, weak memory, `unsafe`
  code, assembly, the compiler or the hardware.
- A proof says nothing about time, memory use or the compiled binary unless a
  registered obligation states it.
- The audit program runs in the Lean environment of the code that it
  audits, so a krepi module could in principle change what `#print axioms`
  or the program reports; `leanchecker` replays the declarations, and the
  comparator checks the axioms of a new export of the solution against
  the list that the audit admitted, so it rejects an axiom that the audit
  missed or that a proof module hid from it, within the limit below. The
  list itself comes from the audit's report, and a name added to it must
  pass the allowlist, or the unit is not run ([comparator](#comparator)).
- The comparator of a lane is not isolated from the base build of its
  lane. In CI it runs a copy of xtask that the base run cannot write and
  requires exactly one base record of its lane, commit, tree, image and
  run, which it reads again before it writes the receipt of the lane, but
  the stage's build outputs and the copied sources that its challenges
  import are written by the base build of the lane, which has no sandbox,
  so a metaprogram of a proof module could tamper with them. The
  [guard](#guard), the review of the specifications and the replay with
  `leanchecker` remain; isolating the comparator further is future work.
- The gate runs the workflows and the xtask of the head that it judges,
  and the rules of `main` require no approving review: a pull request that
  changes the gate or its workflows is judged by its own version, and only
  review catches a change that weakens them. An administrator of the
  repository can also change the rules themselves ([CI job](#ci-job)).
