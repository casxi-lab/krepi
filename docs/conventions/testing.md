# Testing

Tests and test tooling are written in Rust. The kernel workspace, the
repository tasks in `xtask/` and the host tooling crate in `tools/`, which
holds the test tools, have host tests, and the QEMU boot suite runs the
kernel on QEMU virt; this page states the rules that every test follows,
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

`cargo xtask check` runs the required host checks from the repository root
as the steps listed below, in lanes of two segments. The first segment is the
lint lane, which runs `toolchain`, `manifests`, `fmt` and `clippy` one after
another. Once it has passed, the second segment starts its three lanes at
once, and each runs its steps one after another: the debug lane runs `test`,
`docs`, `lean`, `subset` and `workflows`, the release lane runs
`test-release`, and the formal lane has no step yet; it is the place of a
formal step. `cargo xtask check --sequential` runs every step in one lane
instead, in the order of the list, and stops at the first failure.

The steps `fmt`, `clippy`, `test` and `test-release` run commands. Each of
their commands runs in a process group of its own, with no input; the check
kills the group when the command has ended or the check stops, before it
collects the command, and then waits up to 60 s for the group to be empty,
failing the step if processes of the group outlive that. A passing command
therefore leaves no process of its group behind either. A command's output
and error output go to the log of its step,
`artifacts/check/<UTC time>Z-<process ID>/<NN>-<step>.log`, where `NN` is the
number of the step in the list, such as `05-test.log`, after a line with the
command; when the step ends, the check prints its log and a line with its
status and seconds in one piece, so the output of two lanes never
interleaves, and the output of such a step appears only when the step ends.
The other steps are checks that `xtask` implements itself. They run inside
the check process and print as they go, and the commands that they start,
such as `git ls-files`, the version queries of `toolchain`, the Cargo
resolutions of `manifests` and `subset` and the builds of the compile-fail
cases, run in the process group of the check and write to no step log.

Once a step fails, no further step or command starts, and the running
commands of the command steps are killed with their groups. The step of a
killed command, and a step whose next command no longer starts, is
`cancelled`; a step that had not started is `not run`. A check that `xtask`
implements itself is not stopped: one that runs when another step fails
finishes and keeps its own result, and so do the commands that it started.

The check ends with a summary table on its standard output: one row per step
in the order of the list, with its segment, lane, status, start and seconds
from the start of the check (`-` for a step that did not run), and a row for
the lane without steps. It then names the failed step with the reason on its
standard error and exits with 1, or prints `check passed` and exits with 0;
a receipt that was asked for and cannot be written makes it exit with 1.
From before its first step until it prints the summary, SIGINT and SIGTERM,
and SIGHUP unless it is ignored, as under `nohup`, stop the check as a
failure does: it kills the running commands of the command steps with their
groups, prints the summary and `check interrupted by` with the name of the
signal, writes the receipt and exits with 128 plus the number of the signal,
such as 143 for SIGTERM and 130 for SIGINT, whatever the steps did. A signal
that arrives later, while the check prints the summary or writes the
receipt, is ignored. As the commands of the command steps run in groups of
their own, a Ctrl-C in a terminal reaches them only through the check, but
it reaches the commands that the checks of `xtask` start directly, so that
such a check can fail.

`cargo xtask check --slow` also runs the slow tests, described after the
list. The options `--sequential`, `--slow` and `--receipt <path>` can be
combined and given in any order, before `check` as well as after it, as in
`cargo xtask --slow check --sequential`.

The steps are:

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
   - The root manifest `kernel/Cargo.toml` has the shape of the
     [source layout](../architecture.md#source-layout): without `[package]`
     it passes; with it, the package is `krepi-kernel`, the manifest holds
     only the tables and keys that the layout allows, sets
     `lints.rust.unsafe_code = "forbid"`, and the package has only the
     library and test targets that Cargo reports, so a binary, example,
     benchmark or build script that Cargo finds by itself fails as well;
     its library, parsed with `syn`, has an unconditional `#![no_std]`
     among its crate attributes. The proof gate runs the same check on its
     export.
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
3. `fmt` in the kernel workspace, the user-space workspace, `xtask` and the
   host tooling crate `tools`;
4. `clippy` with warnings as errors in the same four workspaces on all of
   their targets for the host, and then on every member of the kernel
   workspace for the bare-metal target `aarch64-unknown-none-softfloat`, on
   its library, binary and example targets, which are the ones that build
   for it; this ends the lint lane;
5. `test`, the first step of the debug lane: the tests of the same four
   workspaces, and with `--slow` then their slow tests;
6. `test-release`, the release lane: the tests of the kernel and user-space
   workspaces, from which the kernel and user-space images are to be built,
   in the release profile, which keeps `overflow-checks = true`;
7. `docs`: relative links and anchors in Markdown and the `cargo xtask`
   commands that documents mention;
8. `lean`: the source rules of the tracked `.lean` files below
   `verification/`, each a UTF-8 regular file, with the items of
   `verification/tcb.json`, which must be readable: each file lies below
   `verification/Krepi/` or `verification/externals/` and is a module file;
   outside comments and strings, but for the `{}` parts of strings,
   `native_decide`, `bv_decide` and the option `native` of `decide` appear
   only in a file that a `native-decision` item names, and `axiom` only
   below `verification/externals/`; no string reads otherwise as an
   interpolated string; and no file of the statement side imports the root
   module `Krepi` or a module below `Krepi.Proofs`;
9. `subset`: the [mechanical checks](provable-subset.md#mechanical-checks)
   of the provable Rust subset. The files that the `paths` blocks of the
   contracts list, apart from test code, hold no `static mut`, no
   interior-mutability type, no `cfg` attribute outside the allowlist and
   no macro that holds one of their names or `static`; the roots of the
   test code come from `cargo metadata`, which the step runs only when a
   contract lists a file. When there are compile-fail cases below
   `kernel/`, the unchanged kernel workspace builds and each case fails its
   build with its error code; `cargo check` runs each build in a copy of
   the tracked kernel workspace below `artifacts/subset/` that the step
   removes. Its unit tests run in the `test` step, on trees of files in
   memory and, for the compile-fail cases and the step itself, on a
   workspace and a Git repository of their own that they build below the
   build directory of `xtask`;
10. `workflows`: every `.yml` or `.yaml` file below `.github/workflows/` is
    YAML without anchors, aliases, merge keys, repeated keys or characters
    that YAML parsers read differently, and never mentions
    `pull_request_target`, not even in a comment or through an escape; every
    job sets its own `permissions`; and in a workflow that runs on
    `pull_request`, no job requests write access and nothing outside `on`
    references `secrets`. Besides these rules of `xtask/src/workflows.rs`,
    which is written to be copied unchanged into another repository, the
    step checks with `xtask/src/formal/toolchain.rs` that a workflow that
    runs on `pull_request` names the proof-tool image of
    `verification/image-pin.json` by its pinned digest, and that every such
    workflow mentions the image's repository only in that form
    ([image pin](../formal-verification.md#image-pin)). In a workflow that
    runs on `pull_request`, or whose triggers cannot be read, it also
    rejects a step that uses `actions/cache` or `actions/cache/save` at any
    pin, both of which save a cache, and any mention of them with a pin in
    the text, comments included, in any letter case; a job of a pull request
    restores a cache with `actions/cache/restore`. As it does not read the
    steps of a reusable workflow or of a local action, it rejects there a
    job that calls a workflow and a step that uses a local action. It does
    not read other actions that can save a cache as a side effect, such as
    the setup actions of language toolchains with a cache input, which the
    workflows of pull requests do not use.

The checks that `xtask` implements itself read only files that Git tracks,
so a fresh clone and a working copy with build output give the same result;
Cargo, in the command steps and in the resolutions of `manifests` and
`subset`, reads the working copy, and in the builds of the compile-fail
cases a copy of its tracked files. The check does not run the proof gate,
`cargo xtask formal run`, which needs the pinned tools; CI runs the gate in
the job `formal run` of `.github/workflows/formal.yml`, described below.
The `fmt` step formats every module, and the `clippy` step lints the
kernel workspace for the bare-metal target `aarch64-unknown-none-softfloat`
as well as for the host, so it also lints the modules that are compiled only
for that target. The `test` and `test-release` steps build the kernel
workspace for the host only and do not test those modules; only
`cargo xtask qemu-boot` builds them into the images and runs those.

A slow test is a Cargo test marked `#[ignore = "slow"]` whose function name
starts with `slow_`. `cargo xtask check --slow` runs the slow tests in the
`test` step, after the other tests of the four workspaces, with
`cargo test --workspace --locked -- --ignored slow_` in each. libtest then
runs the ignored tests whose path contains `slow_`, so the name of no other
ignored test, of no module and of no Rust file of the workspaces contains
`slow_`; the unit test `check::tests::slow_tests_follow_the_naming_rule`
checks this and the marking of the slow tests on every tracked Rust file of
the workspaces. There is no slow test yet. A test that is ignored for
another reason, such as the one that needs the pinned Lean, is no slow test,
and `--slow` does not run it. The release tests are the same with and
without `--slow`.

`cargo xtask check --receipt <path>` also writes a JSON receipt of the run to
`<path>`, whether the check passes, fails or is interrupted. Its `format` is
2. It records the mode, `parallel` or `sequential`, and whether the run
included the slow tests; the commit and whether the working tree was clean
before and after the run; the result, `passed`, `failed` or `interrupted`,
which a stop signal sets whatever the steps did, with the number of that
signal or `null`; each lane with its segment and the names of its steps, the
formal lane with none; each step with its lane and status (`passed`,
`failed`, `cancelled` or `not run`), the milliseconds from the start of the
check to its start, `null` for a step that did not run, its duration, the
reason of a failed or cancelled step, and the facts that it observed, such
as the version output of the tools that the toolchain step found; the runner
image (`ImageOS`, `ImageVersion`) and the GitHub Actions run
(`GITHUB_RUN_ID`, `GITHUB_RUN_ATTEMPT`, `GITHUB_EVENT_NAME`, `GITHUB_REF`,
`GITHUB_SHA`). A value the environment does not provide is `null`.

CI runs in lines, each a workflow of `.github/workflows/` on GitHub-hosted
`ubuntu-24.04-arm` runners:

- The pull request line, `check.yml` on the head commit of every pull
  request to `main`, and the main line, the same workflow on every push to
  `main`. Its job `cargo xtask check` installs `clang-18` and
  `qemu-system-arm` from the Ubuntu archive and the toolchain of
  `rust-toolchain.toml` with rustup, with its bare-metal target, runs the
  check and uploads the receipt as the artifact
  `check-receipt-<commit>-<attempt>`. After the check, the same job runs
  `cargo xtask qemu-boot --output-dir artifacts/qemu-boot`, described
  below, and uploads that directory as the artifact
  `qemu-boot-<commit>-<attempt>`, also when the suite fails. The job `image`
  runs `cargo xtask image`, uploads the images as
  `images-<commit>-<attempt>` and gives the SHA-256 of each as an output;
  the job `suite` downloads them and runs `cargo xtask suite --images` with
  those digests, with `--base` and the base commit of the pull request on a
  pull request, so that a pull request runs the smoke cases and the suites
  that it selects and `main` every suite, both without the slow cases, and
  uploads its report as `suite-<commit>-<attempt>`. The job `check summary`
  runs after the other three whatever their outcome and succeeds only if
  each of them did. A push to a pull request cancels the run of its earlier
  head; runs on `main` are not cancelled.
- The full line, `full.yml`, runs only when the label `full-check` is added
  to a pull request to `main`, on its head, and never on a push to it: its
  first job fails unless the head contains the `main` of that moment, and
  then `cargo xtask check --slow`, the images and `cargo xtask suite --slow`
  run.
- The nightly line, `nightly.yml`, every day at 10:43 UTC and on a manual
  run, on `main` only: `cargo xtask check --slow`, the images and
  `cargo xtask suite --slow`.
- The weekly line, `weekly.yml`, on Sundays at 11:29 UTC and on a manual
  run, on `main` only: the images and `cargo xtask suite`.

Every job of these lines has a `timeout-minutes`. In the jobs that run
`cargo xtask check`, `cargo xtask image` or `cargo xtask suite`, that
command also ends at a deadline that `timeout` sets two minutes before the
limit of its job, so that the uploads still run when the command takes too
long; `cargo xtask qemu-boot` runs after the check in the same job without
a deadline of its own. The step starts the command as the last command of
its script with `exec bash .github/scripts/deadline.sh`, so that this script
is the process of the step and receives the signals with which the runner
stops a step: SIGINT when the run is cancelled, SIGTERM some seconds later
and then SIGKILL. `timeout` runs the command in a process group of its own,
which those signals do not reach, so the script passes SIGINT and SIGTERM
on to `timeout`, which passes them on to the command, and does not end
before the command has: a check that a newer push to its pull request
cancels writes its receipt with the result `interrupted`, and the upload
after it finds the receipt. The script exits with the status of the
command, and with 124 when the deadline stopped it, also when `timeout`
had to kill it then. Along the longest chain of jobs that need each
other the limits add up to 18 minutes on the pull request line and to 43
minutes on the full line, within the 20 and 60 minutes that those lines
allow. After each completed run of another workflow of the directory,
the workflow `run record` (`run-record.yml`) writes its record with
`cargo xtask run-record`, described below, adds the summary to the run's
summary page and uploads the record as `run-record-<run>-<attempt>`, kept
90 days for a run on `main` that a pull request did not trigger and 30 days
for the others; it runs the code of the default branch with read
permissions only, and a manual run of it on `main` records the run whose ID
it takes. Unit tests of the check read the committed workflows and hold
them to these limits, to the label of the full line as its only trigger, to
`--slow` in the full and nightly lines only, to the one job named
`cargo xtask check` and the summary of the pull request line, to the list
of workflows that the record workflow follows, to a retention by the rule
below for every upload step of every workflow, against a table of those
steps, to downloads that take the name of their
artifact from an output of the job that uploaded it, so that a rerun of
the downloading job alone still finds the artifact, and to main commands
that run under that script as the last command of their step, at a
deadline one or two minutes before the limit of their job. Where GNU `env`
and GNU `timeout` are on the path, as on the runners, a unit test also
sends SIGINT to the script and requires that it ends only after its command
has, with the status of the command.

Every upload step of every workflow of the directory sets `retention-days`,
which the repository setting of 90 days bounds. A job that runs on `main`
and elsewhere writes `${{ github.ref == 'refs/heads/main' && 90 || 30 }}`:
90 days for a run on `main` and 30 for the others, as in the lines and the
formal workflow. A job that runs on `main` only, such as the formal canary
and the publication of the proof-tool image, may write 90; a workflow that
runs on pull requests only, such as the build of that image, may write 30;
and the record workflow keeps a record as long as the run that it records.
The artifacts hold receipts, records, summaries and logs, which the zip of
the artifact compresses, and the images that the QEMU suites boot.

The lines use two caches, which only the workflow `cache` (`cache.yml`)
saves, from `main`. The cargo cache holds `~/.cargo/registry/index/`,
`~/.cargo/registry/cache/`, `xtask/target/` and `tools/target/` under the
key `cargo-<runner system>-<runner architecture>-<digest>` of
`rust-toolchain.toml` and the `Cargo.lock` of the four workspaces. The tools
cache holds the `.deb` packages of `clang-18`, `qemu-system-arm` and their
dependencies, which apt keeps in `~/.cache/krepi-ci/apt/`, and the Rust
toolchain of `rust-toolchain.toml` below `~/.rustup/`, under the key
`tools-<runner system>-<runner architecture>-<digest>` of
`rust-toolchain.toml` and `toolchains.toml`. apt, which runs as root, also
leaves a lock file and a directory `partial/` there that the runner user
cannot read, so each step that installs with apt then removes both and gives
the directory to the runner user: `du` and the save read the packages alone.
An entry is used only under its exact key. The line workflows set
`cache-mode: read`, restore both caches with `actions/cache/restore` in each
job that builds or installs, and save none. A restored cache is not trusted
for its versions: apt installs a cached package only when its digest matches
the index of the archive, and the `toolchain` step of the check still
compares the versions with `toolchains.toml`. The job `cargo xtask check` of
the pull request and main lines reports the size of each path of the two
caches in its summary and marks a size for which `du` failed, as the measure
of the workflow `cache` would.

The workflow `cache` runs on a push to `main` that changes it,
`rust-toolchain.toml`, `toolchains.toml` or the `Cargo.lock` of one of the
four workspaces, and on Mondays at 08:47 UTC, which brings back an entry
that GitHub removed after seven days without use. Its job `cache build`
looks up each entry; for a missing one it installs Clang, QEMU and the Rust
toolchain as the lines do, runs `cargo xtask check`, which builds what the
lines build, measures the paths with `du` and saves the entry with
`actions/cache/save` when it is at most 2 GB for the cargo cache and 0.8 GB
for the tools cache, both decimal, and otherwise reports it over its limit
and saves nothing. The limits leave room above the sizes that the check job
measured, 0.68 GB and 0.65 GB. Its job `cache prune`, the only job with `actions: write`,
runs no code of the repository and lives in a workflow that does not run on
pull requests: once the current entry of a kind is on `main` within its
limit, it deletes the older entries of that kind. The caches then hold at
most 2.8 GB, and at most 5.6 GB between a save and the deletion, within the
10 GB that GitHub keeps for a repository. A unit test holds the workflows to
these keys, paths, triggers, permissions and limits.

The workflow `release` (`release.yml`) drafts a release of the check
receipt and the images of one successful run of the workflow `check` on a
push to `main`, with their SHA-256 digests, and never publishes one. It runs
only by hand, on `main`, with the ID of that run, best a run of the commit
at the head of `main`: GitHub refuses the workflow token a release whose
commit has workflow files that differ from those of the default branch.
Its job `release assets`,
with read permissions only, reads the run through the API, finds its two
artifacts, `images-<commit>-<attempt>` and
`check-receipt-<commit>-<attempt>`, exactly one of each, downloads them with
`actions/download-artifact`, which checks the digest of each artifact, runs
`cargo xtask release-assets`, described below, and uploads the assets as
`release-assets-<run>-<attempt>`. Its job `draft release`, the only job
with a write permission, `contents: write`, runs no code of the repository.
On the files of that artifact it checks `SHA256SUMS` with
`sha256sum --check`, requires that the tag `check-<commit>` does not exist,
creates the release as a draft and as a prerelease that is not the latest,
and requires that the tag still does not exist; a tag that exists fails the
run and is left as it is. It then uploads the assets to the draft and
requires that their names, sizes and digests, as GitHub reads them back, are
those of the files. GitHub lists a draft only to people with push access;
the workflow does not rely on it creating no tag for a draft but checks
that. Publishing a draft, which creates its tag, is a separate step that a
person takes. A unit test holds the workflow to its trigger, its condition
on `main`, its permissions, the draft and the checks of the tag around it.

The workflow `usage` (`usage.yml`) writes the usage summary of the CI of a
month for krepi and the public repositories kosmo and kalyx. It runs on the
second day of each month at 06:19 UTC for the month before, and on a manual
run of `main` for the month of its input, as `YYYY-MM`, the current month
ending at the time of the run, or, with no input, for the month before. Its
one job has read permissions only and uses no other credential: with the
workflow token it reads, for each repository, the runs created in the month,
one query for each day, among them the runs of dynamic workflows such as
code scanning, the jobs of every attempt of each run, the artifacts that
have not expired and the cache usage, and with an anonymous pull token of
the container registry the tags of the package `casxi-lab/krepi-formal` and
the config and layers of their manifests. A request that fails names its
repository or package and fails the run. Text from the API goes only through
files and `jq`, and workflow commands are off while the data is read.
`cargo xtask usage`, described below, writes the summary, which goes to the
summary page of the run, and the data and the summary are uploaded as
`usage-<month>-<run>-<attempt>`. A unit test holds the workflow to its
schedule and its manual run, its condition on `main`, its read permissions
and the commands that are off while it reads.

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

`cargo xtask qemu <ELF>` runs an image on QEMU virt and records what the
guest writes to its serial port, without evaluating it; it is a tool and is
not part of the check, whose tests run it on the test image described
below. It starts `qemu-system-aarch64` from the search path, or the
executable that `--qemu` names, with this command line, where `<image>` is
the canonical path of `<ELF>`:

```text
qemu-system-aarch64 -accel tcg,thread=single \
    -machine virt-8.2,secure=off,virtualization=off,gic-version=2 \
    -cpu cortex-a76 -smp 1 -m 128M -nic none -display none \
    -serial stdio -monitor none -kernel <image>
```

`virt-8.2` is a versioned machine type that QEMU 8.2 and its later versions
provide alike; the guest has no EL2, no EL3 and no network card, and its
PL011 is on QEMU's standard streams. The library entry `run_image_on` of
the runner can instead run an image on the same machine with EL2,
`virt-8.2,secure=off,virtualization=on,gic-version=2`, with the command line
otherwise unchanged and a receipt with the same keys, for a test image that
enters at EL2; the QEMU boot suite uses it, and `cargo xtask qemu` has no
option for it. The guest runs on the host clock;
`--clock icount` adds `-icount shift=3,align=off,sleep=off` after the
accelerator, a functional reproduction as described under
[environments](#environments). The run ends when QEMU ends by itself, when
it has run for `--timeout` seconds (default 60, greater than 0 and at most
600), when more than `--max-bytes` bytes of serial output have arrived
(default 262144, at most 16777216), or at SIGINT, SIGTERM or SIGHUP, which
the command catches from immediately before QEMU starts. The command stops a
QEMU that still runs with SIGTERM, and kills it if it has not ended within
the stop grace, then collects the rest of its output. It writes three files
into the new directory `--output-dir`, by default
`artifacts/qemu/<UTC time>Z-<12 hexadecimal digits>`: `transcript.bin`, the
serial output; `qemu-stderr.txt`, QEMU's standard error, which never joins
the serial output; and `summary.json`, the receipt below, with sorted keys.
It prints the exit reason, the count of serial bytes and the path of the
receipt. It exits with 0 for `guest_shutdown`, 1 for `qemu_exit`, `deadline`
and `output_limit`, 130 for `interrupted`, 2 for `error`, for a receipt with
`errors`, for a usage error and for a run that fails before QEMU starts,
such as for a missing image or QEMU or an existing output directory, which
writes no receipt, and 120 when it cannot write its own output. `clap`
reads the command line as for `cargo xtask serial-capture`.

The receipt of `cargo xtask qemu` has these keys:

| Key | Value |
| --- | --- |
| `schema_version` | `1` |
| `exit_reason` | Why the run ended. `guest_shutdown`: QEMU ended by itself with status 0 and reported no signal, as it does when the guest powers the machine off. `qemu_exit`: QEMU ended by itself with another status, by a signal that the command did not send, or with status 0 after it reported such a signal on its standard error as `<program>: terminating on signal <N>`, as it does when SIGINT, SIGTERM or SIGHUP from another process ends it. `deadline`: QEMU still ran at the timeout, and the command stopped it. `output_limit`: more than `max_bytes` bytes of serial output arrived, while QEMU ran or while the command collected the rest of the output, and the command stopped QEMU if it still ran. `interrupted`: SIGINT, SIGTERM or SIGHUP reached the command, which stopped QEMU if it still ran. `error`: QEMU did not start, as it or the interrupt handlers could not be started or installed. `interrupted` takes precedence over `output_limit`, and `output_limit` over the others. The reason follows from what the command did and from QEMU's report of a signal, as QEMU exits with status 0 when one of those signals ends it |
| `errors` | The text of each step that failed, such as the start of QEMU or a write of the transcript; present only when one failed |
| `started_at`, `finished_at` | UTC times in RFC 3339 form with six fraction digits, such as `2026-10-14T07:45:17.000123Z`: immediately before QEMU starts, and once the files are written |
| `elapsed_seconds` | Seconds from immediately before QEMU starts until it has ended or been stopped, on the monotonic clock |
| `timeout_seconds`, `max_bytes`, `clock` | The limits and the time source of the run: `--timeout` as a number, `--max-bytes` and `host` or `icount` |
| `image` | The image as the command read it before QEMU started: `path`, its canonical path, `bytes` and `sha256` |
| `qemu` | `executable`, the canonical path of the QEMU executable; `version`, the first line of its `--version` output; and `command`, the exact arguments of the run, the executable first |
| `process` | How QEMU ended: `exit_code`, the code it exited with, and `signal`, the number of the signal that ended it, of which one is null; both are null when it had not ended within the kill grace. `intentional_shutdown` tells whether the command signalled a QEMU that still ran, and `forced_kill` whether it killed it. `null` when QEMU did not start |
| `transcript` | `file`, `transcript.bin`, with the `bytes` and `sha256` of the file as it is on disk once the run has ended: every byte that the guest wrote to its UART, up to and including the read that passed the limit, which may hold up to 64 KiB more; `null`, with an entry in `errors`, if the file cannot be read |
| `stderr` | `file`, `qemu-stderr.txt`, with its `bytes` and `sha256` in the same way |

The receipt names the image and its digest, the QEMU version and command
line, and the inputs of the run; the command builds no image and records no
toolchain, which whatever builds an image records. The output is not read:
whether a guest booted or passed a check is for the suite that runs it to
decide.

The test image, which the function `test_elf::write` of the host tooling
crate writes to a given path, is an AArch64 executable for QEMU virt that
writes `krepi test image: PL011 output, then PSCI SYSTEM_OFF` and a carriage
return and line feed to the PL011 UART, then powers the machine off with
PSCI `SYSTEM_OFF` through `hvc #0`. Host code writes it: the program is a
fixed list of AArch64 instruction words, and the ELF writer of the `object`
crate lays out the executable around it, with one read and execute segment
for the program and its message at `0x4020_0000`, where it starts, one
read-only segment for the GNU build-id note, and the symbols `_start` and
`message`. It needs no bare-metal target, assembler, compiler or linker,
and the image is the same on every host. The test of the `xtask` binary
runs `cargo xtask qemu` on it with the QEMU of the host, which shows that
the image boots, that its output reaches the transcript and that its
power-off ends the run as `guest_shutdown`.

`cargo xtask image --output-dir <dir>` writes the images that the QEMU
suites boot into the new directory `<dir>`, which must not exist, and then
`images.json`, the record of their digests. Its `format` is 1, and `images`
lists each image with its `name`, its `file` in the directory, its `bytes`,
the SHA-256 of the file as written (`sha256`) and the `commit` that
`git rev-parse HEAD` names. The one image today is the test image, named
`test-elf`, in the file `test-elf.elf`. The command prints the size and
digest of each image and the path of the record, and exits with 0, or with
2 after a usage error or a failure. It is not part of the check. Its unit
tests run in the `test` step above and compare the record with the file and
with the digest of the test image computed with `shasum -a 256`.

The QEMU suites are listed in `suites.toml` at the repository root. Each
`[[suite]]` has a `name`, the `image` that it boots, by its name in the
record of `cargo xtask image`, the `paths`, prefixes of repository paths
below `kernel/` or `user/` whose change selects it on a pull request, and its
cases. Each `[[suite.case]]` has a `name`, `smoke`, whether every pull
request runs it, `slow`, whether only the slow runs do, `runs`, the cold
boots of the case from 1 to 10, each in a new QEMU process, and `timeout`,
the limit of one run in seconds from 1 to 600. No case is both smoke and
slow, and names are unique and made of lowercase letters, digits and
hyphens. The one suite today, `test-elf`, boots the test image and lists no
paths; its case `boot` is a smoke case of one run, and `repeat`, a slow
case, makes three.

`cargo xtask suite` runs the cases of `suites.toml` on QEMU virt through the
library entry of the QEMU runner, with the command line of
`cargo xtask qemu`, the host clock, the `timeout` of the case and a limit of
4,096 bytes of serial output. It is not part of the check. Which cases run
depends on its options:

- `--base <rev>`: the merge base of `<rev>` and `HEAD`, and the paths that
  `git diff --name-only --no-renames` gives between it and `HEAD`, both
  sides of a rename or a deletion included. Each path selects suites by
  prefix: one below `tools/` or `xtask/`, `rust-toolchain.toml`,
  `toolchains.toml`, a path below `.cargo/`, `suites.toml` or a path below
  `.github/workflows/` that does not start with `.github/workflows/formal`
  selects every suite; one below `kernel/` or `user/` selects the suites that
  list a prefix of it; any other path, such as one below `docs/` or
  `verification/`, selects none. The smoke cases run whatever the paths, and
  a selected suite runs its other cases that are not slow.
- Without `--base`, every suite runs its cases that are not slow.
- `--slow` adds the slow cases of the suites that run.

With `--images <dir>`, the images come from `<dir>/images.json`, the record
of `cargo xtask image`, and each image that a case to run boots needs
`--expect <name>=<SHA-256>`: the command computes the SHA-256 of the file,
and a digest that differs from the record's or the expected one, a missing
entry, file or `--expect` ends the command as `ERROR` before any QEMU starts.
Without `--images`, it writes the images into `images/` of its output
directory. A run passes when its receipt has no `errors`, it ended as
`guest_shutdown`, it booted the image with the expected digest, its receipt
describes its transcript, and the transcript is what the image writes, for
the test image its line; a case of more than one run also needs equal exit
reasons and identical transcripts. Each run writes the directory
`<suite>/<case>-<n>` of `cargo xtask qemu`. The command writes the report
`summary.json` into the new directory `--output-dir`, by default
`artifacts/suite/<UTC time>Z-<process ID>`: the status `PASS`, `FAIL`,
`ERROR` or `INTERRUPTED`, the start and end times, the commit, the GitHub
Actions run (`GITHUB_RUN_ID`, `GITHUB_RUN_ATTEMPT`, `GITHUB_EVENT_NAME`,
`GITHUB_REF`, `GITHUB_SHA`), the base, merge base and changed paths, the
images with their digests, and each suite with why it runs, the paths that
select it, and the cases that run, each with why, its runs, their exit
reasons and the digests of their receipts and transcripts, and its checks.
A case that does not run is not listed. The command prints a line for each
suite, run and case, each failed check and the status with the path of the
report, with control characters escaped, and exits with 0 for `PASS`, 1 for
`FAIL`, 2 for `ERROR` and for a usage error, 130 for `INTERRUPTED` and 120
when it cannot write its own output; `--qemu` names the QEMU executable as
for `cargo xtask qemu`. SIGINT, SIGTERM and SIGHUP are caught from
immediately before the first QEMU starts. Its unit tests run in the `test`
step above: one per row of the mapping and per line of CI, on manifests
written for them; the changed paths of a Git repository that they create;
the digest check of the images; the judge over hand-written receipts and
transcripts and weakened forms of them; and the command on a fake QEMU, a
shell script that prints a line and exits. A test of the `xtask` binary runs
`cargo xtask image` and then `cargo xtask suite` on the image by its digest,
and with another digest, with the QEMU of the host, as the image and suite
jobs of CI do.

`cargo xtask run-record --input <run.json> --output <dir>` writes the record
of one run of a workflow from the data of the GitHub API; it is not part of
the check. The input is what the workflow `run record`, described above,
writes with `jq`: `run`, with the `id`, `attempt`, `workflow`, `path`,
`event`, `head_branch`, `head_sha` and `conclusion` of the run, and `jobs`,
each with its `id`, `name`, `conclusion`, `labels`, `runner_group_name`,
`runner_name`, `annotations` (`level`, `title` and `message`) and its
`started_at` and `completed_at`, as seconds since 1970 that `jq` converts
with `fromdateiso8601`, and no other field. `--workflow <file>` gives the
workflow file at the head of the run, from which each job's limit is read:
its `timeout-minutes`, 360 without one, and none when it is an expression.
A job takes the limit of the job of the file whose name is its own, also
followed by the values of a matrix in parentheses. Failing that, a name in
the file that holds expressions `${{ }}`, such as
`leanchecker ${{ matrix.mode }}`, fits a job's name when each expression
stands for some text, possibly empty, between the text around it, also once
the values of a matrix in parentheses are left out; the names that fit give
the limit when they all give the same one. Otherwise the job has no known
limit. `--own <run.json> --now <seconds>` gives the run of
the record workflow itself. The command creates the new directory `<dir>`
and writes `record.json` and `summary.md` into it. The record, of `format`
2, holds the run with its line: `pull request` or `main` for the workflow
`check` on a pull request or a push, `full`, `nightly` and `weekly` for
those workflows, `none` for the others. Each job has its runner class:
`none` for a job that ran on no runner, to which the API gives no runner
name, or an empty one when it was cancelled before a runner took it;
`self-hosted` by its labels; `larger hosted` for a runner group other than
`GitHub Actions`; and `standard hosted` otherwise. It also has its seconds;
its minutes, the seconds rounded up to whole minutes and 0 for a job that
ran on no runner; its limit, its conclusion, its result and its
annotations. The result is the conclusion, or
`TIMEOUT` for a job that did not succeed and either ran at least as long as
its limit or has the failure annotation
`Process completed with exit code 124.`, which the runner writes when the
main command of a step exits with 124, as `timeout` does when it stops the
command at its deadline; the field `timeout` gives the reason, `limit` or
`deadline`, and is `null` otherwise. The first condition alone was the rule
of format 1, so the new rule finds every `TIMEOUT` that the old one found;
no command that the lines run exits with 124 by itself. The record also
holds the wall clock of the run, from the first start to the last end of the
jobs that ran on a runner, the sum of the minutes, the limit of the line,
1,200 s for the pull request line and 3,600 s for the full line, whether the
run or one of its jobs took more than 80% of it, which the summary states as
a run that "exceeds 80% of its limit", the days for which the record is
kept, 90 for a run on `main` that a pull request did not trigger and 30 for
the others, and with `--own` the record workflow's run until `--now`: its
wall clock and minutes, and each of its jobs with its runner class, seconds
and minutes. The summary, which the workflow adds to the run's summary page,
gives the same in Markdown with the text of the run escaped, and names each
job that was stopped at the deadline of its main command.
`cargo xtask run-record --id <text>` checks the run ID of a manual run of
the record workflow, digits without a leading zero, and prints it. The
command prints only the paths that it writes and exits with 0, or with 2
after a usage error or a failure. Its unit tests run in the `test` step
above, on the input of two runs of the repository read back from the API, on
the records of format 1 of two runs in which a job ran past its limit, which
stay `TIMEOUT` under the new rule, on a grid of jobs on which the new rule
contains the old one, and on runs written for each rule.

`cargo xtask release-assets --run <run.json> --images <dir> --receipt <file>
--output-dir <dir>` writes the assets of a draft release; it is not part of
the check. `--run` is the run as the workflow `release` writes it with `jq`,
with the fields of the `run` of the input of `cargo xtask run-record`: it
must be a run of `.github/workflows/check.yml` on a push to `main` that
succeeded, with a commit of 40 lowercase hexadecimal digits. `--images` is
the directory of the artifact of its images: its `images.json` must be a
record of `cargo xtask image` that names that commit for every image and
gives each image a regular file of the directory by a plain name, with the
size and SHA-256 of that file, and the directory holds no other file.
`--receipt` is its check receipt, which must have `format` 2, that commit
and the result `passed`. The command creates the new directory `<dir>`,
copies the images, `images.json` and the receipt, as `check-receipt.json`,
into it and writes `SHA256SUMS`: a line `<SHA-256>  <name>` for each of
those files, in the order of their names, as `sha256sum --check` reads it.
It prints the path of each file that it writes and exits with 0, or with 2
after a usage error or a failure. Its unit tests run in the `test` step
above, on a run and files written for each check.

`cargo xtask usage --input <input.json> --output-dir <dir>` writes the usage
summary of a month from the data that the workflow `usage` collects; it is
not part of the check. The input holds the period, from its start up to but
not including its end, in seconds since 1970 and as text, the rate limit of
the API before and after the data was read, the runs of each repository with
the jobs of every attempt, its artifacts and its cache usage, and the tags
of each package with their blobs, and no other field. A run counts once, by
its ID, and only when it was created in the period; a job counts once. The
minutes of a job are its seconds on its runner rounded up to whole minutes,
job by job, as in the run record, which approximates the minutes that
GitHub bills; a job on no runner takes none, and one that has not ended is
listed and takes none. The command sums the minutes by runner class, as the
run record classes runners, for each repository and for all of them, and
lists them by workflow and by runner labels. It sets the bytes of the
artifacts that have not expired and of the blobs of the packages, each blob
counted once, against 50 GB, decimal, and the cache of each repository
against 10 GB, and compares each of five items with its threshold: larger
hosted minutes above 0, self-hosted minutes above 0, standard hosted
minutes above 40,000, the artifacts and the packages above 40 GB, and the
cache of a repository above 8 GB. The summary names each item above its
threshold in neutral words; a threshold never fails the command. It creates
the new directory `<dir>` and writes `usage.json` and `summary.md`, the
same in Markdown with the text of the data escaped, into it, prints only
those paths and exits with 0, or with 2 after a usage error or a failure.
Its unit tests run in the `test` step above, on data written for each rule.

`cargo xtask qemu-boot` is the QEMU boot suite of the kernel: it builds the
QEMU virt default image and the test images, boots them on QEMU virt
through the library entry of the QEMU runner and judges every run; it is
not part of the check, and CI runs it after the check as stated above. It
builds the images with one command, `cargo build --locked --release
--target aarch64-unknown-none-softfloat -p krepi-qemu-virt --bin
krepi-qemu-virt --example el1-brk --example injected-serror --example
el1-fp-trap --example timer-irq --example irq-registers --example
sp-el0-brk --example unexpected-irq --example clean-code-to-pou --example
invalidate-to-poc --example invalidate-tlb-page --example code-publication
--message-format=json-render-diagnostics` in `kernel/`, where
the `.cargo/config.toml` of the repository root gives the target its flags,
takes each image from Cargo's artifact message and records `rustc -vV`.
The test images are the examples of `kernel/boards/qemu-virt/examples`:
each links the production code of the default image and adds its own
`kernel_main`, exception dispatch and trigger sequence, and on the host it
is an empty program. The cases run in order, each run in a new QEMU process
with the command line of `cargo xtask qemu` and the host clock, with a
window of 20 s and a limit of 4,096 bytes of serial output, the QEMU virt
values of the suite. No image stops by itself, so each run ends at its
window.

The case `cold-boot-echo` runs the default image three times; once the
transcript holds `CASXI_READY` and CR LF, the runner sends the 16 bytes
`casxi-sim-check` and CR. It passes when every run ended at its window with
no errors, on the runner's machine with one Cortex-A76 and without an
instruction count, booted the image of the build and holds exactly the
records of the
[boot contract](../domains/boot-platform/boot/contract.md#records), a
Cortex-A76 identity record, `CASXI_BOOT kernel=krepi board=qemu-virt el=1`
and `CASXI_READY`, followed by the 16 bytes sent, a line feed and nothing
else; and when the three image digests are equal and the three transcripts
identical. The cases `el1-brk`, `injected-serror`, `el1-fp-trap`,
`timer-irq`, `irq-preserves-registers`, `sp-el0-brk` and `unexpected-irq`
run their test image once each, `irq-preserves-registers` the image
`irq-registers` and the others the image of their own name:
`injected-serror` on the machine with EL2, the others on the runner's
machine. Each passes when its run ended at its
window with no errors and no input, on the machine of the case with one
Cortex-A76, without an instruction count, booted the image of the build,
and its transcript holds exactly, each line ending in CR LF, the start
record `CASXI_TEST image=<image>`, for each expected exception an empty line
and the exception record of the contract, and then `CASXI_HALTED`, or one
record `CASXI_CHECK name=<check> failures=0x<16 hexadecimal digits>` for
each self-check of the image in order, each with no failure, and
`CASXI_RESUMED`, or, for `sp-el0-brk`, whose vectors halt after its
dispatch, its self-check records alone. Each exception record must have
the vector, class and syndrome of the case and a return address at a
symbol of the image's ELF file, or between two of them. The cases
`clean-code-to-pou`, `invalidate-to-poc`, `invalidate-tlb-page` and
`code-publication` run the test image of their own name once each on the
runner's machine and are judged in the same way, with no exception record:
the transcript holds the start record, the self-check of the image with no
failure and `CASXI_RESUMED`. The expected
records are written into the suite from the contract and the exception
classes of the Arm Architecture Reference Manual; each record and each
self-check is a check of its own.

Each run writes a directory `<case>-<n>` with the files and the receipt of
`cargo xtask qemu`; the receipt of a run of `cold-boot-echo` has one more
key, `input`: for each input, its trigger `after` and its `bytes`, in the
escapes of `<[u8]>::escape_ascii`, and `sent_at`, the count of serial bytes
that had arrived when the runner sent it, or null when it did not. A send
that fails adds its error to `errors`. The suite writes `build.log`, the
standard error of the build, and the suite receipt `summary.json`, with
sorted keys, into the new directory `--output-dir`, by default
`artifacts/qemu-boot/<UTC time>Z-<12 hexadecimal digits>`: the status
`PASS`, `FAIL`, `ERROR` or `INTERRUPTED`, the worst of its cases, the start
and end times, the commit, the GitHub Actions run (`GITHUB_RUN_ID`,
`GITHUB_RUN_ATTEMPT`, `GITHUB_EVENT_NAME`, `GITHUB_REF`, `GITHUB_SHA`, null
outside CI), the toolchain, the build with its command and exit code, the
images by target with their path, size and SHA-256 digest, and each case
with its criterion, image, machine, each run's directory, exit reason and
the digests of its receipt and transcript, and each check with its status
and, when it failed, why. `--qemu` names the QEMU executable as for
`cargo xtask qemu`. The command prints a line for each run, each failed
check and the status with the path of the receipt, and exits with 0 for
`PASS`, 1 for `FAIL`, 130 for `INTERRUPTED`, 2 for `ERROR`, such as a failed
build or a run that could not start, and for a usage error or an output
directory that exists, and 120 when it cannot write its own output. SIGINT,
SIGTERM and SIGHUP are caught from immediately before the first QEMU
starts. Its unit tests run in the `test` step above: they hold hand-written
receipts and transcripts, and weakened and misattributed forms of them,
against the checks of the cases, and run a case with a fake QEMU, a shell
script that writes the records and echoes its input.

`cargo xtask formal toolchain-check --aeneas DIR --charon DIR` checks the
tool manifest `verification/toolchain.json` against checkouts of Aeneas and
Charon and the reviewed Aeneas patch: the Lean, Charon and Rust versions
that the sources name, the digests of the patch and of the Lake lock, the
Mathlib commit and the host columns
([tool checks](../formal-verification.md#tool-checks)). Its unit tests run
in the `test` step above. Two more workflows run it, each for a change of
the tool manifest, the patches, the image recipe or the image check below
`verification/image/` or the two workflows themselves, on a GitHub-hosted
`ubuntu-24.04-arm` runner: `formal image build`
(`.github/workflows/formal-image-build.yml`) on every pull request to
`main`, which then checks that a missing license notice fails the image
build, builds the image of the proof tools without publishing it and checks
it as a user other than root; and `formal image publish`
(`.github/workflows/formal-image-publish.yml`) on every push to `main`,
which does the same and publishes the image only after that check
([changing a tool](../formal-verification.md#changing-a-tool)). Both upload
the build record, with the disk measurement and the output of the check, as
a workflow artifact. The toolchain canary below runs it too, on each run
that reaches it, on the manifest that it derives.

`cargo xtask formal canary STEP` runs a step of the toolchain canary
([toolchain canary](../formal-verification.md#toolchain-canary)), the
workflow `formal canary` (`.github/workflows/formal-canary.yml`): once a
week and on a manual run of `main`, on a GitHub-hosted `ubuntu-24.04-arm`
runner, it derives the tool manifest of Aeneas main, builds the image with
it without publishing it and runs the gate in that image, and it uploads
its records, the build log and the receipt as the artifact
`formal-canary-<run>-<attempt>`. It is not part of the check and not a
required check. Its unit tests run in the `test` step above, on Aeneas and
Charon trees that they write as Git repositories, with stand-ins for the
downloads, hand-written build logs in the plain form of BuildKit and
receipts of the gate; one reads the workflow and keeps its steps copied
from the image workflows and from the job of the gate equal to their
sources.

`cargo xtask formal run` runs the proof gate on a snapshot of the gate
inputs and writes a receipt of the run below `artifacts/formal/runs/`
([gate run](../formal-verification.md#gate-run)): the qualification of the
tools and the base round of krepi's own Lean, with the guard on a pull
request. It is not part of the check: CI runs it in the pinned proof-tool
image as the job `formal run` of `.github/workflows/formal.yml`, on a
GitHub-hosted `ubuntu-24.04-arm` runner, on every push to `main` and on
every pull request to `main`, also when its labels or description change.
The job is not required, and it uploads the receipt and the logs of the run
as the artifact `formal-receipt-<commit>-<attempt>`. The same workflow has
measurement jobs, `leanchecker` in two modes and `lake comparator`, which
run on a manual run of the workflow and on a pull request with the label
`formal-measure` ([CI job](../formal-verification.md#ci-job)). Its unit
tests run in the `test` step above, on Git repositories that they create
with the gate inputs in a minimal form, and with fake tools: shell scripts
that hang, exit with a given status, end by a signal or print what a tool
prints. On the Linux runner of CI the tests run as `linux-aarch64`, so the
installation of each repository holds the `versions.json` of the pinned
image, which the run compares with the tool manifest, and the tests give
the run a user ID other than that of the owner of the installation. The
texts that tests read in the forms of Lean, Lake and `leanchecker` are
output of the pinned Lean 4.35.0, captured with absolute paths replaced;
those stored below `xtask/src/formal/fixtures/base/` name the command that
printed them, and the default answers of the fake tools follow the same
forms. The
repositories lie in the system's temporary directory, outside the
checkout, whose Cargo configuration the gate would otherwise find above
their exports. The tests therefore assume that no
Cargo configuration lies in the temporary directory or above it, such as
`~/.cargo/config.toml` when the temporary directory is below the home
directory; with one there, every run that reaches Cargo fails and names
the file. The test of a stop signal runs the gate in a child process, the
test executable started again for that test alone, with SIGHUP at its
default action even when the tests run under `nohup`; the test of an
ignored SIGHUP starts the test executable again in the same way, once with
SIGHUP ignored.

`cargo xtask formal guard --event PATH` checks a pull request against the
rules for changes of statements, proofs and sources
([guard](../formal-verification.md#guard)). Its unit tests run in the
`test` step above, on Git repositories with a commit for each change and
with `pull_request` events in the form that GitHub writes; the test of its
own Git environment starts the test executable again with Git variables
that name another repository.

`cargo xtask formal check [--write]` holds the inventory of the production
functions of the kernel workspace against the `proves` and `unclosed`
lists of the proof targets and against `verification/open.json`, which it
compares with what the `Open obligations` tables of the contracts give,
applies the rules of the target registry and of
`verification/axioms.json`
([proof targets](../formal-verification.md#proof-targets)), and refuses
what the gate does not support yet
([legacy inventory and admission](../formal-verification.md#legacy-inventory-and-admission));
`--write` first writes `verification/open.json`. It reads the tracked files
and the roots of the targets that `cargo metadata` reports, runs no proof
tool and exits with 1 when it finds a problem. It is not part of the check
and no CI job runs it yet, so it is run before proposing a change to the
kernel workspace, a contract or the registries. Its unit tests run in the
`test` step above, on trees of files in memory and on fixture contracts.

`cargo xtask formal vectors [DOMAIN/COMPONENT]` replays the frozen test
vectors of a component through its specification with the pinned Lean and
compares the results line by line with those that its host tests wrote
([test vectors](../formal-verification.md#test-vectors)). It is not part of
the check: on a pull request that changes the kernel or user-space
workspace, the Lake project, a component's directory, xtask or
`.github/workflows/formal.yml`, the job `formal run` runs the host tests
with `KREPI_VECTOR_RESULTS` set and then the command in the pinned image,
for every component whose contract names a replay. Its unit tests run in the
`test` step above, on Git repositories with a fixture component and a Lake
stand-in, a shell script that records its calls and environment and writes
the expected outputs as the results of the replay; a test that reads the
output and the exit status of the command starts the test executable again
to run it. One test,
`formal::vectors::tests::the_fixture_replays_with_the_pinned_lean`, is
ignored because it needs the pinned Lean: the job runs it in the image, and
a local run needs the `darwin-arm64` installation at
`artifacts/formal/tools`.

`cargo xtask qemu-boot` is the QEMU boot suite of the kernel, and
`cargo xtask suite` runs the QEMU suites of `suites.toml`. The board suites
have entry points of their own (planned), built on the serial port
transport, the serial link, the QEMU command and the serial capture of a
guest, the QEMU runner, and the serial record parsers of the host tooling
crate. Each suite writes its report and the raw serial bytes under
`artifacts/`, together with the identity of the image it ran.

## Evidence and receipts

- Only a receipt that CI or the HIL bench produced, stored where it can be
  retrieved, is acceptance evidence. A local run is a development aid.
- The list of known failures is generated by a tool from the receipts
  (planned) and is not edited by hand. A failure stays on the list until a
  receipt shows the fixed behaviour.
- A receipt records the identity and digest of the image, the toolchain,
  the QEMU version or the board configuration, and the inputs. The toolchain
  is recorded by whatever builds the image; a run of an image that it did
  not build, such as `cargo xtask qemu`, records the image's digest, the
  QEMU version and command line and its inputs.

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
  `endpoint_ipc` in the `kernel` area). In the user-space workspace, the
  crate layout is fixed with the first tests; the kernel workspace follows
  the next point.
- In the kernel workspace, the integration tests of the provable core in
  `kernel/tests/` (planned) see only its `pub` items
  ([provable core](../architecture.md#the-provable-core)). Differential
  random tests drive a host build of the core and the Lean specification
  of a component with the same random sequences of operations and compare
  the results. Tests across the modules of the core, and the host
  interface of differential random tests, are in `#[cfg(test)]` modules
  inside `kernel/src/`, such as `#[cfg(test)] mod drt;` (planned) in
  `lib.rs`, which see its `pub(crate)` items and are test code in the
  inventory
  ([legacy inventory and admission](../formal-verification.md#legacy-inventory-and-admission)).
  No test crate with a library is built. The top-level modules of the
  kernel crates have names that differ from each other: the core has
  `context` (planned), so the save and restore module of the architecture
  crate is `switch` (planned). The core has no dependencies, development
  dependencies included, so differential random tests read and write their
  JSON in `xtask`; the test modules of the core offer one interface per
  operation and exchange data with `xtask` across processes only in a line
  format that `std` reads and writes.
- Frozen data lives in a data directory per area; each file starts with a
  comment that names its source (hand calculation, manual, construction or
  the legacy tree with commit and path).
- Test vector files are frozen data in the form of
  [vector files](../formal-verification.md#vector-and-result-files). When
  `KREPI_VECTOR_RESULTS` names a directory, the host tests of a component
  whose contract names its vector file write their outputs to
  `<domain>/<component>.results` below it, and still assert each output.
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
platform it talks to; `cargo xtask serial-capture` takes the Pi 5 set, and
`cargo xtask qemu` and `cargo xtask qemu-boot` the QEMU virt set. The values
of both sets are those of the legacy tooling crate, which used the same
values on QEMU and on the board; the values for the Pi 5 have not yet been
measured against a board run of krepi.

| Field | Use | QEMU virt | Pi 5 |
| --- | --- | ---: | ---: |
| `reader_poll` | Longest wait of a serial port's reader thread for input before it looks at its stop flag | 100 ms | 100 ms |
| `request_transmit` | Longest transmission of one request of 1 to 128 bytes to a serial port, within the deadline of its session | 2 s | 2 s |
| `capture_slice` | Longest wait of a serial capture for input before it looks at its interrupt flag | 100 ms | 100 ms |
| `link_slice` | Longest wait of a serial link for output in one look: after its output ended, for the ready line and while it drains | 20 ms | 20 ms |
| `link_drain` | How long a serial link collects the output that follows a failure | 250 ms | 250 ms |
| `link_finish` | Longest final read of a finished serial link, until its output ends | 1 s | 1 s |
| `link_finish_slice` | Longest wait in one look of that final read | 50 ms | 50 ms |
| `guest_slice` | Longest wait of a guest's serial capture for output in one look: while it waits for an expected response, while it collects the diagnostics that follow a failure, and while `cargo xtask qemu` supervises QEMU | 100 ms | 100 ms |
| `guest_idle` | How long a guest's serial capture may keep receiving output at a phase boundary before the guest counts as not idle | 250 ms | 250 ms |
| `guest_finish` | Longest final collection of a guest's serial output once the guest has stopped, until its output ends, such as the collection of the rest of QEMU's output by `cargo xtask qemu` | 1 s | 1 s |
| `guest_finish_slice` | Longest wait in one look of that final collection | 50 ms | 50 ms |
| `stop_grace` | How long a stopped process may take to end after SIGTERM before it is killed | 1 s | 1 s |
| `kill_grace` | How long a killed process may take to end before its status is given up | 1 s | 1 s |
| `reap_poll` | Interval between two looks at whether a process has ended | 10 ms | 10 ms |

The unit tests of these tools wait at most 60 s for an event that they
expect, which only a failing test reaches, and pass sets of their own whose
bounds for an expected event are as long; a capture or a QEMU run that a
test ends by its byte limit, the end of its stream or of the process, or an
interrupt has a deadline of 120 s. No test bounds the time that a step
takes.

In the tests of `cargo xtask formal run`, a fake tool that hangs gets a
limit of 1 s, which only decides that it is stopped, and any other fake
tool a limit of 3,600 s. A fake tool that hangs sleeps for 30 s, and so does
a process that a test leaves behind in the group of a command that ends.
The test of a stop signal waits at most 120 s for the gate that it starts
to reach its command, which only a failing test reaches; that command
sleeps for 240 s. In the tests of `cargo xtask formal vectors`, a Lake
stand-in that hangs gets a budget of 1 s, which only decides that it is
stopped, and sleeps for 30 s, and any other a budget of 1,800 s or
3,600 s; the ignored replay with the pinned Lean has 300 s. Each sleep is a
small multiple of the bound of its test, so that it outlasts every wait
that a passing test makes.

In the tests of `cargo xtask check`, a step that the check is to cancel runs
a shell that starts a sleep of 240 s, writes the number of its process group
to a file and waits; the failing step of the test waits for these files
before it fails, so the test drives the interleaving. The check must
end within 10 s after the failing step, which only a check that waited for
such a sleep exceeds, and a step of these tests that waits for a file or for
the check to stop gives up after 60 s, which only a failing test reaches.
The test of a stop signal runs the check in a child process, the test
executable started again for that test alone with SIGHUP at its default
action, and waits at most 120 s for both of its lanes to run, which only a
failing test reaches. No other test bounds how long a step takes.

The process group of the `test` step holds Cargo and the test executables,
not the processes that tests start in process groups of their own. When the
check kills the step, as it does when the release lane fails or a stop
signal arrives, such processes outlive it: a sleep of the tests of the
check, `cargo xtask formal run` or `cargo xtask formal vectors` for up to
240 s.

## Dependencies

The test tooling takes general functionality from crates, as
[contributing](../../CONTRIBUTING.md#dependencies) requires. Each is pinned
to an exact version in the manifest of the crate that uses it:

| Manifest | Dependency | License | Purpose |
| --- | --- | --- | --- |
| `tools/Cargo.toml` | `clap` without default features, with `std`, `help`, `usage` and `error-context` | MIT OR Apache-2.0 | The command lines of `cargo xtask serial-capture`, `cargo xtask qemu` and `cargo xtask qemu-boot`, defined with the builder, with their help, usage and error texts, which have no colour and are not wrapped to the terminal |
| `tools/Cargo.toml` | `libc` without default features | MIT OR Apache-2.0 | The terminal, lock and signal calls of the serial port transport, the signal that the process helpers send, and the pseudo-terminals, signals, file-size limits and child processes of the tests of the transport, the serial capture, the QEMU capture and runner and the process helpers |
| `tools/Cargo.toml` | `object` without default features, with `write_core` and `elf` | MIT OR Apache-2.0 | The ELF writer that lays out and encodes the test image around its instruction words: the ELF header, the program and section headers, the symbol table and the string tables |
| `tools/Cargo.toml` | `serde_json` without default features, with `preserve_order` | MIT OR Apache-2.0 | Report values, whose objects keep the order of their keys, and their JSON text, and the messages of Cargo from which `cargo xtask qemu-boot` takes the image |
| `tools/Cargo.toml` | `sha2` without default features | MIT OR Apache-2.0 | The SHA-256 digests in the report of the ELF fixture patching and in the receipts of the serial capture, of `cargo xtask qemu` and of `cargo xtask qemu-boot`, the suffix of their run directories, and the build-id of the test image |
| `xtask/Cargo.toml` | `clap` without default features, with `std`, `help`, `usage` and `error-context` | MIT OR Apache-2.0 | The command lines of `cargo xtask check`, `cargo xtask image`, `cargo xtask suite`, `cargo xtask run-record`, `cargo xtask release-assets`, `cargo xtask usage`, `cargo xtask formal run`, `cargo xtask formal guard`, `cargo xtask formal toolchain-check`, `cargo xtask formal check`, `cargo xtask formal vectors` and `cargo xtask formal canary`, defined with the builder, with their help, usage and error texts, which have no colour and are not wrapped to the terminal |
| `xtask/Cargo.toml` | `libc` without default features | MIT OR Apache-2.0 | The process groups of the commands of `cargo xtask check`, `cargo xtask formal run` and `cargo xtask formal vectors`: killing a command's group, finding whether any of its processes remain, seeing that a command has ended without collecting it, and the default disposition of `SIGCHLD` that this needs; finding whether SIGHUP is ignored when the run starts; and the effective user of the run, the bytes available on the file system of its run directory and the largest resident set of a process that it collected, which its receipt records |
| `xtask/Cargo.toml` | `serde` without default features, with `alloc` and `derive` | MIT OR Apache-2.0 | The types into which `cargo xtask formal toolchain-check` reads `verification/toolchain.json`, `cargo xtask formal check` reads `verification/targets.json` and `verification/axioms.json`, `cargo xtask formal run` reads `verification/targets.json`, `verification/qualification/cases.json`, `verification/extraction.toml`, `verification/statements.json`, `verification/axioms.json`, `verification/tcb.json` and the `translation.json` that Aeneas writes, the type into which the `subset` step of `cargo xtask check` reads its compile-fail cases, the type into which `cargo xtask formal vectors` reads the `vectors` block of a contract, the record `images.json` that `cargo xtask image` writes and `cargo xtask suite` reads, the suites of `suites.toml`, the run and jobs that `cargo xtask run-record` reads, the run that `cargo xtask release-assets` reads, the data of a month that `cargo xtask usage` reads, the record of a step of `cargo xtask formal canary`, and the types of the receipt of `cargo xtask formal run`, which the canary also reads |
| `xtask/Cargo.toml` | `serde_json` without default features, with `preserve_order` | MIT OR Apache-2.0 | The JSON text of the receipts of `cargo xtask check` and `cargo xtask formal run`, of `verification/open.json`, of the record `images.json` of `cargo xtask image`, of the report of `cargo xtask suite` and of the record of `cargo xtask run-record`, reading `images.json` and the run and jobs of a record, reading the run, `images.json` and the check receipt that `cargo xtask release-assets` checks, the summary of `cargo xtask usage`, reading the output of `cargo metadata` in the `manifests` and `subset` steps, in `cargo xtask formal run` and in `cargo xtask formal check`, and reading `verification/toolchain.json`, `verification/targets.json`, `verification/models.json`, `verification/qualification/cases.json`, `verification/statements.json`, `verification/axioms.json`, `verification/tcb.json`, `verification/image-pin.json`, the `versions.json` of the proof-tool image, the Lake locks of the Aeneas Lean library and of `verification/`, the `translation.json` that Aeneas writes, the messages that `lean --json` prints, the event of a pull request that `cargo xtask formal guard` reads, and the tool manifest, the Lake locks, the statement registry, the records of its steps and the receipt that `cargo xtask formal canary` reads and writes |
| `xtask/Cargo.toml` | `syn` without default features, with `full`, `parsing` and `visit` | MIT OR Apache-2.0 | Parsing the source files of the kernel workspace for the inventory of `cargo xtask formal check` and for the `subset` step of `cargo xtask check`, walking their items and reading their attributes, paths and tokens, the crate attributes of the library of the root package of the kernel workspace for the `manifests` step and `cargo xtask formal run`, and in a unit test of the check the Rust files of every workspace for the names of the slow tests |
| `xtask/Cargo.toml` | `proc-macro2` without default features, with `span-locations` | MIT OR Apache-2.0 | The token type under `syn`, whose span locations give the line of each problem that the `subset` step reports |
| `xtask/Cargo.toml` | `signal-hook` without default features | MIT OR Apache-2.0 | The handler that lets SIGINT and SIGTERM, and SIGHUP unless it is ignored, stop `cargo xtask check`, `cargo xtask formal run` and `cargo xtask formal vectors`; the emulation of their default action with which the two formal commands then end, whereas the check exits with 128 plus the signal number; and the names of the signals in the output of the check |
| `xtask/Cargo.toml` | `sha2` without default features | MIT OR Apache-2.0 | The SHA-256 digests of the images that `cargo xtask image` writes into `images.json` and that `cargo xtask suite` checks before it boots them and `cargo xtask release-assets` before it writes them into `SHA256SUMS`, and of the receipts and transcripts of its runs, of the Aeneas patch and the Lake lock that `cargo xtask formal toolchain-check` compares with `verification/toolchain.json`, and of the output files of the commands of `cargo xtask formal run` and `cargo xtask formal vectors`, the Lean files that Aeneas writes in the former and the `versions.json` of the proof-tool image, and of the Lean archives, the channel manifest and the Lake lock of Aeneas main, which `cargo xtask formal canary` writes into the derived tool manifest |
| `xtask/Cargo.toml` | `tar` without default features | MIT OR Apache-2.0 | Unpacking the tar archive of the gate inputs that `git archive` writes for `cargo xtask formal run` |
| `xtask/Cargo.toml` | `toml` without default features, with `parse` and `serde` | MIT OR Apache-2.0 | Reading the Cargo manifests and configuration files, `suites.toml`, `toolchains.toml`, `rust-toolchain.toml`, Charon's `rust-toolchain`, `verification/extraction.toml`, the compile-fail cases of the `subset` step, the `vectors` blocks of the contracts, and Charon's `charon/Cargo.toml` and the channel manifest of a nightly that `cargo xtask formal canary` reads |
| `xtask/Cargo.toml` | `walkdir` | MIT OR Unlicense | The listing of the tool installation that `cargo xtask formal run` takes at the start and at the end of a phase, without following symbolic links |
| `xtask/Cargo.toml` | `yaml-rust2` without default features | MIT OR Apache-2.0 | The YAML event parser of the `workflows` step, and the YAML loader with which that step reads the actions that the steps of a workflow use, `cargo xtask run-record` reads the limits of the jobs of a workflow and the unit tests of the check read the committed workflows |

No test has a development dependency yet. Development dependencies are added
only when a test category needs them, are pinned to an exact version and are
listed here with their purpose.
