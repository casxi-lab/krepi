---
name: formal-upgrade
description: Upgrade the proof tools that krepi pins (Lean, Aeneas, Charon and the Rust nightly), requalify them, repair the proofs that break one at a time from the receipt and record the cost of each repair, or triage a verdict of the weekly toolchain canary; use it for an upgrade task or a canary verdict, not for proof work on a component.
---

# Formal upgrade

This manual is for the person or the agent who moves the pinned proof
tools to new versions, or who reads a verdict of the toolchain canary.
[Formal verification](formal-verification.md) defines the tools, the
image, the gate and its receipt; this page says how to change the tools
and how to repair what the change breaks. It adds no rule to the gate or
the guard.

A formal upgrade is a separate upgrade task with pull requests of its own.
It is never part of a change to a feature, a specification or a proof. The
canary never performs one: it only records what an upgrade to the tools of
Aeneas main would break ([toolchain
canary](formal-verification.md#toolchain-canary)), and what it records is
the work of the next upgrade.

## Status of the tool pins

`verification/toolchain.json` and the patch in `verification/tooling/` are
not on the statement side ([statements and
proofs](formal-verification.md#statements-and-proofs)), and the guard has
no rule for them. A pull request that changes only these, and not
`verification/lean-toolchain`, `verification/lake-manifest.json` or
`verification/lakefile.*`, therefore changes no statement hash and needs
no label `spec`, although it can change the generated definitions, the
qualification and the results of the audits. Such a pull request belongs
to an upgrade and goes as the two-step change of [changing a
tool](formal-verification.md#changing-a-tool); its review checks the
results of the requalification and the records of the proof repairs below.

A new Lean, or a new Lake lock of the Aeneas Lean library, also changes
the Lake project files, which are on the statement side, and so does a
repair of a proof below `verification/Krepi/Qualification/`. Such a pull
request is a statement change: it needs the label `spec`, the fields that
the guard checks for it and an approval of the new statement hash
([guard](formal-verification.md#guard)). The Lake project of the
[calibration target](formal-verification.md#calibration-target) keeps no
`lean-toolchain` and no `lake-manifest.json` of its own and takes those of
`verification/` in each stage, so the upgrade changes nothing there; a
repair of its proofs is not a statement change, since that project is not
on the statement side, and needs no label `spec`.

## Procedure

1. **Choose the versions.** Start from the Aeneas commit: it fixes the
   Lean of its `backends/lean/lean-toolchain`, its Lake lock with the
   Mathlib commit, the Charon of its `charon-pin` and the nightly of that
   Charon's `charon/rust-toolchain`, with the release archives and the
   channel manifest that belong to them. The artifact of a canary run on
   that commit holds all of them: each derived field with its committed
   value in `derive.txt` and in the data of `verdict.json`, the derived
   manifest in `toolchain.json`, the changes of the Lake project in
   `derived.diff` and the `versions.json` of the image that the run built.
   The derived manifest is written in the layout of `serde_json`; write its
   values into the committed file, so that the diff shows only what moved.
2. **Port the patch.** When the reviewed patch does not apply to the new
   commit, port it at the tool boundary, never in generated Lean: keep its
   Apache-2.0 notice, and record in `patch_origin` the source, the SHA-256
   and the changes of the version that it was ported from.
3. **The recipe.** The first pull request changes the tool manifest, the
   patch and, where needed, the image recipe and the Lake project files,
   as [changing a tool](formal-verification.md#changing-a-tool) describes:
   `switch_export_sha256` of `linux-aarch64` is `null` for the first build
   of `formal image build`, and then takes `opam.switch_export_sha256`
   from the `versions.json` that the build uploads. After the merge,
   `formal image publish` publishes the image from `main`.
4. **The pin.** The second pull request pins the published digest in
   `verification/image-pin.json` and in `IMAGE` of
   `.github/workflows/formal.yml`. The job `formal run` of the gate's CI on
   it, the qualification job, which the label `full-check` starts, is the
   first run of the gate in the new image, and its receipt is the result
   of the requalification. The same pull request also carries the label
   `formal-calibration`, so that the workflow `formal calibration` runs
   the comparator part in the new image and checks that the comparator
   rejects its two fixed challenges ([calibration
   target](formal-verification.md#calibration-target)); the canary does
   not exercise `lake comparator`, so the pin is not switched before that
   run passes.
5. **Requalify.** Every unit of the qualification that is not `VERIFIED`
   in that receipt is a case whose outcome changed. Find the cause of each
   by a controlled comparison: the same case, arguments and environment in
   the old and in the new image. Then revise the expectation in
   `verification/qualification/cases.json` and name the cause, as
   [revised
   expectations](porting/verification-qualification.md#revised-expectations)
   does for the cases taken from the CAS project. A changed outcome of a
   shape that a registered target uses reaches the proofs of that target
   too.
6. **Repair the proofs, one at a time.** Take the units that are not
   `VERIFIED`, the `failures` and the logs in `logs/` of the run from the
   receipt ([receipt](formal-verification.md#receipt),
   [results](formal-verification.md#results)), and repair one proof file
   or one theorem at a time in the stage of a local run with `--keep`, as
   [repairing a proof](#repairing-a-proof) describes.
7. **Record the cost** of each repair ([repair cost](#repair-cost)).

The upgrade is complete when the gate is `VERIFIED` on the head that
carries the new pin and the last repair, every revised expectation names
its cause, and every repair has its cost record.

## Repairing a proof

- Reproduce the failure in the stage of a local run with `--keep`, as
  [editing proofs](formal-verification.md#editing-proofs) describes, and
  copy the repair back to the checkout. Only a run of the gate in CI is
  evidence.
- Change the proof, not the statement. Never edit generated Lean, weaken a
  statement, add an axiom or register a trusted item without review. A
  repair that needs another statement is a statement change, in a pull
  request of its own with the label `spec`, the review and the approval of
  the new hash.
- A repair is a proof pull request: the label `proof`, `Phase: proof`, the
  `Author` field and, when an AI system wrote the proof, the label
  `ai-proof` ([guard](formal-verification.md#guard)). It changes no source
  of the kernel. A raised heartbeat limit needs `Heartbeats-Review`.
- A failure that the new tools cause in the gate itself, such as output of
  a new Lean that the gate does not read, is a tool failure: it is fixed in
  the gate's code within the upgrade, not in a proof.

## Repair cost

Each repaired proof file or theorem gets one row:

| Proof | Pull request | Hours | Heartbeats | Cause |
| --- | --- | --- | --- | --- |
| The proof file, or the theorem by its full name | The repair pull request | The hours spent on it, to the quarter hour | The heartbeats of each repaired theorem before and after, from `base.heartbeats.counts` of the last receipt on the old image and of the receipt of the repair, and any limit that the repair raised | What in the new tools broke it |

The rows go into the description of the repair pull request and are
collected in the project's coordination records, outside this repository.
A proof that still holds needs no repair and gets no row; the receipt
shows it.

## Canary verdicts

The canary writes one verdict per run, the finding of the first step that
did not pass, into `verdict.json` of its artifact, the summary of the
workflow run and one annotation; [toolchain
canary](formal-verification.md#toolchain-canary) defines the findings. Its
detail starts with the step and the commit of `main` that the run tested.
Triage each run:

| Verdict | What it means | What follows |
| --- | --- | --- |
| `PASSED` | The gate verifies the commit with the tools of Aeneas main | Nothing; the resolved versions are in the artifact |
| `BROKEN` at `resolve` or `derive` | Aeneas main has a form of its pins that the committed checks refuse too: the Lean toolchain, the nightly, the `charon-pin` or the Mathlib lock | A finding with the detail; the next upgrade adapts the checks or the pins |
| `BROKEN` at `patch` | The reviewed patch does not apply to Aeneas main | A finding with the run, the Aeneas commit and Git's output from `patch.json`; the next upgrade ports the patch |
| `BROKEN` at `build` | A tool stage of the recipe fails: a compile error of Aeneas or Charon, a failing `lake build Aeneas`, a missing notice | A finding with the stage and the failure block of `build.log`. Read the text of a `backend` failure first: a network error of `lake exe cache get` that no rule of the canary knows is no breakage, and the run is repeated |
| `BROKEN` at `gate` | The gate does not verify the commit in the new image | Compare the canary's receipt with the units of a merge record of `formal.yml` that `cargo xtask formal receipt` calls `CURRENT` for the same commit of `main`, such as that of a manual or weekly run on it, or that of the head whose merge the job `formal receipt review` judged: a unit is broken only when it is `VERIFIED` there and not in the canary. A finding names those units, the qualification cases among them and the tool failures of the gate, as the estimate of an upgrade |
| `DEFECT` | A field that the canary derived disagrees with a tool or a check, or the canary cannot read a form of the trees or the downloads | No breakage: the canary is fixed, and the run is repeated |
| `FAILED` | The run did not complete: a step limit, the disk, the network, the runner, or a step of the canary's own | No breakage: find the cause in the logs of the job and run it again. A build that reached its limit while it built Mathlib, because Mathlib had no build cache for the new Lake lock, or a disk that filled, is a limit of the job and of the hosted runner, not of the tools |

The canary runs the whole gate without the [comparator
part](formal-verification.md#comparator), so it never exercises
`lake comparator`, its messages or its sandbox: `PASSED` says nothing
about them, and the units of the comparator in a merge record have no
counterpart in a canary receipt, so a `BROKEN` at `gate` compares the
other units only. A change of the toolchain pin runs `formal calibration`,
which runs the comparator part and its two challenges that must be
rejected, before it switches (step 4 of the [procedure](#procedure)).

A finding is registered in the project's coordination records, never in
this repository, and nothing of a canary run is repaired: the breakage is
fixed only by an upgrade. A canary receipt records no image reference and
is no evidence about krepi; only the gate in the pinned image is.

## Rules that stay

The rules of the [repository instructions](../AGENTS.md) and of
[formal verification](formal-verification.md) apply to every pull request
of an upgrade, as to any other.
