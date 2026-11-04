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
and `verification/legacy.json` exist and are empty. Everything else on this
page is planned: the pinned tools, the Lake project, the `Krepi` Lean modules,
the qualification crate and the `cargo xtask formal` commands. They are set
up by porting the tooling of the CAS project and the prototype tree, and this
page
changes with them. No target is registered and nothing is proved.

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
| `verification/toolchain.json` | Pinned tools: Lean, the Aeneas release and source commit, Charon, reviewed Aeneas patches, the Rust nightly used by Charon, and the Lake lock of the Aeneas library | Planned |
| `verification/tooling/` | Reviewed tool patches and frozen tool environments named by the pins | Planned |
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
| `xtask/src/formal/` | The `cargo xtask formal` commands | Planned |

Generated Lean, extraction outputs, logs and receipts go to the ignored
`artifacts/formal/` directory, and the Lake build directory
`verification/.lake/` is ignored as well. Generated definitions are never
edited.

## Tools

The pinned tools are built once per machine into a directory outside the
checkout and sealed: every installed file is recorded with its size and
digest, and later commands refuse an installation whose pins differ from
`toolchain.json` or whose files changed. Setup is the only networked step.
The pins and the setup procedure are ported from the CAS project, whose
installation supports only macOS on Apple silicon; the hosts that krepi
supports are fixed together with the CI runner. Any change of a tool version,
patch or pin requires a new installation and a passing qualification.

## Commands

The `cargo xtask formal` family follows the CAS project. None of these commands
exists yet.

| Command | Purpose |
| --- | --- |
| `cargo xtask formal setup` | Builds and seals the pinned tools |
| `cargo xtask formal tools` | Checks the selected installation |
| `cargo xtask formal qualify` | Tool qualification regression on the code shapes in `verification/qualification` |
| `cargo xtask formal run [--target NAME]...` | The proof gate: qualification, the specifications and every target (or the named ones) with its mutants |
| `cargo xtask formal check` | Registry, legacy and inventory metadata only; runs no tool and proves nothing |
| `cargo xtask formal impact --base REV` | Classifies changed functions since `REV` and reports scope reductions |
| `cargo xtask formal inventory` | Lists every production function by inventory key |
| `cargo xtask formal editor` | Prepares `verification/` for interactive editing |

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
alters a translation fails before it reaches a target. The Aeneas release
that the prototype used rejected some constructs, for example `Iterator::any`
and `flatten`. Code inside a proof target uses the provable Rust subset that
a coding convention states (planned).

## Legacy inventory and admission

`cargo xtask formal inventory` (planned) lists every production function by
file, owner and name, found by a conservative lexical scan that skips test
code. `legacy.json` lists the functions that have no proof at the time the
inventory is adopted; its `baseline` is the commit of that adoption and is
`null` until then. An entry leaves the list when a target proves the function
or, with review, when the function is no longer a production function. A
legacy function is never trusted by a proof and appears in a target's
`unclosed` list when reached. `cargo xtask formal check` reports new
functions that are neither legacy nor proved, and
`cargo xtask formal impact --base REV` reports a removed target, theorem or
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
