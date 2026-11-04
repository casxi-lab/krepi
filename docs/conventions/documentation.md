# Documentation

Every mechanism, service or runtime adaptation that krepi provides is
described by exactly one feature document. Feature documents are the entry
point for its interface, semantics, tested examples, design, implementation
and verification. The complete target scope of the system is described by
the domain documents below `docs/domains/`: one page per subject domain, and
four documents for each component that has a component directory, stating
its requirements, contract, specification and proof path. Porting records
below `docs/porting/` describe where ported code came from; their form is in
[porting](porting.md).

Architecture notes (`docs/architecture.md`), the
[formal verification](../formal-verification.md) page and these conventions
are neither feature documents nor domain documents.

No feature document, domain page or component directory exists yet. A
feature document is written with the first change that provides the feature;
a domain page when the first work in its domain starts; a component directory
with its four documents when the first work on that component starts.

## Location and identity

A feature document lives at `docs/features/<area>/<feature>.md`. Its feature
ID is `krepi.<area>.<feature>`, written in lowercase with hyphens between
words, for example `krepi.kernel.endpoint-ipc`. The file path and the ID must
agree. An ID is never reused or renamed after it is published; when a feature
is split or merged, the old ID stays listed in the `aliases` field of its
successor.

| Area | Scope |
| --- | --- |
| `kernel` | EL1 mechanisms: objects and capabilities, memory and address spaces, interrupts, scheduling and budgets, IPC, notifications and waits, SMP |
| `platform` | Boot and firmware images, QEMU virt and Pi 5 board support, device trees, PCIe and RP1, device authority |
| `services` | The EL0 root, process creation, file, block, stream, UART and job services, storage, recovery |
| `runtime` | The application ABI and SDK, CRT and TLS, sysroots, Rust, C, C++ and Go standard-library adaptation |

New areas, for example for compatibility layers or language runtimes, are
added to this table with their first feature document.

## Metadata

A document starts with a metadata block between two `---` lines. Scalars use
`key: value`; lists use `key:` followed by lines of the form `  - value`. A
list field that does not apply holds the single scalar `none` where the table
allows it.

| Field | Required | Content |
| --- | --- | --- |
| `id` | yes | The feature ID |
| `title` | yes | Short English title |
| `status` | yes | `implemented`, `partial` or `planned` |
| `modules` | yes | Source files or directories that implement the feature, relative to the repository root |
| `operations` | no | ABI operation names the feature defines, as the operation inventory writes them |
| `tests` | yes | Host test files that verify it, including unit-test files below `src/` |
| `suites` | yes | QEMU and board suites, or `none` |
| `theorems` | yes | Fully qualified Lean theorem names below `verification/Krepi/`, or `none` |
| `related` | no | Other feature IDs |
| `aliases` | no | Former feature IDs |

Planning identifiers and acceptance records are not part of the metadata, nor
of any other document in this repository (see
[planning references](#planning-references)).

## Sections

The body uses these level-two sections in this order. A section that does not
apply keeps its heading and states why.

1. `Summary`: what the feature does, which protection domain owns it and what
   it does not do.
2. `Interface`: ABI operations with their arguments, results and errors,
   service protocols, SDK functions, and command or fixture entry points.
3. `Semantics`: authority and ownership, admission and rejection, failure and
   recovery, bounds and limits, cancellation, and what is undefined.
4. `Examples`: numbered examples, each a level-three heading `### exN: title`.
   Every example has a test whose name starts with `exN_` in one of the listed
   test files. At least one example covers a rejected or degenerate input.
5. `Design`: the mechanisms chosen, the invariants they keep, their
   behaviour on several CPUs, and the alternatives they exclude.
6. `References`: hardware manuals, specifications and literature by author,
   title and year, or the URL of a normative document.
7. `Implementation`: responsibilities of the listed modules and key functions.
8. `Verification`: host tests, QEMU and board suites with the configuration
   each runs under, Lean theorems and their scope, trusted assumptions, and
   what remains unverified.
9. `Limitations`: explicit limits and unsupported cases.

Each suite that the Verification section relies on is listed under `suites`;
the section states what evidence it produces and what it does not establish.
A QEMU result is not a board result, and a host test is not a QEMU result.

## Reverse annotations

Lookup works in both directions:

- Every source file listed in `modules` contains a module-level documentation
  line `//! Feature: <id>`; a file serving several features lists one line per
  ID. A directory listed in `modules` carries the line in its `mod.rs`.
- Every source file below `src/` carries at least one such line, except crate
  roots and files that only declare submodules and re-export items.
- Every integration-test module is listed under `tests` by at least one
  feature document, and every suite under `suites`.
- Example tests use the `exN_` prefix of the document they illustrate.
- Lean theorems name their feature ID in their documentation comment.

## Domain documents

A subject domain is an area of the target scope of the system, such as memory
and address spaces or IPC and waits. A component is a part of the system that
features build on and that has its own contract, such as the object table or
the capability table. The domain documents describe the complete feature set
of every subject domain, whether krepi provides a feature or not, and state
for each component with a component directory its requirements, the rules its
code follows, the design of its Lean specification and the proof path of its
code. Feature documents remain the description of what the system provides.

### Directory tree

```text
docs/domains/
  README.md                 the subject-domain index
  <domain>/
    README.md               the domain page
    <component>/
      requirements.md
      contract.md
      specification.md
      proof.md
```

- **Index.** `docs/domains/README.md` lists every domain with its scope,
  states the conventions that every domain shares and what lies outside every
  domain, and links each domain page once it exists.
- **Domains.** Each subject domain has one directory, named in lowercase with
  hyphens, as the index lists it; `cross-cutting` comes last.
- **Contents.** A domain directory holds its `README.md` and the directories of
  its components, nothing else. A component directory holds exactly the four
  component documents.
- **Placement.** A component that several domains use lives below
  `cross-cutting/`; a component that serves one domain lives in the directory
  of that domain. A component directory takes the name of its contract.

### Domain pages

A domain page describes the complete feature set of its domain. Its level-two
sections are, in this order:

1. `Overview`: the scope of the domain, its theoretical and hardware limits,
   and the division of work with other domains and components, by link.
2. `Conventions`: the rules of this domain only, such as authority rules,
   error and result conventions, bounds, ordering and progress guarantees.
3. `Feature index`: a table with the columns Feature, Scope, Feature documents
   and Components. The first cell of each row holds one link to a sub-feature
   section and nothing else, and every sub-feature section is linked exactly
   once.
4. One section per sub-feature, in the order of the Feature index. Other pages
   and the coordination repository link these sections by anchor, so a title
   changes only together with every link to it.
5. `Dependencies`: a table with the columns Feature, Depends on and Reason.
6. `Exclusions`: what the domain leaves out, and where it belongs instead.
7. `References`: hardware manuals, specifications and literature.

A sub-feature section has seven parts, in this order:

| Part | Content |
| --- | --- |
| Description | Objects, operations, authority, state and its transitions, failure behaviour, and what the feature does not do |
| Design background | Mechanisms, the results from systems research and hardware manuals they rely on, and their limits |
| Consumers | The services, runtimes and applications that build on it, in this and other domains |
| Interface | Operations, results and errors, which failures are errors and which are states |
| Prerequisites | Links to sections of the page, other domain pages, components and feature documents |
| Engineering notes | Pitfalls, bounds and budgets, cancellation points, per-CPU and shared state, expected sizes |
| Verification | Independent evidence: invariants, required counterexamples, environments, and links to the specification and proof path of a component where one exists |

Each part starts a paragraph with its label in bold, as in **Consumers.**, and
is never a heading.

### Writing rules for domain pages

- **Normative present tense.** A domain page states what each feature does, as
  a rule, in the present tense. It avoids words that date the text, such as
  "currently", "already", "not yet", "today", "will" and "planned". What krepi
  provides shows only through the Feature documents column and the `status`
  of the linked documents.
- **Decided rules in place.** A decided rule is stated in the section it
  governs, without a reference to the decision.
- **Names.** A code span names only an item that exists or that a contract
  fixes. Any other item, including a name a plan proposes, is described by its
  role.
- **Independent evidence.** Verification relies on invariants, constructions
  and environments that are independent of the code under test, as
  [testing](testing.md#independent-evidence) requires.
- **Headings and lines.** Headings are ASCII, unique on the page and free of
  math, and lines wrap at about 80 columns.

### Component documents

Each kind of content has one home, and the other documents link it.

| Content | Home | Not repeated in |
| --- | --- | --- |
| Observable behaviour of a component: criteria, examples, entry points, evidence and deliberate limits | `requirements.md` | Feature documents |
| Rules that code and tests follow: terms, rule sections, testing obligations, extractability and current deviations | `contract.md` | Domain pages and the other component documents |
| Model, design rationale, and the correspondence of contract clauses and requirements to Lean | `specification.md` | The contract |
| Targets, obligations, premises, trusted items, mutants and what is not proved | `proof.md` | The Verification sections of feature documents |
| Gate mechanics, receipts, the trusted-boundary table and library models | [Formal verification](../formal-verification.md) | `proof.md`, which names the rows it relies on |
| Interface, tested examples and status of a provided capability | Its feature document | Domain pages, which link it |
| Proposal records, decisions, task mapping | The coordination repository | Any document in this repository |

- **Requirements.** `requirements.md` starts with a metadata block whose only
  field, `features`, lists the IDs of the feature documents the requirements
  constrain. Its level-two sections are `Sources`, `Configurations`,
  `Requirements`, `Liveness, time and performance`, `Scope` and
  `Contract sections without a requirement`. Each requirement is a
  level-three heading that holds only its ID, followed by its title in bold,
  the observable behaviour and the criterion that decides it, and the fields
  Examples, Entry points, Contract, Specification, Proof path and Evidence.
  `Configurations` names the boards, CPU counts and image configurations a
  requirement holds for.
- **Contract.** `contract.md` has no metadata. Its introduction says what the
  page governs and links the other three documents. `Terms` comes first,
  followed by the rule sections, a section of testing obligations, an
  `Extractability` section that states which code follows the provable Rust
  subset, `Current deviations` while any deviation remains, and `References`
  when it cites sources.
- **Specification.** `specification.md` starts with a metadata block whose only
  field, `specifications`, lists the Lean modules it describes, each
  registered under `specifications` in `verification/targets.json`. Its
  level-two sections are `Widths and quantifiers`; `Model`, with one
  subsection per section of the Lean module; `Design decisions`;
  `Contract correspondence`; `Requirement correspondence`, with one
  level-three section per requirement ID; and `Dependencies`.
- **Proof path.** `proof.md` starts with a metadata block of two lists:
  `targets`, the registered targets of the component, and `planned`, the
  kebab-case names of its targets that are not registered. Its level-two
  sections are `Targets`, `Trusted boundary`, `Unclosed dependencies`,
  `Mutants`, `Qualification` and `Not proved`. A planned target uses the name
  it will carry in `verification/targets.json`.

### Requirement IDs

A requirement ID, such as `IPC-R03`, is a prefix of two to five uppercase
letters, `-R` and two digits. Each component has its own prefix, and its IDs
run from R01 in steps of one. An ID is never renumbered or reused: a withdrawn
requirement keeps its headings with **Withdrawn.** and the reason in place of
its text. Requirement IDs label requirements within their component; they are
not planning identifiers.

## Planning references

Plans and their records belong to the project's coordination records, kept
outside this repository:
milestone and task numbers, proposal IDs and versions, decision numbers,
capability and interface codes, codes of discovered requirements and open
decisions, the order in which work closes, and the mapping of tasks to
requirements and targets. No document or code comment in this repository uses
them, in prose or in code spans. The forms to avoid include `krepi/` followed
by a stage number and a slash and F, V or P with two digits; a task suffix of
`/T` and two digits; `system/` followed by M or V and two digits; and `CAP-`,
`IF-` or `ADR-` followed by digits. A document states the technical content
instead:

- an item that does not exist is named by the module or file its contract
  fixes and marked (planned);
- a proof that is to be written is named by its target and obligation names in
  `proof.md`;
- a limit that waits for other work states the condition that lifts it;
- a decision is stated as the rule it made, where the rule applies.

## Language and notation

Every document is written in English and contains no Han characters. Dated
work logs, decisions attributed to people and the history of how a design was
reached stay out of this repository. Mathematics, where a document needs it,
is written in LaTeX: `$...$` inline and `math` fenced blocks for display.
Register names, addresses, operation names, commands and file paths are code
spans.

## Tooling

`cargo xtask docs check` (planned) is to validate metadata, referenced paths,
items, operations, tests, suites and examples, section order, the generated
index, the reverse annotations, the domain tree, planning references, Han
characters and local links in every Markdown file at the root and below
`docs/`, as part of `cargo xtask check`. `cargo xtask docs index` (planned)
regenerates `docs/features/README.md`, and `cargo xtask docs find` (planned)
prints the documents that list or annotate a source path, item, test, suite
or theorem. Until these commands exist, review checks these rules.
