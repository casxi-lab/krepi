---
targets:
  - fdt
planned: []
---

# Device-tree proof path

The proof path of the `fdt` component: the target that is to refine the
[specification](specification.md) of the [contract](contract.md), the
premises of its theorems with the guards that keep them, the code shapes
that the implementation adopts so that the tools translate it into code a
proof can rely on, its trusted boundary, its mutants and what no theorem
states. The module `fdt` does not exist yet, so the target is registered in
`verification/targets.json` in the state `planned`, with its name, module,
description and roots alone ([proof targets](../../../formal-verification.md#proof-targets)).
Its obligations, its mutants and the lists of the functions that it proves
and reaches are registered once the code exists, as this page plans them;
until then the target is extracted and type-checked only when a run names
it.

The statements of the specification itself, its invariants, its
properties, its specification tests and the statements that its
unreachable error branches are never taken, are registered in
[`verification/statements.json`](../../../../verification/statements.json)
as planned and are proved by proof pull requests below
[`verification/Krepi/Proofs/Fdt/`](../../../../verification/Krepi/Proofs/Fdt/)
([statements and proofs](../../../formal-verification.md#statements-and-proofs)).
They are not obligations of the target: the refinement theorems of the
target take the invariants that they establish as hypotheses
([premises](#premises)).

## Targets

### fdt

| Field | Value |
| --- | --- |
| Name | `fdt`, in the state `planned` |
| Module | `Fdt`, the namespace of the generated definitions |
| Feature | None: no feature document describes the component, whose requirements list no feature, and a feature ID is that of a feature document ([documentation](../../../conventions/documentation.md#location-and-identity)) |
| Entries | The 11 rows of the [entry table](contract.md#entry-points), lines 109 to 119 of the contract: one target, not split |
| Roots | The 60 functions that the rows name, below |
| Budget | The default of 1,800 s ([cluster and budget](#cluster-and-budget)) |

The roots are the full paths of the functions that the rows of the entry
table name, in the crate `krepi_kernel` of the root package and its module
`fdt` ([extractability](contract.md#extractability)). A short name in a row
is a function of the nearest type named before it in the same row, so
`ram` of line 111 is `MemoryMap::ram` and `ram` of line 112 is
`BootMemory::ram`. `cells_u64`, which no type precedes, is a function of
the module, as the contract calls it, `cells_u64(bytes, cells)`. The value
types of line 118 and the constants of line 119 are not roots: the
extraction reaches them through the functions that use them.

| Line | Functions | Roots |
| ---: | ---: | --- |
| 109 | 1 | `krepi_kernel::fdt::Fdt::parse` |
| 110 | 15 | `krepi_kernel::fdt::Fdt::nodes`, `krepi_kernel::fdt::Fdt::find_node`, `krepi_kernel::fdt::Fdt::reservations`, `krepi_kernel::fdt::Fdt::total_size`, `krepi_kernel::fdt::Node::name`, `krepi_kernel::fdt::Node::parent`, `krepi_kernel::fdt::Node::property`, `krepi_kernel::fdt::Node::string_property`, `krepi_kernel::fdt::Node::enabled`, `krepi_kernel::fdt::Node::address_cells`, `krepi_kernel::fdt::Node::size_cells`, `krepi_kernel::fdt::Node::reg`, `krepi_kernel::fdt::Node::ranges`, `krepi_kernel::fdt::Node::dma_ranges`, `krepi_kernel::fdt::Node::translate_reg` |
| 111 | 4 | `krepi_kernel::fdt::Fdt::discover_memory`, `krepi_kernel::fdt::MemoryMap::ram`, `krepi_kernel::fdt::MemoryMap::reserved`, `krepi_kernel::fdt::MemoryMap::dynamic` |
| 112 | 8 | `krepi_kernel::fdt::Fdt::discover_boot_memory`, `krepi_kernel::fdt::BootMemory::ram`, `krepi_kernel::fdt::BootMemory::reserved`, `krepi_kernel::fdt::BootMemory::dynamic`, `krepi_kernel::fdt::BootMemory::dtb`, `krepi_kernel::fdt::BootMemory::image`, `krepi_kernel::fdt::BootMemory::ram_bytes`, `krepi_kernel::fdt::BootMemory::is_available` |
| 113 | 1 | `krepi_kernel::fdt::BootMemory::find_available` |
| 114 | 8 | `krepi_kernel::fdt::Fdt::discover_cpus`, `krepi_kernel::fdt::CpuTopology::count`, `krepi_kernel::fdt::CpuTopology::profile`, `krepi_kernel::fdt::CpuTopology::affinity`, `krepi_kernel::fdt::CpuTopology::validate_timers`, `krepi_kernel::fdt::CpuProfile::logical_id`, `krepi_kernel::fdt::CpuProfile::affinity_shift`, `krepi_kernel::fdt::CpuProfile::conduit` |
| 115 | 6 | `krepi_kernel::fdt::cells_u64`, `krepi_kernel::fdt::Reg::new`, `krepi_kernel::fdt::AddressMap::new`, `krepi_kernel::fdt::AddressMap::kind`, `krepi_kernel::fdt::AddressMap::to_parent`, `krepi_kernel::fdt::AddressMap::to_child` |
| 116 | 3 | `krepi_kernel::fdt::MemoryPlan::all_ram`, `krepi_kernel::fdt::MemoryPlan::new`, `krepi_kernel::fdt::MemoryPlan::from_boot_memory` |
| 117 | 11 | `krepi_kernel::fdt::MemoryPlan::managed_banks`, `krepi_kernel::fdt::MemoryPlan::ram`, `krepi_kernel::fdt::MemoryPlan::reservations`, `krepi_kernel::fdt::MemoryPlan::boot_ranges`, `krepi_kernel::fdt::MemoryPlan::firmware_ranges`, `krepi_kernel::fdt::MemoryPlan::described_bytes`, `krepi_kernel::fdt::MemoryPlan::managed_bytes`, `krepi_kernel::fdt::MemoryPlan::contains_ram`, `krepi_kernel::fdt::MemoryPlan::is_available`, `krepi_kernel::fdt::MemoryPlan::permits_backing`, `krepi_kernel::fdt::MemoryPlan::available_ranges` |
| 118 | 3 | `krepi_kernel::fdt::Span::new`, `krepi_kernel::fdt::Span::end`, `krepi_kernel::fdt::Span::contains` |
| 119 | 0 | None: the eight constants |

**Iterators.** `Fdt::nodes`, `Fdt::reservations`, the entries of a `Reg`
and `MemoryPlan::available_ranges` give iterators, whose types the contract
does not name. The `next` of an iterator is reached from the roots that
walk it, and a root that only returns an iterator does not reach it: no
function of the module walks the usable ranges, so the `next` of the
iterator of `available_ranges` is reached by no root. Its refinement
theorem needs that `next` to state the ranges that the iteration gives, as
`MemoryPlan.availableRanges` lists them. This is an open obligation of the
target, which the contract records in its
[open obligations](contract.md#open-obligations): the `next` of each
iterator type joins `start_from` once the implementation names the types,
and before the implementation merges. Its carriers are the implementation,
which names the types and adds their `next` to the roots, and the
refinement proof of the target, which proves each `next` against the
representation of an iterator by its list ([premises](#premises)). The new
roots change the roots of the target, which is reviewed as a change of a
statement ([guard](../../../formal-verification.md#guard)).

**Obligations.** One for each root: its refinement theorem states that, for
every input of its machine widths ([widths and quantifiers](specification.md#widths-and-quantifiers))
and under the premises below that its inputs need, the function returns the
value that its specification gives, related to it by the representation of
the value types, or fails with the error that its specification gives, and
that a failure returns nothing else. The mutants below name the theorem
that each must fail as the refinement theorem of a function; the
registration gives each theorem its Lean name. A function with a loop is
proved to return as well, since Aeneas translates a loop as a function
that may diverge.

### Premises

The refinement theorems take these hypotheses. Each is an invariant of the
specification ([invariants](specification.md#invariants)) or a condition of
the boot, with the function or the code that establishes it, what
preserves it and what relies on it. The translation of the module does not
show which module may build a value, so the
[compile-time guards](#compile-time-guards) make each premise of a value
true of every value that another module holds.

| Premise | Established by | Preserved by | Consumed by |
| --- | --- | --- | --- |
| A tree is one that `Fdt::parse` returned from its bytes, so its record tree keeps `Fdt.WellFormed` | `Fdt::parse` (`ParseWellFormed`) | No entry changes a tree, and its bytes stay borrowed while it lives (guards 1 and 2) | The node access; `Node::translate_reg`, whose climb takes at most `MAX_DEPTH` buses (`TranslateRegFuelSuffices`); the discoveries, which find the root (`DiscoverMemoryNoBadTree`, `DiscoverBootMemoryNoBadTree`) |
| A node is one of its tree: in the specification an index below its number of nodes, in the code a begin-node token of its checked structure block | `Fdt::nodes`, `Fdt::find_node` and `Node::parent`, the only functions that give a node | No entry changes a node | Every function of `Node` |
| A `Reg` keeps `Reg.WellFormed` | `Reg::new` and `Node::reg` (`RegNewWellFormed`, `NodeRegWellFormed`) | No entry changes it | The iteration of its entries, whose `next` does not fail; `Fdt::discover_memory` |
| An `AddressMap` keeps `AddressMap.WellFormed` | `AddressMap::new`, `Node::ranges` and `dma_ranges` (`AddressMapNewWellFormed`, `NodeRangesWellFormed`, `NodeDmaRangesWellFormed`) | No entry changes it | `to_parent`, `to_child` and `Node::translate_reg`, whose translated span stays within its width (`WindowTranslationNoOverflow`) |
| A `MemoryMap` keeps `MemoryMap.WellFormed` | `Fdt::discover_memory` and `discover_boot_memory` (`DiscoverMemoryWellFormed`, `DiscoverBootMemoryWellFormed`) | No entry changes it | The sum of the RAM ranges of the discovery of the boot memory (`RamBytesFit`); the queries of the boot memory; the boot code, which gives its ranges to the boot memory map |
| A `BootMemory` keeps `BootMemory.Consistent`, with the limit and the alignment that it holds | `Fdt::discover_boot_memory`, which gives it those of its profile (`DiscoverBootMemoryConsistent`) | No entry changes it | `is_available` and `find_available`, which exclude the image and the tree (`FindAvailableNoLimitExceeded`); `MemoryPlan::from_boot_memory` |
| A `CpuTopology` keeps `CpuTopology.Supported` | `Fdt::discover_cpus` (`DiscoverCpusSupported`) | No entry changes it | `CpuTopology::affinity` and `validate_timers`; the start of the secondary CPUs in the boot code |
| A `MemoryPlan` keeps `MemoryPlan.WellFormed` | `MemoryPlan::all_ram`, `new` and `from_boot_memory` (`AllRamWellFormed`, `MemoryPlanNewWellFormed`, `FromBootMemoryWellFormed`) | The publication of the boot memory map, which keeps it unchanged (`PublishPlanWellFormed`, `PublishTopologyWellFormed`, `StartSecondariesWellFormed`) | The queries; `described_bytes` and `managed_bytes`, whose sums fit 64 bits; `available_ranges` (`AvailableRangesWellFormed`, `UsableRangesExact`); the kernel direct map and the page ownership table of the [page-tables](../../memory/page-tables/contract.md) component |
| An iterator of the module stands for a list of the specification: its calls of `next` give the items of that list in order, and then none. The nodes are those of `Fdt.nodes`, the reservation entries those of `Fdt.reservations`, the entries of a `Reg` those of `Reg.entries`, and the usable ranges those of `MemoryPlan.availableRanges` | The functions that give the iterators, `Fdt::nodes`, `Fdt::reservations`, `Reg::new` and `Node::reg`, and `MemoryPlan::available_ranges`, whose refinement theorems relate the iterator that each gives to its list | Each `next`, which advances only the iterator's own cursor over checked bytes or values and does not fail ([check and execute](contract.md#check-and-execute)), and gives the head of the rest of the list | The functions that walk an iterator, such as `Fdt::find_node` and the discoveries over the nodes and `Fdt::discover_memory` over the entries of a `Reg`; the callers of `available_ranges`, the kernel direct map and the page ownership table of the page-tables component, to which `UsableRangesExact` and `AvailableRangesWellFormed` carry over |
| The bytes of the hand-over tree do not change while the kernel runs | The firmware or the loader of QEMU, before the cold entry; the board, which forms the slice of the tree ([open obligations](contract.md#open-obligations)) | The boot memory map, which keeps their pages as boot storage ([state fields](contract.md#state-fields)) | Every tree of the hand-over bytes, and the CPU topology that the boot publishes from it (`BootState.FromHandOver`) |

### Compile-time guards

Premises that the translation does not show are fixed when the code
compiles ([rule 6](../../../conventions/provable-subset.md#6-compile-time-guards)),
each with a compile-fail case that the `subset` step runs
([mechanical checks](../../../conventions/provable-subset.md#mechanical-checks)):

1. **Private fields.** `Fdt`, `Node`, `Reg`, `AddressMap`, `MemoryMap`,
   `BootMemory`, `CpuTopology`, `MemoryPlan` and the iterator types
   keep their fields private to the module, so that only the functions of
   the premises build them, and a value that another module holds keeps
   the premise of its type. The case for each type writes a struct literal
   of it in another module and expects `E0451`. `Span`, `ReservedRegion`,
   `HandOverProfile`, `CpuProfile` and `TimerInterrupts` carry no invariant
   and have public fields: their specification holds for every value.
2. **Borrowed bytes.** A tree borrows the slice of its bytes for its
   lifetime, and its nodes and iterators borrow the tree, so no write to
   the bytes compiles while any of them lives. The case writes a byte of a
   slice while a tree of it lives and expects `E0506`.
3. **No duplication guard.** No value of the component carries a right
   that a copy would break: every value is immutable once built, so its
   types may implement `Clone` and `Copy`, and no guard against them is
   planned.

The `subset` step also checks the module mechanically for `static mut`,
interior mutability and `cfg` outside its allowlist
([rules 7 and 8](../../../conventions/provable-subset.md#8-no-interior-mutability)),
and the contract states that the module has no `unsafe` code and no
assembly ([extractability](contract.md#extractability)).

### Cluster and budget

The target reaches no function of another component and cuts none, so it
has no premise of another target. The page-tables component reads the boot
memory map as values and relies on `MemoryPlan.WellFormed` and on the
usable ranges of `UsableRangesExact`: its target and this one form a
cluster connected by premises, in which the theorems of this target about
`MemoryPlan::all_ram`, `new`, `from_boot_memory` and `available_ranges` are
restated over the generated types of the other target. The gate does not
check premises yet, so `cargo xtask formal check` refuses them
([proof targets](../../../formal-verification.md#proof-targets)), and the
two targets are registered without them until it does. A Lean module never
imports the generated definitions of both targets: their enumerations and
external declarations would clash
([R6](../../../conventions/provable-subset.md#r6-enumeration-names-across-targets)).

Estimates for the budget:

- The statements of the specification: the proofs of its 41 statements of
  invariants and 8 properties about 7,000 lines (4,500 to 11,000), and of
  its 20 specification tests about 600 lines (300 to 1,500); the 13
  statements of unreachable branches are not estimated apart, and the
  proofs of all of them about 8,000 lines (5,000 to 14,000). The witnesses
  are proved in the specification.
- The gate: the target keeps the default budget of 1,800 s, which its
  extraction, the type check of its generated definitions, the build of its
  proofs and its mutants share. The modules of the specification that its
  proofs import build in about 30 s from scratch, of which the witnesses
  take about 24 s, and `leanchecker` evaluates the witnesses again, about
  20 s more. The shard of the calibration target, 12 functions and 30
  mutants, took 409 s; the shard of this target is measured when its
  obligations are registered, and its budget is set from that measurement.

## Trusted boundary

The target relies on these rows of the
[trusted boundary](../../../formal-verification.md#trusted-boundary): the
Lean kernel and the three standard axioms; Mathlib and the Aeneas Lean
library; Charon, the Rust nightly and Aeneas; and the compiler, which no
proof covers. It relies on no assembly, `unsafe` code, atomics, IRQ path or
hardware: the module has none. The bytes that the firmware hands over are
its input, which it checks; the board's forming of their slice is an open
obligation, not a trusted item ([unclosed dependencies](#unclosed-dependencies)).

The target is to add no item to the boundary:

- **Cut points.** None: no function of the module reads hardware or global
  state, so none needs to be translated without its body.
- **Models and trusted axioms.** None: no item of `models.json` or
  `tcb.json`, and no `trusted_axioms`. The witnesses of the specification
  use `decide +kernel`, which the kernel checks, and no native decision.
- **Derived methods.** The module calls no method that a `#[derive(..)]`
  defines, such as a derived `eq` of spans, which would stay unverified: it
  compares values field by field.
- **Unconstrained items.** None when the module keeps the
  [code shapes](#code-shapes). Each library item below would otherwise be
  reached as an external declaration without a model. A theorem must hold
  for every interpretation of such a declaration
  ([R2](../../../conventions/provable-subset.md#r2-iteratorany)), so no
  result that depends on it could be proved, and a model of it is refused
  while models are not compared with their implementations
  ([models](../../../formal-verification.md#models)).

| Library item | Where the module would reach it | Shape that avoids it |
| --- | --- | --- |
| `core::str::from_utf8` and `str` comparisons | The UTF-8 of node and property names, of string values and of the root `compatible` of a hand-over tree, with the entries that its profile requires; the components of a path; `okay`, `ok`, `memory`, `cpu` and the PSCI methods | Code shape 3 |
| Equality, `starts_with` and the iterators of `[u8]` | Property names, the prefix `memory@` and the lists of the PSCI `compatible` | Code shapes 3 and 5 |
| `u32::from_be_bytes`, `u64::from_be_bytes` and `TryFrom<&[u8]>` for arrays | Header words, tokens, cells and reservation entries | Code shape 1 |
| `slice::sort` and its relatives | The RAM banks of the boot memory map, sorted by their start | Code shape 7 |
| The provided methods of `Iterator` and the `IntoIterator::into_iter` of a `for` loop | The walks of nodes, reservation entries, windows and ranges | Code shapes 4 and 5 |
| `u64::is_power_of_two`, `count_ones`, `trailing_zeros`, `core::cmp::max` and `min` | The alignment and the candidates of `find_available` | Code shape 8 |

## Unclosed dependencies

The target leaves open what the contract lists in
[open obligations](contract.md#open-obligations): the forming of the slice
of the hand-over tree by each board, and, until the implementation names
its iterator types, the `next` of each of them, which then joins the roots
([iterators](#fdt)). It cuts no function, and it reaches no function of
another component.

## Mutants

The target registers 29 source mutants, 1 to 3 for each row of the entry
table, among them off-by-one changes of three limits of the parse,
`MAX_DEPTH`, `MAX_PROPERTY_NAME` and `MAX_BLOB_SIZE`, and of three other
limits. Each is registered with its file, the text that it finds
and replaces and the theorems that must fail once the code exists; the
table describes the edit. Each must make the refinement theorem of the
function that it names fail.

| Name | Line | Source change | Must fail |
| --- | ---: | --- | --- |
| `parse-depth-off-by-one` | 109 | The depth check admits a node at depth `MAX_DEPTH`, a path of 33 nodes | Refinement of `Fdt::parse` |
| `parse-name-padding-unchecked` | 109 | The zero check of the padding after a node name is dropped, so a nonzero byte there gives no `BadPadding` | Refinement of `Fdt::parse` |
| `parse-reservation-overlap-unchecked` | 109 | The comparison of a reservation entry with the earlier entries is dropped, so overlapping entries give no `Overlap` | Refinement of `Fdt::parse` |
| `find-node-first-sibling` | 110 | A path component that matches two siblings gives the first of them instead of `AmbiguousMapping` | Refinement of `Fdt::find_node` |
| `enabled-rejects-ok` | 110 | `enabled` is true only for `okay`, not for `ok` | Refinement of `Node::enabled` |
| `address-cells-inherited` | 110 | An absent `#address-cells` takes the value of the parent instead of 2 | Refinement of `Node::address_cells` |
| `memory-overlap-unchecked` | 111 | A RAM range is not compared with the earlier ranges, so overlapping ranges give no `Overlap` | Refinement of `Fdt::discover_memory` |
| `memory-ranges-off-by-one` | 111 | The count of RAM ranges admits `MAX_MEMORY_REGIONS + 1` ranges | Refinement of `Fdt::discover_memory` |
| `dynamic-not-counted` | 111 | An enabled child of `/reserved-memory` with `size` and without `reg` is not counted | Refinement of `Fdt::discover_memory` |
| `hand-over-size-off-by-one` | 112 | The size check admits a hand-over tree of one byte more than the `max_blob_size` of the profile | Refinement of `Fdt::discover_boot_memory` |
| `hand-over-image-on-tree-unchecked` | 112 | The check that the image shares no address with the tree is dropped | Refinement of `Fdt::discover_boot_memory` |
| `is-available-ignores-tree` | 112 | `is_available` leaves the span of the tree out of its exclusions | Refinement of `BootMemory::is_available` |
| `find-available-unaligned` | 113 | After a candidate that touches an exclusion, the next candidate starts at the end of that exclusion without aligning it up | Refinement of `BootMemory::find_available` |
| `find-available-touch-at-end` | 113 | A candidate that ends exactly at the start of an exclusion is taken to touch it | Refinement of `BootMemory::find_available` |
| `cpus-repeated-id-accepted` | 114 | A CPU node with the ID of an earlier CPU node is accepted | Refinement of `Fdt::discover_cpus` |
| `logical-id-unmasked` | 114 | `logical_id` reads the ID without masking the bits outside the affinity fields | Refinement of `CpuProfile::logical_id` |
| `cells-high-cell-dropped` | 115 | `cells_u64` of two cells keeps only the low cell | Refinement of `cells_u64` |
| `translate-first-window` | 115 | A request that two windows hold translates through the first instead of failing with `AmbiguousMapping` | Refinement of `AddressMap::to_parent` |
| `reg-low-4gib-unchecked` | 115 | `Reg::new` does not check that a span of one address cell ends within the first 4 GiB | Refinement of `Reg::new` |
| `plan-boot-storage-off-by-one` | 116 | The capacity check admits 5 spans of boot storage | Refinement of `MemoryPlan::all_ram` |
| `plan-boot-storage-inward` | 116 | A span of boot storage is rounded inward to whole pages instead of outward | Refinement of `MemoryPlan::all_ram` |
| `plan-window-outside-ram` | 116 | `new` does not check that one bank holds the managed window | Refinement of `MemoryPlan::new` |
| `available-ranges-past-reservation` | 117 | A usable range ends at the end of the next reservation instead of its start | Refinement of `MemoryPlan::available_ranges` |
| `permits-backing-all-banks` | 117 | `permits_backing` looks for a bank instead of a managed bank | Refinement of `MemoryPlan::permits_backing` |
| `managed-bytes-of-banks` | 117 | `managed_bytes` sums the banks instead of the managed banks | Refinement of `MemoryPlan::managed_bytes` |
| `span-new-wraps` | 118 | `Span::new` accepts a span whose end leaves 64 bits | Refinement of `Span::new` |
| `span-contains-end-off-by-one` | 118 | `contains` holds also when its argument ends one byte after the span | Refinement of `Span::contains` |
| `max-property-name-off-by-one` | 119 | `MAX_PROPERTY_NAME` is 65 | Refinement of `Fdt::parse` |
| `max-blob-size-off-by-one` | 119 | `MAX_BLOB_SIZE` is 2 MiB and 1 byte | Refinement of `Fdt::parse` |

### Specification mutations

Two changes of the specification check that the refinement theorems bind
it, by hand, until a tool makes such changes. Each makes the specification
stronger than the contract, so that the implementation no longer refines
it. Each is expected to make the refinement theorem of its function fail;
when that theorem still holds, the specification is weaker than the
implementation where the change lies, and that is recorded as a finding.

| Change | Expected outcome |
| --- | --- |
| The postcondition of `Fdt.parse` also requires zero bytes in the padding after each property value, as section 5.4 of DTSpec v0.4 does and the contract does not | The refinement theorem of `Fdt::parse` fails on a tree with a nonzero byte after a property value, which the implementation accepts as the trees of QEMU virt require; so do the replay of `fdt-parser-7` and the proof of `ParseAcceptsNameAtLimit` |
| The postcondition of `Fdt.discoverMemory` also requires its RAM ranges in address order, rejecting a tree whose memory nodes are in another order | The refinement theorem of `Fdt::discover_memory` fails on a tree with two memory nodes, the higher first, whose ranges the implementation gives in tree order |

## Qualification

The implementation adopts these code shapes, so that the pinned tools
translate every root into code that a proof can rely on. Each cites the
[provable Rust subset](../../../conventions/provable-subset.md) or the
qualification cases that record the outcome of the shape in
`verification/qualification/cases.json`.

### Code shapes

1. **Words from bytes.** Big-endian words and cells are put together from
   single bytes with shifts, masks and `as` casts, each byte read after a
   check of its index, not with `from_be_bytes` or a conversion of a slice
   into an array (`arithmetic`, `integer-conversions`, `slices`). A read
   that would pass the end of its block gives the error of the contract
   before any index leaves the slice, so no input makes an entry panic.
2. **Checked arithmetic.** A sum that the contract checks against 64 bits
   uses `checked_add` taken apart with `match` (`checked`); offsets inside
   a tree, which stay below `MAX_BLOB_SIZE`, and sums that an invariant
   bounds, such as `described_bytes`, may use plain arithmetic, whose
   absence of overflow the premises give. A `u64` becomes a `usize` by an
   `as` cast after a comparison with the bound, and `i64::from` of a `u32`
   is avoided, since it stays an external function (`integer-conversions`).
3. **Strings as bytes.** The module checks UTF-8 and the character sets of
   names in index loops over bytes (`string-bytes`), and keeps names,
   paths and string values as byte slices that it compares with a helper
   loop. A `match` on string literals reaches the `str` equality, an
   external function (`string-match`), and an `Option` of references is
   not compared with `==` (`option-reference-eq`, rejected). An entry that
   gives a name or a string value gives the bytes that it checked, and an
   entry that takes a path reads it through `as_bytes`.
4. **One loop per function.** Each function holds at most one loop, and a
   nested loop goes into a helper function: the comparison of a property
   name with the earlier ones of its node, of a reservation entry, RAM
   range, bank or span with the earlier ones, and of a candidate with the
   exclusions (`nested-loop`, rejected; `split-loop`, translated). A check
   that returns early comes before the call of the helper that holds the
   loop, in a function without a loop (`return-before-loop`,
   `flag-before-loop` and `loop-in-branch`, rejected; `checks-before-loop`
   and `returns-then-helper`, translated). `unwrap` is not used in a loop
   (`unwrap-in-loop`, rejected).
5. **Index loops and own iterators.** Tables are walked by index loops,
   not by iterator adapters or `for` loops over library iterators
   (R2, R3, `iterator-adapters`, `index-loop`,
   `generic-into-iterator-loop`). The iterators of the module implement
   `next` alone, which advances a private cursor over checked bytes or
   values and does not fail ([check and execute](contract.md#check-and-execute));
   the module walks them by calling `next` in a `while` loop.
6. **No closures, no allocation.** `match` takes the place of combinators
   with closures, and no function takes a callback
   ([R4](../../../conventions/provable-subset.md#r4-closures-as-callbacks),
   `option-combinators`). The results live in arrays of the capacities of
   the contract with a count: 32 RAM ranges, 128 reserved regions, 32
   banks, 4 spans of boot storage, 128 firmware reservations and the 32
   open nodes of the walk of the tokens, with no `Vec`
   ([rule 2](../../../conventions/provable-subset.md#2-no-allocation-at-run-time),
   `const-generic`, `vector-operations`).
7. **Sorting by hand.** The banks are sorted by their start with an
   insertion sort whose inner loop is a helper function (`split-loop`), not
   with a sort of the library, which has no model and takes a closure for
   a key ([R4](../../../conventions/provable-subset.md#r4-closures-as-callbacks)).
8. **Bit tests by hand.** An alignment is a power of two when it is not 0
   and `align & (align - 1)` is 0, and the greater or lesser of two values
   is chosen with `if`, not with a function of the library
   ([R2](../../../conventions/provable-subset.md#r2-iteratorany),
   `arithmetic`).
9. **Error types.** `Error` and `PlanError` keep the names that the
   contract fixes; the functions return `Result` with one of them and
   propagate errors with `?` without a conversion (`error-conversion`).
   Other components name an enumeration `Error` too, so no Lean module
   imports the generated definitions of this target together with those of
   such a target
   ([R6](../../../conventions/provable-subset.md#r6-enumeration-names-across-targets),
   `r6-same-enum-name`).
10. **One shape for every board.** The Pi 5 and QEMU virt differ in the
    values of their profiles, which they give the entries, not in a
    `cfg` ([rule 7](../../../conventions/provable-subset.md#7-no-shape-changing-cfg),
    `cfg-shape`), and the module has no interior mutability
    ([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
11. **Bounded loops.** Every loop is bounded by the
    [work bounds](contract.md#work-bounds) of its entry, including the
    climb of `Node::translate_reg` over at most `MAX_DEPTH` buses, which is
    a loop with a count rather than a recursion
    ([rule 4](../../../conventions/provable-subset.md#4-bounded-work-per-entry)).
12. **Profiles.** `HandOverProfile`, `CpuProfile` and `TimerInterrupts`
    are structures with public fields, `Copy`, passed by value; every
    value of their fields has the behaviour that the contract gives it, so
    no entry checks a profile before it uses it. `HandOverProfile` holds
    its `compatible` entries as one byte slice, separated by NUL bytes, not
    as a slice of slices, and its alignment as the exponent `alignment_log2`;
    a `BootMemory` keeps the limit and that exponent in private fields, not
    the slice. `CpuProfile` holds no borrow, since a `CpuTopology` holds it
    and the topology is published in the boot state: its affinity level is
    the enumeration `AffinityLevel`, its CPU counts the bits of a `u8`, and
    its timer interrupts an `Option` of a `TimerInterrupts`, an array of
    five `u32` and a `u8` count. A function that reads an enumeration of a
    profile takes it by value, never through an array index
    ([constructs the tools do not support](../../../conventions/provable-subset.md#constructs-the-tools-do-not-support)).

The qualification cases cover these shapes. A shape of the implementation
that no case records gets a case of its own before the target is
registered as formal.

## Not proved

- **The values of the profiles.** The specification and its statements
  hold for every hand-over profile and every CPU profile. Whether the
  profile that a board gives holds the values of its hardware, such as the
  128 KiB and the root `compatible` of the Pi 5 or its affinity level and
  CPU count, is in no theorem: the profile is an input that the board gives,
  which its tests and the hardware-in-the-loop bench check.
- **The publication of the boot results.** The transactions of
  `Krepi.Spec.Fdt.Boot`, which publish the boot memory map and the CPU
  topology once each before the secondary CPUs start, are proved on the
  specification by the statements of [invariants](specification.md#invariants),
  but no theorem of the target covers the code that runs them, which lies
  in the boot code of the boards. No registered theorem states either that
  each transaction changes only its own field: that follows from its
  definition.
- **Steps.** The [work bounds](contract.md#work-bounds) bound the steps of
  each entry; the refinement theorems show that each function returns, and
  no theorem states the number of its steps or its time.
- **The bytes of `/chosen`.** `UnreadValuesIgnored` states that the values
  of `/chosen` other than its `device_type` and, when that is `memory`, its
  `status`, and those of a dynamic reservation other than its `status` and
  flags, leave the results unchanged, for trees of records; no theorem
  states it for the bytes of two trees, whose offsets differ with the
  lengths of those values.
- **The pages of the hand-over bytes.** The premise that the bytes of the
  hand-over tree do not change while the kernel runs rests on the published
  boot memory map, which keeps their pages as boot storage
  ([state fields](contract.md#state-fields)). The boot state holds those
  bytes but not their address, so no registered theorem relates the
  published map to their pages. The board's boot code, which gives the span
  of the tree to the boot memory map as boot storage, carries it, and a
  proof that composes that boot code with this target is to state it.
- **The trees of the node witnesses.** The witnesses of the node entries
  read trees of records that pass the check of `Fdt.WellFormed`; no theorem
  states that each is the parse of some bytes.
