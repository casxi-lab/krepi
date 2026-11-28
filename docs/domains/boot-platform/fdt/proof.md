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
states. The target is registered in `verification/targets.json` as a formal
target, with its roots, the functions that it proves and reaches, its
obligations, its proof modules and its mutants in two parts
([proof targets](../../../formal-verification.md#proof-targets)), and the
gate verifies it.

The statements of the specification itself, its invariants, its
properties, its specification tests and the statements that its
unreachable error branches are never taken, are registered in
[`verification/statements.json`](../../../../verification/statements.json)
and proved below
[`verification/Krepi/Proofs/Fdt/`](../../../../verification/Krepi/Proofs/Fdt/)
([statements and proofs](../../../formal-verification.md#statements-and-proofs)).
They are not obligations of the target: the refinement theorems of the
target take the invariants that they establish as hypotheses
([premises](#premises)).

## Targets

### fdt

| Field | Value |
| --- | --- |
| Name | `fdt`, formal |
| Module | `Fdt`, the namespace of the generated definitions |
| Feature | `krepi.platform.device-tree`, the [device tree](../../../features/platform/device-tree.md), whose `theorems` are the refinement theorems of the roots |
| Entries | The 11 rows of the [entry table](contract.md#entry-points), lines 109 to 119 of the contract: one target, not split |
| Roots | 64: the 60 functions that the rows name, below, and the `next` of the four iterator types ([iterators](#fdt)) |
| Budget | Two parts, each with a budget of its own ([cluster and budget](#cluster-and-budget)) |

The roots are the full paths of the functions that the rows of the entry
table name, in the crate `krepi_kernel` of the root package and its module
`fdt` ([extractability](contract.md#extractability)). A short name in a row
is a function of the nearest type named before it in the same row, so
`ram` of line 111 is `MemoryMap::ram` and `ram` of line 112 is
`BootMemory::ram`. `cells_u64`, which no type precedes, is a function of
the module, as the contract calls it, `cells_u64(bytes, cells)`. The value
types of line 118 and the constants of line 119 are not roots: the
extraction reaches them through the functions that use them. Neither are
the other public types of the module, which line 118 does not list: the
iterator types `Nodes`, `Reservations` and `AvailableRanges`, `Reg` and
`AddressMap`, which lines 110 and 115 name through their functions, and
`MappingKind`, which `AddressMap::kind` returns.

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
and `MemoryPlan::available_ranges` give iterators of the types `Nodes`,
`Reservations`, `Reg` and `AvailableRanges`, which the contract names in
its [open obligations](contract.md#open-obligations). A root that only
returns an iterator does not reach its `next`, and no function of the
module walks the usable ranges, so the `next` of each type is a root of its
own. Its refinement theorem follows from the representation of an iterator
by its list alone, `Stands` of `Krepi.Statements.Basic`
([premises](#premises)): the theorem of the function that gives the
iterator relates the calls of `next` from every state that the iterator
reaches to the list of the specification, and so covers the code of
`next`. A source mutant that survives in the code of a `next` is therefore
classified by the theorems of the functions that give its iterator.

**Obligations.** One for each root: its refinement theorem states that, for
every input of its machine widths ([widths and
quantifiers](specification.md#widths-and-quantifiers)) and under the
premises below that its inputs need, the function returns the value that
its specification gives, related to it by the representation of the value
types, or fails with the error that its specification gives, and that a
failure returns nothing else. A function with a loop is proved to return as
well, since Aeneas translates a loop as a function that may diverge. The
refinement theorems lie below `Krepi.Proofs.Fdt.Refinement`, in five
modules that restate the triples of the generated functions that the other
modules prove, each a `@[step]` lemma about one function, so that the build
of a mutant fails in the triple of the function that it edits, and the
modules that import a module that fails are not built. Each obligation
holds the refinement theorem of its root and the theorems that its proof
uses and that unfold a generated definition, the triples and the lemmas
about generated constants such as `max_name_val`, each in the first
obligation in the order of the roots whose proof uses it; the 18 modules
that hold them are the proof modules of the target.

### Premises

The refinement theorems take these hypotheses. Each is an invariant of the
specification ([invariants](specification.md#invariants)), a condition of
the boot, a representation of a value or of an external declaration, or the
platform of the extraction, with the function or the code that establishes
it, what preserves it and what relies on it. The translation of the module
does not show which module may build a value, so the [compile-time
guards](#compile-time-guards) make each premise of a value true of every
value that another module holds.

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
| An iterator of the module stands for a list of the specification (`Stands`): its calls of `next` give the items of that list in order, and then none, at every later call too, the iterator staying where it is (the fixed point, which `fixed_iff` of the refinement modules states as a triple). The nodes are those of `Fdt.nodes`, the reservation entries those of `Fdt.reservations`, the entries of a `Reg` those of `Reg.entries`, and the usable ranges those of `MemoryPlan.availableRanges` | The functions that give the iterators, `Fdt::nodes`, `Fdt::reservations`, `Reg::new` and `Node::reg`, and `MemoryPlan::available_ranges`, whose refinement theorems relate the iterator that each gives to its list | Each `next`, which advances only the iterator's own cursor over checked bytes or values and does not fail ([check and execute](contract.md#check-and-execute)), and gives the head of the rest of the list | The functions that walk an iterator, such as `Fdt::find_node` and the discoveries over the nodes and `Fdt::discover_memory` over the entries of a `Reg`; the callers of `available_ranges`, the kernel direct map and the page ownership table of the page-tables component, to which `UsableRangesExact` and `AvailableRangesWellFormed` carry over |
| A `&str` argument stands for the name or path of the specification (`StrRepr`): `as_bytes`, which the translation keeps as a declaration without a body ([trusted boundary](#trusted-boundary)), returns the bytes of the UTF-8 encoding of that string. The generated `Str` is `Slice U8` | Rust: a `&str` holds UTF-8, and `as_bytes` returns its bytes | Nothing changes a `&str` | `Node::property`, `Node::string_property` and `Fdt::find_node`, the three functions that read a name or a path through `as_bytes`; their theorems hold for every interpretation of the declaration that meets the premise |
| A `usize` has 64 bits (`Usize64`, `System.Platform.numBits = 64`), the first premise of every refinement theorem | The extraction triple, `aarch64-unknown-none`, and the 64-bit platforms that the contract describes | - | Every refinement theorem: it does not restrict the inputs, it names the platform of the contract and of the extraction |
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
   the premise of its type. One case stands for the guard of every type:
   `kernel/compile-fail/fdt-private-fields.toml` writes a struct literal of
   `Fdt` in another module and expects `E0451`. `Span`, `ReservedRegion`,
   `HandOverProfile`, `CpuProfile` and `TimerInterrupts` carry no invariant
   and have public fields: their specification holds for every value.
2. **Borrowed bytes.** A tree borrows the slice of its bytes for its
   lifetime, and its nodes and iterators borrow the tree, so no write to
   the bytes compiles while any of them lives. The case
   `kernel/compile-fail/fdt-borrowed-bytes.toml` writes a byte of a slice
   while a tree of it lives and expects `E0506`.
3. **No duplication guard.** No value of the component carries a right
   that a copy would break: every value is immutable once built, so its
   types may implement `Clone` and `Copy`, and none has a guard against
   them.

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

Budget and parts: the gate runs the 29 registered mutants of the target in
two parts, each a job with its own budget
([shards and merge](../../../formal-verification.md#shards-and-merge)). The
registry puts the mutants of the [mutant table](#mutants) into the parts in
turn, the first into part 1, the second into part 2 and so on, so that the
parts take 15 and 14. Each part extracts the target, builds its proofs
and then runs its mutants; part 1 also concludes the target. The budget of
each part is 1.5 times the seconds that the part took on the standard
runner, rounded up to a minute, at most 1,800 s and at least 1.25 times
those seconds, and the parts of a target have at most 7,200 s in all. The
number of parts is the least for which no part takes more than 1,440 s.
Each mutant extracts the target again and builds the generated definitions
and the proof modules that the edit reaches. On the standard runner each
of four parts took 581 s to 689 s, about 170 s to extract and build the
target and up to 69 s for each of its mutants, so two parts of 15 and 14
mutants come to about 1,210 s each and one part of 29 would pass 1,440 s;
the measurement of the two parts on the standard runner decides their
budgets.

## Trusted boundary

The target relies on these rows of the [trusted
boundary](../../../formal-verification.md#trusted-boundary): the Lean
kernel and the three standard axioms; Mathlib and the Aeneas Lean library;
Charon, the Rust nightly and Aeneas; the compiler, which no proof covers;
and the unconstrained declarations, one item ([below](#trusted-boundary)).
It relies on no assembly, `unsafe` code, atomics, IRQ path or hardware: the
module has none. The bytes that the firmware hands over are its input,
which it checks; the board's forming of their slice is an open obligation,
not a trusted item ([unclosed dependencies](#unclosed-dependencies)).

The target adds one item to the boundary, an unconstrained declaration
with its premise, and no cut point, model or trusted axiom:

- **Cut points.** None: no function of the module reads hardware or global
  state, so none needs to be translated without its body.
- **Models and trusted axioms.** None: no item of `models.json` or
  `tcb.json`, and no `trusted_axioms`. The witnesses of the specification
  use `decide +kernel`, which the kernel checks, and the proofs use no
  native decision and no axiom of the Aeneas library that `tcb.json` would
  have to admit.
- **Derived methods.** The extraction translates the `clone` that
  `#[derive(Clone)]` defines for `ReservedRegion`, `Span` and
  `parser::Frame`, which no function of the module calls; the target lists
  them in `derived`, and they stay unverified. The module calls no method
  that a `#[derive(..)]` defines, such as a derived `eq` of spans: it
  compares values field by field.
- **Unconstrained items.** One, `core::str::{str}::as_bytes`, which
  `Node::property`, `Node::string_property` and `Fdt::find_node` call on
  the name or path that they take. The translation keeps it as a
  declaration without a body and without a model, which is refused while
  models are not compared with their implementations
  ([models](../../../formal-verification.md#models)); a theorem must hold
  for every interpretation of such a declaration
  ([R2](../../../conventions/provable-subset.md#r2-iteratorany)), so the
  theorems of the three functions take the premise `StrRepr`
  ([premises](#premises)) and hold for every interpretation that meets it.
  No other library item is reached while the module keeps the
  [code shapes](#code-shapes); each item below would otherwise be reached
  as an external declaration without a model, and no result that depends
  on it could be proved.

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
of the hand-over tree by each board. Its `unclosed` is empty: it proves
every function of the module that it reaches, it cuts no function, and it
reaches no function of another component.

## Mutants

The target registers 29 source mutants, 1 to 3 for each row of the entry
table, among them off-by-one changes of three limits of the parse,
`MAX_DEPTH`, `MAX_PROPERTY_NAME` and `MAX_BLOB_SIZE`, and of three other
limits. Each is registered with its file, the text that it finds
and replaces, the part that runs it ([cluster and budget](#cluster-and-budget))
and the theorems of which one must fail: the refinement theorem of the
function that it names and the theorems of that proof that unfold the
function or constant that the edit changes, where the build of the mutant
fails ([obligations](#fdt)). The table describes the edit.
`parse-depth-off-by-one` and `memory-ranges-off-by-one` pass their check
and then fail at the write beyond the array of the open nodes or of the RAM
ranges, a panic in Rust and a failed `update` in the generated code,
rather than admitting the node or the range.

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
   the module walks them by calling `next` in a `while` loop
   (`own-iterator-next`, `iterator-driven-loop`), and a view of the tree
   that a function takes by value borrows it (`borrowed-view-by-value`).
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
12. **Profiles.** `HandOverProfile`, `CpuProfile` and `TimerInterrupts` are
    structures with public fields, `Copy`, passed by value; every value of
    their fields has the behaviour that the contract gives it, so no entry
    checks a profile before it uses it. Each field has the width of the
    specification ([widths](specification.md#widths-and-quantifiers)).
    `HandOverProfile` holds its limit `max_blob_size` as a `u64`, its
    alignment as the exponent `alignment_log2`, a `u8`, and its `compatible`
    entries as one `&[u8]`, separated by NUL bytes, not as a slice of
    slices; a `BootMemory` keeps the limit and that exponent in private
    fields of the same types, a `u64` and a `u8`, not the slice. The check
    of the alignment does not compute `1 << alignment_log2` in 64 bits,
    which overflows from an exponent of 64: it takes an exponent of 64 or
    more apart, for which only the address 0 is aligned, and tests the other
    exponents with a mask, as in shape 8. `CpuProfile` holds no borrow,
    since a `CpuTopology` holds it and the topology is published in the boot
    state: its affinity level is the enumeration `AffinityLevel`, its CPU
    counts the bits of a `u8`, and its timer interrupts an `Option` of a
    `TimerInterrupts`, an array of five `u32` and a `u8` count. A function
    that reads an enumeration of a profile takes it by value, never through
    an array index
    ([constructs the tools do not support](../../../conventions/provable-subset.md#constructs-the-tools-do-not-support)).

The qualification cases cover these shapes, and four cases record shapes
of the module that the list above does not name: `slice-is-empty`, the
`is_empty` of a slice; `fallible-constant`, the limits that `fdt.rs`
converts with `as`, which the tools make computations that the functions
bind; `negation-return`, a negated Boolean returned, as `path_valid` and
`MemoryPlan::is_available` return one; and `option-array-by-value`, the
timer interrupts of a profile, an `Option` of a `Copy` structure that
`CpuTopology::validate_timers` takes apart before it passes their array to
a helper with a loop. A shape of the implementation that no case records
gets a case of its own before the code that has it merges.

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
