---
targets:
  - page-tables
planned: []
---

# Page-tables proof path

The proof path of the `page-tables` component: the target that is to refine
the [specification](specification.md) of the [contract](contract.md), the
premises of its theorems with the guards that keep them, the code shapes
that the implementation adopts so that the tools translate it into code a
proof can rely on, its trusted boundary, its mutants and what no theorem
states. The target is registered in `verification/targets.json` as a formal
target, with its roots, the functions that it proves and reaches, its
obligations, its proof modules and its mutants in four parts
([proof targets](../../../formal-verification.md#proof-targets)), and the
gate verifies it.

The statements of the specification itself, its invariants, its properties,
its specification tests and the statements that its unreachable error
branches are never taken, are registered in
[`verification/statements.json`](../../../../verification/statements.json)
and proved below
[`verification/Krepi/Proofs/PageTables/`](../../../../verification/Krepi/Proofs/PageTables/)
([statements and proofs](../../../formal-verification.md#statements-and-proofs)).
They are not obligations of the target: the refinement theorems of the
target take the invariants that they need as hypotheses
([premises](#premises)).

## Targets

### page-tables

| Field | Value |
| --- | --- |
| Name | `page-tables`, formal |
| Module | `PageTables`, the namespace of the generated definitions |
| Feature | `krepi.kernel.kernel-memory`, the [kernel memory](../../../features/kernel/kernel-memory.md), whose `theorems` are the refinement theorems of the roots |
| Entries | The 11 rows of the [entry table](contract.md#entry-points) of the core, lines 107 to 117 of the contract: one target, not split; the row of the adapter, line 118, is excluded ([unclosed dependencies](#unclosed-dependencies)) |
| Roots | 31: the 28 functions that the rows name, below, and the `next` of the three plan iterator types ([plans as iterators](#page-tables)) |
| Budget | Four parts, each with a budget of its own ([cluster and budget](#cluster-and-budget)) |

The roots are the full paths of the functions that the rows of the entry
table name, in the crate `krepi_kernel` of the root package and its module
`page_tables` ([extractability](contract.md#extractability)). A short name
in a row is a function of the nearest type named before it in the same row,
so `end`, `contains` and `overlaps` of line 107 are functions of
`PhysRange`, and `lookup_block` and `used` of `Tables`; `descriptor`,
`direct_address`, `kernel_map` and `direct_map`, which the rows qualify by
the module, are functions of the module. Every name of the rows expands so.
The value type `Kind` of line 107 is not a root, nor are the other value
types, such as `WritePlan` with its steps, and the constants, such as
`DIRECT_BASE`, `DIRECT_MAP_TABLES`, `KERNEL_TABLES`, `EXTENTS` and
`EXCLUSION_RECORDS`: the extraction reaches them through the functions that
use them.

| Line | Functions | Roots |
| ---: | ---: | --- |
| 107 | 9 | `krepi_kernel::page_tables::descriptor`, `krepi_kernel::page_tables::direct_address`, `krepi_kernel::page_tables::PhysRange::new`, `krepi_kernel::page_tables::PhysRange::end`, `krepi_kernel::page_tables::PhysRange::contains`, `krepi_kernel::page_tables::PhysRange::overlaps`, `krepi_kernel::page_tables::Tables::lookup_page`, `krepi_kernel::page_tables::Tables::lookup_block`, `krepi_kernel::page_tables::Tables::used` |
| 108 | 3 | `krepi_kernel::page_tables::Tables::new`, `krepi_kernel::page_tables::Tables::reset`, `krepi_kernel::page_tables::Tables::clone_kernel_from` |
| 109 | 1 | `krepi_kernel::page_tables::Tables::map_page` |
| 110 | 1 | `krepi_kernel::page_tables::Tables::map_block` |
| 111 | 1 | `krepi_kernel::page_tables::Tables::unmap_page` |
| 112 | 2 | `krepi_kernel::page_tables::kernel_map`, `krepi_kernel::page_tables::direct_map` |
| 113 | 1 | `krepi_kernel::page_tables::Ownership::new` |
| 114 | 2 | `krepi_kernel::page_tables::Ownership::choose`, `krepi_kernel::page_tables::Ownership::assign` |
| 115 | 3 | `krepi_kernel::page_tables::Ownership::reserve`, `krepi_kernel::page_tables::Reservation::initialized`, `krepi_kernel::page_tables::Ownership::publish` |
| 116 | 2 | `krepi_kernel::page_tables::Ownership::cancel`, `krepi_kernel::page_tables::Ownership::release` |
| 117 | 3 | `krepi_kernel::page_tables::Ownership::owner`, `krepi_kernel::page_tables::Ownership::validate`, `krepi_kernel::page_tables::Ownership::stats` |

**Plans as iterators.** `kernel_map`, `direct_map` and `clone_kernel_from`
give their steps one at a time, by an iterator of the core over their input
([write plans and publication](contract.md#write-plans-and-publication)),
of the types `KernelMapPlan`, `DirectMapPlan` and `ClonePlan`, which the
contract names in its [open obligations](contract.md#open-obligations). The
adapter calls their `next`, and no other root does, so the `next` of each
type is a root of its own. Its refinement theorem follows from the
representation of a plan by its list of steps alone, `Stands` of
`Krepi.Statements.Basic` ([premises](#premises)): the theorem of the entry
that gives the iterator relates the calls of `next` from every state that
the iterator reaches to the plan of the specification, `mapPlan` or the
plan of the copy, and so covers the code of `next`. A source mutant that
survives in the code of a `next` is therefore classified by the theorems of
the entries that give its iterator. The plans of `map_page`,
`map_block`, `unmap_page` and `reset` are values: the first three have at
most seven steps, and that of `reset` one `Zero` for each table in use.

**Obligations.** One for each root: its refinement theorem states that, for
every input of its machine widths ([widths and
quantifiers](specification.md#widths-and-quantifiers)) and under the
premises below that its inputs need, the function returns the value that
its specification gives, for a write entry the set or the table after its
write phase and the plan or the value that it returns, related to it by the
representation of the value types, or fails with the error that its
specification gives, and that a failure returns nothing else and writes
nothing. A function with a loop is proved to return as well, since Aeneas
translates a loop as a function that may diverge. The refinement theorems
lie below `Krepi.Proofs.PageTables.Refinement`, in three modules that
restate the triples of the generated functions that the other modules
prove, each a `@[step]` lemma about one function, so that the build of a
mutant fails in the triple of the function that it edits, and the modules
that import a module that fails are not built. Each obligation holds the
refinement theorem of its root and the theorems that its proof uses and
that unfold a generated definition, the triples and the lemmas about
generated constants, each in the first obligation in the order of the
roots whose proof uses it; the 15 modules that hold them are the proof
modules of the target.

### Premises

The refinement theorems take these hypotheses where a function needs them,
and the properties of the specification take the invariants among them.
Each is an invariant of the specification
([invariants](specification.md#invariants)), a rule that the boot wiring or
a caller keeps, or a representation of a value of the code, with the
function or the code that establishes it, what preserves it and what relies
on it. The translation of the module does not show which module may build
a value, so the [compile-time guards](#compile-time-guards) make each
premise of a value true of every value that another module holds.

| Premise | Established by | Preserved by | Consumed by |
| --- | --- | --- | --- |
| A set keeps `Tables.WellFormed` at the `base` and `bits` of its pool | `Tables::new` on zero storage (`NewWellFormed`); `reset` and `clone_kernel_from`, whose plans zero every table in use (`ResetWellFormed`, `CloneKernelFromWellFormed`); `kernel_map` and `direct_map` on the new kernel sets (`BootKernelMapWellFormed`, `BootDirectMapWellFormed`) | `map_page`, `map_block`, `unmap_page`, `kernel_map` and `direct_map`, once the plan has run (`MapPageWellFormed`, `MapBlockWellFormed`, `UnmapPageWellFormed`, `KernelMapWellFormed`, `DirectMapWellFormed`) | The walk of every entry, which meets no bad table descriptor on such a set; the properties `AfterEveryWrite`, `TablesInUseCounted`, `PlansPublishInOrder` and `KernelTablesOnlyFilled`; the source of `clone_kernel_from`, whose checks are these rules |
| The storage that `Tables::new` takes is zero in all its tables | The boot wiring for the kernel tables, whose pools are storage of the image that is zero when it is loaded; for the tables of a process, the page ownership table, whose pages are zero before they reach a holder (`AfterEveryWrite`, the rows of `assign` and `publish`) | No plan writes a table that is not in use, and the plans of `reset` and `clone_kernel_from` zero every table in use before it leaves use ([table pool](contract.md#table-pool)) | `Tables::new`, which checks nothing ([check and execute](contract.md#check-and-execute)); `NewWellFormed` |
| The plan of each write entry on a set runs in full and in order before the next entry on the set, and only the plans change the pool of a set | `krepi_arch::mmu::apply`, which executes each step of a plan that the check of its entry fixed and does not fail, an [open obligation](contract.md#open-obligations); the caller, which holds the token of the set from the entry to the last step of its plan | The token of the set; the borrow of its inputs by a plan iterator (guard 3) | Every entry, whose walk reads the pool that `Tables.apply` of the earlier plans gives; the well-formedness lemmas and `AfterEveryWrite`, which state the set once its plan has run |
| A plan iterator stands for a list of steps of the specification (`Stands`): its calls of `next` give the steps of `mapPlan`, for `kernel_map` and `direct_map`, or of the plan of `Tables.cloneKernelFrom`, in order, and then none, at every later call too, the iterator staying where it is (the fixed point, which `fixed_iff` of the refinement modules states as a triple) | `kernel_map`, `direct_map` and `clone_kernel_from`, whose refinement theorems relate the iterator that each gives to its list | Each `next`, which advances a private cursor over the checked input and does not fail ([check and execute](contract.md#check-and-execute)) | `krepi_arch::mmu::apply`, which executes the steps; `PlansPublishInOrder` and `KernelTablesOnlyFilled`, which carry over to the steps |
| A layout of `kernel_map` has at most 16 ranges, each with one of the four kinds of a layout | The board crate, which writes the layout of its image; the type of a layout (code shape 6) | A layout is a constant of the board | `kernel_map`, which checks neither rule ([kernel mappings](contract.md#kernel-mappings)); `Layout`, `layoutKinds` |
| The boot memory map of `direct_map` is one that the fdt entries built, so it keeps `MemoryPlan.WellFormed` and its usable ranges are on page boundaries, disjoint and in address order (`BuiltPlan`) | `MemoryPlan::all_ram`, `new` and `from_boot_memory` of the [fdt](../../boot-platform/fdt/proof.md) target (`AllRamWellFormed`, `MemoryPlanNewWellFormed`, `FromBootMemoryWellFormed`, `UsableRangesExact`) | The publication of the boot memory map, which keeps it unchanged | `direct_map`, whose checks of a usable range off pages and of a leaf that an earlier usable range shares never fail (`DirectMapRangesOnPages`, `DirectMapRangesApart`); `BootOwnersMatchDirectMap` |
| W^X, the first rule of the boot wiring: `kernel_map` and `direct_map` run at most once each, before the MMU is on | The boot wiring, which calls each once on the boot CPU ([entry points](contract.md#entry-points)); the transactions `Shared.buildKernelMap` and `Shared.buildDirectMap`, which run only before `Shared.enable` | No transaction writes the direct map's set once the MMU is on (`DirectMapUnchangedAfterBoot`) | `NoWritableExecutable`, through `WxPremises` |
| W^X, the second rule: the boot memory map is well-formed and each `ReadExecute` range of the layout lies in the span of boot storage of the kernel image | The board, which gives the boot memory map the span of the image as boot storage and builds the layout from the symbols of its link ([descriptors and attributes](contract.md#descriptors-and-attributes)) | The boot memory map never changes once published | `NoWritableExecutable`, by which the text has no alias in the direct map; `Ownership::new` of the kernel root, which excludes the image |
| W^X, the third rule: a plan that fills an invalid entry of the lower kernel set after boot maps an executable kind only at a page of the text of the image, and a page of the text only with `ReadExecute` | The code of the core that fills such an entry under the token of the kernel tables, which the third rule of [W^X](contract.md#descriptors-and-attributes) binds; the [address-space contract](../address-space/contract.md#address-spaces-and-asids) writes no fill after boot | Each fill, which writes only invalid entries (`KernelTablesOnlyFilled`) | `NoWritableExecutable`, through `WxPremises` |
| A fill of the lower kernel set after boot keeps off the guard pages | The code that fills, as the [guard](contract.md#descriptors-and-attributes) rule states, since `map_page` does not know the guards | `kernel_map` writes no entry of a guard page (`AfterEveryWrite`, the row of `kernel_map`) | The translation fault of an access to a guard, which the QEMU tests show; no registered theorem ([not proved](#not-proved)) |
| A `usize` has 64 bits (`Usize64`, `System.Platform.numBits = 64`), the first premise of every refinement theorem | The extraction triple, `aarch64-unknown-none`, and the 64-bit platforms that the contract describes | - | Every refinement theorem: it does not restrict the inputs, it names the platform of the contract and of the extraction |
| A page ownership table keeps `Ownership.Invariant`: `Ownership.WellFormed`, `Ownership.OneOwner`, `Ownership.HolderRanges`, `Ownership.GenerationsBelowCounter` and `Ownership.FreeExtentsMaximal` | `Ownership::new` (`NewOwnershipWellFormed`, `NewOneOwner`, `NewHolderRanges`, `NewGenerationsBelowCounter`, `NewFreeExtentsMaximal`) | `assign` of a choice of `choose`, `reserve`, `publish`, `cancel` and `release` (the preservation statements and `AssignWellFormed` to `ReleaseWellFormed`) | `choose`, whose scan in address order gives the first fit (`PlacementFirstFit`); `owner` and `stats`; the checks of a receipt, a packet or a reservation, which find one extent; `TakeAcceptsChoice` |
| The table of the kernel root keeps `Ownership.FreeOrHeldUsable` of its boot memory map: its free and held pages are the pages of the usable ranges | `Ownership::new` on the managed banks of a well-formed boot memory map and one exclusion for each span of its boot storage and each firmware reservation, which the boot wiring gives it (`NewFreeOrHeldUsable`) | The same five write entries | The zeroing of a chosen range through the direct map, which maps its pages; `BootOwnersMatchDirectMap`; the second rule of W^X |
| The choice that `assign` takes is one of `choose` on the same table, taken under the same token (`Ownership.Chose`), the requirement of its row | The private fields of the choice, which only `choose` builds ([guard 1](#compile-time-guards)); the caller, which runs `choose`, its zeroing and `assign` as one transaction under the token of the page ownership table (`Shared.allocate`) | The token: no other entry runs on the table between `choose` and `assign` | The row of `assign` in `AfterEveryWrite` and its preservation statements, which take it as a hypothesis. The checks of [check and execute](contract.md#check-and-execute) refuse only the three cases that the contract lists, an exhausted counter, a range not inside one free extent and the extents beyond the capacity (`assignRechecks`), which a choice of `choose` passes (`TakeAcceptsChoice`); a choice off page boundaries or of a length that is not whole pages passes them and breaks `Ownership.WellFormed`, so only guard 1 keeps such a choice from `assign` |
| The outcome that `assign` and `Reservation::initialized` take is true exactly when the zeroing of the range completed | The caller, which zeroes the range through the direct map with `krepi_arch::mmu::zero_frames`, an [open obligation](contract.md#open-obligations) | - | The rule that a page reaches a holder only once its bytes are zero ([page ownership](contract.md#page-ownership)); no registered theorem ([not proved](#not-proved)) |
| A `PhysRange` keeps its invariant: its length is not 0 and its end fits in 64 bits | `PhysRange::new` | No entry changes a range | `end`, `contains`, `overlaps`, `direct_address` and the entries of the page ownership table, which take their banks, exclusions, windows and receipts as ranges |
| Each shared field is written under its token, held by one CPU at a time from the first check of an entry to the end of its plan; with one CPU, the executing CPU holds it | The caller ([state fields](contract.md#state-fields)) | - | Every write entry, whose refinement is sequential; the transactions of `Krepi.Spec.PageTables.Tokens` |

The representation of a page ownership table reads only the extents and
the exclusion records below their counts; the slots above them are not part
of the abstract table, so the modification set of an entry, stated on the
abstract table, is exact although an entry may leave old values in those
slots.

The premises of the table sets and those of the page ownership table are
not connected: no premise of one group names a value of the other. The
properties that relate them, `BootOwnersMatchDirectMap` and the second rule
of W^X, are statements of the specification, not premises of the target.

### Compile-time guards

Premises that the translation does not show are fixed when the code
compiles ([rule 6](../../../conventions/provable-subset.md#6-compile-time-guards)),
each with a compile-fail case that the `subset` step runs
([mechanical checks](../../../conventions/provable-subset.md#mechanical-checks)):

1. **Private fields.** `Tables`, `Ownership`, `PhysRange`, `Reservation`,
   `Initialized`, the choice that `choose` returns (`Choice` in the
   specification) and the plan iterators keep their fields private to the
   module, so that only the functions of the premises build them, and a
   value that another module holds keeps the premise of its type: no other
   module makes a range of length 0, a choice that `choose` did not give, a
   packet whose zeroing did not complete, or a reservation that hides an
   attempted zeroing. A choice is built only by `choose`. One case stands
   for the guard of every type: `kernel/compile-fail/page-tables-private-fields.toml`
   writes a struct literal of `PhysRange` in another module and expects
   `E0451`. `Allocation` carries no invariant, since `release`, `publish`
   and `validate` check every receipt ([page ownership](contract.md#page-ownership)),
   and `Kind` and the steps of a plan are enumerations whose every value
   the specification describes.
2. **No duplication.** `Tables`, `Ownership`, `Reservation` and
   `Initialized` implement neither `Clone` nor `Copy`, by the assertion of
   rule 6: a copy of a set would keep a record of tables in use that its
   pool no longer has, a copy of the page ownership table would give the
   same pages twice, a copy of a reservation kept across a failed zeroing
   could be cancelled as if no zeroing had been attempted, and a packet is
   published once. One case stands for the guard of every type:
   `kernel/compile-fail/page-tables-no-clone.toml` derives `Clone` for
   `Tables` and expects `E0283`. A receipt is bookkeeping, not authority
   ([terms](contract.md#terms)), and may be copied.
3. **Borrowed inputs.** A plan iterator borrows the set that its entry
   wrote, the guard addresses of a layout, which `kernel_map` takes by
   value with that borrow, the boot memory map of `direct_map` and the
   source of a copy, for its lifetime, so no other entry on the set and no
   write to the source compiles while the plan lives. The case
   `kernel/compile-fail/page-tables-borrowed-source.toml` calls `map_page`
   on the source of a copy while the plan of the copy lives and expects
   `E0502`.
4. **Region and capacity in the type.** The region and the capacity of a
   set are parameters of its type, as in the specification: `kernel_map`
   takes a set of the lower region and `direct_map` one of the upper
   region, and `clone_kernel_from` a source of the region and the capacity
   of its target ([copying the kernel tables](contract.md#copying-the-kernel-tables)),
   which no error of the contract checks. The case
   `kernel/compile-fail/page-tables-region-in-type.toml` passes a set of the
   upper region to `kernel_map` and expects `E0308`.

The `subset` step also checks the module mechanically for `static mut`,
interior mutability and `cfg` outside its allowlist
([rules 7 and 8](../../../conventions/provable-subset.md#8-no-interior-mutability)),
and the contract places the stores, the barriers and the register writes in
the adapter, so the module has no `unsafe` code and no assembly
([extractability](contract.md#extractability)).

### Cluster and budget

The target cuts no function. It reaches eight functions of the
[fdt](../../boot-platform/fdt/proof.md) component, through the usable ranges
of the boot memory map that `direct_map` walks: `MemoryPlan::available_ranges`,
`managed_banks` and `reservations`, the `next` of `AvailableRanges` with
`available_step`, `furthest_holding` and `nearest_start`, and
`span::prefix`. It proves them again, on its own generated types and for
every input under the premises of the fdt proof path, and lists them in its
`proves`, so it depends on no theorem of the fdt target. It relies on the
boot memory map of that component, which it reads as values: `direct_map` relies on the usable
ranges of a map that the fdt entries built (`BuiltPlan`), so this target and the
`fdt` target form a cluster connected by premises, in which the theorems of the
`fdt` target about `MemoryPlan::all_ram`, `new`, `from_boot_memory` and
`available_ranges` are restated over the generated types of this target. The
gate does not check premises yet, so `cargo xtask formal check` refuses them
([proof targets](../../../formal-verification.md#proof-targets)), and the two
targets are registered without them until it does. A Lean module never imports
the generated definitions of both targets: their enumerations and external
declarations would clash
([R6](../../../conventions/provable-subset.md#r6-enumeration-names-across-targets)).
Within the target, the premises of the table sets and those of the page
ownership table are not connected ([premises](#premises)), so their proofs
can be written apart.

Budget and parts: the gate runs the 29 registered mutants of the target in
four parts, each a job with its own budget
([shards and merge](../../../formal-verification.md#shards-and-merge)). The
registry puts the mutants of the [mutant table](#mutants) into the parts in
turn, the first into part 1, the second into part 2 and so on, so that the
parts take 8, 7, 7 and 7. Each part extracts the target, builds its proofs
and then runs its mutants; part 1 also concludes the target. The budget of
each part is 1.5 times the seconds that the part took on the standard
runner, rounded up to a minute, at most 1,800 s and at least 1.25 times
those seconds, and the parts of a target have at most 7,200 s in all. The
number of parts is the least for which no part takes more than 1,440 s. By
the build of its proof modules in the gate and the ratio of the parts of
the calibration target, a part of 10 mutants would take more than 1,440 s,
so the registry starts from four parts; that is an estimate, and the
measurement of the parts on the standard runner decides their number. The replay of the 9,382 cases of the vector
file, about 270 s on a Darwin host, is a separate run of
`cargo xtask formal vectors`.

## Trusted boundary

The target relies on these rows of the
[trusted boundary](../../../formal-verification.md#trusted-boundary): the
Lean kernel and the three standard axioms; Mathlib and the Aeneas Lean
library; Charon, the Rust nightly and Aeneas; and the compiler, which no
proof covers. It relies on no assembly, `unsafe` code, atomics, IRQ path or
hardware: the module has none. The execution of its plans, the zeroing of
frames and the registers of the MMU are those of the adapter, an open
obligation, not a trusted item ([unclosed dependencies](#unclosed-dependencies)).

The target adds no trusted item to the boundary:

- **Cut points.** None, and no `opaque` entry: no function of the module
  reads hardware or global state, so none needs to be translated without
  its body.
- **Models and trusted axioms.** None: no item of `models.json` or
  `tcb.json`, and no `trusted_axioms`. The witnesses of the specification
  use `decide +kernel` and `rfl`, which the kernel checks, and the proofs
  use no native decision and no axiom of the Aeneas library that
  `tcb.json` would have to admit.
- **Derived methods.** The extraction translates the `clone` that
  `#[derive(Clone)]` defines for `Extent`, `Exclusion`, `PhysRange` and
  `Step`, which no function of the module calls; the target lists them in
  `derived`, and they stay unverified. The module calls no method that a
  `#[derive(..)]` defines, such as a derived `eq` of kinds or ranges: it
  compares kinds with `match` and ranges field by field.
- **Unconstrained items.** None while the module keeps the
  [code shapes](#code-shapes). Each library item below would otherwise be
  reached as an external declaration without a model. A theorem must hold
  for every interpretation of such a declaration
  ([R2](../../../conventions/provable-subset.md#r2-iteratorany)), so no
  result that depends on it could be proved, and a model of it is refused
  while models are not compared with their implementations
  ([models](../../../formal-verification.md#models)).

| Library item | Where the module would reach it | Shape that avoids it |
| --- | --- | --- |
| `u64::is_power_of_two`, `trailing_zeros`, `next_multiple_of`, `core::cmp::max` and `min` | The alignment of a request, the rounding of a start, of an end and of an exclusion to pages, the blocks of the direct map | Code shape 8 |
| `slice::sort` and its relatives | The ranges of a layout, the usable ranges and the banks, sorted by their start | Code shape 7 |
| The provided methods of `Iterator` and the `IntoIterator::into_iter` of a `for` loop | The walk of the tables of a copy, the pages of a layout, the leaves of the direct map, the scan of the extents and the cut of the banks | Code shapes 4 and 5 |
| `Option` and `Result` combinators that take closures | The walk, the free extent of a choice and the checks of a receipt | Code shape 6 |
| `Vec` and the other collections of `alloc` | The extents, the exclusion records, the new tables of a map and the steps of a plan | Code shape 6 |

## Unclosed dependencies

The target leaves open what the contract lists in
[open obligations](contract.md#open-obligations): the adapter
`kernel/arch/src/mmu.rs`, whose `store_descriptor`, `zero_table`,
`synchronize`, `enable` and `zero_frames` store the descriptors, zero the
tables and frames, execute the barriers and the invalidation and turn the
MMU on. The row of the adapter in the entry table, line 118,
`krepi_arch::mmu::apply`, `enable` and `zero_frames`, is excluded from the
target: `enable` and `zero_frames` are `unsafe`, and `apply` stores
descriptors, executes barriers and invalidates the TLB, whose effect belongs
to the boot component. The contract registers the row in its open
obligations, and it counts as a declared unproved entry. Its `unclosed`
is empty: it proves every function that it reaches, the eight of the fdt
component among them ([cluster and budget](#cluster-and-budget)), and it
cuts no function.

## Mutants

The target registers 29 source mutants, 1 to 3 for each row of the entry
table, among them one that maps a writable page executable and three
off-by-one changes, of the capacity of the pool of `direct_map`, of the
capacity of the extents of `Ownership::new` and of the width of the direct
address. Each is registered with its file, the text that it finds and
replaces, the part that runs it ([cluster and budget](#cluster-and-budget))
and the theorems of which one must fail: the refinement theorem of the
function that it names and the theorems of that proof that unfold the
function that the edit changes, where the build of the mutant fails
([obligations](#page-tables)). The table describes the edit. A mutant
that edits a function which other entries call changes their refinement
too. Two edits lie in such a helper, away from the place that the mutant
names: `direct-map-tables-off-by-one` edits the comparison of the free
tables with the new tables in the write phase, which `kernel_map` shares,
and `release-stale-generation` drops the comparison of the generation in
the check of a holder, which `find_held` gives `publish`, `cancel` and
`validate` as well. `unmap-page-of-block` edits `unmap_page` itself, not
the walk of `page_leaf`, where the check of a block is, which `lookup_page`
shares. `new-extents-off-by-one` passes its check and then fails at the
write beyond the array of the extents, a panic in Rust and a failed
`update` in the generated code, rather than admitting the extent.

| Name | Line | Source change | Must fail |
| --- | ---: | --- | --- |
| `read-write-executable` | 107 | The bits of `ReadWrite` leave PXN clear, so a writable page of the kernel is executable at EL1 | Refinement of `page_tables::descriptor` |
| `direct-address-limit-off-by-one` | 107 | `direct_address` gives an address for a range that ends one byte beyond $2^{39}$ | Refinement of `page_tables::direct_address` |
| `lookup-block-rounds-down` | 107 | `lookup_block` rounds an address off 2 MiB down to its block instead of `Alignment` | Refinement of `Tables::lookup_block` |
| `reset-keeps-record` | 108 | `reset` leaves the record of tables in use as it was instead of 1 | Refinement of `Tables::reset` |
| `clone-copies-private-leaf` | 108 | `clone_kernel_from` copies a `KernelPrivateReadWrite` leaf of the source instead of `InvalidDescriptor` | Refinement of `Tables::clone_kernel_from` |
| `clone-reach-unchecked` | 108 | The check that the walk of the source reached every table in use is dropped | Refinement of `Tables::clone_kernel_from` |
| `map-page-overwrites-valid` | 109 | `map_page` replaces a valid level 3 entry instead of `AlreadyMapped` | Refinement of `Tables::map_page` |
| `map-page-store-before-fence` | 109 | The plan stores the table descriptor of a new table before its `Fence` | Refinement of `Tables::map_page` |
| `map-block-over-table` | 110 | `map_block` replaces a level 2 table descriptor by the block instead of `AlreadyMapped` | Refinement of `Tables::map_block` |
| `map-block-output-unaligned` | 110 | `map_block` does not check the physical address at 2 MiB | Refinement of `Tables::map_block` |
| `unmap-without-invalidate` | 111 | The plan of `unmap_page` leaves out `Invalidate` | Refinement of `Tables::unmap_page` |
| `unmap-page-of-block` | 111 | `unmap_page` clears the level 2 entry of a block that holds the page instead of `NotMapped` | Refinement of `Tables::unmap_page` |
| `kernel-map-guard-unchecked` | 112 | `kernel_map` does not refuse a range that covers a guard page | Refinement of `page_tables::kernel_map` |
| `direct-map-tables-off-by-one` | 112 | `direct_map` admits a map that needs one table more than the pool has free | Refinement of `page_tables::direct_map` |
| `direct-map-block-past-range` | 112 | `direct_map` writes a block where less than 2 MiB of the usable range is left | Refinement of `page_tables::direct_map` |
| `new-extents-off-by-one` | 113 | The capacity check of the initialization admits one extent more than the capacity | Refinement of `Ownership::new` |
| `new-exclusion-inward` | 113 | An exclusion is rounded inward to whole pages instead of outward | Refinement of `Ownership::new` |
| `new-overlap-unchecked` | 113 | Two banks that share a page are not refused with `InvalidRange` | Refinement of `Ownership::new` |
| `choose-high-from-lowest` | 114 | A high placement scans the extents from the lowest | Refinement of `Ownership::choose` |
| `choose-alignment-unchecked` | 114 | An alignment that is not a power of two is not refused | Refinement of `Ownership::choose` |
| `assign-keeps-counter` | 114 | `assign` does not advance the generation counter | Refinement of `Ownership::assign` |
| `reserve-published` | 115 | `reserve` holds its pages published instead of reserved | Refinement of `Ownership::reserve` |
| `initialized-ignores-failure` | 115 | `Reservation::initialized` gives a packet after a failed zeroing | Refinement of `Reservation::initialized` |
| `publish-ignores-state` | 115 | `publish` does not check that the extent of the packet is reserved | Refinement of `Ownership::publish` |
| `cancel-after-attempt` | 116 | `cancel` frees a reservation whose zeroing was attempted | Refinement of `Ownership::cancel` |
| `release-without-merge` | 116 | `release` leaves the freed extent apart from the free extents next to it | Refinement of `Ownership::release` |
| `release-stale-generation` | 116 | `release` does not compare the generation of the receipt | Refinement of `Ownership::release` |
| `owner-last-excluder` | 117 | `owner` gives the last owner of the exclusion records that touch a page instead of the first | Refinement of `Ownership::owner` |
| `stats-reserved-as-free` | 117 | `stats` counts the reserved pages as free bytes | Refinement of `Ownership::stats` |

### Specification mutations

Two changes of the specification check that the refinement theorems bind
it, by hand, until a tool makes such changes. Each makes the specification
stronger than the contract, so that the implementation no longer refines
it. Each is expected to make the refinement theorem of its function fail;
when that theorem still holds, the specification is weaker than the
implementation where the change lies, and that is recorded as a finding.

| Change | Expected outcome |
| --- | --- |
| The plan of `Tables.mapPage`, `mapPlan` and the plan of `Tables.mapBlock` put a `Fence` before the `Store` of every table descriptor, also of a new level 3 table under a new level 2 table, one `Fence` for each table descriptor | The refinement theorem of `Tables::map_page` fails on a page that needs a new level 2 and a new level 3 table, whose plan has one `Fence` by the rule of [new tables](contract.md#write-plans-and-publication); so does the specification test `PlansFollowContractOrder` |
| The frame of `Tables.unmapPage` also returns a level 3 table to the pool once its last page is unmapped, lowering the record of tables in use | The refinement theorem of `Tables::unmap_page` fails on the last page of a level 3 table, which the implementation leaves in place, as [table pool](contract.md#table-pool) requires |

## Qualification

The implementation adopts these code shapes, so that the pinned tools
translate every root into code that a proof can rely on. Each cites the
[provable Rust subset](../../../conventions/provable-subset.md) or the
qualification cases that record the outcome of the shape in
`verification/qualification/cases.json`.

### Code shapes

1. **Descriptors by bits.** A descriptor is put together and read with
   shifts, masks and `|` on `u64`, and a kind is turned into its bits by a
   `match` (`arithmetic`, `literal-variant-match`), not by a bitfield type
   or a conversion of the library, so the bits of each row of the kind
   table are visible to the proof.
2. **Checked arithmetic.** An end that the contract compares with $2^{64}$
   uses `checked_add` taken apart with `match` (`checked`): the end of a
   physical range, the end of a pool, the rounded start of a range of a
   request and its end. A comparison with $2^{\mathrm{bits}}$ comes after
   the check of `bits`, so the shift that forms it stays below 64. The count
   of failures of a reservation stays at $2^{64} - 1$ with `saturating_add`
   (`checked`). A `u64` becomes a `usize` by an `as` cast after a comparison
   with the bound (`integer-conversions`).
3. **The generation counter as an enumeration.** The counter is the next
   generation or exhausted, an enumeration taken apart with `match`, and it
   advances with `checked_add` (`checked`, `literal-variant-match`).
4. **One loop per function.** Each function holds at most one loop, and a
   nested loop goes into a helper function: the comparison of a bank with
   the later ones, the cut of a bank by each exclusion, the walk of the
   entries of each table of a copy, the pages of each range of a layout and
   the leaves of each usable range (`nested-loop`, rejected; `split-loop`,
   translated). A check that returns early comes before the call of the
   helper that holds the loop (`return-before-loop`, `flag-before-loop` and
   `loop-in-branch`, rejected; `checks-before-loop` and
   `returns-then-helper`, translated). `unwrap` is not used in a loop
   (`unwrap-in-loop`, rejected).
5. **Index loops and own iterators.** Tables, extents, exclusion records,
   banks and ranges are walked by index loops, not by iterator adapters or
   `for` loops over library iterators (R2, R3, `iterator-adapters`,
   `index-loop`, `generic-into-iterator-loop`). The plan iterators of
   `kernel_map`, `direct_map` and `clone_kernel_from` implement `next`
   alone, which advances a private cursor over the checked input and does
   not fail ([check and execute](contract.md#check-and-execute)).
6. **No closures, no allocation.** `match` takes the place of combinators
   with closures, and no function takes a callback: the zeroing of pages is
   the caller's, between two entries
   ([R4](../../../conventions/provable-subset.md#r4-closures-as-callbacks),
   `option-combinators`, `r4-closure-callback`). The state lives in arrays
   of the capacities of the contract with a count: the pool of $N$ tables, a
   const parameter of the set, the 160 extents, the 132 exclusion records,
   the 16 ranges of a layout and the at most seven steps of the plans of
   `map_page`, `map_block` and `unmap_page`, with no `Vec`
   ([rule 2](../../../conventions/provable-subset.md#2-no-allocation-at-run-time),
   `const-generic`, `vector-operations`). The kind of a range of a layout is
   an enumeration of the four kinds of a layout, so both rules of a layout
   hold of every value of its type.
7. **Sorting by hand.** The ranges of a layout and the banks are sorted by
   their start with an insertion sort whose inner loop is a helper function
   (`split-loop`), not with a sort of the library, which has no model and
   takes a closure for a key
   ([R4](../../../conventions/provable-subset.md#r4-closures-as-callbacks)).
   The usable ranges are not sorted: `direct_map` takes them in the address
   order of a boot memory map that the fdt entries built (`BuiltPlan`).
8. **Bit tests by hand.** An alignment is a power of two when it is not 0
   and `align & (align - 1)` is 0; a start is rounded down with a mask and
   up by adding the alignment less one, checked, before the mask; and the
   greater or lesser of two values is chosen with `if`, not with a function
   of the library
   ([R2](../../../conventions/provable-subset.md#r2-iteratorany),
   `arithmetic`).
9. **Error types.** The errors of table sets and of the page ownership table
   are two enumerations with the names that the contract gives their
   variants and names of their own, unlike the `Error` and `PlanError` of
   the fdt target; the functions return `Result` with one of them and
   propagate errors with `?` without a conversion (`error-conversion`). No
   Lean module imports the generated definitions of this target together
   with those of another target that names an enumeration the same
   ([R6](../../../conventions/provable-subset.md#r6-enumeration-names-across-targets),
   `r6-same-enum-name`).
10. **One shape for every board.** QEMU virt and the Pi 5 differ in the
    values of their layouts and boot memory maps, not in a `cfg`
    ([rule 7](../../../conventions/provable-subset.md#7-no-shape-changing-cfg),
    `cfg-shape`), and the module has no interior mutability
    ([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
11. **Bounded loops.** Every loop is bounded by the
    [work bounds](contract.md#work-bounds) of its entry: the walk reads one
    entry at each level, the copy each entry of each table in use once, the
    maps each range and each leaf once, and the page ownership table each
    extent once and, at each pass of the cursor of `Ownership::new` over a
    bank, every exclusion
    ([rule 4](../../../conventions/provable-subset.md#4-bounded-work-per-entry)).

The qualification cases cover these shapes, and four cases record shapes
of the module that the list above does not name: `slice-is-empty`, the
`is_empty` of the banks that `Ownership::new` takes; `capacity-at-new`, the
pool of a set and the extents of the page ownership table, arrays of a
const length whose storage `new` takes and whose counts only the entries
change; `nested-index-call`, the reads of the pool whose inner index is a
function call, which the tools guard with an assertion of the outer index;
and `fallible-constant`, the bits of a descriptor and the limits made with
shifts, which the tools make computations that the functions bind. A shape
of the implementation that no case records gets a case of its own before
the code that has it merges.

## Not proved

- **The execution of the plans.** The specification states the steps of
  each plan and their order, and `Tables.apply` their effect on the pool;
  what the stores, the barriers and the invalidation do for the walks and
  the TLBs of the CPUs is not modelled, and the adapter that executes them
  is an [open obligation](contract.md#open-obligations). No theorem states
  that a CPU translates an address as the abstract mapping says.
- **The rules of the boot wiring and of the fills.** `NoWritableExecutable`
  holds under `WxPremises`: the first two rules are kept by the boot wiring
  and the board, and the third by the code of the core that fills the lower
  kernel set. No theorem of this target proves them; a proof that composes
  the boot wiring with this target is to state the first two, and the
  refinement of the code that fills, the third. No registered theorem
  states either that a fill keeps off the guard pages.
- **The zeroing.** That a page reaches a holder only once its bytes are
  zero rests on the outcome that the caller gives `assign` and
  `Reservation::initialized`; no theorem states the bytes of a frame, which
  the adapter's `zero_frames` writes.
- **The measured counts of the 8 GB model.** The specification test
  `DirectMapCountsOfPi5Models` states the counts of the five Pi 5 models of
  [table pool](contract.md#table-pool) on the specification; that the 8 GB
  board gives those counts is checked by the board runs
  ([testing obligations](contract.md#testing-obligations)), not by a
  theorem.
- **Steps.** The [work bounds](contract.md#work-bounds) bound the steps of
  each entry; the refinement theorems show that each function returns, and
  no theorem states the number of its steps or its time.
- **Concurrency.** The tokens of the shared fields are held by one CPU at a
  time, and with one CPU by the executing CPU; the transactions of
  `Krepi.Spec.PageTables.Tokens` are sequential, and no theorem states the
  order that the barriers give on several CPUs.
