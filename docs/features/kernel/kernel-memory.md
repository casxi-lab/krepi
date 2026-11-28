---
id: krepi.kernel.kernel-memory
title: Kernel memory
status: implemented
modules:
  - kernel/src/page_tables.rs
  - kernel/src/page_tables/boot.rs
  - kernel/src/page_tables/boot/direct.rs
  - kernel/src/page_tables/boot/layout.rs
  - kernel/src/page_tables/copy.rs
  - kernel/src/page_tables/encoding.rs
  - kernel/src/page_tables/ownership.rs
  - kernel/src/page_tables/ownership/placement.rs
  - kernel/src/page_tables/ownership/receipts.rs
  - kernel/src/page_tables/range.rs
  - kernel/src/page_tables/walk.rs
  - kernel/src/page_tables/write.rs
  - kernel/arch/src/mmu.rs
  - kernel/boards/qemu-virt/src/boot_memory.rs
  - kernel/boards/qemu-virt/src/main.rs
tests:
  - kernel/src/page_tables/tests.rs
  - kernel/src/page_tables/tests/banks.rs
  - kernel/src/page_tables/tests/boot.rs
  - kernel/src/page_tables/tests/capacity.rs
  - kernel/src/page_tables/tests/examples.rs
  - kernel/src/page_tables/tests/kinds.rs
  - kernel/src/page_tables/tests/mapping.rs
  - kernel/src/page_tables/tests/models.rs
  - kernel/src/page_tables/tests/ownership.rs
  - kernel/src/page_tables/tests/paging.rs
  - kernel/src/page_tables/tests/plans.rs
  - kernel/src/page_tables/tests/reservations.rs
  - kernel/src/page_tables/tests/results.rs
  - kernel/arch/src/mmu/tests.rs
  - kernel/boards/qemu-virt/src/boot_memory/tests.rs
suites:
  - qemu-boot
theorems: none
related:
  - krepi.platform.device-tree
  - krepi.platform.qemu-virt-boot
---

# Kernel memory

## Summary

The module `page_tables` of the provable core `krepi-kernel` holds the
memory logic of the kernel at EL1: the descriptors and kinds of the stage 1
translation tables of the EL1&0 regime, with the rule that no frame is
mapped writable and executable; the table sets with their pools and the
entries that look up, map, unmap, reset and copy them; the kernel's lower
mappings of its image and its devices from a layout that the board gives;
the kernel direct map of the usable RAM of the boot memory map; and the
page ownership table, which gives every managed page one owner and hands
pages out against receipts. The module writes no table and touches no
memory: an entry that changes a set checks every rule and returns a write
plan, which the adapter `mmu` of the architecture crate `krepi-arch`
executes, and the caller zeroes pages between two entries, through the
adapter's `zero_frames`. The adapter also turns the MMU on with the kernel
tables. On QEMU virt the boot wiring of the board builds the boot memory
map, the page ownership table of the kernel root and the two kernel table
sets on the boot CPU and turns the MMU on with the caches off, in the
default image and in the test images of its QEMU cases. The feature does
not manage the address spaces of processes, their ASIDs, VM objects or the
authority to map device registers, it never changes the direct map after
boot, and it does not turn the caches on or run on the Raspberry Pi 5, whose
board crate is planned.

## Interface

- **Entries.** The `pub` items of `krepi_kernel::page_tables`, which the
  [entry table of the contract](../../domains/memory/page-tables/contract.md#entry-points)
  lists with their callers:
  - `direct_address(range)`, the address of a physical range in the direct
    map, and `PhysRange::new(start, len)`, `start` and `size`;
  - `Tables::<N, UPPER>::new(pool)`, a `const fn` that takes zero storage
    for a set of `N` tables of the lower region, or of the upper one when
    `UPPER` is true;
  - `kernel_map(set, layout, base, bits)` on a lower set and
    `direct_map(set, memory, base, bits)` on an upper set with the boot
    memory map `fdt::MemoryPlan`, which return the plans `KernelMapPlan` and
    `DirectMapPlan`, or a `TableError`;
  - `Ownership::<E, X>::new(arena, banks, exclusions)`,
    `choose(owner, pages, alignment, placement)`, which gives a `Choice`,
    and `assign(choice, zeroed)`, which gives an `Allocation`, or an
    `OwnershipError`;
  - the value types that they take and give, `Kind`, `LayoutKind`,
    `LayoutRange`, `Layout`, `Step`, `WritePlan`, `Exclusion`, `Excluder`,
    `Placement`, `Direction` and `Allocation`, and the constants `ENTRIES`,
    `DIRECT_BASE`, `MAX_PLAN_STEPS`, `DIRECT_MAP_TABLES`, `KERNEL_TABLES`,
    `MAX_LAYOUT_RANGES`, `EXTENTS` and `EXCLUSION_RECORDS`.
- **Entries of the core.** `descriptor`, `PhysRange::end`, `contains` and
  `overlaps`; `Tables::lookup_page`, `lookup_block`, `used`, `reset`,
  `map_page`, `map_block`, `unmap_page` and `clone_kernel_from`; and
  `Ownership::reserve`, `Reservation::initialized`, `Ownership::publish`,
  `cancel`, `release`, `owner`, `validate` and `stats` are `pub(crate)`,
  for the modules of the core that take pages and fill the tables of
  address spaces, which are planned.
- **Plans.** `map_page`, `map_block`, `unmap_page` and `reset` return a
  `WritePlan`: `Zero(0)` to `Zero(zero_tables - 1)`, then at most seven
  steps. `ClonePlan`, `KernelMapPlan` and `DirectMapPlan`, which
  `clone_kernel_from`, `kernel_map` and `direct_map` return, give their
  steps through an inherent `next(&mut self)`, which never fails. A step is
  `Zero(t)`, `Store(t, i, d)`, `Fence`, `Sync` or `Invalidate(v)`, with a
  table named by its index in the pool.
- **Adapter.** The items of `krepi_arch::mmu`, the row of the adapter in
  the entry table:
  - `apply(pool, plan)`, which executes a whole plan of a set of `N`
    tables on its pool: any value of the trait `Plan<N>`, which
    `KernelMapPlan`, `DirectMapPlan`, `ClonePlan` and `WriteSteps`, the
    steps of a `WritePlan`, implement;
  - `Pool::<N>::new(base)`, an `unsafe` `const fn` that names the pool of
    one set at the address at which the executing CPU reaches it;
  - `enable(lower, direct, bits, caches)`, `unsafe`, which turns the MMU on
    with the roots of the lower kernel set and of the direct map for the
    physical address size `bits`;
  - `zero_frames(range)`, `unsafe`, which zeroes a physical range through
    the direct map, and `physical_width()`, the physical address size of
    the CPU from `ID_AA64MMFR0_EL1`, or none.
- **Boot wiring.** `krepi_qemu_virt::boot_memory::wire(tree)`, `unsafe`,
  which the QEMU virt images call once on the boot CPU with the MMU off and
  which returns `Wired`: the span of the tree, the link symbols, the
  physical address size, the counts of the two plans and the boot memory
  map.
- **Host tests.** `cargo test --locked --manifest-path kernel/Cargo.toml
  -p krepi-kernel` runs the tests of the module, and `-p krepi-arch` and
  `-p krepi-qemu-virt` those of the adapter and of the boot wiring. With
  `KREPI_VECTOR_RESULTS` set to a directory, the results test writes the
  outputs of the frozen vectors to `memory/page-tables.results` below it
  ([host results](../../formal-verification.md#host-results)).

## Semantics

- **Check, then plan.** Every entry checks its arguments and the state in
  the [error order](../../domains/memory/page-tables/contract.md#errors-of-table-sets)
  of the contract, and a refused call returns the first error and changes
  nothing. Otherwise its plan follows from the state and the arguments, and
  the caller executes it in order, holding the token of the set from the
  first check to the last step; no step fails and no entry panics.
- **Descriptors and W^X.** Every leaf has one of nine kinds, with exactly
  the bits of its row and its output address in bits 12 to 47. No kind is
  writable and executable; the kernel kinds give EL0 no access; the user
  kinds are tagged with the ASID and never execute at EL1. The lower kernel
  set maps each page of the image with one kind, and the direct map maps
  only free and held pages, `ReadWrite` and execute-never, so no frame has
  a writable and an executable mapping at once.
- **Table sets.** A set holds the tables of one region, which its type
  names, in a pool of `N` tables with the root at index 0. A new table is
  the free table of the lowest index; a table returns to the pool only
  through `reset` and the copy. No entry replaces a valid entry: a change
  is an unmap and a map, two plans. A block of 2 MiB is always `ReadWrite`,
  and no entry splits a block or turns a table into one.
- **Publication.** A plan writes a new table completely before the one
  store of its table descriptor, after `Fence`; a plan that makes an entry
  valid ends with `Sync`; an unmap stores the invalid entry and then
  invalidates the address; a plan for the kernel tables writes only invalid
  entries.
- **Execution.** `apply` carries out the steps of a plan in order, each
  before it asks for the next: it zeroes a new table and stores a descriptor
  with volatile stores of 8 bytes, executes `DMB ISHST` for `Fence`,
  `DSB ISH` and `ISB` for `Sync`, and invalidates the TLB entries of a page
  in the inner-shareable domain for `Invalidate`. `enable` invalidates the
  TLB entries of the executing CPU, writes `MAIR_EL1`, `TCR_EL1` and the
  TTBRs, and sets `SCTLR_EL1.M` and `WXN`; with the caches off, as on QEMU
  virt, Normal memory is Non-cacheable and `C` and `I` stay clear.
  `enable` and `zero_frames` check nothing and do not fail: a size without
  an encoding in `TCR_EL1` writes no register, and a range outside the
  window of the direct map is not written.
- **Boot.** The boot wiring of QEMU virt gives the boot memory map two
  spans of boot storage, the image and then the tree, builds the page
  ownership table of the kernel root, maps the text `ReadExecute`, the
  read-only data and the pages of the tree `ReadOnly`, the data, BSS and
  stack `ReadWrite` and the registers of the PL011 and the GICv2 `Device`,
  with the guard page below the stack left out, executes the plans of
  `kernel_map` and `direct_map` and turns the MMU on, once, before it
  returns; a failure panics with a static message.
- **Kernel mappings.** `kernel_map` maps every page of the at most 16
  ranges of the layout at its physical address with the kind of its range,
  and writes no entry of a guard page. It refuses a range off page
  boundaries, a page that two ranges share and a range over a guard page.
  The boot wiring calls it once, before the MMU is on.
- **Direct map.** `direct_map` maps every usable range of the boot memory
  map at `DIRECT_BASE | pa`, with a block wherever an aligned 2 MiB lies in
  one range and pages elsewhere, so the firmware reservations, the image,
  the device tree and every other boot storage have no direct address. A
  map that needs more tables than the pool holds, or a range that ends
  above $2^{39}$, fails before its first step. The boot wiring builds it
  once and nothing changes it afterwards.
- **Page ownership.** Every managed page has one owner: free, firmware,
  image, boot storage or one holder, with an owner identity, a generation
  and a state, reserved or published. An exclusion takes every page that
  it touches, and banks never merge. An allocation is `choose`, the
  caller's zeroing through the direct map and `assign`, which gives a new
  generation that is never reused; a failed zeroing leaves the pages free.
  A staged reservation holds its pages at once and gives a receipt only
  when it is published after its zeroing; it may be cancelled only before
  any attempt, and a dropped reservation keeps its pages held. A release,
  a cancel or a publication by another owner, at another arena, twice or
  with a stale receipt is refused and changes nothing.
- **Bounds.** The pool of the direct map holds 80 tables, the lower kernel
  set 32, and the page ownership table of the kernel root 160 extents and
  132 exclusion records over at most 32 banks; a request beyond them fails
  with `OutOfTables` or `MetadataExhausted` before any change. Each entry,
  and each call of the `next` of a plan, ends within the
  [work bounds](../../domains/memory/page-tables/contract.md#work-bounds)
  of the contract and waits for nothing.
- **Undefined.** Nothing: every argument has a result or an error. The
  callers keep the rules that the module cannot check: zero storage for
  `Tables::new` and the tables not in use, the token of a set or of the
  page ownership table, a layout of the four kinds of the kernel, and the
  zeroing before `assign` and before a packet is published. The `unsafe`
  entries of the adapter and of the boot wiring have obligations that their
  callers keep, which their `# Safety` sections state.

## Examples

### ex1: The descriptors of the kernel kinds

At the output address `0x4008_0000`, `descriptor` gives the page descriptor
`0x40_0000_4008_0787` for `ReadExecute`, with AP[2] 1, PXN 0 and UXN 1;
`0x60_0000_4008_0787` for `ReadOnly`; `0x60_0000_4008_0707` for
`ReadWrite`; `0x60_0000_4008_0f07` for `KernelPrivateReadWrite`, whose nG
bit tags it with the ASID; and `0x60_0000_4008_0403` for `Device`, with
AttrIndx 0 and SH `0b00`. Each has AF and the page bits `0b11`, and each
has PXN or AP[2] set, so none is writable and executable. The address
`0xffff_0000_4008_0fff` gives the same `ReadWrite` descriptor, since only
its bits 12 to 47 are taken. A block of `0xffff_ff80_4020_0000` to
`0x4020_0000` in an upper set has the block descriptor
`0x60_0000_4020_0705`, the page descriptor of `ReadWrite` with bit 1
clear.

### ex2: A page is mapped, looked up and unmapped

In a new lower set of 3 tables at `base` `0x1_0000_0000` with width 40,
`map_page` of `0x4008_0000` to itself as `ReadWrite` returns the plan
`Zero(2)`, `Store(2, 128, 0x60_0000_4008_0707)`, `Zero(1)`,
`Store(1, 0, 0x1_0000_2003)`, `Fence`, `Store(0, 1, 0x1_0000_1003)` and
`Sync`: the new level 3 table and then the new level 2 table, each complete
before the store that reaches it. Once the plan is executed, the set has 3
tables in use and `lookup_page` gives the descriptor. `unmap_page` returns
the page `0x4008_0000` and the plan `Store(2, 128, 0)`,
`Invalidate(0x4008_0000)`; after it, `lookup_page` and a second
`unmap_page` fail with `NotMapped`, and the 3 tables stay in use.

### ex3: Text and data on one page are refused

A layout of the text `0x4008_0000+0x2000` as `ReadExecute` and the data
`0x4008_1000+0x1000` as `ReadWrite`, given in the order data, text, would
map the page `0x4008_1000` writable and executable. `kernel_map` takes the
ranges in the order of their starts, finds that page of the text again in
the data and fails with `AlreadyMapped`, without a plan; the set keeps its
root alone in use. This is the rejected input of the feature. With the
data at `0x4008_2000+0x1000`, the same layout maps 3 pages and uses 3
tables: `0x4008_1000` as `ReadExecute`, `0x40_0000_4008_1787`, and
`0x4008_2000` as `ReadWrite`, `0x60_0000_4008_2707`.

### ex4: The direct map of QEMU virt

The boot memory map of the 128 MiB of QEMU virt at `0x4000_0000`, with a
device tree of `0x800` bytes at its start and the image at
`0x4020_0000+0x10_0000` as boot storage, has the usable ranges
`0x4000_1000+0x1f_f000` and `0x4030_0000+0x7d0_0000`, as in
[ex7 of the device tree](../platform/device-tree.md#ex7-seeds-in-the-chosen-node-change-no-result).
`direct_map` into a set of the 80 tables of the pool maps them with 62
blocks and 767 pages, `0x7ef_f000` bytes, in 4 tables: the root, one level
2 table, and a level 3 table for each of the two blocks that the tree and
the image cover in part. The pages of the tree and of the image have no
direct address; `0xffff_ff80_4000_1000` maps the page `0x4000_1000`, and
`0xffff_ff80_4040_0000`, which `direct_address` gives for `0x4040_0000`,
maps the block of `0x4040_0000`.

### ex5: The direct map of the Raspberry Pi 5 of 8 GB

The three banks of the 8 GB model, `0x0+0x3fc0_0000`,
`0x4000_0000+0xc000_0000` and `0x1_0000_0000+0x1_0000_0000`, with the
firmware reservation `atf@0`, `0x0+0x8_0000` and `no-map`, the image
`0x8_0000+0x12_7000` and the device tree `0x20_0000+0x1_3ad4`, give a
direct map of 4,092 blocks and 581 pages, `0x1_ffa4_5000` bytes, in 11 of
the 80 tables of the pool, which leaves 69
([table pool](../../domains/memory/page-tables/contract.md#table-pool)).
The page `0x1a_7000`, the first after the image, is mapped; the last page
of the device tree, `0x21_3000`, has no direct address and the page after
it has one; the hole `0x3fc0_0000+0x40_0000` has no block, and the
last block, `0x1_ffe0_0000`, is mapped.

### ex6: An allocation in one step

A page ownership table of 8 extents in the arena 1, with the bank
`0x4000_0000+0x1_0000` and the firmware reservation `0x4000_0800+0x10`,
which touches the first page, manages 15 pages, and the owner of the first
page is the firmware. A high placement of 2 pages for the owner identity 7
chooses `0x4000_e000+0x2000`; when the caller's zeroing of that range
fails, `assign` fails with `ZeroFailed` and the pages stay free. After a
zeroing that completes, the same range is chosen again and assigned, with
the receipt of the arena 1, the owner identity 7 and the generation 1, and
its pages are held and published. Its release by the owner identity 8
fails with `WrongOwner`; by 7 it succeeds, and a second release of the
same receipt fails with `InvalidAllocation`. The 15 pages are free again.

### ex7: A staged reservation after a failed zeroing

In a page ownership table of 4 extents in the arena 3 with the bank
`0x4000_0000+0x4000`, the owner identity 4 reserves 2 pages and holds
`0x4000_0000+0x2000`, reserved, with the generation 1, before any zeroing.
A failed zeroing returns the reservation, marked as attempted, with 1
failure; its cancel then fails with `ZeroFailed` and returns it, since its
bytes may hold part of a zeroing. After a zeroing that completes, the
packet keeps the count of 1 failure, and its publication gives the receipt
of `0x4000_0000+0x2000` with the generation 1; after its release, the 4
pages are free.

### ex8: The copy of the lower kernel set

A lower set of 8 tables at `0x1_0000_0000`, which `kernel_map` fills with
the console registers `0x900_0000+0x1000` as `Device`, the text
`0x4008_0000+0x1000` as `ReadExecute` and the data `0x4008_1000+0x1000` as
`ReadWrite`, uses 5 tables. `clone_kernel_from` into a new set at
`0x2_0000_0000` gives the plan `Zero(0)`; the stores of the valid entries
of the source in the order of the tables and of their entries,
`Store(0, 0, 0x2_0000_1003)`, `Store(0, 1, 0x2_0000_3003)`,
`Store(1, 72, 0x2_0000_2003)`, `Store(2, 0, 0x60_0000_0900_0403)`,
`Store(3, 0, 0x2_0000_4003)`, `Store(4, 128, 0x40_0000_4008_0787)` and
`Store(4, 129, 0x60_0000_4008_1707)`, whose table descriptors point into
the pool of the target; and `Sync`. Once it is executed, the target has 5
tables in use and the same leaves as the source, and the source is
unchanged. The page `0x8000` of the process, mapped into the target as
`UserReadWrite`, `0x60_0000_4010_0f47`, is not mapped in the source.

## Design

- The module computes every write as a plan and leaves the stores, the
  barriers and the invalidations to the adapter of the architecture crate,
  so it holds no `unsafe`, defines no callback for a hardware action and
  runs on the host as it runs at EL1. A plan iterator reads only entries
  that none of its own earlier steps writes, so the caller may execute
  each step before it asks for the next.
- The two maps and the copy give their steps one at a time, so that a plan
  needs no storage in proportion to the map: the maps take their leaves in
  address order, one 1 GiB slot after the other, with a cursor of scalars,
  and the copy walks the tables of the source once to check that every
  table in use is reached exactly once before it gives its first store.
- The region of a set is a parameter of its type, so `kernel_map` takes
  only lower sets and `direct_map` only upper ones. The plan iterators
  borrow the set and the source of a copy for their lifetime, so neither
  changes while a plan lives. Sets, page ownership tables, reservations and
  packets are neither `Clone` nor `Copy`, and the types whose values keep
  an invariant have private fields; compile-fail cases check each rule.
- The adapter takes a whole plan through a trait of the architecture crate
  and writes through a `Pool` that only `unsafe` code makes, so `apply` is
  safe and the core gives no callback. The two kernel sets are statics of
  the image in a wrapper of the alignment of a table; `Tables` is
  `#[repr(C)]` with its pool first, so the address of a static is that of
  its pool, which the board gives `kernel_map`, `direct_map` and
  `Pool::new`. `Tables::new` makes the statics part of the data of the
  image, zero but for the record of the tables in use.
- The page ownership table records one owner for every page in extents and
  exclusion records, and splits an allocation into a choice, the caller's
  zeroing and an assignment, so that no callback runs inside the table and
  a failed zeroing changes nothing. Generations only grow, so a stale
  receipt is always refused.
- The code follows the
  [provable Rust subset](../../conventions/provable-subset.md) in the code
  shapes of the [proof path](../../domains/memory/page-tables/proof.md): a
  descriptor is put together with shifts and masks, a kind gives its bits
  by a `match`, an end that may pass 64 bits is checked, a function holds
  at most one loop, every loop walks arrays of plain data and scalars, and
  each plan iterator implements `next` alone, without the `Iterator` trait.
  Every type and function that a root of the proof target names is defined
  in `kernel/src/page_tables.rs`.
- On several CPUs: the caller holds the token of a set or of the page
  ownership table from the first check of an entry to the last step of its
  plan; the kernel tables are built before the secondary CPUs start, and
  afterwards only invalid entries of the lower kernel set are filled. The
  acknowledgement of a TLB invalidation by the other CPUs is not the
  module's.
- Excluded: sealing, splitting or merging the direct map after boot, a
  byte heap, the tables of address spaces with their ASIDs, the execute
  right of VM objects, and any access to memory through an address.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  the VMSAv8-64 translation table format of the 4 KiB granule, the
  attributes of its descriptors, break-before-make, `TLBI VAAE1IS`,
  `DMB`, `DSB` and `ISB`.
- Arm Limited, *Learn the architecture - AArch64 memory management Guide*,
  version 1.4, document 101811_0104_01_en, 2024,
  <https://documentation-service.arm.com/static/670e4dc89fbc7343d3e4cee1>.
- Arm Limited, *Learn the architecture - Memory Systems, Ordering, and
  Barriers*, version 1.0, document 102336_0100_01_en, 2022,
  <https://documentation-service.arm.com/static/62a304f231ea212bb662321d>.
- devicetree.org, *Devicetree Specification*, release v0.4, 2023,
  <https://github.com/devicetree-org/devicetree-specification/releases/download/v0.4/devicetree-specification-v0.4.pdf>:
  section 3.5.2, `no-map` and `reusable`.
- B. Simner, A. Armstrong, J. Pichon-Pharabod, C. Pulte, R. Grisenthwaite,
  P. Sewell, "Relaxed virtual memory in Armv8-A", European Symposium on
  Programming (ESOP), 2022, <https://arxiv.org/abs/2203.00642>.
- The [references of the contract](../../domains/memory/page-tables/contract.md#references),
  which name the sections and the files that its rules rely on.

## Implementation

- `kernel/src/page_tables.rs`: the module root, with the constants, the
  types of the entries and of the plans, the two error enums, the
  assertions that four types are not `Clone`, and `descriptor`,
  `direct_address`, `kernel_map` and `direct_map`.
- `kernel/src/page_tables/encoding.rs`: the bits of each kind, the table
  and block descriptors and the readers of the fields of a descriptor.
- `kernel/src/page_tables/range.rs`: `PhysRange::new`, `start`, `size`,
  `end`, `contains` and `overlaps`.
- `kernel/src/page_tables/walk.rs`: the first checks of an entry, the
  check of a pool, the walk of a set, `Tables::new`, `used`, `lookup_page`
  and `lookup_block`.
- `kernel/src/page_tables/write.rs`: `reset`, `map_page`, `map_block` and
  `unmap_page`, with their plans and the count of free tables.
- `kernel/src/page_tables/copy.rs`: `clone_kernel_from`, with the checks
  of the pools, of the descriptors of the source and of its reach, and
  `ClonePlan::next`.
- `kernel/src/page_tables/boot.rs`: what the two maps share: the place of a
  leaf in a set, the check of a leaf with the count of new tables, and the
  cursor that gives the steps of a map in the order of its plan.
- `kernel/src/page_tables/boot/layout.rs`: the checks of `kernel_map`,
  the order of the ranges, their pages and the guard pages, and
  `KernelMapPlan::next`.
- `kernel/src/page_tables/boot/direct.rs`: the checks of `direct_map` over
  the usable ranges of the boot memory map, and `DirectMapPlan::next`.
- `kernel/src/page_tables/ownership.rs`: `Ownership::new`, with the banks
  and the exclusions, `owner` and `stats`.
- `kernel/src/page_tables/ownership/placement.rs`: `choose`, `assign` and
  `reserve`.
- `kernel/src/page_tables/ownership/receipts.rs`: `validate`, `release`,
  `publish`, `cancel`, `Reservation::initialized` and the merge of freed
  extents with their neighbours.
- `kernel/arch/src/mmu.rs`: the adapter, with the trait `Plan` and its
  implementations, `WriteSteps`, `Pool`, `apply` with the stores, the
  barriers and the invalidations of the steps, `enable`, `zero_frames`,
  `physical_width`, and the values of `TCR_EL1`, `MAIR_EL1` and
  `SCTLR_EL1`.
- `kernel/boards/qemu-virt/src/boot_memory.rs`: the boot wiring of QEMU
  virt, `wire`, with the boot memory map, the banks and exclusions of the
  page ownership table, the layout of the image, the counts of the steps of
  a plan, and the statics of the two kernel sets, of the map and of the
  table.
- `kernel/boards/qemu-virt/src/main.rs`: `image::device_tree`, the slice of
  the tree at the start of RAM, and `image::boot_memory`, which calls the
  wiring between the boot records of the default image.

## Verification

- **Host.** The tests of the module run in the `test` and `test-release`
  steps of `cargo xtask check`: the 47 frozen vectors that the
  [contract](../../domains/memory/page-tables/contract.md#legacy-test-vectors)
  carries over, with their expected outputs; each row of the kind table
  and the direct address; the plans of the write entries in the order of
  the contract; the kinds, the guard pages and the refusal of a shared page
  of the kernel's mappings; the direct maps of the five Pi 5 models against
  a page model, with the counts of the contract; the page ownership table
  of QEMU virt and of the five Pi 5 models against an independent page
  model, which checks that every managed page has exactly one owner and
  that the free pages are exactly the pages of the direct map; the
  capacities at the limit and one above, and the free tables of a pool
  whose record of tables in use is all its tables but one, all of them or
  above them; the examples above; and the results test, which compares
  every output of the vector file with its expected output. They establish
  the rules on tables in host memory, not a CPU walking them.
- **Compile-time guards.** The `subset` step of `cargo xtask check` builds
  the four compile-fail cases of the module below `kernel/compile-fail/`: a
  `PhysRange` written without `PhysRange::new`, which its private fields
  refuse; a set that derives `Clone`, which the assertion of the module
  refuses; a map into the source of a copy while its plan lives, which the
  borrow refuses; and an upper set given to `kernel_map`, which its type
  refuses.
- **QEMU and board.** The cases `kernel-memory` and `boot-memory` of the
  QEMU boot suite, which `cargo xtask qemu-boot` runs after the check in
  the `check` workflow of CI and the suite `qemu-boot` of
  `cargo xtask suite` runs from the images of the image job, boot their
  test images in release on QEMU virt, `virt-8.2` with one Cortex-A76 and
  128 MiB under TCG, with the kernel tables of the boot wiring and the
  caches off. `kernel-memory` runs once: five faults, each with its
  exception class, fault status code, write bit, address and a return
  address from the ELF file, a translation fault at level 3 for a read of
  the last page of the tree and of the first page of the image through the
  direct map and for a read of the guard, a permission fault for a write to
  the read-only data, and an instruction abort with a permission fault at
  level 2 for a branch to a page of the direct map; and twelve self-checks,
  the six edge pages of the usable ranges written, zeroed by `zero_frames`
  and read back through the direct map, which translates each to its
  physical address as Normal memory, the five faults, and the `Device`
  attribute of the console, through which every later record goes.
  `boot-memory` runs three times, with identical transcripts whose counts
  of the tables, blocks and pages of the two plans equal those that the
  suite computes from the contract, the runner's RAM, the link symbols of
  the ELF file and the device tree that QEMU dumps for the machine. The
  case `cold-boot-echo` boots the default image with the wiring. They
  establish that the tables that the plans build translate and check
  permissions as the contract says on one CPU of QEMU virt; they establish
  nothing for the caches on, several CPUs or a board.
- **Proofs.** None of the code. The proof target `page-tables` is
  registered as planned in `verification/targets.json`, with the functions
  of the core rows of the contract's
  [entry table](../../domains/memory/page-tables/contract.md#entry-points)
  and the `next` of the three plan iterators as its roots; it is extracted
  and type-checked when a run names it, and its refinement proofs are
  planned. The statements of the specification are about the
  specification, not the code. The results that the host tests write are
  not yet compared with the replay of the specification.
- **Unverified.** The bank shapes of the 1, 2, 4 and 16 GB models, which
  the tests take from the ranges that the fdt contract infers; the tables
  on a Raspberry Pi 5 and with the caches on; the ordering that the
  barriers give on several CPUs; the panic of `apply` on a step outside its
  pool and the panics of the boot wiring, which no test takes; and the
  argument of the `SAFETY` comments of the stores, that no Rust reference
  reads an entry after a step writes it, which is not shown under either
  aliasing model of Rust, Stacked Borrows or Tree Borrows: a plan holds a
  shared reference to its set while `apply` executes it, and Miri reports
  undefined behaviour for a host copy of the boot wiring under both models,
  whether the plan is passed by value or by reference. The open obligations
  leave it to the proof of the unsafe sites; a later design of the core, in
  which a plan holds no reference while it executes, removes it.

## Limitations

- QEMU virt only: the Pi 5 board crate, with its boot wiring, is planned.
- The caches stay off: `enable` takes the choice, but no image turns them
  on, and the cache maintenance that turning them on needs is not
  provided.
- RAM above 16 GiB in all, more than 32 banks, a layout of more than 16
  ranges and a direct map of RAM at or above $2^{39}$ are not supported.
- The direct map is never changed after boot: no page of it is sealed, and
  no block is split or merged.
- One CPU: the acknowledgement of a TLB invalidation by the other CPUs is
  not covered.
- The modules of the core that take pages and fill the tables of address
  spaces are planned, so the entries that only they call have no caller
  yet.
