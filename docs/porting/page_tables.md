---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/arch/aarch64/paging.rs
  - src/arch/aarch64/paging/block.rs
  - src/arch/aarch64/paging/protection.rs
  - src/arch/aarch64/paging/tests.rs
  - src/platform/mapping.rs
  - src/mmu.rs
  - src/arch/aarch64/address.rs
destination:
  - kernel/src/page_tables.rs
  - kernel/src/page_tables/encoding.rs
  - kernel/src/page_tables/walk.rs
  - kernel/src/page_tables/write.rs
  - kernel/src/page_tables/copy.rs
  - kernel/src/page_tables/boot.rs
  - kernel/src/page_tables/boot
  - kernel/src/page_tables/tests.rs
  - kernel/src/page_tables/tests/paging.rs
  - kernel/src/page_tables/tests/mapping.rs
treatment: ported
features:
  - krepi.kernel.kernel-memory
---

# Porting record: kernel/src/page_tables.rs

## Summary

The module `page_tables` of the provable core `krepi-kernel`, the code of
the [page-tables contract](../domains/memory/page-tables/contract.md)
apart from the page ownership table, which has a
[record of its own](page_tables-ownership.md). It takes the bounded stage 1
translation tables of the prototype's architecture code, with their blocks
of 2 MiB and the allocation of their tables, from `src/arch/aarch64/paging.rs`
and its two child files; the construction of the direct map from
`src/platform/mapping.rs`; the rule by which the prototype's MMU setup in
`src/mmu.rs` gave each page of the image its kind, which is now
`kernel_map` over a layout; and the direct address with its base from
`src/arch/aarch64/address.rs`. The tests of the tables and of the direct
map come with them. The legacy areas `src/arch`, `src/mmu` and
`src/platform` are ported, as
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies them: the descriptors, the walk, the checks and their errors
are kept except for the changes below, and the code is written again in
the [provable Rust subset](../conventions/provable-subset.md), in the code
shapes of the [proof path](../domains/memory/page-tables/proof.md). The
other parts of `src/mmu.rs` belong to the boot wiring of QEMU virt, to its
test images and to the module `mmu` of `krepi-arch`, whose records
[boot_memory](boot_memory.md), [qemu-virt](qemu-virt.md) and [mmu](mmu.md)
take them.

| Legacy path | krepi path |
| --- | --- |
| `src/arch/aarch64/paging.rs`: `Kind`, `Error`, `PageTables` and the constants | `kernel/src/page_tables.rs` |
| `src/arch/aarch64/paging.rs`: `Kind::bits` | `kernel/src/page_tables/encoding.rs` |
| `src/arch/aarch64/paging.rs`: `validate`, `child`, `leaf`, `descriptor`, `new` and `used_tables`; `src/arch/aarch64/paging/block.rs`: `ram_block_descriptor` | `kernel/src/page_tables/walk.rs` |
| `src/arch/aarch64/paging.rs`: `map_page`, `unmap_page` and `reset`; `src/arch/aarch64/paging/block.rs`: `map_ram_block`; `src/arch/aarch64/paging/protection.rs`: `available_tables`, `next_table` and `allocate_table` | `kernel/src/page_tables/write.rs` |
| `src/arch/aarch64/paging.rs`: `clone_kernel_from` and `clone_child` | `kernel/src/page_tables/copy.rs` |
| `src/platform/mapping.rs`: `map_backing` | `kernel/src/page_tables.rs` (`direct_map`), `kernel/src/page_tables/boot.rs` and `kernel/src/page_tables/boot/direct.rs` |
| `src/mmu.rs`: the kinds of the pages of the image in `init_and_verify` | `kernel/src/page_tables.rs` (`kernel_map`), `kernel/src/page_tables/boot.rs` and `kernel/src/page_tables/boot/layout.rs` |
| `src/arch/aarch64/address.rs`: `DIRECT_BASE` and `direct_address` | `kernel/src/page_tables.rs` |
| `src/arch/aarch64/paging/tests.rs` | `kernel/src/page_tables/tests/paging.rs` |
| `src/platform/mapping.rs`, its tests | `kernel/src/page_tables/tests/mapping.rs` |

## Changes

- **Layout.** The tables were part of the architecture code; they are a
  module of the provable core, so that the core can check and plan every
  write and the architecture crate only executes the plans. Every type that
  an entry names, `Tables`, `Kind`, `TableError`, `Step`, `WritePlan`, the
  layout and the three plan iterators, and the module functions
  `descriptor`, `direct_address`, `kernel_map` and `direct_map` are defined
  in `kernel/src/page_tables.rs`, and the other files hold their behaviour
  in `impl` blocks and private helpers: the roots of the proof target name
  the items where they are defined.
- **Names.** `PageTables` is `Tables`, whose parameter `UPPER` has no
  default; `Error` is `TableError`, with the same seven errors;
  `descriptor`, the lookup of a page leaf, is `lookup_page`;
  `ram_block_descriptor` is `lookup_block`; `map_ram_block` is
  `map_block`; and `used_tables` is `used`. The private `Kind::bits` is
  read through the module function `descriptor(kind, address)`, which takes
  bits 12 to 47 of its address.
- **Entries.** `pub` is kept only for the rows of the contract's entry
  table that `krepi-arch` or a board calls, `direct_address`,
  `Tables::new`, `kernel_map` and `direct_map`, for the `next` of the three
  plan iterators, and for the value types that these and the adapter take
  and return; the other rows are `pub(crate)`, since only modules of the
  core call them. So `used_tables`, `reset`, `clone_kernel_from`,
  `map_page`, `descriptor`, `unmap_page`, `map_ram_block` and
  `ram_block_descriptor`, public in the prototype, are `pub(crate)` under
  the names above, and the public `PAGE_SIZE` and `BLOCK_SIZE` of
  `paging.rs` are private constants of the module.
- **Storage.** `Tables::new(pool)` takes the zero storage of the pool by
  value and sets the record of the tables in use to 1; it is a `const fn`,
  so that a board can build a set in a static. It replaces `new()`, which
  built zero tables itself, and the `Default` implementation. The type is
  `#[repr(C)]` with the pool as its first field, so that the address of a
  set is the address of its table 0: a board that places the set in a
  static aligned to 4 KiB names `base` by the address of that static. The
  prototype's `#[repr(C, align(4096))]` also aligned the set itself, which
  the board's static does here, so the sets of the host tests need no
  alignment of 4 KiB.
- **Record of tables.** A set records only the number of its tables in
  use, those of the lowest indices; the array `free` and the reuse of a
  freed table are gone with the sealing of the direct map, so a table
  returns to the pool only through `reset` and through the copy.
- **Plans.** `map_page`, `map_block`, `unmap_page` and `reset` check as
  before and return a `WritePlan` of their stores, barriers and
  invalidation, in the order of the contract, in place of writing the
  tables; `unmap_page` returns the plan with the page. The plan of `reset`
  zeroes the tables in use, where the prototype filled every table of the
  pool. `clone_kernel_from` returns the plan iterator `ClonePlan`, which
  gives the zeroing of the target's tables in use and the stores of the
  source's valid entries, rebased into the target's pool, one step at a
  time.
- **Copy.** The checks of the copy are those of the prototype, all before
  its first step: the pools, the base and the width, every descriptor of
  the source, and the walk that records the level of each table and checks
  that every table in use is reached exactly once. The plan keeps those
  levels and gives a store for each valid entry of the source, its table
  descriptors rebased, where the prototype copied whole tables and rebased
  them in place; it zeroes the target's tables in use, where the prototype
  reset every table of the target.
- **Direct map.** `map_backing(plan, tables, base, bits)` is
  `direct_map(set, memory, base, bits)` on an upper set with the boot memory
  map of the fdt module. It checks the whole map, the leaves of every usable
  range and the tables that the map needs, before it returns the plan
  iterator `DirectMapPlan`, which gives the steps of the blocks and pages in
  address order; `MappingStats` is gone, and the tests count the blocks,
  pages and bytes of the plan.
- **Kernel mappings.** `init_and_verify` of `src/mmu.rs` mapped every page
  of the boot storage with the kind that the linker symbols gave it, text
  `ReadExecute`, read-only data and the other boot storage `ReadOnly` and
  the rest `ReadWrite`, skipped the guard page of the stack and mapped the
  devices `Device`. That rule is `kernel_map(set, layout, base, bits)`: the
  board gives the ranges with their kinds and the guard pages as a
  `Layout`, and `kernel_map` checks that every range lies on page
  boundaries, that no two share a page and that none covers a guard,
  before it returns the plan iterator `KernelMapPlan`.
- **Iterators.** The three plan iterators have an inherent `next` and do
  not implement `Iterator`; each borrows its set, and the copy its source,
  for its lifetime.
- **Direct address.** `DIRECT_BASE` and `direct_address` are kept, with
  the same results; `direct_address` is written with an `if` in place of
  `bool::then`. `VA_BITS` and `DIRECT_LIMIT` are gone: the end of the
  window is a private constant of the module.
- **Code shapes.** Each function holds at most one loop, every loop walks
  arrays of plain data and scalars, and no function reaches a library
  method without a model: `is_multiple_of`, `try_from`, iterator adapters
  and `assert_eq!` in production code are written as arithmetic, `match`
  and comparisons.
- **Derives.** `Kind`, `TableError`, `Step` and `WritePlan` derive
  `Clone`, `Copy`, `Debug`, `PartialEq` and `Eq` for the tests; no
  production code calls a derived method. A set is neither `Clone` nor
  `Copy`, which an assertion of the module fixes.
- **Documentation.** The module documentation and every comment are
  written again and name the feature with
  `//! Feature: krepi.kernel.kernel-memory` in place of the prototype's
  feature line.
- **Tests.** A helper of the tests executes each plan on the pool of its
  set, as the architecture crate will; the tests of the prototype then
  read the tables as before. New tests: the rows of the kind table and the
  direct address, the plans of every write entry in the order of the
  contract, the kernel's mappings with their kinds, guard pages and refused
  layouts, the direct maps of the five Raspberry Pi 5 models against a page
  model, the pool at capacity, the results of the frozen vectors and the
  examples of the feature document.

## Tests carried over

| Legacy tests | krepi tests |
| --- | --- |
| `src/arch/aarch64/paging/tests.rs`, 19 of its 21 tests | The same names in `kernel/src/page_tables/tests/paging.rs` |
| `src/platform/mapping.rs`, 4 tests | The same names in `kernel/src/page_tables/tests/mapping.rs` |
| `src/arch/aarch64/address.rs`, `direct_spans_preserve_high_pa_and_reject_range_wrap` | Its cases, the vector `as-32` of the [address-space contract](../domains/memory/address-space/contract.md), in `direct_addresses_keep_the_start_and_end_at_the_window` of `kernel/src/page_tables/tests/kinds.rs` |

These are 23 of the vectors of the page-tables contract. The tests read
`used` where the prototype's read `used_tables`, `lookup_page` and
`lookup_block` where they read `descriptor` and `ram_block_descriptor`,
and the counts of the plan of `direct_map` where they read `MappingStats`;
no expected value changes.

## Behaviour changes

- An entry that changes a set returns its plan and writes nothing, and its
  plan has the order of the contract:
  `page_tables::tests::plans`.
- `direct_map` checks the whole map before its first step, where the
  prototype could leave a partial map to discard; the output of the vector
  `dm-03` is unchanged:
  `exhausted_storage_never_reports_a_complete_map` and
  `direct_map_one_table_over_the_pool_fails` in
  `page_tables::tests::capacity`.
- `kernel_map` refuses a layout whose ranges share a page or cover a guard
  page with `AlreadyMapped`, where the prototype took the boundaries of
  the kinds from its linker symbols:
  `kernel_map_refuses_text_and_data_on_one_page` and
  `kernel_map_refuses_a_range_over_a_guard` in
  `page_tables::tests::boot`.
- The plan of `reset` zeroes the tables in use, at most the capacity, and
  not every table of the pool; the tables not in use are zero already:
  `whole_address_space_reset_reclaims_intermediate_tables` and
  `zeroed_table_storage_can_be_initialized_in_place` in
  `page_tables::tests::paging`, and the plan of `reset` in
  `page_tables::tests::plans`.

## Hardware evidence to re-obtain

- On QEMU virt, `virt-8.2` with one Cortex-A76 and 128 MiB, with the
  tables that the boot wiring builds and the MMU on: a write to a
  `ReadOnly` page, an execution from an execute-never page and an access to
  a guard page each take the fault of the contract, a `Device` page of the
  console is written and the edges of the direct map behave as the map
  says, the case `kernel-memory` of `cargo xtask qemu-boot`, and three cold
  boots give the same counts, the case `boot-memory`, both in CI.
- On a Raspberry Pi 5 of 8 GB: the direct map of the whole RAM, 11 tables,
  4,092 blocks and 581 pages, with the MMU on and the caches that the board
  chooses, with the firmware, EEPROM and BL31 versions of the bench.

## Not carried over

- `src/arch/aarch64/paging.rs`: the `Default` implementation, `new()`
  without storage, `#[repr(C, align(4096))]`, the array `free` with
  `used_tables`, and the writes into the tables, as the changes above state.
- `src/arch/aarch64/paging/protection.rs`: `protect_ram_page`, the sealing
  of one page of the direct map with the split and the merge of its block,
  since the direct map is never changed after boot; with it, the tests
  `sealed_ram_pages_split_and_restore_blocks_without_table_leaks` and
  `splitting_capacity_and_non_ram_permissions_fail_without_publication`
  of `src/arch/aarch64/paging/tests.rs`, whose vectors the contract does not
  apply.
- `src/platform/mapping.rs`: `MappingStats`.
- `src/mmu.rs`: everything but the rule of the kinds: the static tables and
  their export name, the reads of `ID_AA64MMFR0_EL1`, `DAIF` and
  `SCTLR_EL1` with the checks of the boot state, the probe pages and the
  fault probes, the diagnostic mappings at `HIGH_VA` and `REMAP_VA`, the
  branches of the feature profiles, the call that turns the MMU on, the
  checks after it, and the declarations and re-exports of `address_space`,
  `code`, `direct` and `fault`. The boot wiring, the test images and the
  module `mmu` of `krepi-arch` take or leave them in their records,
  [boot_memory](boot_memory.md), [qemu-virt](qemu-virt.md) and
  [mmu](mmu.md).
- `src/arch/aarch64/address.rs`: `translation_control` with its test
  `both_walk_regions_have_matching_policies_and_ttbr0_asids`, which the
  module `mmu` of `krepi-arch` takes ([mmu](mmu.md)), and the public constants
  `VA_BITS` and `DIRECT_LIMIT`.
