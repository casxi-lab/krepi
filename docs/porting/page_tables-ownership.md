---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/memory/mod.rs
  - src/memory/types.rs
  - src/memory/extents.rs
  - src/memory/page.rs
  - src/memory/reservation.rs
  - src/memory/tests.rs
  - src/memory/tests/banks.rs
  - src/memory/tests/reservations.rs
destination:
  - kernel/src/page_tables.rs
  - kernel/src/page_tables/range.rs
  - kernel/src/page_tables/ownership.rs
  - kernel/src/page_tables/ownership
  - kernel/src/page_tables/tests/ownership.rs
  - kernel/src/page_tables/tests/banks.rs
  - kernel/src/page_tables/tests/reservations.rs
treatment: redesigned
features:
  - krepi.kernel.kernel-memory
---

# Porting record: kernel/src/page_tables/ownership.rs

## Summary

The page ownership table of the module `page_tables` of the provable core
`krepi-kernel`, the part of the
[page-tables contract](../domains/memory/page-tables/contract.md#page-ownership)
that gives every managed page one owner, from the prototype's page
allocator in `src/memory`: the physical ranges, the extents of the banks
with their receipts and generations, the placement of a request and the
staged reservation, with their tests. The rest of the module has the
[record of the page tables](page_tables.md). The legacy area `src/memory`
is classified as ported by
[porting](../conventions/porting.md#classification-of-the-legacy-areas),
but this part is redesigned: the allocation with a zeroing callback is
split into a choice, the caller's zeroing and an assignment; the table no
longer counts failures; and it records the owner of every excluded page.
The rules and the tests of the prototype are kept, as the contract's
behaviour changes state, and the code is written again in the
[provable Rust subset](../conventions/provable-subset.md), in the code
shapes of the [proof path](../domains/memory/page-tables/proof.md).

| Legacy path | krepi path |
| --- | --- |
| `src/memory/mod.rs`, `src/memory/types.rs`: the types `PhysRange`, `Allocation`, `Stats` and `Error`; the types of the other files | `kernel/src/page_tables.rs` |
| `src/memory/types.rs`: the functions of `PhysRange` | `kernel/src/page_tables/range.rs` |
| `src/memory/extents.rs`: `from_regions` and `exclude`, `stats`; `src/memory/page.rs`: `from_regions` | `kernel/src/page_tables/ownership.rs` |
| `src/memory/extents.rs`: `choose`, `assign`, `allocate_placed` and `reserve_placed`; `src/memory/page.rs`: `allocate` and `allocate_in`; `src/memory/reservation.rs`: `reserve` and `reserve_in` | `kernel/src/page_tables/ownership/placement.rs` |
| `src/memory/extents.rs`: `allocation_index`, `validate` and `free`; `src/memory/reservation.rs`: `initialize`, `validate_initialized`, `publish_initialized` and `cancel_unused` | `kernel/src/page_tables/ownership/receipts.rs` |
| `src/memory/extents.rs`, its test | `kernel/src/page_tables/tests/ownership.rs` |
| `src/memory/tests.rs` | `kernel/src/page_tables/tests/ownership.rs` |
| `src/memory/tests/banks.rs` | `kernel/src/page_tables/tests/banks.rs` |
| `src/memory/tests/reservations.rs` | `kernel/src/page_tables/tests/reservations.rs` |

## Changes

- **Layout.** The types are defined in `kernel/src/page_tables.rs` beside
  those of the page tables, and the files below
  `kernel/src/page_tables/ownership` hold their behaviour; the module
  re-exports nothing. `PageAllocator` with its `Extents` is `Ownership`,
  `memory::Error` is `OwnershipError`, `PageReservation` is `Reservation`
  and `InitializedPages` is `Initialized`.
- **Entries.** `pub` is kept only for the rows of the contract's entry
  table that a board calls, `PhysRange::new`, `Ownership::new`, `choose`
  and `assign`, for the value types that they take and return, and for
  `start` and `size` of `PhysRange`, which the zeroing of frames in
  `krepi_arch::mmu` reads and which the contract lists as open
  obligations of their own; the other rows are `pub(crate)`, since only
  modules of the core call them.
  So these public items of the prototype are `pub(crate)`, under the names
  that the items below give: `end`, `contains` and `overlaps` of
  `PhysRange`; `free`, `stats` and the type `Stats`; the types
  `PageReservation` and `InitializedPages`, with `initialize`; and
  `reserve`, `reserve_in`, `validate_initialized`, `publish_initialized`
  and `cancel_unused`.
- **Initialization.** `Ownership::new(arena, banks, exclusions)` takes the
  banks and the exclusions, each a range with its owner, firmware, image or
  boot storage, and keeps at most `X` exclusion records beside its `E`
  extents; `owner(address)` names the owner of any page. It replaces
  `PageAllocator::new` of one range and `from_regions`, whose reservations
  were ranges without an owner that left no record. The banks are sorted by
  an insertion sort, and the free extents of a bank come from a cursor that
  moves past the exclusions that hold its position.
- **Allocation.** `allocate(owner, pages, alignment, zero)` and
  `allocate_in`, which called a zeroing callback under the table, are
  `choose(owner, pages, alignment, placement)`, which gives the range that
  the caller zeroes as a `Choice` and writes nothing, and
  `assign(choice, zeroed)`, which takes the outcome of the zeroing. The
  placement is a value of each request, a direction and an optional window,
  in place of the state that `prefer_high_addresses` set and of the window
  of `allocate_in`.
- **Staged reservation.** `reserve` and `reserve_in` are `reserve` with a
  `Placement`; `PageReservation::initialize(zero)` is
  `Reservation::initialized(zeroed)`, which takes the outcome of the
  caller's zeroing and gives the packet, or the reservation with one more
  failure; `publish_initialized` is `publish` and `cancel_unused` is
  `cancel`, which return the refused value with the error.
  `validate(owner, allocation, state)` checks a receipt, published, or the
  allocation of a packet, reserved, in place of `validate` and
  `validate_initialized`.
- **Release.** `free` is `release`, with the same checks; freed extents
  merge with their free neighbours in the same bank, as before.
- **Values.** `Allocation` and `Stats` have public fields, in place of the
  accessors `range`, `owner` and `generation`: a receipt is bookkeeping,
  and each entry checks it against the table. `Stats` names its fields
  `managed`, `free`, `allocated`, `allocations`, `free_extents`,
  `largest_free`, `extents` and `capacity`, and has no peak of allocated
  bytes, which only the byte heap read, and no counts of failures. The
  functions of `PhysRange` are no longer `const fn`; `start` is kept, `len`
  is `size`, `is_empty` is gone, and `end`, `contains` and `overlaps` serve
  the core.
- **Holders.** An extent records its holding as free or as held by an owner
  identity with a generation and a state, reserved or published, in place
  of a generation of 0 for a free extent. The state lets `validate` and
  `release` tell the pages of a published receipt from those of a
  reservation, now that a receipt is a value with public fields. The
  generation counter stops at $2^{64} - 1$, as before.
- **Code shapes.** Each function holds at most one loop over arrays of
  plain data and scalars, a sum or an end that may pass 64 bits is checked,
  and no library sort, iterator adapter or callback is called.
- **Derives.** `PhysRange`, `Allocation`, `Stats`, `OwnershipError` and the
  small values derive `Clone`, `Copy`, `Debug`, `PartialEq` and `Eq` for
  the tests; no production code calls a derived method. The table, a
  reservation and a packet are neither `Clone` nor `Copy`, which assertions
  of the module fix.
- **Documentation.** The documentation and every comment are written again
  and name the feature with `//! Feature: krepi.kernel.kernel-memory` in
  place of the prototype's feature line.
- **Tests.** The tests hold no byte array of the RAM and no zeroing
  callback: a test asserts that each choice is the range that the
  prototype's callback zeroed, and then assigns it with the outcome of that
  callback. New tests: the owner of every kind of page, the capacities of
  the extents and of the exclusion records at the limit and one above, the
  page ownership table of QEMU virt and of the five Raspberry Pi 5 models
  against an independent page model and the direct map, the results of the
  frozen vectors and the examples of the feature document.

## Tests carried over

| Legacy tests | krepi tests |
| --- | --- |
| `src/memory/extents.rs`, 1 test | The same name in `kernel/src/page_tables/tests/ownership.rs` |
| `src/memory/tests.rs`, 11 of its 15 tests | The same names in `kernel/src/page_tables/tests/ownership.rs` |
| `src/memory/tests/banks.rs`, 6 tests | The same names in `kernel/src/page_tables/tests/banks.rs` |
| `src/memory/tests/reservations.rs`, 6 tests | The same names in `kernel/src/page_tables/tests/reservations.rs` |

These are the 24 vectors `own-01` to `own-11` and `own-16` to `own-28` of
the page-tables contract. Changed expected values:

- `invalid_page_requests_never_call_zero_backend`,
  `partial_zero_failure_does_not_publish_or_consume_allocation` and
  `failed_initialization_retains_partial_bytes_and_cannot_cancel_as_unused`
  drop their assertions on the counts of failed requests and failed
  zeroings, which the table no longer keeps; their other outputs stay.

## Behaviour changes

- The allocation is `choose`, the caller's zeroing and `assign`, and the
  staged reservation takes the outcome of the zeroing in
  `Reservation::initialized`; the outputs are unchanged:
  `page_alignment_and_zeroing_work_above_four_gib` and
  `partial_zero_failure_does_not_publish_or_consume_allocation` in
  `page_tables::tests::ownership`, and
  `failed_initialization_retains_partial_bytes_and_cannot_cancel_as_unused`
  in `page_tables::tests::reservations`.
- A refused request writes nothing: the table keeps no count of failed
  requests and of failed zeroings, and its statistics are unchanged by a
  refusal:
  `invalid_page_requests_never_call_zero_backend` in
  `page_tables::tests::ownership` and
  `failed_initialization_retains_partial_bytes_and_cannot_cancel_as_unused`
  in `page_tables::tests::reservations`.
- The table records the owner of every excluded page, firmware, image or
  boot storage, in at most 132 exclusion records apart from its extents,
  and `owner` names it; no output of a vector changes:
  `owners_follow_the_extents_then_the_exclusions_by_kind` in
  `page_tables::tests::ownership`,
  `exclusions_to_capacity_initialize` and
  `one_exclusion_over_capacity_fails` in `page_tables::tests::capacity`,
  and `boot_owners_match_the_direct_map_on_every_board_shape` in
  `page_tables::tests::boot`.

## Hardware evidence to re-obtain

- On QEMU virt, `virt-8.2` with one Cortex-A76 and 128 MiB, and on a
  Raspberry Pi 5 of 8 GB, once a board builds the page ownership table of
  the kernel root: pages allocated, written, released and allocated again,
  whose zeroes are read back through the direct map, and the free pages of
  the table equal to the pages of the direct map, on three cold boots.

## Not carried over

- `src/memory/mod.rs`: the declaration of the module `heap` and the
  re-export of `HeapAllocator`, since the kernel has no byte heap, and the
  re-exports of the other types, which are defined in the module root.
- `src/memory/tests.rs`: the 4 tests of the byte heap,
  `heap_alignment_padding_and_adjacent_frees_coalesce`,
  `fragmentation_fails_large_request_until_adjacent_spans_are_released`,
  `bounded_heap_trace_matches_independent_byte_ownership_model` and
  `address_rounding_and_span_end_overflow_do_not_reach_backend`, whose
  vectors the contract does not apply, and the helper that zeroed a byte
  array.
- `src/memory/types.rs`: the public `PAGE_SIZE`, `PhysRange::is_empty`,
  the accessors of `Allocation`, and the fields
  `peak_allocated_bytes`, `allocation_failures` and `zero_failures` of
  `Stats`.
- `src/memory/extents.rs`: `Extents::new` of one range, `reject` and
  `record_zero_failures` with the counts of failures.
- `src/memory/page.rs`: `PageAllocator::new` of one range,
  `prefer_high_addresses` and the zeroing callbacks of `allocate` and
  `allocate_in`.
- `src/memory/reservation.rs`: the zeroing callback of `initialize`,
  `InitializedPages::retry`, the accessors `range` of a reservation and of
  a packet, which `allocation` replaces, the accessor `failures` of a
  reservation, whose count a packet gives once its zeroing completes, and
  the charge of failed zeroings to the table at publication.
