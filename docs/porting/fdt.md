---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/fdt/mod.rs
  - src/fdt/format.rs
  - src/fdt/parser.rs
  - src/fdt/nodes.rs
  - src/fdt/translation.rs
  - src/fdt/discovery.rs
  - src/fdt/cpus.rs
  - src/fdt/types.rs
  - src/fdt/pi5.rs
  - src/fdt/pi5/selection.rs
  - src/platform/memory.rs
  - src/platform/memory/available.rs
  - src/platform/mod.rs
  - src/fdt/tests/mod.rs
  - src/fdt/tests/parser.rs
  - src/fdt/tests/translation.rs
  - src/fdt/tests/discovery.rs
  - src/fdt/tests/cpus.rs
  - src/fdt/pi5/tests.rs
  - src/fdt/pi5/tests/boundaries.rs
  - src/fdt/pi5/tests/builder.rs
  - src/fdt/pi5/tests/firmware.rs
  - src/fdt/pi5/tests/platform.rs
  - src/fdt/pi5/tests/selection.rs
  - src/platform/tests.rs
destination:
  - kernel/src/fdt.rs
  - kernel/src/fdt
treatment: ported
features:
  - krepi.platform.device-tree
---

# Porting record: kernel/src/fdt.rs

## Summary

The module `fdt` of the provable core `krepi-kernel`, the code of the
[device-tree contract](../domains/boot-platform/fdt/contract.md): the
bounded parser of the flattened device tree, the access to its nodes and
properties with the translation of addresses, the memory discovery, the CPU
nodes and the Pi 5 boot memory from `src/fdt`, and the boot memory map from
`src/platform/memory.rs` and `src/platform/memory/available.rs`, with the
errors and the span check of the memory plan from `src/platform/mod.rs`.
The tests of these files come with them: those of `src/fdt` without the
Pi 5 device bindings, and the 13 tests of the memory plan in
`src/platform/tests.rs`. The legacy areas `src/fdt` and `src/platform` are
ported, as
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies them: the behaviour is kept except for the changes below, and
the code is written again in the
[provable Rust subset](../conventions/provable-subset.md), in the code
shapes of the [proof path](../domains/boot-platform/fdt/proof.md).

| Legacy path | krepi path |
| --- | --- |
| `src/fdt/mod.rs`, `src/fdt/types.rs`, the types of the other files and the memory plan errors of `src/platform/mod.rs` | `kernel/src/fdt.rs` |
| `src/fdt/format.rs` | `kernel/src/fdt/format.rs` |
| `src/fdt/types.rs`, the functions of `Span` | `kernel/src/fdt/span.rs` |
| `src/fdt/parser.rs` | `kernel/src/fdt/parser.rs` |
| `src/fdt/nodes.rs` | `kernel/src/fdt/nodes.rs` |
| `src/fdt/translation.rs` | `kernel/src/fdt/translation.rs` |
| `src/fdt/discovery.rs` | `kernel/src/fdt/discovery.rs` |
| `src/fdt/cpus.rs` | `kernel/src/fdt/cpus.rs` |
| `src/fdt/pi5.rs` | `kernel/src/fdt/pi5.rs` |
| `src/fdt/pi5/selection.rs` | `kernel/src/fdt/pi5/selection.rs` |
| `src/platform/memory.rs`, with `range` of `src/platform/mod.rs` | `kernel/src/fdt/plan.rs` |
| `src/platform/memory/available.rs` | `kernel/src/fdt/plan/available.rs` |
| `src/fdt/tests/mod.rs` | `kernel/src/fdt/tests.rs` |
| `src/fdt/pi5/tests.rs` | `kernel/src/fdt/pi5/tests.rs` |
| `src/platform/tests.rs`, the tests of the memory plan | `kernel/src/fdt/plan/tests.rs` |

The other test files keep their names below `kernel/src/fdt/tests/` and
`kernel/src/fdt/pi5/tests/`.

## Changes

- **Layout.** Every `pub` type, the two error enums, the limits and
  `cells_u64` are defined in `kernel/src/fdt.rs`, and the other files hold
  their behaviour in `impl` blocks and private helpers. The prototype
  defined the types in the files of their behaviour and re-exported them
  from `src/fdt/mod.rs`; the roots of the proof target name the types where
  they are defined, and a re-export is not the type. The boot memory map,
  which was `platform::MemoryPlan` beside the device bindings, is part of
  the module, in `plan.rs`.
- **Entries.** `pub` is kept for the rows of the contract's entry table and
  the value types that they take and return. `PsciConduit::name` is gone:
  the private `method_is` of `cpus.rs` compares the method of `/psci` with
  the name of each conduit, given as a literal. `Reservations::new` and
  `AvailableRanges::new` are gone: their entries build the iterators.
- **Errors.** `Error` has no `DynamicReservation`: a dynamic reservation is
  accepted (below). The memory plan's `platform::Error` is `PlanError`,
  without `DeviceSize`, which only the device windows used. The span check
  `range` of `src/platform/mod.rs`, which built a `memory::PhysRange` and
  mapped its errors, is a check of a `Span` in `plan.rs` with the same
  outcome: a span of size 0, `InvalidRange`; one whose end leaves 64 bits,
  `Overflow`.
- **Spans of the boot memory map.** The map takes and gives `Span` values
  with a page of its own, 4 KiB, where the prototype used the `PhysRange`
  and the page of `src/memory`, which belong to another component. Its
  queries `contains_ram`, `is_available` and `permits_backing` are false
  for a span of size 0 or one whose end leaves 64 bits, which a
  `PhysRange` could not hold. The banks are sorted by an insertion sort in
  place of the library sort, and sums are taken by loops.
- **Boot storage.** It holds up to 4 spans, where the prototype allowed 2,
  so that a board can give the boot bundle as a span of its own;
  `MemoryPlan::from_pi5` takes the further spans after the image and the
  tree as a third argument.
- **Widths.** The nine limits, `Fdt::total_size`, `CpuTopology::count` and
  the index of `affinity`, and `CpuProfile::logical_id` and
  `affinity_shift` are `u64`, the widths of the specification, where the
  prototype used `usize` or `u32`. `PI5_MAX_BLOB_SIZE` is defined with the
  other limits. The functions of `CpuProfile` and `CpuTopology` are no
  longer `const fn`.
- **New entries.** `MemoryMap::dynamic` and `Pi5BootMemory::dynamic` give
  the number of dynamic reservations, of type `u64`, which the prototype
  rejected.
- **Names and strings.** `Node::name` gives the checked bytes of the name
  and `Node::string_property` the checked bytes of the string, where the
  prototype gave `&str`; `property`, `string_property` and `find_node`
  read their argument as bytes. Words are put together from single bytes,
  and UTF-8 and the character sets of names are checked by loops over the
  bytes, in place of `from_be_bytes`, `str::from_utf8` and the character
  methods of the library.
- **Iterators.** `Nodes`, `Reservations`, `Reg` and `AvailableRanges` have
  an inherent `next` and do not implement `Iterator`. `Reg::next` gives a
  `Span`, where the prototype's `Iterator` gave a `Result`, since
  `Reg::new` has checked every entry. `AvailableRanges` keeps the managed
  banks and the reservations as slices in place of a reference to the map,
  and its `next` moves past the furthest end of the reservations that hold
  its position, where the prototype stepped through them; the ranges are
  the same.
- **Views.** The tree, its nodes and the iterators are taken by value and
  every loop lives in a helper over slices of plain data and scalars. The
  node access and the duplicate check of the parse read the tokens of the
  checked structure block again without the checks of the parse, where the
  prototype decoded them again with its checking decoder. `AddressMap`
  records whether its property is present in a flag, with an empty slice
  for an absent property, in place of an `Option` field; `AddressMap::new`
  still takes an `Option`.
- **CPU nodes.** `discover_cpus` compares the ID of a CPU node with
  `id << affinity_shift` without the mask of `logical_id`, which gives the
  same errors, since a flag bit makes the two values differ.
  `validate_qemu_timers` takes the shift of its 32-bit CPU mask modulo 32,
  as the specification does; for the supported counts the mask is the same.
- **Derives.** `Span` no longer derives `Default`; `MemoryMap`,
  `Pi5BootMemory` and `MemoryPlan` derive `Debug` only, as before, and the
  views and the small values are `Copy`. No production code calls a derived
  method.
- **Documentation.** The module documentation and every comment are written
  again and name the feature with `//! Feature: krepi.platform.device-tree`
  in place of the prototype's feature line.
- **Tests.** The test builders keep their shape. The environment variables
  of the ignored firmware tests are `KREPI_PI5_SOURCE_DTB_DIR` and
  `KREPI_PI5_VALIDATED_DTB_DIR`, in place of `CASXI_PI5_SOURCE_DTB_DIR` and
  `CASXI_PI5_VALIDATED_DTB_DIR`. New tests: the limits at the limit and 1
  above, the errors that no vector gives, the error orders, the dynamic
  reservations, the five RAM models of the Pi 5, the results of the frozen
  vectors and the examples of the feature document.

## Tests carried over

| Legacy tests | krepi tests |
| --- | --- |
| `src/fdt/tests/parser.rs`, 9 tests | The same names in `kernel/src/fdt/tests/parser.rs` |
| `src/fdt/tests/translation.rs`, 5 tests | The same names in `kernel/src/fdt/tests/translation.rs` |
| `src/fdt/tests/discovery.rs`, 6 tests | The same names in `kernel/src/fdt/tests/discovery.rs` |
| `src/fdt/tests/cpus.rs`, 6 tests | The same names in `kernel/src/fdt/tests/cpus.rs` |
| `src/fdt/pi5/tests.rs`, 4 tests | The same names in `kernel/src/fdt/pi5/tests.rs` |
| `src/fdt/pi5/tests/boundaries.rs`, 5 tests | The same names in `kernel/src/fdt/pi5/tests/boundaries.rs` |
| `src/fdt/pi5/tests/selection.rs`, 3 tests | The same names in `kernel/src/fdt/pi5/tests/selection.rs` |
| `src/fdt/pi5/tests/platform.rs`, 2 tests | The same names in `kernel/src/fdt/pi5/tests/platform.rs` |
| `src/fdt/pi5/tests/firmware.rs`, 2 ignored tests | The same names in `kernel/src/fdt/pi5/tests/firmware.rs`, ignored |
| `src/platform/tests.rs`, the 13 tests of the memory plan | The same names in `kernel/src/fdt/plan/tests.rs` |

These are the 55 vectors of the contract. Changed expected values:

- `reserved_memory_requires_explicit_identity_and_static_regions` and
  `rejects_active_dynamic_reservations_and_conflicting_flags`: the dynamic
  child is accepted with 1 dynamic reservation and no reserved region,
  where the prototype gave `DynamicReservation`.
- `source_firmware_rejects_dynamic_reservations` keeps its name and expects
  the two shipped trees to be accepted with 1 dynamic reservation, the
  placeholder RAM `0x0+0x28000000` and the region `0x0+0x80000/no-map`.
- `exact_capacity_is_supported_and_excess_input_is_rejected`: three spans
  of boot storage that are all the image fail with `Overlap`, where the
  prototype gave `Capacity`.
- `allocator_consumes_the_same_rounded_boot_and_firmware_exclusions` holds
  the managed bank, the reservations and the backing of the two ranges in
  place of the page allocator of `src/memory`;
  `full_ram_registers_all_bank_pages_and_reservation_union` compares the
  bytes of the usable ranges with the managed bytes less the four
  exclusions in place of the free bytes of that allocator.
- `merged_firmware_preserves_placeholder_ram_and_boot_exclusions` keeps
  every assertion of the component and drops those of the Pi 5 kernel
  resources.

## Behaviour changes

- A dynamic reservation, an enabled child of `/reserved-memory` with a
  `size` and no `reg`, is counted and accepted, whatever the cells of its
  `size`: `fdt::tests::discovery`, `fdt::tests::dynamic`,
  `fdt::pi5::tests::rejects_active_dynamic_reservations_and_conflicting_flags`
  and the ignored `source_firmware_rejects_dynamic_reservations`.
- Boot storage of 4 spans is accepted and of 5 fails with `Capacity`:
  `boot_storage_of_four_spans_is_accepted` and
  `boot_storage_of_five_spans_fails_with_capacity` in
  `fdt::tests::limits`, and the case of
  `exact_capacity_is_supported_and_excess_input_is_rejected` above.
- `Span::contains` checks the ends of both spans before it compares them,
  and fails with `Overflow` where the prototype gave `false`:
  `span_contains_checks_both_ends_before_comparing` in
  `fdt::tests::limits`.

## Hardware evidence to re-obtain

- On QEMU virt: the parse and the boot memory map of the hand-over tree on
  three cold boots, with the same results, through the boot wiring of the
  board ([boot_memory](boot_memory.md)): the case `boot-memory` of
  `cargo xtask qemu-boot`, in CI.
- On a Raspberry Pi 5 of 8 GB: the hand-over tree that the firmware leaves,
  its three RAM ranges and two reserved regions, and the boot memory map
  built from it, with the firmware, EEPROM and BL31 versions of the bench.

## Not carried over

- `src/fdt/mod.rs`: the module `pci` and the re-exports of the Pi 5 device
  bindings, `Pi5Interrupts`, `Pi5PpiTrigger`, `Pi5TimerPpi`, `Pi5Rp1` and
  `Pi5Sdio`, which belong to the components of those bindings.
- `src/fdt/pi5.rs`: the declarations of `binding`, `interrupts`, `rp1` and
  `sdio` and their re-exports, for the same reason.
- `src/fdt/pi5/tests.rs`: the declaration `mod kernel;` of the tests of the
  Pi 5 kernel resources, which go with the Pi 5 board support.
- `src/platform/mod.rs`: the modules `devices`, `mapping`, `pi5` and `rp1`,
  the re-exports of `Devices`, `Pi5Resources` and the other Pi 5 items, and
  the error `DeviceSize`, which belong to the board support and the
  page-tables component.
- `src/platform/tests.rs`: the 4 tests of device windows,
  `preserves_high_device_addresses_and_adjacent_gic_windows`,
  `device_windows_must_be_valid_disjoint_and_bounded`,
  `devices_cannot_alias_ram_outside_the_managed_window` and
  `optional_controller_window_preserves_device_order_and_failure_is_atomic`,
  which go with the Pi 5 board support, and the helper that built a
  `PhysRange`.
- `src/fdt/pi5/tests/firmware.rs`: the assertions of
  `merged_firmware_preserves_placeholder_ram_and_boot_exclusions` on the
  Pi 5 kernel resources, the UART, the GIC distributor and the absence of a
  high page, which go with the Pi 5 board support.
- `Error::DynamicReservation`, `platform::Error::DeviceSize` and the
  `Iterator` implementations, as the changes above state.
