---
id: krepi.platform.device-tree
title: Device tree
status: implemented
modules:
  - kernel/src/fdt.rs
  - kernel/src/fdt/cpus.rs
  - kernel/src/fdt/discovery.rs
  - kernel/src/fdt/format.rs
  - kernel/src/fdt/hand_over.rs
  - kernel/src/fdt/hand_over/selection.rs
  - kernel/src/fdt/nodes.rs
  - kernel/src/fdt/parser.rs
  - kernel/src/fdt/plan.rs
  - kernel/src/fdt/plan/available.rs
  - kernel/src/fdt/span.rs
  - kernel/src/fdt/translation.rs
  - kernel/boards/qemu-virt/src/boot_memory.rs
  - kernel/boards/qemu-virt/src/main.rs
tests:
  - kernel/src/fdt/tests.rs
  - kernel/src/fdt/tests/any_profile.rs
  - kernel/src/fdt/tests/cpus.rs
  - kernel/src/fdt/tests/discovery.rs
  - kernel/src/fdt/tests/dynamic.rs
  - kernel/src/fdt/tests/examples.rs
  - kernel/src/fdt/tests/limits.rs
  - kernel/src/fdt/tests/order.rs
  - kernel/src/fdt/tests/parser.rs
  - kernel/src/fdt/tests/profiles.rs
  - kernel/src/fdt/tests/results.rs
  - kernel/src/fdt/tests/results/differential.rs
  - kernel/src/fdt/tests/translation.rs
  - kernel/src/fdt/cpus/tests.rs
  - kernel/src/fdt/cpus/tests/before.rs
  - kernel/src/fdt/hand_over/tests.rs
  - kernel/src/fdt/hand_over/tests/boundaries.rs
  - kernel/src/fdt/hand_over/tests/builder.rs
  - kernel/src/fdt/hand_over/tests/firmware.rs
  - kernel/src/fdt/hand_over/tests/models.rs
  - kernel/src/fdt/hand_over/tests/platform.rs
  - kernel/src/fdt/hand_over/tests/selection.rs
  - kernel/src/fdt/plan/tests.rs
  - kernel/src/fdt/plan/tests/before.rs
suites:
  - qemu-boot
theorems: none
related:
  - krepi.platform.qemu-virt-boot
---

# Device tree

## Summary

The module `fdt` of the provable core `krepi-kernel` reads the flattened
device tree that the firmware, or the loader of QEMU, hands to the kernel,
as untrusted input: it parses the tree within fixed bounds, gives access to
its nodes and properties and translates their addresses through `reg`,
`ranges` and `dma-ranges`, discovers the RAM ranges, the reserved regions,
the dynamic reservations and the CPU nodes, checks the hand-over tree of
the Raspberry Pi 5 against the storage of the image and of the tree, and
builds the boot memory map, the RAM banks with the boot storage and the
firmware reservations left out by whole pages, which the page-tables
component of the memory domain takes as its input. The code belongs to the
kernel at EL1 and runs on the boot CPU before the secondary CPUs start. It
reads byte slices and values, never an address, and it allocates, maps and
changes nothing. It does not apply overlays, resolve aliases or `phandle`
references, or read the bindings of the Pi 5 devices, which the components
that use them read through its node access. On QEMU virt the boot wiring
of the board reads the tree that QEMU's loader places at the start of RAM
and builds the boot memory map from it, with the image and the tree as boot
storage, in the default image and in the test images of the memory cases;
the Pi 5 board crate, which reads the hand-over tree of the firmware, is
planned.

## Interface

- **Entries.** The `pub` items of `krepi_kernel::fdt`, which the
  [entry table of the contract](../../domains/boot-platform/fdt/contract.md#entry-points)
  lists with their callers:
  - the parse `Fdt::parse(&[u8])`, which returns the tree `Fdt`, a view of
    the bytes, or an `Error`; `Fdt::total_size`, `reservations`, `nodes`
    and `find_node(path)`; and, of a `Node`, `name`, `parent`, `property`,
    `string_property`, `enabled`, `address_cells`, `size_cells`, `reg`,
    `ranges`, `dma_ranges` and `translate_reg`;
  - the translation `cells_u64`, `Reg::new` and `AddressMap::new`, `kind`,
    `to_parent` and `to_child`;
  - the memory discovery `Fdt::discover_memory`, whose `MemoryMap` gives
    `ram`, `reserved` and `dynamic`, and the boot memory of a hand-over
    tree `Fdt::discover_boot_memory(hand_over, dtb_address, image)`, which
    checks the tree against the `HandOverProfile` of its board and whose
    `BootMemory` gives the same with `dtb`, `image`, `ram_bytes`,
    `is_available` and `find_available`;
  - the CPU nodes `Fdt::discover_cpus(profile)`, against the `CpuProfile`
    of the board with its `PsciConduit`, `AffinityLevel` and
    `TimerInterrupts`, whose `CpuTopology` gives `count`, `profile`,
    `affinity` and `validate_timers`, and of a `CpuProfile`, `logical_id`,
    `affinity_shift` and `conduit`;
  - the boot memory map `MemoryPlan::all_ram`, `new` and
    `from_boot_memory`, which return a `MemoryPlan` or a `PlanError`, with
    the queries `managed_banks`, `ram`, `reservations`, `boot_ranges`,
    `firmware_ranges`, `described_bytes`, `managed_bytes`, `contains_ram`,
    `is_available`, `permits_backing` and `available_ranges`;
  - `Span::new`, `end` and `contains`, and the limits `MAX_BLOB_SIZE`,
    `MAX_DEPTH`, `MAX_TOKENS`, `MAX_PROPERTIES`, `MAX_PROPERTY_NAME`,
    `MAX_RESERVATIONS`, `MAX_MEMORY_REGIONS` and `MAX_RESERVED_REGIONS`.

  The boards differ in the profiles that they give these entries, not in
  the entries.
- **Iterators.** `Nodes`, `Reservations`, `Reg` and `AvailableRanges`,
  which `Fdt::nodes`, `Fdt::reservations`, `Node::reg` and `Reg::new`, and
  `MemoryPlan::available_ranges` return, give their items through an
  inherent `next(&mut self)`, which never fails.
- **Boot wiring.** On QEMU virt, `image::device_tree` of the default image
  forms the slice of the tree at `0x4000_0000`, first of its 40-byte header
  and then of its `totalsize`, at most 2 MiB, and
  `krepi_qemu_virt::boot_memory::wire` parses it and builds the boot memory
  map with `Fdt::discover_memory` and `MemoryPlan::all_ram`, the image and
  then the tree as boot storage.
- **Host tests.** `cargo test --locked --manifest-path kernel/Cargo.toml
  -p krepi-kernel` runs the tests of the module. With
  `KREPI_VECTOR_RESULTS` set to a directory, the results test writes the
  outputs of the frozen vectors to `boot-platform/fdt.results` below it
  ([host results](../../formal-verification.md#host-results)). The two
  ignored tests of the trees that the Raspberry Pi firmware ships read their
  files from the directories that `KREPI_PI5_SOURCE_DTB_DIR` and
  `KREPI_PI5_VALIDATED_DTB_DIR` name.

## Semantics

- **Untrusted input.** Every entry checks its input before it returns, and
  a rejected input gives one `Error` or `PlanError`, the error of the first
  broken rule in the
  [error orders](../../domains/boot-platform/fdt/contract.md#rejection-and-error-priority),
  and no partial value. No byte string makes an entry panic or read outside
  the slice.
- **Bounds.** A tree is at most 2 MiB, and a Pi 5 hand-over tree at most
  128 KiB; a node lies at most 31 below the root; the structure block holds
  at most 65,536 tokens, a node at most 512 properties, a property name at
  most 64 bytes and the reservation map at most 128 entries; a discovery
  gives at most 32 RAM ranges and 128 reserved regions; and the boot memory
  map holds at most 32 banks of 16 GiB together, 4 spans of boot storage
  and 128 firmware reservations. Each entry ends within the loop bounds of
  the [contract](../../domains/boot-platform/fdt/contract.md#work-bounds)
  and waits for nothing.
- **Ownership.** A tree and its nodes and iterators borrow the bytes, which
  stay unchanged while they live, and copy none of them; the other values
  are plain values that no entry changes once it has returned them. The
  boot CPU builds them; the boot memory map and the CPU topology are
  published once, before the secondary CPUs start
  ([state fields](../../domains/boot-platform/fdt/contract.md#state-fields)).
- **Reservations.** A dynamic reservation, a child of `/reserved-memory`
  with a `size` and no `reg`, is counted and is neither a reserved region
  nor a reason to reject the tree; the kernel allocates no pool for it.
- **Boot memory map.** The boot storage and the firmware reservations are
  rounded outward to whole 4 KiB pages; the usable ranges leave out every
  such page, `reusable` reservations included, and never bridge two banks
  or a hole.
- **Determinism.** The results are functions of the bytes and the
  arguments: no entry reads the seeds that QEMU writes into `/chosen`.
- **Undefined.** Nothing: every byte string and every argument has a result
  or an error.

## Examples

### ex1: The RAM of a QEMU virt tree

A tree of the shape that QEMU virt hands over, a root of 2 address cells
and 2 size cells with the node `memory@40000000` of `reg`
`0x4000_0000+0x800_0000`, parses, and its memory discovery gives the one
RAM range `0x4000_0000+0x800_0000`, no reserved region and no dynamic
reservation.

### ex2: A truncated tree is rejected

A tree cut one byte short of its `totalsize`, and its first 39 bytes, both
fail the parse with `Truncated`, and no tree is returned. This is the
rejected input of the feature.

### ex3: A dynamic reservation is counted and not reserved

A `/reserved-memory` of 2 and 2 cells with an empty `ranges` whose child
`linux,cma` has a `size` of one cell, `reusable` and no `reg` is accepted:
the discovery gives no reserved region and 1 dynamic reservation.

### ex4: The boot memory map of the Pi 5 8 GB model

A Pi 5 hand-over tree with the three RAM ranges of the 8 GB model,
`0x0+0x3fc0_0000`, `0x4000_0000+0xc000_0000` and
`0x1_0000_0000+0x1_0000_0000`, and `atf@0`, `0x0+0x8_0000/no-map`, at the
address `0x20_0000` and with the image `0x8_0000+0x2_0000`, gives
`ram_bytes` of 8 GiB less 4 MiB. `MemoryPlan::all_ram` with the image and
the tree as boot storage and the reserved region as a firmware reservation
gives the usable ranges `0xa_0000+0x16_0000`, `0x20_1000+0x3f9f_f000`,
`0x4000_0000+0xc000_0000` and `0x1_0000_0000+0x1_0000_0000`: the hole at
`0x3fc0_0000` lies in no bank, and the pages of `atf@0`, of the image and
of the tree are not available.

### ex5: A device address is translated through a bus

A node `/soc@107c000000` of 1 and 1 cells with the `ranges` window from
child 0 to parent `0x10_7c00_0000` of size `0x400_0000` holds
`serial@1001000` of `reg` `0x100_1000+0x200`: `translate_reg` gives
`0x10_7d00_1000+0x200`, and the request `0x3ff_ff00+0x200`, which the
window holds only in part, fails with `Unmapped`.

### ex6: The CPU topology of the Pi 5

A `/cpus` of 1 and 0 cells with four Cortex-A76 nodes of the IDs `0`,
`0x100`, `0x200` and `0x300` and the `enable-method` `psci`, and a `/psci`
with the `method` `smc`, gives for the Pi 5 profile 4 CPUs, the affinity
`0x200` for CPU 2 and none for the index 4; `logical_id` of `0x8100_0200`
is 2, since the flag bits of `MPIDR_EL1` change no logical ID. The same
tree fails for the QEMU virt profile with PSCI over HVC with `BadProperty`.

### ex7: Seeds in the chosen node change no result

Two QEMU virt trees that differ only in the `rng-seed` and `kaslr-seed` of
`/chosen` give the same RAM ranges, reserved regions and dynamic
reservations, and, with the tree at the start of RAM and the image at
`0x4020_0000+0x10_0000` as boot storage, the same usable ranges
`0x4000_1000+0x1f_f000` and `0x4030_0000+0x7d0_0000`.

## Design

- The parse checks the header, the blocks, the reservation map and every
  token once, and the tree it returns is a view of the checked bytes, so
  that the node access reads the checked structure block without checking
  it again and no entry copies or allocates. Every table of a result has a
  fixed capacity, a limit of the contract.
- The error orders are those of the prototype tree, so that an input that
  breaks several rules gives the error of the first, and every entry fails
  closed: it fills a local value while it checks and returns it only when
  every rule holds.
- The code follows the
  [provable Rust subset](../../conventions/provable-subset.md) in the code
  shapes of the [proof path](../../domains/boot-platform/fdt/proof.md):
  words are put together from single bytes, names and strings are checked
  and compared as bytes, a function holds at most one loop, every loop
  walks slices of plain data and scalars, the views of a tree are taken by
  value, and each iterator implements `next` alone, without the `Iterator`
  trait, whose provided methods have no model. Every type that an entry
  names is defined in `kernel/src/fdt.rs`, so that the roots of the proof
  target name it there, and the types whose values keep an invariant have
  private fields.
- The boot memory map rounds every exclusion outward to whole pages, keeps
  adjacent banks apart and sorts the banks by their start, so that the
  page-tables component never maps or hands out a page that boot storage or
  firmware uses.
- On several CPUs: the values are built on the boot CPU and never changed,
  and the boot memory map and the CPU topology are published once before
  the first secondary CPU starts.
- Excluded: overlays, aliases and `phandle` resolution, a pool for a dynamic
  reservation, device bindings, and any read of the tree through an address.

## References

- devicetree.org, *Devicetree Specification*, release v0.4, 2023,
  <https://github.com/devicetree-org/devicetree-specification/releases/download/v0.4/devicetree-specification-v0.4.pdf>.
- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  `MPIDR_EL1`.
- Arm Limited, *Arm Power State Coordination Interface*, DEN 0022.
- Raspberry Pi Ltd, *Raspberry Pi 5 Product Brief*,
  <https://datasheets.raspberrypi.com/rpi5/raspberry-pi-5-product-brief.pdf>.
- The QEMU Project, QEMU 8.2.2, `hw/arm/virt.c`,
  <https://gitlab.com/qemu-project/qemu/-/blob/v8.2.2/hw/arm/virt.c>.
- The [references of the contract](../../domains/boot-platform/fdt/contract.md#references),
  which name the sections, files and commits that its rules rely on.

## Implementation

- `kernel/src/fdt.rs`: the module root, with the types of the entries, the
  two error enums, the limits and `cells_u64`.
- `kernel/src/fdt/format.rs`: the header constants, the words read from
  bytes, the character sets of names and the padding.
- `kernel/src/fdt/span.rs`: `Span::new`, `end` and `contains`, and the
  comparisons of spans at their exact ends that the other files share.
- `kernel/src/fdt/parser.rs`: `Fdt::parse`, `total_size` and
  `reservations`, with the checked walk of the tokens.
- `kernel/src/fdt/nodes.rs`: `Fdt::nodes` and `find_node`, the `next` of
  `Nodes` and of `Reservations`, and the entries of `Node`.
- `kernel/src/fdt/translation.rs`: the cells, `Reg` with its `next`, and
  `AddressMap`.
- `kernel/src/fdt/discovery.rs`: `Fdt::discover_memory` and `MemoryMap`.
- `kernel/src/fdt/cpus.rs`: `Fdt::discover_cpus`, `CpuTopology` and
  `CpuProfile`.
- `kernel/src/fdt/hand_over.rs` and `kernel/src/fdt/hand_over/selection.rs`:
  `Fdt::discover_boot_memory`, `BootMemory` and `find_available`.
- `kernel/src/fdt/plan.rs` and `kernel/src/fdt/plan/available.rs`:
  `MemoryPlan` with its entries and queries, and the `next` of
  `AvailableRanges`.
- `kernel/boards/qemu-virt/src/main.rs`: `image::device_tree`, the slice of
  the tree that QEMU's loader places at the start of RAM.
- `kernel/boards/qemu-virt/src/boot_memory.rs`: the parse of the tree and
  the boot memory map of the boot wiring, `memory_plan` with the boot
  storage of the image and the tree, written once into a static of the
  board.

## Verification

- **Host.** The tests of the module run in the `test` and `test-release`
  steps of `cargo xtask check`: every frozen vector of the
  [contract](../../domains/boot-platform/fdt/contract.md#legacy-test-vectors)
  that the component holds, with its expected output; each limit at the
  limit and 1 above; the errors that no vector gives; for each step of the
  two error orders, an input that breaks it and a later one; dynamic
  reservations; the five RAM models of the Pi 5; the examples above; and
  the results test, which compares every output of the vector file with its
  expected output. They establish the rules on trees that the tests build,
  not on the trees that a board hands over. The two ignored tests of the
  firmware trees need files outside the repository and do not run in CI.
- **Compile-time guards.** The `subset` step of `cargo xtask check` builds
  the two compile-fail cases below `kernel/compile-fail/`: a tree built
  without the parse, which the private fields refuse, and a byte of the
  input written while a tree lives, which the borrow refuses.
- **QEMU and board.** The case `boot-memory` of the QEMU boot suite, which
  `cargo xtask qemu-boot` runs after the check in the `check` workflow of
  CI and the suite `qemu-boot` of `cargo xtask suite` runs from the images
  of the image job, boots its test image three times in release on QEMU
  virt, `virt-8.2` with one Cortex-A76 and 128 MiB, each in a new QEMU
  process with a tree that holds new seeds in `/chosen`. Each transcript
  holds the `totalsize` of the tree and the numbers of RAM banks, firmware
  reservations, spans of boot storage, managed banks and usable ranges of
  the boot memory map, which equal those that the suite computes from the
  contract, the runner's RAM and the size of the tree that QEMU dumps for
  the machine, and the three transcripts are identical. The case
  `kernel-memory` reads and writes the edges of the usable ranges of the
  map. They establish the parse and the boot memory map of the tree that
  QEMU hands over, and that the seeds reach no result, on QEMU virt; they
  establish nothing for a Pi 5 tree, which a board run checks.
- **Proofs.** None of the code. The proof target `fdt` is registered as
  planned in `verification/targets.json`, with the roots that the
  [proof path](../../domains/boot-platform/fdt/proof.md) names; it is
  extracted and type-checked when a run names it, and its refinement proofs
  are planned. The statements of the specification are about the
  specification, not the code. The results that the host tests write are
  not yet compared with the replay of the specification.
- **Unverified.** The hand-over trees of the 1, 2, 4 and 16 GB models,
  which the tests take from the ranges that the contract infers, and the
  tree that a Raspberry Pi 5 hands over at boot; the trees of a QEMU other
  than the one that the case runs, whose size the suite takes from that
  QEMU.

## Limitations

- QEMU virt only: the Pi 5 board crate, with its reading of the hand-over
  tree, is planned.
- RAM above 16 GiB in all, a tree above 2 MiB and a Pi 5 hand-over tree
  above 128 KiB are not supported.
- Overlays, aliases, abbreviated paths and `phandle` references are not
  resolved, and PCI addresses of three cells are not translated.
- A dynamic reservation is recorded, not allocated.
