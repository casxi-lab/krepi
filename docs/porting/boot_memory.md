---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/qemu/memory.rs
  - src/boot_memory.rs
  - src/mmu.rs
  - src/mmu/direct.rs
destination:
  - kernel/boards/qemu-virt/src/boot_memory.rs
  - kernel/boards/qemu-virt/src/boot_memory/tests.rs
  - kernel/boards/qemu-virt/src/main.rs
treatment: ported
features:
  - krepi.platform.device-tree
  - krepi.kernel.kernel-memory
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/boards/qemu-virt/src/boot_memory.rs

## Summary

The boot wiring of the QEMU virt board crate, the module `boot_memory`:
`wire` reads the device tree that QEMU's loader places at the start of
RAM, builds the boot memory map and the page ownership table of the kernel
root, executes the plans of the two kernel table sets of the image with the
adapter [mmu](mmu.md) of `krepi-arch` and turns the MMU on with the caches
off. It takes from `discover` of `src/board/qemu/memory.rs` the reading of
the tree: the slice of its 40-byte header, the bound of its `totalsize` at
2 MiB and the slice of the tree, which are `image::device_tree` of the
default image in `src/main.rs`, and `Fdt::parse`, `discover_memory` and
`MemoryPlan::all_ram` with the boot storage, which are in `wire`. It takes
from `src/boot_memory.rs` the boot information, the boot memory map written
once into a static before the MMU is on, and from its `verify_allocators`
the page allocator of the kernel root in arena 1 over the managed banks and
the reservations of the map, which is now the page ownership table. It
takes from `init_and_verify` of `src/mmu.rs` the layout of the image from
the link symbols `__text_start`, `__text_end`, `__rodata_start`,
`__rodata_end`, `__stack_guard`, `__stack_bottom` and `__image_end`, with
the kind of each part, the guard page below the stack left out, the pages
of the tree and the pages of the devices, and its order: the lower kernel
tables, the direct map, then the call that turns the MMU on; and from
`src/mmu/direct.rs` the upper set of 80 tables in a static of the image,
whose address is the root of `TTBR1_EL1`. The parts that compute the map,
the exclusions, the banks, the layout and the counts of a plan are plain
code with host tests; the statics and `wire` are compiled only for the
bare-metal target. The legacy areas `src/board` and `src/mmu` are ported,
as [porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies them; the area `src/boot_memory`, which that table does not
list, is ported too, as this first record that takes code from it
classifies it: its boot information is the board's wiring, and its probes
are left behind.

## Changes

- **The tree.** `image::device_tree` forms the slice of the 40-byte header
  at `TREE_BASE`, `0x4000_0000`, and then of `totalsize` bytes once that
  is from 40 to `fdt::MAX_BLOB_SIZE`, 2 MiB, so that the tree ends at or
  below the image, as the legacy `discover` did with its `DTB_LIMIT`; it
  panics with `device tree size out of bounds` in place of `DTB exceeds
  reserved boot window`. Its `unsafe` site is an open obligation of the
  [fdt contract](../domains/boot-platform/fdt/contract.md#open-obligations).
- **The boot memory map.** `wire` parses the tree, discovers its memory
  and gives `MemoryPlan::all_ram` two spans of boot storage, the image from
  `__text_start` to `__image_end` and then the tree of its `totalsize`, as
  the [fdt contract](../domains/boot-platform/fdt/contract.md) orders them,
  in place of the one span from the start of RAM to `__image_end`. So the
  RAM between the pages of the tree and the image is usable. A failure of
  the parse panics with `invalid device tree`, one of the discovery or the
  map with `boot memory map rejected`, in place of `invalid boot FDT`,
  `invalid FDT memory contract` and `invalid kernel memory plan`. The map
  refuses an image or a tree outside RAM, which the legacy
  `init_and_verify` asserted.
- **Written once.** The map is written into the static `MEMORY` and the
  page ownership table into `OWNERSHIP` by two private functions that are
  not inlined, so that the copies of the discovery and the temporaries of
  the table leave the stack before the next step. `wire` is an `unsafe fn`
  whose caller calls it once, on the boot CPU with every exception masked
  and the MMU off, in place of the atomic `READY` of the legacy
  `discover`, its assertion and `info`; it returns `Wired`, with the span
  of the tree, the link symbols, the physical address size, the counts of
  the two plans and the map, which the caller keeps.
- **The page ownership table.** `ownership(map)` gives
  `Ownership::new` the arena 1, the managed banks and the exclusions of
  the map: its first boot storage span as `Image`, the others as
  `BootStorage` and the firmware reservations as `Firmware`, each a
  `PhysRange` of the page-rounded span of the map. The legacy
  `verify_allocators` built a page allocator of 160 extents in arena 1 over
  the managed banks and the reservations and exercised it; the wiring
  builds the table and allocates nothing.
- **The kernel tables.** The lower kernel set holds 32 tables and the
  direct map 80, the capacities of the
  [table pool](../domains/memory/page-tables/contract.md#table-pool), in
  place of the 80 tables of the legacy lower set; each is a static of the
  image in a `#[repr(C, align(4096))]` wrapper, so that the address of the
  static is the address of the pool, initialized by `Tables::new` and so in
  the data of the image. The export names of the legacy statics for the
  feature profiles are left out. `wire` exposes the provenance of each
  static, forms the only references to the sets and the handles of their
  pools once, and executes the plan of `kernel_map` with the layout and
  that of `direct_map` with the map, each wrapped in `Counted`, by one
  `mmu::apply` each, then calls `mmu::enable` with their roots, the
  physical address size of `mmu::physical_width` and the caches off. A
  refused layout or map panics with `kernel tables rejected`; an
  unsupported size with `unsupported physical address size`.
- **The layout.** `layout` maps the text `ReadExecute`, the read-only data
  `ReadOnly`, the data and BSS up to the guard and the stack from its
  bottom to the end of the image `ReadWrite`, the pages of the tree
  `ReadOnly` and the page of the PL011 and the 128 KiB from the distributor
  to the end of the CPU interface of the GICv2 `Device`, from the
  constants of the board, with the guard page left out. The legacy code
  mapped each page of its one boot range in place, with `ReadOnly` for the
  pages of that range outside the image, and the device windows of its
  `Devices`. The parts of the image come from the link symbols; their
  order and the one guard page are those of the link script.
- **Counts.** `Counts` counts the steps of a plan: the root and one table
  for each `Zero`, a block for each store of a block descriptor and a page
  for each store of a page descriptor; `Counted` passes the steps of a plan
  on unchanged and counts them. The test image of `boot-memory` writes
  them ([qemu-virt](qemu-virt.md)).
- **Checks.** `wire` asserts that the MMU is off (`MMU must be off`); the
  initialization checks of the image have checked the caches off and the
  rest of the state before. The read of `DAIF` with the assertion of masked
  interrupts is the caller's obligation.
- **Annotations.** The module documentation names the features
  `krepi.platform.device-tree`, `krepi.kernel.kernel-memory` and
  `krepi.platform.qemu-virt-boot`, in place of the legacy annotation
  `system.kernel.memory`.

## Tests carried over

None: the legacy files held no host tests. The new tests of
`boot_memory::tests` hold the boot storage and the usable ranges of a map
of the runner's RAM, the exclusions and the bank, the layout and a refused
empty part of the image, and the counts of the plans of the two sets
against the formulas of the
[table pool](../domains/memory/page-tables/contract.md#table-pool),
written from the contract.

## Behaviour changes

| Change | Evidence |
| --- | --- |
| The boot storage is the image and then the tree, so the RAM between the pages of the tree and the image is usable and in the direct map | `boot_memory::tests::the_boot_storage_is_the_image_and_then_the_tree`; the case `boot-memory` of `cargo xtask qemu-boot`, whose counts give two spans of boot storage and two usable ranges, and the case `kernel-memory`, which reads and writes the first page after the tree |
| The lower kernel set maps only the image, the tree and the device frames, with the kinds of the layout and no guard page, in 32 tables | `boot_memory::tests::the_layout_maps_the_image_the_tree_and_the_devices`, `boot_memory::tests::an_empty_part_of_the_image_is_refused`, `boot_memory::tests::the_lower_kernel_set_has_the_tables_and_pages_of_the_contract`; the case `kernel-memory`, whose faults show the read-only data, the guard and the excluded pages |
| The direct map has the tables, blocks and pages of the contract for the map | `boot_memory::tests::the_direct_map_has_the_tables_blocks_and_pages_of_the_contract`; the case `boot-memory` |
| The page ownership table of the kernel root is built at boot with the exclusions of the image, the tree and the firmware, and no allocation is made | `boot_memory::tests::the_exclusions_name_the_image_the_tree_and_the_firmware` |
| The tables are written by the steps of the plans, which the counts see unchanged | `boot_memory::tests::a_counted_plan_passes_its_steps_on_unchanged`, `boot_memory::tests::counts_classify_the_steps` |
| A failure of the wiring panics with one of its static messages, without the records of the legacy checks; the default image writes no record of the wiring | The case `cold-boot-echo`, whose transcript holds only the boot records and the echo; no test takes the panics |

## Hardware evidence to re-obtain

- On QEMU virt, `virt-8.2` with one Cortex-A76 and 128 MiB: the boot
  memory map, the page ownership table, the two kernel sets and the MMU on
  with the caches off, in the default image, the case `cold-boot-echo`;
  the counts at three cold boots, the case `boot-memory`; and the edges of
  the direct map, the faults of the layout and the `Device` console, the
  case `kernel-memory`; all of `cargo xtask qemu-boot`, in CI.
- On a Raspberry Pi 5 of 8 GB, with the board support of that board
  (planned): the tree that the firmware hands over, its boot memory map and
  the kernel tables of the whole RAM, with the firmware, EEPROM and BL31
  versions of the bench.

## Not carried over

- From `src/board/qemu/memory.rs`: the check of a RAM range of at least
  128 MiB at the start of RAM, as the runner gives the machine that RAM and
  the map refuses boot storage outside it; the checks of the nodes of the
  CPU, the PL011, the GICv2 and the timer, with the interrupt parent and the
  timer interrupts, and the device windows of `Devices`, as the board's
  addresses are its constants; the slots of `virtio-block`, a feature
  profile; the high page at 4 GiB; and the record `CASXI_FDT`.
- From `src/boot_memory.rs`: `BootInfo` with its devices, its high page and
  its fields of the feature profiles; `READY`, `info` and the assertion of
  `discover`, which the caller's obligation to call `wire` once replaces;
  `zero`, the zeroing callback of the allocators, which the page ownership
  table does not take ([page_tables-ownership](page_tables-ownership.md));
  and `verify_allocators` with its allocation probes and the record
  `CASXI_MEMORY` of its own form, which the host tests of the page ownership
  table cover; its call of the probes of `banks` is in
  [qemu-virt](qemu-virt.md).
- From `src/mmu.rs`: the static of the lower tables with its export name
  and `TABLE_CAPACITY`; the assertions of the image in RAM and in a boot
  range and of one guard page, which the map and the link script give; the
  probe pages, the diagnostic mappings at `HIGH_VA` and `REMAP_VA` with
  their remaps, and the map of the high page; the checks after the MMU is
  on, the translations of the reserved pages, of the image, of a probe page
  and of the devices, the denial of EL0 and the faults of the probes, which
  the case `kernel-memory` takes in its own form; the branches of the
  feature profiles; and the record `CASXI_MMU`.
- From `src/mmu/direct.rs`: `READY`, `prepare`'s assertion that the map is
  not empty, `require_root`, `verify` with `verify_page` and
  `verify_absent`, whose edges the case `kernel-memory` checks instead, and
  the record `CASXI_DIRECT`; `backing_address`, `protect_backing`,
  `verify_readonly_backing` and `backing_table_count`, which seal or name
  pages of the direct map after boot, which the contract does not do; and
  the export name of the static.
- The legacy feature annotation `system.kernel.memory`.
