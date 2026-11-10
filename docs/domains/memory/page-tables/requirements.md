---
features: none
---

# Page-tables requirements

The observable behaviour of the `page-tables` component of the
[memory and address spaces](../README.md) domain. The rules that its code
and tests follow are in the [contract](contract.md). No feature document
covers the component, so the metadata lists none.

## Sources

- The descriptors and kinds, the table sets with their pools, the mapping
  of pages and blocks, the direct map and the page ownership table take the
  rules of the prototype's page tables, page allocator and construction of
  the direct map, which the [references](contract.md#references) of the
  contract list, with their host tests as the frozen
  [vectors](contract.md#legacy-test-vectors).
- The write plans, the kernel's lower mappings from a layout, the one-step
  allocation without a callback, the exclusion records of the page
  ownership table and the counts of the five Raspberry Pi 5 models are
  new; the [behaviour changes](contract.md#legacy-test-vectors)
  of the contract list where they differ from the prototype.
- The descriptor formats, the memory attributes, the barriers and the TLB
  maintenance follow the Arm Architecture Reference Manual; the exclusion
  of `no-map` reservations follows the Devicetree Specification; the order
  of publication follows the
  [SMP design rules](../../../conventions/smp.md#page-tables-and-published-data).

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host.
- **Raspberry Pi 5.** The models with 1, 2, 4, 8 and 16 GB of RAM, each with
  its four Cortex-A76 cores of which one runs. Only the 8 GB model is run on
  a board in release 0.1, with the bank shape that the prototype measured;
  the other four are verified by host tests with the bank shapes that the
  [fdt contract](../../boot-platform/fdt/contract.md#memory-discovery)
  infers from that measurement, and are not run on a board.
- **Host.** The host tests of the module `page_tables` of the core (planned)
  run on the development host and in CI, with the frozen vectors and the
  tests that the [contract](contract.md#testing-obligations) adds.
- One CPU: no requirement here covers secondary CPUs or the acknowledgement
  of TLB invalidation across CPUs.

## Requirements

### PGT-R01

**Descriptor kinds.** Every leaf that the component writes has one of the
nine kinds of the [contract](contract.md#descriptors-and-attributes), with
exactly the AP, PXN, UXN, AttrIndx, SH, nG and AF bits of its row and its
output address in bits 12 to 47, and every other bit 0. No kind is writable
and executable; the kernel kinds give EL0 no access and are global except
`KernelPrivateReadWrite`; the user kinds are tagged with the ASID and never
execute at EL1; `Device` and `UserDevice` use AttrIndx 0. The criterion: the
descriptor of every kind equals the bits of its row, written from the Arm
Architecture Reference Manual, and the frozen vectors that read descriptor
bits hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `page_tables::Kind`, `page_tables::descriptor` and
  `Tables::lookup_page` and `lookup_block` (planned).
- **Contract.** [Descriptors and attributes](contract.md#descriptors-and-attributes).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `pt-01`, `pt-02`, `pt-06`, `pt-11`,
  `pt-15` and `pt-21` as host tests of the module `page_tables` (planned),
  and a host test of each row of the kind table against bits written from
  the manual. They show the encoding on the host; they do not show that a
  CPU translates and checks permissions as the bits say, which PGT-R05 and
  PGT-R06 show on QEMU virt.

### PGT-R02

**Mapping and looking up a page.** `map_page` maps a page of the region of
its set to a physical page with a kind, and afterwards `lookup_page` gives
that descriptor. It refuses a misaligned address or base, an address outside
the region, a physical address beyond the width, a pool outside the width,
an address that a page or a block already maps and a map that needs more
tables than the pool has free, each with the error of the
[contract](contract.md#errors-of-table-sets) in its order, and a refused
call changes no table and uses no table. A lower set refuses the addresses
of the upper region and the other way round. The criterion: the frozen
vectors hold, with the tables and the count of tables in use unchanged
after every refusal.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::new`, `map_page`, `lookup_page` and `used`
  (planned).
- **Contract.** [Abstract mapping](contract.md#abstract-mapping),
  [Write plans and publication](contract.md#write-plans-and-publication)
  and [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `pt-01`, `pt-03`, `pt-04`, `pt-05`,
  `pt-13` and `pt-14` as host tests. They show the logic on a pool in host
  memory; they do not show a CPU walking the tables.

### PGT-R03

**Blocks.** `map_block` maps a 2 MiB-aligned virtual address to a 2 MiB
physical block as `ReadWrite` with one level 2 descriptor; it never turns a
level 3 table into a block, nor a block into pages, and a page of a block
can be neither unmapped nor mapped again as a page. Contiguous 8 GiB of
blocks from address 0 use 9 tables, across the 1 GiB and 4 GiB boundaries.
The criterion: the frozen vectors hold, among them 4,096 blocks in a pool
of 9 tables and the refusal of one more with `OutOfTables`.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `map_block`, `lookup_block`, `unmap_page`, `map_page`
  and `used` (planned).
- **Contract.** [Abstract mapping](contract.md#abstract-mapping) and
  [Kernel direct map](contract.md#kernel-direct-map).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `pt-15`, `pt-16` and `pt-17` as host
  tests. They build the descriptors of 8 GiB without touching 8 GiB of RAM.

### PGT-R04

**Unmapping and reset.** `unmap_page` removes one page leaf and returns its
physical page; its plan stores the invalid entry and then invalidates the
TLB entries of the address, and the tables under it stay in the pool. It
refuses an address without a page leaf with `NotMapped`. `reset` leaves the
root alone in use with every entry 0. No entry removes or changes a valid
entry of the kernel tables. The criterion: the frozen vectors hold, and the
plan of `unmap_page` equals the order of the contract.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `unmap_page`, `reset`, `map_page` and `lookup_page`
  (planned).
- **Contract.** [Abstract mapping](contract.md#abstract-mapping) and
  [Write plans and publication](contract.md#write-plans-and-publication).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `pt-05`, `pt-09` and `pt-11` as host
  tests, and the host test of the plans of the
  [contract](contract.md#testing-obligations). They show the logic and the
  order of the steps; they do not show the invalidation on a CPU, which the
  QEMU case of break-before-make of the boot component shows for its
  primitive ([BOOT-R13](../../boot-platform/boot/requirements.md#boot-r13)).

### PGT-R05

**Kernel direct map.** The direct map maps every page of every usable
range of the boot memory map at `DIRECT_BASE | pa`, as `ReadWrite`: global,
EL1 read and write, execute-never and no EL0 access, with a 2 MiB block
wherever an aligned 2 MiB lies in one usable range and 4 KiB pages
elsewhere. No page of a firmware reservation, `no-map` or not, of the image,
of the device tree, of the boot bundle or of another boot storage, no hole
between banks and no RAM outside the managed banks has a direct address. A
map that needs more tables than the pool has, or a range beyond $2^{39}$,
fails before any write. The criterion: on the 8 GB layout of the prototype,
every page below 8 GiB is mapped to itself or absent exactly as an
independent page model says, with `0x1ffbfe000` bytes; the four other Pi 5
models give the counts of tables, blocks and pages of the
[contract](contract.md#table-pool); on QEMU virt with the MMU on, the edges
of the mapped and the excluded ranges behave as the map says.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `page_tables::direct_map`, `direct_address`,
  `lookup_page`, `lookup_block` and `used`, and `krepi_arch::mmu::apply` and
  `enable` (planned).
- **Contract.** [Kernel direct map](contract.md#kernel-direct-map),
  [Table pool](contract.md#table-pool) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `dm-01` to `dm-04` as host tests, `dm-04`
  for the 8 GB model; the host tests of the 1, 2, 4 and 16 GB models and of
  the pool at capacity of the [contract](contract.md#testing-obligations);
  the QEMU tests of the edges of the direct map, and three cold boots with
  the same counts. On the Pi 5, the board runs of the 8 GB model build the
  map of the whole RAM. The host tests do not show a CPU translating; the
  other four models are shown on the host only, from inferred bank shapes.

### PGT-R06

**Kernel mappings of the image.** `kernel_map` maps the image at its
physical addresses in the lower region: its text `ReadExecute`, its
read-only data `ReadOnly`, its data, BSS and stacks `ReadWrite`, the device
tree `ReadOnly` where the board maps it, and the registers of the console
and the interrupt controller `Device`, with the page below each stack left
invalid as a guard. It refuses a layout whose ranges do not start and end on
page boundaries, share a page or cover a guard, so that no page has two
kinds and no page is mapped writable and executable. The criterion: on QEMU
virt with the MMU on, a write to a `ReadOnly` page, an execution from an
execute-never page and an access to the guard each take the fault of the
contract, and a `Device` page of the console is written; on the host, a
layout whose text and data share a page is refused.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `page_tables::kernel_map`, and `krepi_arch::mmu::apply`
  and `enable` (planned).
- **Contract.** [Kernel mappings](contract.md#kernel-mappings) and
  [Descriptors and attributes](contract.md#descriptors-and-attributes).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The QEMU tests and the host test of a shared page of the
  [contract](contract.md#testing-obligations). They show the permissions
  of the kernel's own mappings on QEMU virt with one CPU; they do not show
  the mappings of a process.

### PGT-R07

**Write plans and publication.** Every entry that changes a table returns a
write plan whose steps `krepi_arch::mmu::apply` executes in order: a new
table is zeroed and filled before one store of its table descriptor makes it
reachable, with `DMB ISHST` before that store; a plan that makes an entry
valid ends with `DSB ISH` and `ISB`; the plan of an unmap stores the invalid
entry and then invalidates the address with the broadcast TLB invalidation
and its barriers; a plan for the kernel tables writes only invalid entries.
No plan step fails. The criterion: the plans of `map_page`, `map_block`,
`unmap_page`, `clone_kernel_from`, `kernel_map` and `direct_map` equal the
order of the contract, written from it.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `map_page`, `map_block`, `unmap_page`,
  `clone_kernel_from`, `kernel_map`, `direct_map` and
  `krepi_arch::mmu::apply` (planned).
- **Contract.** [Write plans and publication](contract.md#write-plans-and-publication).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path; the stores, the
  barriers and the register writes are
  [open obligations](contract.md#open-obligations).
- **Evidence.** The host tests of the plans; the QEMU tests of PGT-R05 and
  PGT-R06, which run with the tables that the plans built. They show the
  order of the steps and that the tables work on one CPU of QEMU virt; they
  do not show the ordering that the barriers give on several CPUs.

### PGT-R08

**One owner for every page.** The page ownership table gives every managed
page exactly one owner: free, firmware, image, boot storage or one holder.
At initialization an exclusion removes every page that it touches, rounded
out to whole pages within each bank, and a page that no exclusion touches is
free; the banks never merge, also when they are adjacent, so no range of a
holder spans two banks. The table refuses no bank, overlapping or
misaligned banks, the arena 0 and more extents than its capacity. The
criterion: for the boot memory map of every board shape, every managed page
has exactly one owner, the free pages are exactly the pages of the direct
map, and the frozen vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Ownership::new`, `owner` and `stats` (planned).
- **Contract.** [Page ownership](contract.md#page-ownership).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `own-03`, `own-04`, `own-05`, `own-17`,
  `own-18`, `own-19`, `own-21` and `own-22` as host tests, with the
  independent page model of `own-22`, and the host test of each board shape
  of the [contract](contract.md#testing-obligations). They show the
  bookkeeping; they do not show the contents of RAM.

### PGT-R09

**Allocation and release.** An allocation chooses a free range of whole
pages in one bank at the requested alignment, the lowest for a low
placement and the highest for a high one, inside the caller's window; the
caller zeroes it through the direct map, and only then is it assigned to its
owner with a new generation, which is never reused. A failed zeroing leaves
the pages free. A release returns the pages to free only with the receipt
of their arena, owner and generation, so a release by another owner, at
another arena, twice or with a stale receipt is refused, with the errors of
the [contract](contract.md#page-ownership), and changes nothing. The
criterion: the frozen vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Ownership::choose`, `assign`, `release`, `validate`
  and `stats`, and `krepi_arch::mmu::zero_frames` (planned).
- **Contract.** [Page ownership](contract.md#page-ownership) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `own-01`, `own-06` to `own-11`, `own-16`,
  `own-18`, `own-20`, `own-21` and `own-22` as host tests. They model the
  zeroing by the test; the QEMU and board runs that allocate, write, release
  and allocate again read the zeroes back through the direct map.

### PGT-R10

**Staged reservation.** A reservation holds pages at once without zeroing
them; the holder zeroes them through the direct map and publishes them, and
only the publication gives a receipt. A failed zeroing keeps the
reservation, with its count of failures, for another attempt; a reservation
may be cancelled only before any attempt, and a dropped reservation or
packet keeps its pages held. Publication and cancel by another owner or at
another arena are refused and return the packet. The criterion: the frozen
vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Ownership::reserve`, `Reservation::initialized`,
  `Ownership::publish`, `cancel`, `validate`, `release` and `stats`
  (planned).
- **Contract.** [Page ownership](contract.md#page-ownership).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `own-23` to `own-28` as host tests. They
  show the bookkeeping of a reservation; they do not show the zeroing on a
  CPU.

### PGT-R11

**Capacities.** The capacities are constants of the core, sized for 16 GiB
of RAM: the pool of the direct map holds 80 tables, which leaves 61 free on
the inferred shape of the 16 GB model; the lower kernel set holds 16; the
page ownership table manages at most 16 GiB in at most 32 banks with at most
160 extents and 132 exclusions. A request beyond a capacity fails before any
write with `OutOfTables` or `MetadataExhausted`. The criterion: a direct map
that needs exactly 80 tables succeeds and one that needs 81 is refused; a
page ownership table at exactly 160 extents works and one more extent is
refused; an initialization with 132 exclusions succeeds and one with 133 is
refused.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `page_tables::direct_map`, `Ownership::new`, `choose`
  and `reserve` (planned).
- **Contract.** [Table pool](contract.md#table-pool) and
  [Page ownership](contract.md#page-ownership).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of the capacities of the
  [contract](contract.md#testing-obligations), and the frozen vectors
  `dm-03`, `own-05` and `own-08`.

### PGT-R12

**Copying the kernel tables.** `clone_kernel_from` gives a set that no CPU
uses a private copy of the lower kernel set: the same pages, kinds and
output addresses, global ones included, in tables of its own pool at the
indices of the source, so that a later write to one of the two sets leaves
the other unchanged. It refuses, before any write, pools that overlap, a
misaligned base, a width outside 32 to 48, a pool that ends above the
width, a source with a block, with a table descriptor that holds an
attribute bit, with a leaf of a kind other than `ReadExecute`, `ReadOnly`,
`ReadWrite` and `Device` or above the width, and a source whose table
descriptors do not reach its tables in use exactly once. The criterion:
the frozen vectors hold, and the plan of the copy equals the order of the
contract.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::clone_kernel_from`, `map_page`, `unmap_page`,
  `lookup_page` and `used` (planned).
- **Contract.** [Copying the kernel tables](contract.md#copying-the-kernel-tables),
  [Abstract mapping](contract.md#abstract-mapping) and
  [Write plans and publication](contract.md#write-plans-and-publication).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `pt-07`, `pt-08`, `pt-10`, `pt-12` and
  `pt-18` as host tests, and the host test of the plans of the
  [contract](contract.md#testing-obligations). They show the copy on sets
  that the tests build; they do not show a process running on the copy,
  which the tables of address spaces show.

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits or retries.
- The direct map is built once at boot, in a number of steps proportional to
  the RAM in 2 MiB blocks and the edges of its ranges; on the 8 GB model,
  4,092 blocks, 581 pages and 11 tables.
- No requirement bounds the time that a step takes.

## Scope

- One CPU. The acknowledgement of TLB invalidation by other CPUs, and the
  local form of `TLBI` that the record of an address space allows, are not
  covered.
- The address spaces of processes, their ASIDs and the switch of
  `TTBR0_EL1` are not covered, apart from the copy of the kernel's lower
  tables into the lower tables of a process (PGT-R12); neither are VM
  objects, the execute right or the authority to map device registers into
  a process.
- The direct map is never changed after boot: no page is sealed, split or
  merged.
- The kernel has no byte heap.
- The caches: the memory attributes and `SCTLR_EL1` follow the board's
  choice of the caches, and the maintenance at that change is the boot
  component's; the effect of the caches is shown only on the Pi 5.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Determinism](contract.md#determinism) and
  [State fields](contract.md#state-fields) bind the code without an
  observable behaviour of their own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
