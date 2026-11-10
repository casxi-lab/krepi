# Memory and address spaces

## Overview

The memory and address-spaces domain decides who owns each page of physical
RAM, how the kernel and every process see memory through the translation
tables, and when memory may change hands. It covers the ownership of
physical pages, the page tables with the kernel direct map, the ASIDs that
tag the translations of an address space, the VM objects and their kinds,
the access of the kernel to buffers of a process, W^X with the publication
of code, and the barriers that guard the reclamation of memory.

Three limits bound the domain. The translation regime is stage 1 of EL1&0
with 4 KiB granules: two regions of 39 bits, the lower one for the address
spaces of processes and the kernel's image, the upper one, 512 GiB from
`0xffffff8000000000`, for the kernel direct map; three levels of tables and
2 MiB blocks. The physical address size is the one that the CPU reports, 40
bits on the Cortex-A76 of QEMU virt and of the Raspberry Pi 5. The RAM is at
most 16 GiB in at most 32 banks, the largest Pi 5 model, and QEMU virt has
128 MiB in one bank. A result on QEMU virt with one CPU does not show the
behaviour of the caches, of relaxed memory or of several CPUs.

The domain builds on others, listed in the
[subject-domain index](../README.md). The boot and platform domain gives the
banks of RAM and the excluded ranges in the boot memory map of its fdt
component, and the cache and TLB maintenance of the executing CPU in its
boot component; the multicore domain acknowledges TLB invalidation across
CPUs; the devices and DMA domain decides which device registers a driver
may map and when DMA to a page has ended; the kernel objects and
capabilities domain holds the capabilities and quotas that name VM objects;
the security and lifecycle domain decides who may add the execute right.
The [page-tables](page-tables/requirements.md) component holds the
descriptors, the table sets, the kernel's own mappings, the direct map and
the page ownership table.

## Conventions

- **One owner per page.** Every managed page of RAM has exactly one owner at
  any time: free, firmware, the image, other boot storage, or one holder
  with its generation. Ownership changes only through the page ownership
  table.
- **Zero before handing out.** A page reaches a new holder only after its
  bytes are zero, and a receipt is published only after the zeroing has
  completed.
- **Write-once kernel mappings.** The kernel fills only invalid entries of
  its own tables and never changes or removes a valid one; the direct map is
  built once at boot.
- **Plans, not callbacks.** Code that changes a table computes the complete
  write plan before its first write, and the architecture crate executes the
  steps in order; no step fails.
- **W^X for every alias.** No frame is writable and executable at the same
  time, counting all its mappings in every address space.
- **Reuse after acknowledgement.** A page, a table or an ASID is reused
  only after every CPU and device that may still reach it has acknowledged
  that it no longer does.
- **Fixed capacities.** The pools of tables and the metadata of the page
  ownership table have capacities fixed at boot; a request beyond them fails
  before any write.

## Feature index

| Feature | Scope | Feature documents | Components |
| --- | --- | --- | --- |
| [Physical page ownership](#physical-page-ownership) | The owner of every managed page, allocation, staged reservation and release with receipts | - | [page-tables](page-tables/requirements.md) |
| [Page tables and the kernel direct map](#page-tables-and-the-kernel-direct-map) | Descriptors and kinds, table sets and their writes, the kernel's mappings of its image and devices, the direct map | - | [page-tables](page-tables/requirements.md) |
| [ASIDs](#asids) | The tags of the translations of an address space, their allocation and reuse | - | The ASID allocator of the address spaces |
| [VM objects and their kinds](#vm-objects-and-their-kinds) | Regions and VM objects, their kinds, commit and release, the mappings that are not VM objects | - | The VM of the core |
| [User-buffer access](#user-buffer-access) | How the kernel reads and writes memory that a process can write | - | The user copies of the kernel |
| [W^X and code publication](#wx-and-code-publication) | The rule against writable executable frames and the publication of code | - | [page-tables](page-tables/requirements.md) |
| [Reclamation barriers](#reclamation-barriers) | The acknowledgements that precede the reuse of pages, tables and ASIDs | - | The reclamation of address spaces and VM objects |

## Physical page ownership

**Description.** The page ownership table records the owner of every
managed page: a 4 KiB page that lies wholly in a managed bank of RAM. At
boot every page that a firmware reservation, the image or another boot
storage touches is theirs for good, and every other page is free. An
allocation takes a run of free pages in one bank, at a power-of-two
alignment, low or high and inside an optional window, and gives its owner a
receipt with a new generation; a staged reservation holds the pages first
and gives the receipt when the holder publishes them after zeroing; a
release returns them to free. A receipt names its arena, owner and
generation, so a release by another owner, at another table, twice or with
a stale receipt is refused and changes nothing. The table never reads or
writes a page and grants no authority: a receipt is bookkeeping.

**Design background.** The table keeps extents, runs of pages of one owner
in one bank, in fixed metadata, so that a bank of several GiB needs one
entry; a release merges a free extent with its free neighbours in the same
bank and never across banks, so no range spans a hole or two banks. The
generation is a counter that is never reused, so a stale receipt never
names a new allocation. The kernel does not allocate at run time beyond
these capacities, as seL4 hands out memory only from its untyped objects
(Klein et al. 2014).

**Consumers.** The VM objects of processes, which take zeroed pages on
commit; the pools that the kernel carves at boot from the capacity record;
the tables of the address spaces of processes.

**Interface.** `page_tables::Ownership` with `new`, `choose` and `assign`,
`reserve`, `publish`, `cancel` and `release`, `owner`, `validate` and
`stats`, and `page_tables::Reservation::initialized`
([entry points](page-tables/contract.md#entry-points)). Errors name the
broken rule: an invalid range, alignment or size, an overflow, the arena 0,
the capacity of the metadata, no free range, an exhausted generation, a
failed zeroing, and a receipt of another arena, of another owner or of no
held range. No result is a state; every failure is an error.

**Prerequisites.** [Physical memory ranges](../boot-platform/README.md#physical-memory-ranges)
of the boot and platform domain, which give the managed banks and the
exclusions; [Page tables and the kernel direct map](#page-tables-and-the-kernel-direct-map),
through which a page is zeroed; the
[page-tables contract](page-tables/contract.md#page-ownership).

**Engineering notes.** The table manages at most 16 GiB in at most 32
banks with 160 extents; at boot the 8 GB Pi 5 uses 4. A request that would
need more extents is passed over or refused before any write. The table is
shared state; its class and protection are in the
[State fields](page-tables/contract.md#state-fields) of the page-tables
contract.

**Verification.** Invariants: every managed page has exactly one owner; the
pages of one generation form one range in one bank; the free and held pages
of the kernel's table are exactly the pages of the direct map. Required
counterexamples: a release by a foreign owner or arena, a double and a stale
release, a request across adjacent banks, a cancel after a failed zeroing.
Environments: host tests against an independent sparse page model and the
frozen vectors of the prototype; QEMU and Pi 5 runs that write a page,
release it, allocate it to another owner and read zeroes back.

## Page tables and the kernel direct map

**Description.** A table set holds the tables of one region in a pool of
fixed capacity. Its writes map a page with one of nine kinds, map a 2 MiB
block, unmap a page and reset the set; each write is refused before any
change when an address is misaligned or outside the region or the width,
when the place holds a mapping or when the pool has too few tables, and
otherwise returns a write plan that the architecture crate executes. The
kernel's own tables are two sets: the lower one maps the image at its
physical addresses, with its text executable and read-only, its read-only
data read-only, its data and stacks writable and execute-never, a guard
below each stack, and the registers of the console and the interrupt
controller as Device memory; the upper one is the direct map, which maps
every page of the usable ranges of RAM at `0xffffff8000000000` plus its
physical address, read-write and execute-never for EL1 only, with blocks
where it can. The direct map leaves out the image, the device tree, the
boot bundle and every firmware reservation, `no-map` or not. The domain
does not change the direct map after boot.

**Design background.** The descriptors are those of the VMSAv8-64 format of
the Arm Architecture Reference Manual. The kernel writes its own mappings
once and publishes a new table only when it is complete, and an unmap is
followed by a broadcast TLB invalidation; these are three of the conditions
under which VRM shows that a kernel on relaxed-memory Armv8 behaves as on
sequentially consistent memory (Tao et al. 2021), and the table walker is
an observer of its own (Simner et al. 2022). The Devicetree Specification
forbids a mapping of a `no-map` region in the standard mapping of system
memory.

**Consumers.** The page ownership table, which zeroes pages through the
direct map; the VM objects and the address spaces of processes, which use
the table sets for their lower tables; every kernel path that reaches a
frame it owns.

**Interface.** `page_tables::Tables` with `new`, `reset`, `map_page`,
`map_block`, `unmap_page`, `lookup_page`, `lookup_block` and `used`,
`page_tables::kernel_map` and `page_tables::direct_map`, the kinds of
`page_tables::Kind` and `page_tables::direct_address`; in the architecture
crate, `krepi_arch::mmu::apply` and `enable`
([entry points](page-tables/contract.md#entry-points)). Errors name a
misaligned address, an address outside the region or the width, a bad pool,
too few tables, a place that holds a mapping and an address without a leaf.

**Prerequisites.** [Physical memory ranges](../boot-platform/README.md#physical-memory-ranges)
and [Cache and TLB maintenance](../boot-platform/README.md#cache-and-tlb-maintenance)
of the boot and platform domain; the
[page-tables contract](page-tables/contract.md#kernel-direct-map).

**Engineering notes.** Contiguous 8 GiB of blocks need 9 tables; the direct
map of the 8 GB Pi 5 needs 11 tables, 4,092 blocks and 581 pages, and the
16 GB model 19 of the 80 that its pool holds. A table returns to its pool
only on reset. The kernel tables are shared state, classified in the
[State fields](page-tables/contract.md#state-fields) of the page-tables
contract.

**Verification.** Invariants: every leaf has the bits of its kind; a page of
the direct map translates to its own physical address and nothing excluded
translates; a write that is refused changes no table. Required
counterexamples: a misaligned, out-of-region or out-of-width address, a
block over a table, a page inside a block, a map one table beyond the pool.
Environments: host tests against an independent page model of the 8 GiB
layout of the prototype and of the other Pi 5 models; QEMU virt with the MMU
on, writing a read-only page, executing an execute-never page and touching a
guard; the 8 GB Pi 5 with its whole RAM mapped.

## ASIDs

**Description.** Each address space of a process has an ASID, which tags
the translations of its lower tables in the TLB, so that switching between
address spaces needs no invalidation of the others' entries. ASIDs come
from a fixed set whose size bounds the number of processes. An ASID returns
to the set only after its address space is no longer loaded on any CPU and
its TLB entries are invalidated on every CPU that may hold them. Kernel
mappings are global and carry no ASID, except kernel pages that are private
to one address space.

**Design background.** The architecture provides 8- or 16-bit ASIDs in
`TTBR0_EL1`, selected by `TCR_EL1`, and TLB invalidation by ASID; the CPU
may walk the tables of the root and ASID in its `TTBR0_EL1` at any time, so
a CPU joins the record of an address space before it loads it (Simner et
al. 2022).

**Consumers.** The address spaces of processes and the context switch of
the scheduling domain.

**Interface.** No ABI operation: an ASID is taken when a process is created
and returned when it is reaped; the capacity record bounds their number.

**Prerequisites.** [Page tables and the kernel direct map](#page-tables-and-the-kernel-direct-map),
[Reclamation barriers](#reclamation-barriers).

**Engineering notes.** The CPU record of an address space lists the CPUs
that may hold its translations; with one CPU it holds the executing CPU,
and the local invalidation is correct because of the record, not because no
other CPU runs.

**Verification.** Invariants: no two live address spaces share an ASID; a
returned ASID has no TLB entry on any CPU. Environments: QEMU runs with
several processes on one and on several vCPUs, and Pi 5 runs.

## VM objects and their kinds

**Description.** A region is a range that `reserve` establishes in the
caller's own address space; the regions of one address space never
overlap. A VM object is memory that can be mapped into address spaces. An
anonymous object takes zero-filled pages on `commit`, and `decommit`
returns them and keeps the range; `mprotect` changes the permissions within
the rights of the object; `release` works in two phases, refusing new
accesses at once and completing only after unmapping, TLB invalidation and
the draining of references. Copy-on-write, shared and file-backed objects,
with EL0 pagers through a pager port, are further kinds. Some mappings are
not VM objects: the pages of the boot bundle, the segments and stacks that
loading creates and the registers of a device grant, which the kernel
installs directly and records in the address space.

**Design background.** The kinds follow the architecture of the kernel
([address spaces and VM objects](../../architecture.md#address-spaces-and-vm-objects)).
The first VM objects are the private anonymous objects of a single thread;
the commit limit of each process comes from the capacity record.

**Consumers.** The loader and the process service, the C library and
language runtimes for their heaps and stacks, and services that share
buffers.

**Interface.** `reserve`, `commit`, `decommit`, `mprotect` and `release`
on capabilities to the caller's address space and to VM objects. A fault on
a page that a failed pager cannot supply goes to the fault handler of the
thread, or terminates its process.

**Prerequisites.** [Physical page ownership](#physical-page-ownership),
[Page tables and the kernel direct map](#page-tables-and-the-kernel-direct-map),
[Reclamation barriers](#reclamation-barriers).

**Engineering notes.** The writable and executable mappings of each object
are counted to keep W^X. The pages of an object return to the allocator,
and its quota to the owner, only after its release has completed.

**Verification.** Invariants: regions of one address space are disjoint;
the committed pages of a process stay within its limit; a released object
has no mapping. Environments: host tests and QEMU runs of commit, decommit,
`mprotect` and release with concurrent accesses.

## User-buffer access

**Description.** The kernel reads memory that a process can write only by
copying it once into memory that the process cannot write, validates the
copy and uses only the copy afterwards; it writes results into a buffer of
the process by a copy as well. A copy that meets a page that is not mapped
with the access it needs fails the operation that asked for it, and the
kernel state stays as before. Large data goes through buffers that both
sides have authorized beforehand, whose shared indices and descriptors are
read into a private snapshot before use.

**Design background.** Another thread can change shared memory between two
reads of the kernel, so a value is read once
([S6d](../../conventions/smp.md#s6d-user-memory)).

**Consumers.** System calls with buffer arguments, IPC with shared buffers
and the services that exchange data with processes.

**Interface.** The copy-in and copy-out routines of the kernel, whose
failure is an error of the calling operation, not a fault of the kernel.

**Prerequisites.** [VM objects and their kinds](#vm-objects-and-their-kinds),
[Page tables and the kernel direct map](#page-tables-and-the-kernel-direct-map).

**Engineering notes.** A copy is bounded by the size that its operation
admits, and no lock that another CPU needs is held while it may fault.

**Verification.** Required counterexamples: a buffer changed by another
thread during the operation, a buffer that crosses into an unmapped page, a
buffer of the kernel's addresses. Environments: host tests of the
validation of copies and QEMU runs with concurrent writers.

## W^X and code publication

**Description.** No frame is mapped writable and executable at the same
time, counting every alias. No kind of descriptor is both; the direct map
maps only pages of RAM that are free or held, read-write and
execute-never; the image's text has one mapping, read-only and executable;
and executable pages come only from the image and the boot bundle until VM
objects carry the execute right. Code that the kernel writes at run time is
published by cleaning its data cache lines to the point of unification,
removing its writable mapping with a completed TLB invalidation, installing
the executable mapping and invalidating its instruction cache lines, before
it runs.

**Design background.** `SCTLR_EL1.WXN` makes the hardware treat every
writable mapping as execute-never. The publication sequence follows the
Arm Architecture Reference Manual for the concurrent modification of
instructions; the instruction cache is invalidated also for Non-cacheable
memory and with the caches off.

**Consumers.** The loader, which maps the code of the boot bundle; language
runtimes that generate code, once the execute right of VM objects exists.

**Interface.** None of its own: the rule binds every mapping that the
writes of the page tables and the VM objects create.

**Prerequisites.** [Page tables and the kernel direct map](#page-tables-and-the-kernel-direct-map),
[Cache and TLB maintenance](../boot-platform/README.md#cache-and-tlb-maintenance)
of the boot and platform domain; the
[descriptors and attributes](page-tables/contract.md#descriptors-and-attributes)
of the page-tables contract.

**Engineering notes.** The page tables leave the image, the device tree
and the boot bundle out of the direct map, so no writable alias of code
exists; the direct map is never split to seal a page.

**Verification.** Invariant: for every frame, its writable and its
executable mappings are not both present. Required counterexamples: a
layout of the image whose text and data share a page, a write to the text
and an execution from data. Environments: host tests of the layout and of
the descriptors; QEMU runs that take the permission faults; the Pi 5 with
the caches on for the publication of code.

## Reclamation barriers

**Description.** A page, a table or an ASID is reused only after every CPU
and device that may reach it has acknowledged that it no longer does: for a
translation that an unmap removes, the completed TLB invalidation on every
CPU that may hold it; for the tables and the ASID of an address space, the
acknowledgement of every CPU that may run it that its root and ASID have
left its `TTBR0_EL1`; for memory, stacks and objects, the acknowledgement of
every CPU and DMA that may reference them. The set of these CPUs is fixed
when reclamation starts and does not shrink. A timeout, a request that was
only sent and a CPU that has only gone offline are not acknowledgements;
memory whose acknowledgement never arrives stays quarantined.

**Design background.** The rule follows the SMP design rules
([S3](../../conventions/smp.md#s3-reclamation-after-acknowledgement)),
which give the reason for each acknowledgement.

**Consumers.** The release of VM objects and regions, the destruction of
address spaces and processes, and the return of DMA buffers.

**Interface.** None of its own: the operations that reclaim report their
completion only once the acknowledgements have arrived.

**Prerequisites.** [ASIDs](#asids),
[Page tables and the kernel direct map](#page-tables-and-the-kernel-direct-map),
[VM objects and their kinds](#vm-objects-and-their-kinds).

**Engineering notes.** Reclamation that waits runs in bounded steps, with
its progress in the object that it reclaims.

**Verification.** Required counterexamples: a CPU that does not answer, a
DMA that has not drained, a timeout before the acknowledgement.
Environments: QEMU runs on several vCPUs under multi-threaded TCG, then the
Pi 5.

## Dependencies

| Feature | Depends on | Reason |
| --- | --- | --- |
| Physical page ownership | Physical memory ranges | The managed banks and the exclusions come from the boot memory map |
| Physical page ownership | Page tables and the kernel direct map | A page is zeroed through the direct map before it is handed out |
| Page tables and the kernel direct map | Physical memory ranges, Cache and TLB maintenance | The direct map covers the usable ranges; an unmap invalidates the TLB with the primitives of the boot component |
| ASIDs | Page tables and the kernel direct map | An ASID tags the translations of the lower tables of an address space |
| VM objects and their kinds | Physical page ownership, Page tables and the kernel direct map | Commit takes zeroed pages and maps them |
| User-buffer access | VM objects and their kinds | A copy reads and writes the pages that a process has mapped |
| W^X and code publication | Page tables and the kernel direct map, Cache and TLB maintenance | The rule binds every mapping; publication cleans and invalidates caches |
| Reclamation barriers | ASIDs, Page tables and the kernel direct map | Reuse waits for the invalidation of translations and ASIDs |

## Exclusions

- The parsing of the device tree and the boot memory map belong to the
  [boot and platform](../boot-platform/README.md) domain, and so does the
  cache and TLB maintenance of the executing CPU.
- The acknowledgement of TLB invalidation and reclamation across CPUs and
  the start of secondary CPUs belong to the multicore domain.
- The authority to map device registers into a process, the delivery of
  interrupts and the authorization and draining of DMA belong to the devices
  and DMA domain; this domain gives only the descriptors of such pages.
- Capabilities, quotas and the capacity record belong to the kernel objects
  and capabilities domain.
- Who may add the execute right to memory, and the integrity of `exec`,
  belong to the security and lifecycle domain.
- Futex-style waits on user memory belong to the IPC and waits domain.
- The EL0 pagers of file-backed objects and the file systems behind them
  belong to the EL0 services and storage domain.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>.
- Arm Limited, *Learn the architecture - AArch64 memory management Guide*,
  version 1.4, document 101811_0104_01_en, 2024,
  <https://documentation-service.arm.com/static/670e4dc89fbc7343d3e4cee1>.
- Arm Limited, *Learn the architecture - Memory Systems, Ordering, and
  Barriers*, version 1.0, document 102336_0100_01_en, 2022,
  <https://documentation-service.arm.com/static/62a304f231ea212bb662321d>.
- devicetree.org, *Devicetree Specification*, release v0.4, 2023,
  <https://github.com/devicetree-org/devicetree-specification/releases/download/v0.4/devicetree-specification-v0.4.pdf>.
- G. Klein, J. Andronick, K. Elphinstone, T. Murray, T. Sewell, R. Kolanski,
  G. Heiser, "Comprehensive Formal Verification of an OS Microkernel", ACM
  Transactions on Computer Systems 32(1), 2014,
  <https://trustworthy.systems/publications/nicta_full_text/7371.pdf>.
- B. Simner, A. Armstrong, J. Pichon-Pharabod, C. Pulte, R. Grisenthwaite,
  P. Sewell, "Relaxed virtual memory in Armv8-A", European Symposium on
  Programming (ESOP), 2022, <https://arxiv.org/abs/2203.00642>.
- R. Tao, J. Yao, X. Li, S.-W. Li, J. Nieh, R. Gu, "Formal Verification of
  a Multiprocessor Hypervisor on Arm Relaxed Memory Hardware", SOSP 2021,
  <https://www.cs.columbia.edu/~nieh/pubs/sosp2021_vrm.pdf>.
