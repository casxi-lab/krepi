# Page-tables contract

This page governs the code of the `page-tables` component of the
[memory and address spaces](../README.md) domain: the descriptors and
attributes of the stage 1 translation tables of the EL1&0 regime, the table
sets with their pools and the entries that change them, the write plans that
the architecture crate carries out, the kernel's own mappings of its image
and its devices, the kernel direct map, and the page ownership table of the
physical RAM. The component takes the boot memory map of the
[fdt](../../boot-platform/fdt/contract.md) component as values and uses the
cache and TLB maintenance of the
[boot](../../boot-platform/boot/contract.md#cache-and-tlb-maintenance)
component. The observable behaviour that these rules serve, with its
evidence, is in the [requirements](requirements.md), the other document of
the component.

## Terms

- **Region.** One of the two halves of the 39-bit virtual address space of
  the EL1&0 regime: the lower region, the addresses below $2^{39}$, which
  `TTBR0_EL1` translates, and the upper region, the addresses at or above
  `DIRECT_BASE`, $2^{64} - 2^{39}$ or `0xffffff8000000000`, which
  `TTBR1_EL1` translates. No other address translates.
- **Table.** 4 KiB of 512 descriptors of 64 bits. A walk has three levels:
  level 1, the root, where an entry covers 1 GiB; level 2, 2 MiB; and
  level 3, 4 KiB. The index of a virtual address at level 1 is its bits 30
  to 38, at level 2 its bits 21 to 29, at level 3 its bits 12 to 20.
- **Table set.** `page_tables::Tables`: the tables of one region, kept in
  one pool, with the root at index 0 and the record of the tables in use.
  A set never holds addresses of the other region.
- **Pool.** The storage of a set: its capacity of $N$ tables at consecutive
  physical addresses from `base`, a multiple of 4 KiB, table $i$ at
  `base` $+ 4096 i$.
- **Physical width.** `bits`, the physical address size that the CPU
  reports in `ID_AA64MMFR0_EL1.PARange`, from 32 to 48; 40 on the Cortex-A76
  of QEMU virt and of the Raspberry Pi 5.
- **Kind.** `page_tables::Kind`: one of the nine attribute sets of a leaf
  that [Descriptors and attributes](#descriptors-and-attributes) lists.
- **Abstract mapping.** For a set, the partial function $M$ from the
  4 KiB-aligned virtual addresses of its region to the triples of a physical
  page, a kind and a leaf form, page or block, with the set $G$ of the
  1 GiB slots and the set $P$ of the 2 MiB slots under which the set holds a
  table ([Abstract mapping](#abstract-mapping)).
- **Write plan.** `page_tables::WritePlan`: the ordered steps that carry
  out a write of a set
  ([Write plans and publication](#write-plans-and-publication)).
- **Kernel tables.** The two sets of the kernel's own address space: the
  lower kernel set, which maps the image and the device pages of the board
  at their physical addresses, and the direct map's set in the upper region.
- **Direct map.** The mapping of `DIRECT_BASE | pa` to `pa` for every page
  of every usable range ([Kernel direct map](#kernel-direct-map)).
- **Boot memory map.** The value `fdt::MemoryPlan` that the fdt component
  builds at boot from the device tree and the board
  ([boot memory map](../../boot-platform/fdt/contract.md#boot-memory-map)):
  the RAM banks and the managed banks, the boot storage and the firmware
  reservations that it excludes, and its usable ranges. This component
  reads it and never changes it.
- **Managed page.** A 4 KiB page that lies wholly in a managed bank.
- **Managed bytes.** The bytes of the managed pages that are free or held,
  as `Ownership::stats` counts them: the pages that a firmware reservation,
  the image or another boot storage excludes are managed pages but not
  managed bytes. `MemoryPlan::managed_bytes` of the boot memory map counts
  every page of the managed banks instead.
- **Usable range.** A range of whole pages of a managed bank that no boot
  storage and no firmware reservation touches, as
  `MemoryPlan::available_ranges` gives it, in address order.
- **Physical range.** `page_tables::PhysRange`: a nonempty range of
  physical addresses `[start, start + len)` whose end fits in 64 bits. The
  page ownership table takes its banks, exclusions, windows and receipts as
  physical ranges; the boot wiring converts the spans of the boot memory map
  into them.
- **Boot storage.** The spans, at most 4, that the board gives the boot
  memory map for what the firmware or the loader placed: the kernel image,
  with its BSS and stacks, the device tree, and the boot bundle when it is
  loaded as a file of its own.
- **Boot wiring.** The code of a board crate that runs on the boot CPU
  before the MMU is on: it builds the boot memory map, the kernel tables and
  the page ownership table, and turns the MMU on.
- **Page ownership table.** `page_tables::Ownership`: the owner of every
  managed page ([Page ownership](#page-ownership)), identified by its
  arena, a nonzero 64-bit value.
- **Extent.** A range of managed pages in one bank that the page ownership
  table records with one owner.
- **Receipt.** `page_tables::Allocation`: the arena, the owner identity, the
  generation and the range of an allocation; bookkeeping, not authority.
- **Reservation and initialized packet.** `page_tables::Reservation`, held
  pages whose bytes are not yet zeroed, and `page_tables::Initialized`, held
  pages whose zeroing has completed and that are not yet published.
- **Token.** What every entry on a table set or on the page ownership table
  holds from its first check to the end of the execution of its plan, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state
  for shared state; with one CPU, the executing CPU holds it.

## Entry points

The entries of the core are in the module `page_tables` of `krepi-kernel`
(planned); the adapter is the module `mmu` of `krepi-arch` (planned).

| Entry point | Kind | Called by | Rules |
| --- | --- | --- | --- |
| `page_tables::Kind`, `page_tables::descriptor`, `page_tables::direct_address`, `PhysRange::new`, `end`, `contains` and `overlaps`, and `Tables::lookup_page`, `lookup_block` and `used` (planned) | Value types and functions that write nothing, host-testable | The entries of this page; `krepi_arch::mmu`, for `direct_address`; the modules `vm` and `creation` of the core (planned) | [Descriptors and attributes](#descriptors-and-attributes), [Kernel direct map](#kernel-direct-map) |
| `Tables::new`, `Tables::reset` and `Tables::clone_kernel_from` (planned) | Write entries, host-testable; `reset` and `clone_kernel_from` return write plans | `new`: the boot wiring, for the kernel tables; `new`, `reset` and `clone_kernel_from`: the modules `creation` and `lifecycle` of the core (planned), for the lower tables of a process, which `clone_kernel_from` fills from the lower kernel set | [Abstract mapping](#abstract-mapping), [Copying the kernel tables](#copying-the-kernel-tables), [Table pool](#table-pool) |
| `Tables::map_page` (planned) | Write entry, host-testable; returns a write plan | `kernel_map`; the modules `vm` and `creation` of the core (planned) | [Abstract mapping](#abstract-mapping), [Write plans and publication](#write-plans-and-publication) |
| `Tables::map_block` (planned) | Write entry, host-testable; returns a write plan | `direct_map` | [Abstract mapping](#abstract-mapping), [Kernel direct map](#kernel-direct-map) |
| `Tables::unmap_page` (planned) | Write entry, host-testable; returns a write plan | The module `vm` of the core (planned), for a set that is not one of the kernel tables | [Abstract mapping](#abstract-mapping), [Write plans and publication](#write-plans-and-publication) |
| `page_tables::kernel_map` and `page_tables::direct_map` (planned) | Write entries, host-testable; return write plans | The boot wiring, once each, before the MMU is on | [Kernel mappings](#kernel-mappings), [Kernel direct map](#kernel-direct-map) |
| `Ownership::new` (planned) | Write entry, host-testable | The boot wiring, once, for the kernel root | [Page ownership](#page-ownership) |
| `Ownership::choose` and `Ownership::assign` (planned) | A read entry and a write entry, host-testable | The modules of the core that take pages (planned) | [Page ownership](#page-ownership) |
| `Ownership::reserve`, `Reservation::initialized` and `Ownership::publish` (planned) | Write entries and a value function, host-testable | The modules of the core that take pages (planned) | [Page ownership](#page-ownership) |
| `Ownership::cancel` and `Ownership::release` (planned) | Write entries, host-testable | The modules of the core that take and return pages (planned) | [Page ownership](#page-ownership) |
| `Ownership::owner`, `Ownership::validate` and `Ownership::stats` (planned) | Read entries, host-testable | The modules of the core that take pages (planned) | [Page ownership](#page-ownership) |
| `krepi_arch::mmu::apply`, `enable` and `zero_frames` (planned) | Functions; `enable` and `zero_frames` are `unsafe` | `apply`: the boot wiring, and the entry of a system call in `krepi_arch` for the plans that the dispatch of the core returns; `enable`: the boot wiring, once on each CPU; `zero_frames`: the code that zeroes pages for the page ownership table | [Write plans and publication](#write-plans-and-publication) |

## Extractability

The module `page_tables` of the core (planned), below `kernel/src/`
(planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the
descriptors and kinds, the address arithmetic, the table sets with their
pools, the write entries with their plans, the kernel's mappings, the direct
map and the page ownership table. Its items are `pub(crate)` except the
rows of the entry table that the architecture crate or a board crate
calls, with the value types that those rows take and return, among them
`WritePlan` and its steps
([provable core](../../../architecture.md#the-provable-core)). It defines no
callback for a hardware action: every entry that changes a table returns a
write plan, and the zeroing of pages is the caller's, between two entries.
It refers to the fdt module only for the boot memory map and its spans
([module order](../../../architecture.md#module-order-in-the-core)).

The adapter `mmu` of `krepi-arch` (planned), in `kernel/arch/src/mmu.rs`
(planned), does not follow the subset: it stores descriptors into tables,
zeroes tables and frames, executes the barriers and the invalidation of the
local TLB, and writes the registers that turn the MMU on; the invalidation
of a page and the publication of code use the functions of
`krepi_arch::cache` that the
[boot contract](../../boot-platform/boot/contract.md#cache-and-tlb-maintenance)
governs. The boot wiring is code of the board crates. The contract is
written before its code, so this section lists no source paths; the change
that adds the module writes its `paths` block here.

## Descriptors and attributes

A descriptor is invalid when its bits 1 and 0 are `0b00`; its other bits
are then 0. A table descriptor, at level 1 or 2, holds `0b11` in bits 1 and
0 and the physical address of the next table in bits 12 to 47, and no
attribute. A page descriptor, at level 3, holds `0b11` and a block
descriptor, at level 2, holds `0b01` in bits 1 and 0; both hold the output
address in bits 12 to 47, bits 21 to 47 for a block, and the bits of a kind.
`page_tables::descriptor` gives the page descriptor of a kind and an output
address; the block descriptor of `ReadWrite` is its page descriptor with
bit 1 clear, and no other kind has a block form.

| Kind | EL1 | EL0 | Memory | AP[2:1] | PXN | UXN | AttrIndx | SH | nG | AF | Use |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ReadExecute` | RO, executable | None, NX | Normal | `0b10` | 0 | 1 | 1 | `0b11` | 0 | 1 | Text of the image |
| `ReadOnly` | RO, NX | None, NX | Normal | `0b10` | 1 | 1 | 1 | `0b11` | 0 | 1 | Read-only data of the image, the device tree |
| `ReadWrite` | RW, NX | None, NX | Normal | `0b00` | 1 | 1 | 1 | `0b11` | 0 | 1 | Data, BSS and stacks of the image; the direct map |
| `KernelPrivateReadWrite` | RW, NX | None, NX | Normal | `0b00` | 1 | 1 | 1 | `0b11` | 1 | 1 | Kernel pages private to one address space |
| `Device` | RW, NX | None, NX | Device-nGnRnE | `0b00` | 1 | 1 | 0 | `0b00` | 0 | 1 | Registers of the kernel's devices |
| `UserReadExecute` | RO, NX | RO, executable | Normal | `0b11` | 1 | 0 | 1 | `0b11` | 1 | 1 | Code of a process |
| `UserReadOnly` | RO, NX | RO, NX | Normal | `0b11` | 1 | 1 | 1 | `0b11` | 1 | 1 | Read-only data of a process |
| `UserReadWrite` | RW, NX | RW, NX | Normal | `0b01` | 1 | 1 | 1 | `0b11` | 1 | 1 | Data and stacks of a process |
| `UserDevice` | RW, NX | RW, NX | Device-nGnRnE | `0b01` | 1 | 1 | 0 | `0b00` | 1 | 1 | Device registers mapped into a process |

AP[2:1] is bits 7 and 6, PXN bit 53, UXN bit 54, AttrIndx bits 2 to 4, SH
bits 8 and 9, nG bit 11 and AF bit 10; every other bit of a leaf is 0.

- **Memory attributes.** `MAIR_EL1` holds Device-nGnRnE, `0x00`, at
  index 0 and Normal memory at index 1: inner and outer Write-Back with
  read and write allocation, `0xff`, when the board turns the caches on, and
  inner and outer Non-cacheable, `0x44`, otherwise. No kind uses another
  index.
- **RO.** A leaf with AP[2] set: no write at EL1 or EL0.
- **NX.** A leaf with PXN set does not execute at EL1, one with UXN set does
  not execute at EL0.
- **Device.** A leaf of AttrIndx 0: Device-nGnRnE memory, never cached,
  without gathering, reordering or early write acknowledgement, and
  execute-never at both levels.
- **Guard.** An entry that must stay invalid: the page below each stack of
  the image and every page that a mapping leaves out on purpose. No entry of
  this page writes a valid descriptor where a guard is, and an access to a
  guard takes a translation fault.
- **Kernel and user.** The kernel kinds give EL0 no access and are global,
  except `KernelPrivateReadWrite`, which is tagged with the ASID of its
  address space; the user kinds are tagged with the ASID, and EL1 never
  executes them.
- **The descriptor of a device page of a process.** `UserDevice` is the
  descriptor of a register page that a process maps. Which pages a process
  may map so is decided where device authority is granted, not here.

**W^X.** At no time is a frame mapped writable and executable, counting
every alias in every table set together
([address spaces](../../../architecture.md#address-spaces-and-vm-objects)):

1. No kind is writable and executable: every kind that EL1 or EL0 can write
   has PXN and UXN set, and both executable kinds are read-only at both
   levels. `enable` sets `SCTLR_EL1.WXN`, so that the hardware also treats
   every writable mapping as execute-never.
2. The lower kernel set maps each page of the image with one kind
   ([kernel mappings](#kernel-mappings)), which a copy of it into the lower
   tables of a process keeps
   ([copying the kernel tables](#copying-the-kernel-tables)), and the direct
   map maps only pages whose owner is free or a holder, `ReadWrite`. The
   image, the device tree, the boot bundle, every other boot storage and
   every firmware reservation have no alias in the direct map
   ([Kernel direct map](#kernel-direct-map)).
3. The executable pages come only from the image and the boot bundle: the
   text of the image through `ReadExecute` in the lower kernel set and its
   copies, and the code of the boot bundle through `UserReadExecute` in an
   address space. Neither has a writable mapping, since the text has one
   kind in every set that maps it and the pages of the boot bundle, a range
   of their own or part of the image, are mapped by the kernel read-only or
   executable only. No VM object carries the execute right and `mprotect`
   cannot add it, so no page of a holder is mapped executable; a page that
   becomes executable at run time comes with the full VM object model.

### Kernel mappings

`kernel_map` writes the lower kernel set from a layout that the board gives:
at most 16 ranges, each with a kernel kind, and the guard pages.

- The image is linked at its load address and runs at it while the MMU is
  turned on, so the lower kernel set maps every range at its physical
  address. The upper region is the window of the direct map, which may not
  alias the image.
- The ranges of the image are its text, `ReadExecute`; its read-only data,
  `ReadOnly`; and its data, BSS, stacks and the pools of the kernel tables,
  `ReadWrite`. The device tree may be mapped `ReadOnly`, and the registers
  of the console and the interrupt controller of the board are `Device`.
- Every range starts and ends on a page boundary, and two ranges never
  share a page, so each page has one kind; the link layout of an image
  places its sections so. A guard page lies in no range.
- The layout names only the kinds `ReadExecute`, `ReadOnly`, `ReadWrite`
  and `Device`.

### Copying the kernel tables

`Tables::clone_kernel_from(source, source_base, base, bits)` fills a set,
the target, with a private copy of another set of its region, the source.
Its use is the copy of the lower kernel set into the lower tables of a
process: the kernel runs at the physical addresses of its image in the
lower region ([kernel mappings](#kernel-mappings)), and the lower tables of
a process take the place of the lower kernel set in `TTBR0_EL1` while the
process runs, so they map the image and the devices of the kernel as the
kernel's own tables do.

- The two sets are of one region and of one capacity $N$. `source_base` and
  `base` are the bases of their pools, which do not overlap, and `bits` is
  the physical width of both.
- The source holds only pages, no block, each of the kinds `ReadExecute`,
  `ReadOnly`, `ReadWrite` and `Device` with an output address below
  $2^{\mathrm{bits}}$. Its table descriptors hold no attribute bit and reach
  every table in use of its pool exactly once, and no other table.
- The copy empties the target, then gives it the tables of the indices that
  the source uses, with the entries of the source, each table descriptor
  pointing at the target's table of the same index. The leaves keep their
  output addresses and their bits, the global ones included, so both sets
  translate the pages of the source alike; the tables are the target's own,
  so a later write to one of the sets leaves the other unchanged.
- The target is not one of the kernel tables; no CPU holds its root in a
  `TTBR` and no TLB holds a translation of it, as for `reset`, and the
  entry does not check it. The caller holds the token of the source, that
  of the kernel tables for the lower kernel set, so that no plan writes the
  source during the copy.
- The entry checks in this order and returns the first error: `base` and
  `bits` of the source and then of the target (`Alignment`, `AddressWidth`,
  `TableBacking`, as for every entry); the overlap of the two pools, and a
  record of the source's tables in use that holds no table or more than
  $N$ (`TableBacking`); then the walk of the source from its root, entry by
  entry in index order and each table under its entry before the next
  entry: a table descriptor with an attribute bit, or a block in its place
  (`InvalidDescriptor`); one that points at a table outside the tables in
  use or at a table already reached (`TableBacking`); a leaf of another
  kind or with an output address at or above $2^{\mathrm{bits}}$
  (`InvalidDescriptor`); and last a table in use that the walk did not
  reach (`TableBacking`).

## Abstract mapping

The state of a set is its abstract mapping $M$, with $G$ and $P$, and its
pool. The tables that it uses are the root and one table for each element
of $G$ and of $P$: $\mathrm{used} = 1 + |G| + |P|$. For a virtual address
$v$, $\mathrm{blk}(v)$ and $\mathrm{gib}(v)$ are $v$ rounded down to 2 MiB
and to 1 GiB. A page or a block slot is free when $M$ has no entry for it,
and a block slot $b$ is also free of tables when $b \notin P$.

The state of the page ownership table is the owner function $O$ on the
managed pages ([Page ownership](#page-ownership)) and its generation counter
$g$.

### After mapping

Each write entry of a set changes $M$ as its row states once its write
plan has been executed; a failed entry returns an error, changes nothing and
returns no plan: $M' = M$, $G' = G$, $P' = P$.

| Entry | Requires | After mapping |
| --- | --- | --- |
| `Tables::new` | The storage of the pool is zero in all its $N$ tables ([Table pool](#table-pool)); the entry does not check it | $M = \emptyset$, $G = P = \emptyset$, so 1 table in use |
| `reset` | No CPU holds the root in a `TTBR` and no TLB holds a translation of the set ([reclamation](../../../conventions/smp.md#s3-reclamation-after-acknowledgement)); the entry does not check it | $M' = \emptyset$, $G' = P' = \emptyset$ |
| `map_page(v, p, k)` | $v \notin \mathrm{dom}\,M$, so neither a page nor a block covers $v$ | $M' = M[v \mapsto (p, k, \mathrm{page})]$, $G' = G \cup \{\mathrm{gib}(v)\}$, $P' = P \cup \{\mathrm{blk}(v)\}$ |
| `map_block(v, p)` | $v = \mathrm{blk}(v)$, no page of $[v, v + 2^{21})$ in $\mathrm{dom}\,M$ and $v \notin P$ | $M' = M \cup \{v + i \mapsto (p + i, \mathrm{ReadWrite}, \mathrm{block}) : i = 0, 4096, \ldots, 2^{21} - 4096\}$, $G' = G \cup \{\mathrm{gib}(v)\}$, $P' = P$ |
| `unmap_page(v)` | $M(v) = (p, k, \mathrm{page})$ | $M' = M \setminus \{v\}$, $G' = G$, $P' = P$: an empty table stays in the set; the entry returns $p$ |
| `clone_kernel_from(S)` | The rules of [copying the kernel tables](#copying-the-kernel-tables): every entry of $M_S$ a page of `ReadExecute`, `ReadOnly`, `ReadWrite` or `Device` below $2^{\mathrm{bits}}$; no `TTBR` and no TLB holds the target | $M' = M_S$, $G' = G_S$, $P' = P_S$, in the tables of the indices that $S$ uses; $S$ is unchanged |
| `kernel_map(L)` | Every page of every range of $L$ outside $\mathrm{dom}\,M$, the ranges pairwise without a common page and without a guard page of $L$ | $M' = M \cup \{v \mapsto (v, k_j, \mathrm{page}) : v$ a page of range $j$ of $L$ with kind $k_j\}$; $G'$ and $P'$ add the slots of those pages; every guard page of $L$ stays outside $\mathrm{dom}\,M'$ |
| `direct_map(B)` | Every page of every usable range of $B$ below $2^{39}$, its address outside $\mathrm{dom}\,M$ | $M' = M \cup \{\mathtt{DIRECT\_BASE} \mid p \mapsto (p, \mathrm{ReadWrite}, \ell(p)) : p$ a page of a usable range of $B\}$, where $\ell(p)$ is block when $\mathrm{blk}(p)$ and the 2 MiB after it lie in one usable range and page otherwise; $G'$ and $P'$ add the slots of those pages |

### After ownership

Each write entry of the page ownership table changes $O$ and $g$ as its
row states; a failed entry changes nothing: $O' = O$, $g' = g$. A holder is
written $\mathrm{held}(o, n, s)$: owner identity $o$, generation $n$ and
state $s$, reserved or published.

| Entry | Requires | After ownership |
| --- | --- | --- |
| `Ownership::new(a, banks, X)` | The checks of [initialization](#page-ownership) | $O(q)$ is the owner of the exclusions of $X$ that touch $q$, by the order firmware, image, boot storage, for every managed page $q$ that one touches, and free for every other; $g = 1$ |
| `assign(c, zeroed)` | The choice $c$ of `choose` for owner identity $o$, taken under the same token: $O(q) =$ free for every page $q$ of $c$, all in one free extent; `zeroed` tells whether the zeroing of $c$ completed | $O' = O[q \mapsto \mathrm{held}(o, g, \mathrm{published}) : q \in c]$, $g' = g + 1$, or exhausted after $2^{64} - 1$; when the zeroing failed: `ZeroFailed`, $O' = O$, $g' = g$ |
| `reserve(o, m, a, w)` | The checks of `choose` | $O' = O[q \mapsto \mathrm{held}(o, g, \mathrm{reserved}) : q \in c]$ for the range $c$ that `choose` would give, $g' = g + 1$ |
| `publish(o, x)` | $x$ from this arena, $O(q) = \mathrm{held}(o, x.n, \mathrm{reserved})$ exactly for the pages $q$ of $x$ | $O' = O[q \mapsto \mathrm{held}(o, x.n, \mathrm{published}) : q \in x]$, $g' = g$ |
| `cancel(o, r)` | $r$ from this arena, $O(q) = \mathrm{held}(o, r.n, \mathrm{reserved})$ exactly for the pages $q$ of $r$ | When no zeroing of $r$ was attempted: $O' = O[q \mapsto \mathrm{free} : q \in r]$, $g' = g$; after an attempted zeroing: `ZeroFailed`, $O' = O$, $g' = g$, and $r$ is returned |
| `release(o, x)` | $x$ from this arena, $O(q) = \mathrm{held}(o, x.n, \mathrm{published})$ exactly for the pages $q$ of $x$ | $O' = O[q \mapsto \mathrm{free} : q \in x]$, $g' = g$ |

The write entries of this page are the 14 rows of the two tables above:
`Tables::new`, `reset`, `map_page`, `map_block`, `unmap_page`,
`clone_kernel_from`, `kernel_map`, `direct_map`, `Ownership::new`,
`assign`, `reserve`, `publish`, `cancel` and `release`.
`Reservation::initialized` changes only the reservation value that it
consumes ([Page ownership](#page-ownership)). The functions of
`krepi_arch::mmu` change no abstract state of their own: `apply` carries
out the plan whose effect the row of its entry states, `zero_frames`
changes the bytes of frames and no owner, and `enable` writes registers.

### Errors of table sets

| Error | Rule broken |
| --- | --- |
| `Alignment` | A virtual address, a physical address or `base` is not a multiple of 4 KiB; for a block, `v` or `p` not of 2 MiB; a range of a layout does not start or end on a page boundary |
| `AddressWidth` | A virtual address outside the region of the set; a physical address at or above $2^{\mathrm{bits}}$; `bits` outside 32 to 48; a usable range that ends above $2^{39}$ |
| `TableBacking` | A pool of no table, or one that does not end at or below $2^{\mathrm{bits}}$; a table descriptor that points outside the tables in use of the pool; for `clone_kernel_from`, pools that overlap, a table that the walk of the source reaches twice, or a record of the source's tables in use that the walk does not match |
| `OutOfTables` | The plan needs more tables than the pool has free |
| `AlreadyMapped` | A page or block slot that the write needs is not free, or not free of tables for a block; two ranges of a layout share a page, or a range covers a guard page |
| `NotMapped` | `lookup_page` or `unmap_page` at an address without a page leaf, which includes a page of a block; `lookup_block` at a block slot without a block |
| `InvalidDescriptor` | For `clone_kernel_from`, a table descriptor of the source with an attribute bit or a block in its place, or a leaf of the source of another kind than `ReadExecute`, `ReadOnly`, `ReadWrite` and `Device` or with an output address at or above $2^{\mathrm{bits}}$ |

An entry checks in this order and returns the first error: `base`, `bits`
and the region of the virtual address (`Alignment`, `AddressWidth`,
`TableBacking`, in this order); the physical address (`Alignment`, then
`AddressWidth`); the walk (`TableBacking` for a bad table descriptor, then
`AlreadyMapped` or `NotMapped`); and `OutOfTables` last. `kernel_map` and
`direct_map` check their ranges in address order and, for each, alignment,
width and the free slots; then the tables that the whole plan needs. The
order of `clone_kernel_from` is in
[copying the kernel tables](#copying-the-kernel-tables).

## Write plans and publication

A write plan is a sequence of steps, and `krepi_arch::mmu::apply` executes
them in order, each completing before the next:

| Step | Effect | Executed by |
| --- | --- | --- |
| `Zero(t)` | Writes 0 into the 512 entries of table $t$ of the pool | `zero_table` |
| `Store(t, i, d)` | Writes descriptor $d$ into entry $i$ of table $t$ | `store_descriptor` |
| `Fence` | `DMB ISHST` | `synchronize` |
| `Sync` | `DSB ISH`, then `ISB` | `synchronize` |
| `Invalidate(v)` | `DSB ISH`, `TLBI VAAE1IS` of $v$, `DSB ISH`, `ISB` | `krepi_arch::cache::invalidate_tlb_page` |

- The check phase of an entry fixes its whole plan: every step follows from
  the state and the arguments by the rules of this page, and no step fails.
  `kernel_map`, `direct_map` and `clone_kernel_from` give their steps one
  at a time, by an iterator of the core over their input (planned), so
  that a plan needs no storage in proportion to the map; the other plans
  have at most seven steps, apart from `reset`.
- The caller holds the token of the set from the entry to the last step of
  its plan, and executes nothing else on the set in between.
- **New tables.** A plan writes a new table completely before it stores the
  table descriptor that makes the table reachable: `Zero`, the entries of
  the table, `Fence`, then one `Store` of the table descriptor into its
  parent, a table built under another new table first. A plan that needs
  a new level 2 and a new level 3 table is `Zero(t3)`, `Store(t3, ...)`,
  `Zero(t2)`, `Store(t2, ...)`, `Fence`, `Store(root, ...)`, `Sync`
  ([S6b](../../../conventions/smp.md#s6b-new-translation-tables)).
- **New entries.** A plan whose last store makes an entry valid ends with
  `Sync`, before the kernel or EL0 relies on the entry
  ([page tables and published data](../../../conventions/smp.md#page-tables-and-published-data)).
- **Kernel tables.** A plan for one of the kernel tables writes only
  invalid entries and holds no `Invalidate`; no entry of this page removes
  or changes a valid entry of the kernel tables
  ([S6a](../../../conventions/smp.md#s6a-kernel-mappings)).
- **Unmapping.** The plan of `unmap_page` is `Store(t, i, 0)` and then
  `Invalidate(v)`; the page that the entry returns is reused only once every
  CPU that may hold its translation has acknowledged it
  ([S6c](../../../conventions/smp.md#s6c-tlb-invalidation),
  [S3](../../../conventions/smp.md#s3-reclamation-after-acknowledgement)).
- **No remapping.** No entry replaces a valid entry by another: a change of
  the output address or the kind of a page is an `unmap_page` and then a
  `map_page`, two plans, which is break-before-make.
- **Reset.** The plan of `reset` is a `Zero` of every table in use; the
  caller has made the set unreachable before it.
- **Copy.** The plan of `clone_kernel_from` is a `Zero` of every table in
  use of the target, then a `Store` of every valid entry of every table in
  use of the source into the target's table of the same index, its table
  descriptors pointing into the target's pool, and `Sync` last. After the
  `Zero` steps every table of the target is zero, since its tables not in
  use are zero already ([Table pool](#table-pool)), so an entry that is
  invalid in the source is invalid in the target too. No CPU walks the
  target before the caller installs its root, after the `Sync`, so the
  whole set is complete before it is published
  ([S6b](../../../conventions/smp.md#s6b-new-translation-tables)).
- **Before the MMU is on.** The plans of `kernel_map` and `direct_map` run on
  the boot CPU with the MMU off, into sets that no `TTBR` holds; their order
  is the same, and the barriers are harmless there.

`zero_table` and `store_descriptor` reach a table through the address at
which the executing CPU sees its pool: its physical address with the MMU
off; the mapping of the image for the pools of the kernel tables, which lie
in the BSS of the image; and the direct map for a pool of held pages.

**Turning the MMU on.** `krepi_arch::mmu::enable` takes the roots of the two
kernel tables, `bits` and whether the board turns the caches on. It runs
once on each CPU, with the MMU off and every exception masked. It
invalidates the TLB entries of the EL1&0 regime of the executing CPU
(`TLBI VMALLE1`, `DSB NSH`, `ISB`, through `synchronize`); writes `MAIR_EL1`
as [Descriptors and attributes](#descriptors-and-attributes) states; writes
`TCR_EL1` with `T0SZ` and `T1SZ` 25, 4 KiB granules in both regions,
inner-shareable walks whose inner and outer cacheability is that of Normal
memory, `IPS` the encoding of `bits`, the ASID taken from `TTBR0_EL1` with 8
bits, no top-byte ignore and no hardware update of the access or dirty
flags; writes the root of the lower kernel set into `TTBR0_EL1` and the root
of the direct map into `TTBR1_EL1`; executes `ISB`; and sets `SCTLR_EL1.M`
and `WXN`, with `C` and `I` when the board turns the caches on, leaving the
other bits as the cold entry left them, followed by `ISB`.

## Kernel direct map

- `DIRECT_BASE` is `!(2^39 - 1)`, `0xffffff8000000000`.
  `direct_address(range)` is `DIRECT_BASE | start` for a physical range
  whose end is at most $2^{39}$, and nothing otherwise: a range that would
  wrap or leave the window has no direct address.
- `direct_map` maps every page of every usable range of the boot memory
  map, `DIRECT_BASE | pa` to `pa`, `ReadWrite`: global, EL1 read and write,
  execute-never and no EL0 access.
- It walks the usable ranges in address order. At a physical address
  that is a multiple of 2 MiB and has at least 2 MiB of its range left, it
  writes a block; elsewhere a page. A usable range never spans two
  banks, so a block never does either.
- Nothing else is in the direct map: not the pages of a firmware reservation,
  `no-map` or not and also when it is `reusable`; not the image, the device
  tree, the boot bundle or another boot storage; not a hole between banks;
  not the RAM outside the managed banks. The Devicetree Specification
  requires that the operating system create no mapping of a `no-map` region
  in its standard mapping of system memory.
- The direct map covers RAM below $2^{39}$. A usable range that ends
  above it makes `direct_map` fail with `AddressWidth`, before any write.
- The boot wiring writes the direct map once, before the MMU is on, and no
  entry changes it afterwards. A frame of the direct map is never sealed,
  split or merged: the pages that are to be executable or shared differently
  are not in it ([W^X](#descriptors-and-attributes)).
- Contiguous 8 GiB of blocks from address 0 need 9 tables: the root and 8
  level 2 tables. The table counts of the boards are in
  [Table pool](#table-pool).
- The two tests of `src/arch/aarch64/address.rs` in the prototype tree, of
  the direct address and of the value of `TCR_EL1`, are vectors of the
  address-space component of this domain, whose contract cites this
  section; they are not frozen here.

## Page ownership

The page ownership table records one owner for every managed page:

| Owner | Pages | Set by |
| --- | --- | --- |
| Free | Pages that no one holds | `Ownership::new`, `cancel`, `release` |
| Firmware | Every page that a firmware reservation touches, `no-map`, `reusable` or neither | `Ownership::new`; never changed |
| Image | Every page of the boot storage of the kernel image, with its BSS, its stacks and the pools of the kernel tables | `Ownership::new`; never changed |
| Boot storage | Every page of the other spans of boot storage, such as the device tree and a separately loaded boot bundle | `Ownership::new`; never changed |
| A holder, $\mathrm{held}(o, n, s)$ | The pages of one allocation or reservation: owner identity $o$, a 64-bit value that the holder's component gives, generation $n$ and state $s$, reserved or published | `assign`, `reserve`, `publish` |

The holders of release 0.1 are the pools of the tables of address spaces,
the pools that the capacity record carves at boot and the pages of VM
objects; the component of each names its owner identities.

**Invariants.**

- Every managed page has exactly one owner.
- The pages of one holder generation form one range in one bank, and two
  holders never share a generation.
- In the table of the kernel root, which the boot wiring builds from the
  boot memory map, the pages that are free or held are exactly the pages of
  its usable ranges, so exactly the pages of the direct map.
- The firmware, image and boot storage pages never change owner.

**Initialization.** `Ownership::new(arena, banks, exclusions)` takes the
managed banks and the exclusions of the boot memory map with their owners.

- Every bank starts and ends on a page boundary (`InvalidAlignment`); there
  is at least one bank and no two overlap (`InvalidRange`); the arena is not
  0 (`InvalidArena`).
- An exclusion excludes, in every bank that it overlaps, the pages that it
  touches: its start rounded down and its end rounded up to a page, within
  the bank. An exclusion outside every bank changes nothing, and overlapping
  exclusions of one owner exclude their union. A page that exclusions of
  several owners touch takes the first owner in the order firmware, image,
  boot storage; the boot memory map gives no such page.
- The table keeps every exclusion, with its owner, in an exclusion record
  of its own; the excluded pages take no extent.
- The checks run in the order alignment, arena, the number of banks (none
  is `InvalidRange`, more than the capacity of the extents is
  `MetadataExhausted`), overlap, then the number of exclusions against the
  capacity of the exclusion records and the extents that the banks, split
  by the exclusions, need against the capacity of the extents
  (`MetadataExhausted`).

**Placement.** `choose(owner, pages, alignment, placement)` gives, without
writing, the range that an allocation takes:

- `pages` and `alignment` count 4 KiB pages; the alignment is a power of
  two; the placement is low or high, with an optional window, a physical
  range, both chosen by the caller.
- It scans the free extents in address order, from the lowest for a low
  placement and from the highest for a high one. In an extent it takes the
  part inside the window, and there the lowest aligned start, or, for a high
  placement, the highest aligned start whose range ends inside that part.
  The first extent that holds the range gives it, unless taking the range
  would need more extents than the capacity has free; the scan then goes on.
- A range never spans two banks, even adjacent ones, and a window never
  gives access to a hole, an exclusion or another bank.
- The checks run in this order: the size of the request and of its
  alignment in bytes (`AddressOverflow`); `pages` 0 (`InvalidSize`); an
  alignment that is not a power of two, among them 0 (`InvalidAlignment`);
  the generation counter exhausted (`GenerationExhausted`); the rounding of a
  start or the end of a range beyond 64 bits (`AddressOverflow`); then
  `MetadataExhausted` when an extent was passed over for capacity and none
  held the range, and `OutOfMemory` otherwise.

**Zeroing before publication.** A page reaches a holder only once its bytes
are zero, and the core never writes a frame:

- One step: `choose`, then the caller zeroes the chosen range through the
  direct map with `krepi_arch::mmu::zero_frames`, then `assign` with the
  outcome. A failed zeroing leaves the pages free and consumes no
  generation.
- Staged: `reserve` holds the pages at once, reserved, without zeroing them,
  and returns a `Reservation`; the caller zeroes its range, then
  `Reservation::initialized` with the outcome gives an `Initialized`
  packet, or, after a failure, the same reservation with its count of
  failures increased and marked as attempted; `publish` turns the packet
  into a receipt. Other entries may run on the table between the steps.
- `cancel` returns an unused reservation to free; after an attempted
  zeroing it is `ZeroFailed` and returns the reservation, whose holder
  completes a zeroing and publishes it. A reservation or packet that its
  holder drops stays held.

**Receipts.** `release` and `publish` check the arena (`WrongArena`), the
owner identity (`WrongOwner`), and that the receipt names a held range of
exactly its generation and state (`InvalidAllocation`), in this order; a
refused packet is returned to its caller. `cancel` checks first that no
zeroing of the reservation was attempted (`ZeroFailed`), then the arena
(`WrongArena`), the owner identity (`WrongOwner`) and that the reservation
names a held range of exactly its generation in the reserved state
(`InvalidAllocation`), in this order; a refused reservation is returned to
its caller. A released extent merges with the free extents next to it in
the same bank. The generation counter starts at 1, grows by one with each
allocation and reservation, and is never reused: after $2^{64} - 1$ the
table refuses new ones with `GenerationExhausted`.
`validate` makes the checks of `release` without a write. `owner` gives the
owner of a page: the owner of the extent that holds it, or, for a page of a
managed bank in no extent, the first owner in the order firmware, image,
boot storage among the exclusion records that touch it.

**Statistics.** `stats` gives the managed bytes, those of the free and
held pages, without the excluded ones; the free and allocated bytes, where
reserved pages count as allocated; the number of allocations, reservations
included; the number of free extents and the largest; and the extents in
use with the capacity.

**Capacity.** The table manages at most 16 GiB, 4,194,304 pages, which the
boot memory map admits at most, in at most 32 banks. It records at most 160
extents, free and held together, a constant of the core: a request that
would split a free extent beyond it is passed over or refused with
`MetadataExhausted`, and a release never needs an extent. At boot the
table uses one extent for each free run: 4 on the Pi 5 with 8 GB, two in
its first bank, around the image and the device tree, and one in each of
the other two. Apart from the extents it keeps at most 132 exclusion
records, another constant of the core: the 4 spans of boot storage and the
128 firmware reservations that the boot memory map admits at most; more
exclusions fail the initialization with `MetadataExhausted`, and the
records never change after it.

| Error | Rule broken |
| --- | --- |
| `InvalidRange` | No bank, or overlapping banks; a range of length 0 |
| `AddressOverflow` | A size or an end that does not fit in 64 bits |
| `InvalidAlignment` | A bank not on page boundaries; an alignment that is not a power of two |
| `InvalidSize` | A request of 0 pages |
| `InvalidArena` | The arena 0 |
| `MetadataExhausted` | More extents than their capacity, or more exclusions than the capacity of the exclusion records |
| `OutOfMemory` | No free range of the request in the window |
| `GenerationExhausted` | The generation counter after $2^{64} - 1$ |
| `ZeroFailed` | The zeroing of a choice failed, or the cancel of an attempted reservation |
| `WrongArena` | A receipt, packet or reservation of another arena |
| `WrongOwner` | A receipt, packet or reservation of another owner identity |
| `InvalidAllocation` | A receipt, packet or reservation that names no held range of its generation and state, such as a stale or released one |

## Table pool

- A pool holds $N \geq 1$ tables, at a `base` that is a multiple of 4 KiB,
  ending at or below $2^{\mathrm{bits}}$. Every entry on a set other than
  `new`, `reset` and `used` takes `base` and `bits` as arguments, as the
  prototype does, and checks them first ([errors](#errors-of-table-sets));
  `new` and `reset` check nothing ([Check and execute](#check-and-execute)).
- A new table is the one of the lowest free index, zeroed by its plan, and
  a table returns to the pool only through `reset` and through
  `clone_kernel_from`, which empties its target first: `unmap_page` leaves
  an empty table in place.
- **Zero storage.** Every table of a pool that is not in use is zero.
  `new` takes storage that is zero in all its $N$ tables, as the prototype's
  sets start: the BSS of the image for the kernel tables, and held pages,
  which are zero before they are published
  ([zeroing before publication](#page-ownership)), for a process. A table
  leaves use only through `reset` and `clone_kernel_from`, whose plans zero
  every table in use, so the tables not in use stay zero and those plans
  need no `Zero` of them.
- **Count.** A mapping needs the root, one level 2 table for each 1 GiB slot
  that it touches and one level 3 table for each 2 MiB slot that it maps
  in part, with pages. For the direct map, a level 3 table belongs to each
  2 MiB block that a usable range covers in part.
- **Kernel tables.** Both pools are BSS of the image, so their pages are
  image pages. The pool of the direct map holds 80 tables and the pool of
  the lower kernel set 16.
- **The lower kernel set.** It needs 7 tables on QEMU virt and on the Pi 5
  for an image within one 2 MiB block, the device tree, the console and the
  interrupt controller, so 16 leave 9.
- **Beyond capacity.** The boot memory map admits maps whose ranges cover
  more blocks in part than 80 tables allow. `direct_map` then fails with
  `OutOfTables` in its check, before any write, and the boot stops.
- The pools of the tables of address spaces are held pages of the page
  ownership table; their capacity belongs to the address-space component.

**The direct map at 16 GiB.** The table gives the count for each Pi 5
model, from the bank shapes of the
[fdt contract](../../boot-platform/fdt/contract.md#memory-discovery) and
the exclusions that the prototype measured on the 8 GB model: the
firmware's `atf@0` reservation `[0, 0x80000)`, the image
`[0x80000, 0x1a7000)` and the device tree `[0x200000, 0x213ad4)`, which
leave the first two blocks in part.

| Model | Banks | Level 2 | Level 3 | Tables | Blocks | Pages |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 1 GB | 1, inferred | 1 | 2 | 4 | 508 | 581 |
| 2 GB | 2, inferred | 2 | 2 | 5 | 1,020 | 581 |
| 4 GB | 2, inferred | 4 | 2 | 7 | 2,044 | 581 |
| 8 GB | 3, measured | 8 | 2 | 11 | 4,092 | 581 |
| 16 GB | 3, inferred | 16 | 2 | 19 | 8,188 | 581 |

The count of the 8 GB model equals the 11 tables, 4,092 blocks and 581
pages that the prototype measured. At 16 GiB the pool of 80 tables leaves
61 for further 2 MiB blocks covered in part; contiguous 16 GiB of blocks
from address 0 would need 17. QEMU virt with its 128 MiB needs the root,
one level 2 table and one level 3 table for each block that the device tree
or the image covers in part, at most 4.

## Check and execute

- `map_page`, `map_block`, `unmap_page` and `clone_kernel_from` complete
  every check of [Errors of table sets](#errors-of-table-sets) before their
  first write. The write phase records the tables that the plan takes from
  the pool and returns the plan; it cannot fail, and the plan cannot fail.
- `kernel_map` and `direct_map` check every range and the tables that the
  whole plan needs before the first write: a map that does not fit fails
  with `OutOfTables` and leaves the set as it was, with no step executed.
- `Tables::new` and `reset` check nothing and do not fail; `new` relies on
  its caller for storage that is zero, and `reset` for the unreachability
  of the set.
- `choose`, `owner`, `validate`, `stats`, `lookup_page`, `lookup_block`,
  `used`, `descriptor` and `direct_address` write nothing.
- `Ownership::new`, `assign`, `reserve`, `publish`, `cancel` and `release`
  complete their checks, the extents they need against the capacity among
  them, before their first write. The write phase of an ownership entry may
  fail only for capacity, with `MetadataExhausted`, and then restores the
  table from before the entry; since the entries of this page count the
  extents in their checks, their write phases do not fail.
- A rejected request writes nothing, a counter of failures included.
- `krepi_arch::mmu::apply` executes a plan that the check of its entry
  fixed and does not fail. `enable` and `zero_frames` check nothing and do
  not fail; their callers vouch for their arguments.

## Work bounds

- `map_page`, `map_block`, `unmap_page`, `lookup_page` and `lookup_block`
  read at most one entry at each of the three levels; their plans have at
  most seven steps, among them at most two `Zero` of 512 entries each.
- `reset` has a plan of one `Zero` for each table in use, at most $N$.
- `clone_kernel_from` reads each entry of each table in use of the source
  once, at most $512 N$ entries, and marks each table once; its plan has
  one `Zero` for each table in use of the target, at most $N$, one `Store`
  for each valid entry of the source, at most $512 N$, and one `Sync`.
- `kernel_map` checks each of at most 16 ranges against the others and each
  page of each range once, and its plan has one `Store` for each page and
  table, one `Zero` for each new table and one `Fence` for each table
  descriptor.
- `direct_map` walks each usable range once in steps of a block or a
  page: at most RAM / 2 MiB blocks and, at the two ends of each range, at
  most 511 pages each. Its plan has one `Store` for each block, page and
  table descriptor, one `Zero` for each new table, at most 80, and one
  `Fence` for each table descriptor; it runs to its end at boot.
- `Ownership::new` compares each of at most 32 banks with the others and
  each of at most 132 exclusions with each bank, and writes at most 132
  exclusion records; `choose`, `assign`, `reserve`, `publish`, `cancel`,
  `release` and `validate` scan or shift at most the 160 extents once;
  `owner` scans at most the 160 extents and then the 132 exclusion
  records.
- `zero_frames` writes each byte of its range once; `enable` runs a fixed
  sequence.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls.

## Determinism

- A new table is the one of the lowest free index of the pool, so a set
  takes its tables in the order in which its plans first need them;
  `clone_kernel_from` gives its target the indices of the source.
- The order of the steps of a plan is fixed by
  [Write plans and publication](#write-plans-and-publication); the direct
  map is walked in address order, with a block wherever the rule allows one.
- The page ownership table scans its extents in address order and takes the
  first fit; the placement, low or high, and the window are the caller's.
  The range that an allocation receives follows from the state of the table,
  which the order of earlier entries decides. With more than one CPU, that
  order is the multicore interleaving that
  [ND-03](../../../security.md#nd-03) of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  allows; the component leaves no other choice open.
- The generation of an allocation is the counter of the table.
- The tables, the plans and the owners follow from the boot memory map,
  the layout and the requests alone, so cold boots of one board with the
  same firmware give the same direct map and the same kernel tables.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The descriptors of the lower kernel set | Shared | The boot CPU, which builds them before the MMU is on; then the token of the kernel tables, for a plan that fills an invalid entry | The `Sync` that ends the plan | Once, before secondary CPUs start; a later fill by its `Sync`, and another CPU executes `DSB` and `ISB` before it relies on the entry ([published data](../../../conventions/smp.md#page-tables-and-published-data)) |
| The descriptors of the direct map's set | Shared, read-only after boot | The boot CPU, which builds them before the MMU is on | The `ISB` after `enable` writes `TTBR1_EL1` on the boot CPU | Once, before secondary CPUs start; the field never changes after it |
| The tables in use of the pools of the kernel tables | Shared | The boot CPU; then the token of the kernel tables | The end of the write phase of the entry | Under the token |
| The page ownership table: its extents, exclusion records, generation counter and arena | Shared | The token of the page ownership table, held by one CPU at a time; with one CPU, by the executing CPU | The end of the write phase of the entry | Under the token, by the release of the lock that provides it once CPUs share it |
| `MAIR_EL1`, `TCR_EL1`, `TTBR0_EL1`, `TTBR1_EL1` and `SCTLR_EL1` | Per-CPU | The executing CPU | The `ISB` after the writes of `enable` | `none`: each CPU writes its own |

A reservation, an initialized packet and a receipt are values of their
holder and take the class of the holder's state. The boot memory map is a
field of the fdt component, and the table set of an address space a field
of the address-space component. The TLB entries that a plan invalidates are
classified in the
[State fields](../../boot-platform/boot/contract.md#state-fields) of the
boot contract.

## Testing obligations

- The host tests of the module `page_tables` hold the frozen vectors of
  [Legacy test vectors](#legacy-test-vectors), each with its expected output,
  and write their results for the comparison with the specification
  ([host results](../../../formal-verification.md#host-results)).
- Four host tests build the direct map of the Pi 5 models with 1, 2, 4 and
  16 GB from the bank shapes that the fdt contract infers and the exclusions
  of [Table pool](#table-pool), and check every 2 MiB block against an
  independent page model as `dm-04` does, with the counts of tables, blocks
  and pages of that table. The 8 GB model is the frozen vector `dm-04`.
  These models are not run on a board in release 0.1; only the 8 GB model
  is.
- A host test builds a direct map that needs exactly the 80 tables of the
  pool, and one that needs 81 fails with `OutOfTables` and gives no plan.
- A host test initializes the page ownership table from the boot memory map
  of each board shape and checks against an independent page model that
  every managed page has exactly one owner, and that the free pages are
  exactly the pages of the direct map; another fills the 160 extents exactly
  and refuses one more with `MetadataExhausted`; and an initialization with
  132 exclusions succeeds and one with 133 fails with `MetadataExhausted`.
- A host test gives `kernel_map` a layout whose text and data share a page,
  and `kernel_map` refuses it, so no page is mapped writable and executable.
- Host tests hold each plan of `map_page`, `map_block`, `unmap_page`,
  `clone_kernel_from`, `kernel_map` and `direct_map` against the order of
  [Write plans and publication](#write-plans-and-publication), written from
  this page.
- QEMU tests on QEMU virt with the MMU on read and write pages at the edges
  of the direct map's ranges and of its excluded ranges through the direct
  map, and take the fault of a write to a `ReadOnly` page, of an execution
  from an execute-never page, of an access to a guard and of an access to an
  excluded page; a `Device` page of the console is written. Three cold
  boots give the same counts of the direct map and of the kernel tables.
- On the Pi 5 with 8 GB, the board runs build the direct map of the whole
  RAM and check its counts against [Table pool](#table-pool).

## Open obligations

The entries of the page-table logic that later components add, such as the
entries of the tables of an address space and of their ASIDs, are open
obligations of the contracts that add them, carried by the proof of
contexts, user copies and the private VM, by release 0.2; the table below
lists the obligations of the code of this page.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/arch/src/mmu.rs#store_descriptor` (planned) | `unsafe` | Writes the translation tables that the page-table logic describes: one descriptor of a write plan | The proof of the cache and TLB maintenance primitives and of the cache maintenance ranges | `0.2` |
| `kernel/arch/src/mmu.rs#zero_table` (planned) | `unsafe` | Writes the translation tables that the page-table logic describes: the 512 entries of a new table of a write plan | The proof of the cache and TLB maintenance primitives and of the cache maintenance ranges | `0.2` |
| `kernel/arch/src/mmu.rs#synchronize` (planned) | `unsafe` | Neither (executes `DMB ISHST`, `DSB ISH` and `ISB` for a write plan, and `TLBI VMALLE1`, `DSB NSH` and `ISB` before the MMU is on) | The proof of the cache and TLB maintenance primitives and of the cache maintenance ranges | `0.2` |
| `kernel/arch/src/mmu.rs#enable` (planned) | `unsafe` | Neither (writes `MAIR_EL1`, `TCR_EL1`, `TTBR0_EL1`, `TTBR1_EL1` and `SCTLR_EL1`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` |
| `kernel/arch/src/mmu.rs#zero_frames` (planned) | `unsafe` | Neither (writes zeros into the frames of a range through the direct map) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` |
| `kernel/arch/src/mmu.rs` (planned) | `code` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` |

## Legacy test vectors

The component freezes 53 vectors from the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`. A vector of this
page is one `#[test]` function of the prototype; in the vector file it is
the lines whose id starts with the id of the vector and a dot, one line for
each case, `<vector>.<n>` from 1 in the order of the test, where a case is
one call of an entry that the test makes with the output that it asserts.
The expected outputs below are the assertions of the test bodies.

| File | Vectors |
| --- | ---: |
| `src/memory/extents.rs` | 1 |
| `src/memory/tests.rs` | 15 |
| `src/memory/tests/banks.rs` | 6 |
| `src/memory/tests/reservations.rs` | 6 |
| `src/arch/aarch64/paging/tests.rs` | 21 |
| `src/platform/mapping.rs` | 4 |

The prototype's MMU integration, `src/mmu.rs` with the four files below
`src/mmu/`, and its boot memory setup, `src/boot_memory.rs` with
`src/boot_memory/banks.rs`, have no host test, so they give no vector.

**Notation.** Addresses, lengths and descriptors are written as `0x` and
lowercase hexadecimal digits without separators, counts in decimal, bytes
as two lowercase hexadecimal digits each, and a range as `<start>+<length>`.
A kind, an error and a region, `lower` or `upper`, are written by their
names on this page. The output of a call is `ok`, followed by its fields,
or `err=<error>`; a structured value is a list of `key=value` fields
separated by single spaces, in the order of the expected output below.

**Vectors of a property.** `own-22` and `dm-04` assert a property over a
generated family of inputs, which the vector file expands into lines; their
rows state the property and the generation rule. `own-14` is of the same
kind, and its row states them too; it does not apply, so the vector file
has no line for it.

**Behaviour changes.** These rules differ from the prototype:

- The prototype's allocation with a zeroing callback is `choose`, the
  caller's zeroing and `assign`; its staged reservation takes the outcome
  of the zeroing in `Reservation::initialized` instead of a callback. The
  outputs are unchanged.
- A rejected request writes nothing: the table keeps no count of failed
  requests and of failed zeroings. The assertions of `own-07`, `own-11` and
  `own-24` on those counts are dropped; their other outputs stay.
- `direct_map` checks the whole map before its first write, where the
  prototype could leave a partial map to discard; the output of `dm-03` is
  unchanged.
- The direct map is never changed after boot, so the prototype's sealing of
  a page, with the split and merge of its block, is not carried, and
  `pt-19` and `pt-20` do not apply.
- The kernel has no byte heap: `own-12` to `own-15` do not apply.
- The table records the owner of every excluded page, firmware, image or
  boot storage, in at most 132 exclusion records apart from its extents,
  and `owner` names it; the prototype kept only its extents. No output of a
  vector changes.

### `src/memory/extents.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `own-01` | 395 | `generation_exhaustion_never_wraps_to_an_old_receipt` | A table of one page `0x0+0x1000`, capacity 2, whose generation counter is $2^{64} - 1$: the allocation of 1 page gets `0x0+0x1000` with generation `0xffffffffffffffff`; its release is `ok`; the next allocation is `err=GenerationExhausted` and asks for no zeroing | `choose`, `assign`, `release` |

### `src/memory/tests.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `own-02` | 22 | `ranges_preserve_high_addresses_and_reject_invalid_bounds` | `0x1000000000+0x2000` ends at `0x1000002000`, contains `0x1000001000+0x8` and does not overlap `0x1000002000+0x1`; a range of length 0 at `0x1` is `err=InvalidRange`; `0xfffffffffffffffd+0x3` is `err=AddressOverflow`; `0xfffffffffffffffd+0x2` ends at `0xffffffffffffffff` | `PhysRange::new`, `end`, `contains` and `overlaps` |
| `own-03` | 33 | `initialization_rejects_unaligned_ram_and_missing_metadata` | Capacity 8: RAM `0x1+0x1000` and `0x0+0x1001` are each `err=InvalidAlignment`; capacity 0 with RAM `0x0+0x1000` is `err=MetadataExhausted`; arena 0 is `err=InvalidArena` | `Ownership::new` |
| `own-04` | 53 | `overlapping_and_unaligned_reservations_exclude_whole_pages` | RAM `0x0+0x8000`, exclusions `0x1001+0x1`, `0x1fff+0x2`, `0x2000+0x1000` and `0x9000+0x1`, the last outside the RAM: managed bytes `0x6000`; allocations of 1 and 5 pages get `0x0+0x1000` and `0x3000+0x5000`, and the zeroing covers exactly those ranges, never `0x1000+0x2000`; after both releases, 2 free extents | `Ownership::new`, `choose`, `assign`, `release`, `stats` |
| `own-05` | 83 | `reservations_can_cover_all_ram_or_exceed_metadata_capacity` | RAM `0x1000+0x4000` with the exclusion `0x0+0x8000`: managed bytes 0, and an allocation of 1 page is `err=OutOfMemory` without zeroing; capacity 1 with the exclusion `0x2000+0x1000` is `err=MetadataExhausted` | `Ownership::new`, `choose` |
| `own-06` | 98 | `page_alignment_and_zeroing_work_above_four_gib` | RAM `0x100001000+0x8000`: owner 7 allocates 2 pages at an alignment of 4 and gets `0x100004000+0x2000`, which is the range zeroed, owner 7; after its release, the largest free extent is `0x8000` | `choose`, `assign`, `release`, `stats` |
| `own-07` | 118 | `invalid_page_requests_never_call_zero_backend` | RAM `0x0+0x8000`: 0 pages is `err=InvalidSize`; an alignment of 3 and of 0 pages are each `err=InvalidAlignment`; $2^{64} - 1$ pages is `err=AddressOverflow`; none asks for zeroing, and allocated bytes stay 0 | `choose` |
| `own-08` | 141 | `metadata_exhaustion_is_distinct_from_ram_exhaustion` | Capacity 1, RAM `0x0+0x2000`: 1 page is `err=MetadataExhausted` without zeroing; 2 pages succeed; 1 more page is `err=OutOfMemory`; after the release, free bytes `0x2000` and 1 extent in use | `choose`, `assign`, `release`, `stats` |
| `own-09` | 161 | `foreign_owner_and_arena_cannot_release_allocation` | Arena 1 with RAM `0x0+0x1000` and arena 2 with RAM `0x2000+0x1000`: owner 9 allocates 1 page at arena 1; its release by owner 8 is `err=WrongOwner`, at arena 2 `err=WrongArena`, and the statistics stay unchanged; the release by owner 9 at arena 1 is `ok` | `assign`, `release`, `stats` |
| `own-10` | 176 | `double_and_stale_frees_cannot_free_a_reused_address` | RAM `0x0+0x1000`: owner 3 allocates and releases 1 page; a second release of that receipt is `err=InvalidAllocation`; the next allocation gets the same range with another generation, zeroed, and the old receipt stays `err=InvalidAllocation`; 1 allocation remains | `choose`, `assign`, `release`, `stats` |
| `own-11` | 197 | `partial_zero_failure_does_not_publish_or_consume_allocation` | RAM `0x0+0x1000`: an allocation of 1 page whose zeroing fails is `err=ZeroFailed`; after it, allocated bytes 0 and free bytes `0x1000`; the next allocation, by owner 2, gets generation 1 | `choose`, `assign`, `stats` |
| `own-12` | 219 | `heap_alignment_padding_and_adjacent_frees_coalesce` | A byte heap at `0x1003+0x40`: allocations at `0x1010+0x8` and `0x1020+0x10`, which merge into one free extent of `0x40` after their release | Not applicable: the kernel has no byte heap |
| `own-13` | 239 | `fragmentation_fails_large_request_until_adjacent_spans_are_released` | A byte heap of `0x40`: 24 bytes are `err=OutOfMemory` while the free spans are apart, and 48 bytes get `0x0+0x30` once they are adjacent | Not applicable: the kernel has no byte heap |
| `own-14` | 274 | `bounded_heap_trace_matches_independent_byte_ownership_model` | Property. A byte heap of 64 bytes at `0x1000000000`, capacity 64. Steps $s$ from 0 to 399: when $s \bmod 3 = 2$ and an allocation is live, release the live allocation at position $\lfloor s / 3 \rfloor \bmod n$ of the $n$ live ones in the order of their allocation; otherwise owner 5 allocates $s \bmod 9 + 1$ bytes at an alignment of $2^{s \bmod 3}$ bytes. An independent model marks each byte busy or free and expects a fit exactly when some aligned run of free bytes of the length exists. Every allocation succeeds exactly when the model has a fit, with an aligned start on free bytes that read zero, and fails with `err=OutOfMemory` otherwise; after every step the allocated bytes are the model's busy bytes; after the release of every live allocation, free bytes 64 and 1 extent in use | Not applicable: the kernel has no byte heap |
| `own-15` | 323 | `address_rounding_and_span_end_overflow_do_not_reach_backend` | Byte-granular ranges `0xfffffffffffffff9+0x6` and `0xfffffffffffffff8+0x7` of the byte heap: a rounding and an end beyond 64 bits are `err=AddressOverflow` without zeroing | Not applicable: the test drives the byte heap; the same failure of a page request is in `own-07` and `own-28` |
| `own-16` | 339 | `exact_later_extent_can_allocate_without_metadata_for_earlier_split` | Capacity 2, RAM `0x0+0x4000` with the exclusion `0x2000+0x1000`: 1 page skips the first extent, whose split would need a third extent, and gets `0x3000+0x1000`; free bytes `0x2000` after it and `0x3000` after its release | `choose`, `assign`, `release`, `stats` |

### `src/memory/tests/banks.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `own-17` | 4 | `banks_reject_empty_overlap_unaligned_and_excess_metadata` | No bank is `err=InvalidRange`; the banks `0x0+0x2000` with `0x1000+0x1000`, and `0x0+0x1000` twice, are each `err=InvalidRange`; the bank `0x1+0x1000` is `err=InvalidAlignment`; the banks `0x0+0x1000` and `0x2000+0x1000` with capacity 1 are `err=MetadataExhausted` | `Ownership::new` |
| `own-18` | 33 | `adjacent_banks_never_merge_after_release_in_either_order` | Banks `0x1000+0x2000` and `0x3000+0x2000`: two allocations of 2 pages take one bank each; after their release, in either order, 2 free extents, the largest `0x2000`, and 3 pages are `err=OutOfMemory` without zeroing; a high placement of 1 page gets `0x4000+0x1000` | `Ownership::new`, `choose`, `assign`, `release`, `stats` |
| `own-19` | 60 | `unsorted_banks_and_reservations_preserve_physical_order_and_holes` | Banks `0x100000000+0x4000` and `0x0+0x4000`, in this order, with the exclusions `0x3001+0xffffd000` and `0x1001+0x1`: managed bytes `0x5000`; with high placement, 3 pages get `0x100001000+0x3000` and then 1 page `0x2000+0x1000`; after both releases, 3 free extents | `Ownership::new`, `choose`, `assign`, `release`, `stats` |
| `own-20` | 79 | `high_placement_honors_alignment_window_and_backend_failure` | RAM `0x100000000+0x10000`, high placement, window `0x100001001+0xc000`: 2 pages of owner 1 at an alignment of 4 are chosen at `0x100008000+0x2000`, whose failed zeroing is `err=ZeroFailed` and leaves free bytes `0x10000`; owner 2 then gets the same range with generation 1; the window `0x0+0x1000` is `err=OutOfMemory` without zeroing | `choose`, `assign`, `release`, `stats` |
| `own-21` | 103 | `multi_gib_capacity_is_bookkeeping_without_host_ram_access` | Capacity 2, banks `0x40000000+0xc0000000` and `0x100000000+0x100000000`: one allocation of the whole first bank with low placement and one of the whole second with high placement leave free bytes 0 and managed bytes `0x1c0000000`; after both releases, 2 free extents and 2 extents in use | `Ownership::new`, `choose`, `assign`, `release`, `stats` |
| `own-22` | 125 | `mixed_placement_matches_an_independent_sparse_page_model` | Property. Banks `0x100000+0x18000`, `0x118000+0x18000` and `0x100001000+0x18000`, exclusions `0x102fff+0x2`, `0x117fff+0x2` and `0x100014000+0x1000`, capacity 128. Steps $s$ from 0 to 799: when $s \bmod 3 \neq 0$ and an allocation is live, release the live allocation at position $7s \bmod n$ of the $n$ live ones in the order of their allocation; otherwise owner 7 allocates $s \bmod 5 + 1$ pages at an alignment of $2^{s \bmod 4}$ pages, high when $s$ is even and low when it is odd. An independent model marks the pages of each bank busy or free, the excluded pages busy throughout, and expects the lowest, or for a high placement the highest, aligned start of a free run of the length within one bank. Every allocation starts at the model's start, `err=OutOfMemory` exactly when the model has none, and after every step the free bytes are the model's free pages times `0x1000` with every excluded page still busy; after the release of every live allocation, the free bytes are those of the pages that no exclusion touches. Lines `own-22.1` to `own-22.800`, one for each step: `start=<address> free=<bytes>`, `err=OutOfMemory free=<bytes>` or `released free=<bytes>`; line `own-22.801`: `free=<bytes>` | `Ownership::new`, `choose`, `assign`, `release`, `stats` |

### `src/memory/tests/reservations.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `own-23` | 4 | `reservation_excludes_uninitialized_bytes_until_external_zeroing_completes` | Arena 7, RAM `0x0+0x4000`: owner 11 reserves 2 pages and gets `0x0+0x2000` without any zeroing, allocated bytes `0x2000` and 1 allocation; owner 22 allocates 1 page outside it; after the zeroing of the reservation, its packet validates and its publication gives a receipt of `0x0+0x2000`; after both releases, free bytes `0x4000` | `reserve`, `Reservation::initialized`, `validate`, `publish`, `assign`, `release`, `stats` |
| `own-24` | 31 | `failed_initialization_retains_partial_bytes_and_cannot_cancel_as_unused` | Arena 3, RAM `0x0+0x2000`: owner 4 reserves 2 pages; a failed zeroing returns the reservation with 1 failure and leaves the statistics unchanged; its cancel is `err=ZeroFailed` and returns it; a reservation by owner 9 is `err=OutOfMemory`; a second failed zeroing gives 2 failures; after a zeroing, the publication by owner 9 is `err=WrongOwner` and returns the packet, and by owner 4 `ok`; after the release, free bytes `0x2000` | `reserve`, `Reservation::initialized`, `cancel`, `publish`, `release`, `stats` |
| `own-25` | 65 | `arena_and_owner_mismatch_never_consume_the_retained_packet` | Arena 1 with RAM `0x0+0x2000` and arena 2 with RAM `0x2000+0x2000`: owner 7's reservation at arena 1 is not cancelled at arena 2, `err=WrongArena`, nor by owner 8, `err=WrongOwner`, and the statistics of arena 1 stay unchanged; after its zeroing, its validation and publication at arena 2 are `err=WrongArena`, and its publication at arena 1 is `ok`; after its release, a new reservation, zeroed and published, gets the same range with a larger generation, and the old receipt is `err=InvalidAllocation` | `reserve`, `cancel`, `Reservation::initialized`, `validate`, `publish`, `release` |
| `own-26` | 98 | `unused_reservations_roll_back_without_touching_bytes_or_reusing_generations` | Arena 5, RAM `0x0+0x3000`: owner 1 reserves 3 pages; 1 more page is `err=OutOfMemory`; the cancel is `ok`, nothing is zeroed and no allocation remains; a new reservation of 3 pages, zeroed and published, has generation 2 | `reserve`, `cancel`, `Reservation::initialized`, `publish`, `release`, `stats` |
| `own-27` | 118 | `dropped_reservations_stay_excluded_instead_of_implicitly_releasing_backing` | Arena 17, RAM `0x0+0x3000`: a reservation of `0x0+0x1000` and a zeroed packet of `0x1000+0x1000` that their holders drop stay held; the next reservation gets `0x2000+0x1000`, a fourth is `err=OutOfMemory`, and allocated bytes are `0x3000`; after the cancel of the third, `0x2000` | `reserve`, `Reservation::initialized`, `cancel`, `stats` |
| `own-28` | 142 | `staged_placement_respects_windows_banks_exclusions_and_high_alignment` | Arena 29, banks `0x0+0x4000` and `0x8000+0x8000`, exclusion `0xa000+0x1000`: reservations in the windows `0x4000+0x4000`, a hole, and `0xa000+0x1000`, the exclusion, are `err=OutOfMemory`; 0 pages is `err=InvalidSize`; an alignment of 3 is `err=InvalidAlignment`; $2^{64} - 1$ pages is `err=AddressOverflow`; free bytes stay; with high placement, 2 pages at an alignment of 2 in the window `0x8000+0x8000` get `0xe000+0x2000`, and 2 pages in the window `0x8000+0x3000` get `0x8000+0x2000`; after both cancels, the free bytes and free extents are those from before | `Ownership::new`, `reserve`, `cancel`, `stats` |

### `src/arch/aarch64/paging/tests.rs`

Each set is at `base` `0x100000000` with width 40 unless the row says
otherwise.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `pt-01` | 5 | `high_addresses_keep_all_bits_and_enforce_permissions` | Lower set of 6 tables: `0x200000000` to `0x1008000000` as `ReadOnly`; its page descriptor has the output address `0x1008000000`, AP[2] 1, PXN 1, UXN 1 and AP[1] 0 | `map_page`, `lookup_page`, `descriptor` |
| `pt-02` | 19 | `attributes_separate_text_data_and_mmio` | `ReadExecute`: AP[2] 1, PXN 0; `ReadWrite`: AP[2] 0, PXN 1, AttrIndx 1; `Device`: AttrIndx 0, PXN 1 | `Kind`, `descriptor` |
| `pt-03` | 33 | `errors_are_atomic_and_no_implicit_remapping` | Lower set of 3 tables: `0x40000000` to itself as `ReadWrite` uses 3 tables; the same address to `0x40001000` as `Device` is `err=AlreadyMapped` and leaves the descriptor unchanged; `0x80000000` to `0x0` is `err=OutOfTables` with 3 tables in use, and `lookup_page` there is `err=NotMapped` | `map_page`, `lookup_page`, `used` |
| `pt-04` | 53 | `invalid_width_alignment_and_table_backing_rejected` | Lower set of 3 tables, `map_page` as `ReadWrite`: the virtual address `0x1`, the physical address `0x1` and the base `0x100000001` are each `err=Alignment`; the virtual address `0x8000000000` and the physical address `0x10000000000` are each `err=AddressWidth`; the base `0xfffffff000` is `err=TableBacking`; 1 table stays in use after each | `map_page`, `used` |
| `pt-05` | 69 | `unmap_and_reuse_only_the_requested_leaf` | Lower set of 4 tables: `0x0` to `0x1000` as `ReadWrite` and `0x1000` to `0x2000` as `ReadOnly`; `unmap_page` of `0x0` returns `0x1000`, a second is `err=NotMapped`; `0x1000` stays mapped; `0x0` to `0x3000` as `ReadOnly` gives the output address `0x3000` | `map_page`, `unmap_page`, `lookup_page` |
| `pt-06` | 82 | `user_pages_enforce_el0_access_wx_and_asid_scope` | Lower set of 3 tables, each page mapped to its own address: `UserReadExecute` AP `0b11` and UXN 0, `UserReadOnly` AP `0b11` and UXN 1, `UserReadWrite` AP `0b01` and UXN 1, each with PXN 1, nG 1, SH `0b11`, AttrIndx 1 and AF 1, and none writable and executable; `ReadExecute`, `ReadOnly`, `ReadWrite` and `Device` have AP[1] 0, nG 0 and UXN 1 | `Kind`, `descriptor`, `map_page`, `lookup_page` |
| `pt-07` | 114 | `cloned_kernel_tables_are_private_and_keep_global_physical_leaves` | A source set of 10 tables with `0x4000` to `0x40000000` as `ReadExecute`, `0x9000000` to itself as `Device` and `0x40000000` to `0x200000000` as `ReadWrite`, and a target set of 10 tables at `0x10000a000` with `0x80000000` to `0x0` as `ReadWrite`: the copy of the kernel tables into the target leaves the source unchanged; the target uses as many tables as the source; each of the three leaves has the source's descriptor, with that output address and nG 0, under level 1 and level 2 table descriptors that point at the target's tables of the source's indices; `0x80000000` is `err=NotMapped` in the target; after `0x8000` to `0x6000` as `UserReadWrite` in the target, `0x8000` is `err=NotMapped` in the source; after `unmap_page` of `0x4000` in the source, the target still maps it | `clone_kernel_from` with its plan, `map_page`, `unmap_page`, `lookup_page`, `used` |
| `pt-08` | 166 | `kernel_clone_errors_preserve_the_destination` | A source set of 6 tables with `0x0` to `0x4000` as `ReadOnly`, and a target set of 6 tables at `0x100006000` with `0x1000` to `0x8000` as `ReadWrite`. The copy with the source base, the target base and the width `0x100000000`, `0x100000000`, 40 and `0x100000000`, `0x100001000`, 40 is `err=TableBacking`; `0x100000001`, `0x100006000`, 40 and `0x100000000`, `0x100006001`, 40 `err=Alignment`; `0x100000000`, `0x100006000`, 31 `err=AddressWidth`; `0x100000000`, `0xfffffff000`, 40 `err=TableBacking`. With the source root entry 0 replaced by `0x100000003`, by `0x100005003` or by the valid entry with bit 6 set, the copy fails; with root entries 0 and 1 on one table, `err=TableBacking`; with one more table counted in use than the entries reach, `err=TableBacking`; with the leaf replaced by `0x0` to `0x4000` as `UserReadOnly`, `err=InvalidDescriptor`. After each failure the target's tables and its count of tables in use are unchanged | `map_page`, `unmap_page`, `clone_kernel_from`, `used` |
| `pt-09` | 230 | `whole_address_space_reset_reclaims_intermediate_tables` | Lower set of 4 tables: `0x0` to `0x1000` as `ReadWrite` and `0x200000` to `0x2000` as `UserReadWrite`, then `unmap_page` of `0x0`: 4 tables in use; after `reset`, 1 table in use, every entry 0, and `lookup_page` of `0x200000` is `err=NotMapped`; `0x40000000` to `0x8000` as `UserReadExecute` then uses 3 tables and gives the output address `0x8000` | `map_page`, `unmap_page`, `reset`, `lookup_page`, `used` |
| `pt-10` | 258 | `kernel_clone_rejects_leaf_physical_addresses_outside_the_profile` | A source set of 3 tables of width 48 with `0x0` to `0x10000000000` as `ReadOnly`: the copy into a target set of 3 tables at `0x100003000` of width 40 is `err=InvalidDescriptor`, and the target has 1 table in use and every entry 0 | `map_page`, `clone_kernel_from`, `used` |
| `pt-11` | 273 | `private_kernel_stacks_are_privileged_non_executable_and_asid_scoped` | Two lower sets of 6 tables at `0x100000000` and `0x100007000`: `0x20001000` to `0x41000000` and to `0x42000000` as `KernelPrivateReadWrite`, each with AP `0b00`, PXN 1, UXN 1, nG 1, SH `0b11`, AttrIndx 1 and AF 1; the guard `0x20000000` is `err=NotMapped` in both; after `unmap_page` in the first set, the second still maps `0x42000000` | `Kind`, `map_page`, `unmap_page`, `lookup_page` |
| `pt-12` | 308 | `kernel_template_clone_rejects_private_privileged_stack_mappings` | A source set of 3 tables with `0x20001000` to `0x41000000` as `KernelPrivateReadWrite`, and a target set of 3 tables at `0x100004000` with `0x40000000` to itself as `ReadWrite`: the copy is `err=InvalidDescriptor`, and the target's tables and its count of tables in use are unchanged | `map_page`, `clone_kernel_from`, `used` |
| `pt-13` | 335 | `zeroed_table_storage_can_be_initialized_in_place` | A set of 3 tables whose storage and record of tables in use are all 0: after `reset`, 1 table in use; `0x20001000` to `0x41000000` as `KernelPrivateReadWrite` gives that output address | `reset`, `map_page`, `lookup_page`, `used` |
| `pt-14` | 360 | `lower_and_upper_tables_reject_each_others_canonical_addresses` | An upper set of 3 tables refuses `0x0`, `0x1000` and `0x7ffffff000` with `err=AddressWidth`; a lower set of 3 refuses `0xffffff8000000000`, `0xffffff8000001000` and `0xfffffffffffff000`; both refuse `0x8000000000` and `0xffffff7ffffff000`; the upper set maps `0xffffff8000000000` to `0x100000000`, and the lower set keeps 1 table in use | `map_page`, `lookup_page`, `used` |
| `pt-15` | 401 | `blocks_are_privileged_global_nx_and_cannot_be_removed_as_pages` | Upper set of 3 tables: a block of `0xffffff8100000000` to `0x100000000`; its block descriptor has the output address `0x100000000`, bits 1 and 0 `0b01`, AP `0b00`, PXN 1, UXN 1, nG 0, SH `0b11` and AttrIndx 1; at the offsets `0x0`, `0x1000` and `0x1ff000`, `unmap_page` is `err=NotMapped` and `map_page` `err=AlreadyMapped`; the block is unchanged and 2 tables are in use | `map_block`, `lookup_block`, `unmap_page`, `map_page`, `used` |
| `pt-16` | 432 | `block_errors_preserve_existing_storage_and_do_not_promote_page_tables` | Lower set of 3 tables with `0x0` to `0x0` as `ReadOnly`, 3 in use: blocks (virtual, physical) `(0x0, 0x0)` are `err=AlreadyMapped`, `(0x1000, 0x0)` and `(0x200000, 0x1000)` `err=Alignment`, `(0x200000, 0x10000000000)` and `(0x8000000000, 0x0)` `err=AddressWidth`, and `(0x40000000, 0x0)` `err=OutOfTables`, each leaving the tables unchanged with 3 in use; after `unmap_page` of `0x0`, the block `(0x0, 0x0)` stays `err=AlreadyMapped` | `map_block`, `map_page`, `unmap_page`, `used` |
| `pt-17` | 456 | `eight_gib_of_blocks_use_nine_tables_and_cross_root_boundaries` | Upper set of 9 tables: 4,096 blocks map `0xffffff8000000000` plus `pa` to `pa` for every multiple `pa` of `0x200000` below `0x200000000`, with 9 tables in use; `lookup_block` at `pa` `0x0`, `0x3fe00000`, `0x40000000`, `0x100000000` and `0x1ffe00000` gives `pa`; the block of `0x200000000` is `err=OutOfTables` | `map_block`, `lookup_block`, `used` |
| `pt-18` | 487 | `cloning_a_block_map_is_rejected_without_changing_the_destination` | An upper source set of 3 tables with a block of `0xffffff8000000000` to `0x0`, and an upper target set of 3 tables at `0x100004000` with `0xffffff8000001000` to `0x1000` as `ReadOnly`: the copy is `err=InvalidDescriptor`, and the target's tables and its count of tables in use are unchanged | `map_block`, `map_page`, `clone_kernel_from`, `used` |
| `pt-19` | 513 | `sealed_ram_pages_split_and_restore_blocks_without_table_leaks` | A set of 5 tables with the RAM blocks of `0x40000000` to `0x100000000` and of `0x40200000` to `0x100200000`, $t$ tables in use. 20 times: sealing `0x40002000` splits its block with four synchronizations and gives it the bits of `ReadOnly`, while `0x40003000` keeps those of `ReadWrite`; sealing `0x40203000` too, then unsealing `0x40002000` leaves $t + 1$ tables in use, and unsealing `0x40203000` leaves $t$. Afterwards the block of `0x40000000` has the output address `0x100000000` | Not applicable: the direct map never changes after boot |
| `pt-20` | 546 | `splitting_capacity_and_non_ram_permissions_fail_without_publication` | A set of 2 tables with the RAM block of `0x0` to `0x200000`: sealing `0x0` is `err=OutOfTables` without a synchronization, and the block descriptor is unchanged. A set of 3 tables with `0x0` to `0x200000` as `Device`: sealing `0x0` is `err=InvalidDescriptor` without a synchronization | Not applicable: as `pt-19` |
| `pt-21` | 564 | `delegated_device_pages_are_rw_nx_non_global_with_device_attributes` | `UserDevice`: AttrIndx 0, AP `0b01`, PXN 1, UXN 1, nG 1 | `Kind`, `descriptor` |

### `src/platform/mapping.rs`

Each direct map is built in an upper set at `base` `0x80000` with width 40,
from the boot memory map that `MemoryPlan::new`, with a managed window, or
`MemoryPlan::all_ram` of the fdt component builds from the banks, the
boot storage and the firmware reservations of the row.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `dm-01` | 75 | `reservations_and_boot_pages_break_blocks_without_writable_aliases` | Bank `0x0+0x1000000`, managed window the whole bank, boot storage `0x80000+0x1000`, a `reusable` firmware reservation `0x600fff+0x2`, 8 tables: bytes `0xffd000`, 6 blocks and 1,021 pages; `0x80000`, `0x600000` and `0x601000` are `err=NotMapped`; the block of `0x200000` and the pages `0x81000` and `0x602000` are mapped; 4 tables in use | `direct_map`, `lookup_page`, `lookup_block`, `used` |
| `dm-02` | 118 | `mapping_above_four_gib_keeps_pa_bits_and_omits_ram_outside_the_window` | Banks `0x0+0x200000` and `0x100000000+0x400000`, managed window the second bank, boot storage `0x80000+0x1000`, 3 tables: bytes `0x400000`, 0 pages and 2 blocks; the block of `0x100000000` has that output address; the page of `0x0` and the block of `0x100400000` are `err=NotMapped` | `direct_map`, `lookup_page`, `lookup_block` |
| `dm-03` | 150 | `exhausted_storage_never_reports_a_complete_map` | Bank `0x0+0x400000`, boot storage `0x80000+0x1000`, 2 tables: `err=OutOfTables`, 1 table in use | `direct_map`, `used` |
| `dm-04` | 161 | `every_descriptor_in_sparse_eight_gib_matches_a_separate_page_oracle` | Property. Banks `0x0+0x3fc00000`, `0x40000000+0xc0000000` and `0x100000000+0x100000000`, all managed, boot storage `0x80000+0x1000`, a `no-map` firmware reservation `0x1fffff001+0x1`, 16 tables. Every page `pa` below `0x200000000` is mapped exactly when it lies outside the hole `0x3fc00000+0x400000` and is neither `0x80000` nor `0x1fffff000`; a mapped page translates through its block or its page to `pa`, with AP[2], AP[1] and nG 0 and PXN and UXN 1; every other is `err=NotMapped`; the bytes are `0x1ffbfe000`, the mapped pages times `0x1000`. Lines `dm-04.1` to `dm-04.4096`, one for each 2 MiB block from `0x0` in address order: `map=block` when a block maps it so, `map=pages absent=<addresses>` when pages map it so except the listed addresses, comma-separated, `-` for none, and `map=none` when no page of it is mapped; line `dm-04.4097`: `bytes=0x1ffbfe000` | `direct_map`, `lookup_page`, `lookup_block` |

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  the VMSAv8-64 translation table format of the 4 KiB granule with its
  table, block and page descriptors, AP, PXN, UXN, AttrIndx, SH, AF and nG;
  `MAIR_EL1`, `TCR_EL1`, `TTBR0_EL1`, `TTBR1_EL1`, `SCTLR_EL1` with `M`, `C`,
  `I` and `WXN`, and `ID_AA64MMFR0_EL1`; break-before-make; `TLBI VAAE1IS`
  and `TLBI VMALLE1`; `DMB`, `DSB` and `ISB`.
- Arm Limited, *Learn the architecture - AArch64 memory management Guide*,
  version 1.4, document 101811_0104_01_en, 2024,
  <https://documentation-service.arm.com/static/670e4dc89fbc7343d3e4cee1>:
  chapters 7 and 8, the translation granule and the maintenance of the TLB.
- Arm Limited, *Learn the architecture - Memory Systems, Ordering, and
  Barriers*, version 1.0, document 102336_0100_01_en, 2022,
  <https://documentation-service.arm.com/static/62a304f231ea212bb662321d>:
  the barriers that order the stores into tables.
- devicetree.org, *Devicetree Specification*, release v0.4, 2023,
  <https://github.com/devicetree-org/devicetree-specification/releases/download/v0.4/devicetree-specification-v0.4.pdf>:
  section 3.5.2, the `no-map` and `reusable` properties of the children of
  `/reserved-memory`.
- B. Simner, A. Armstrong, J. Pichon-Pharabod, C. Pulte, R. Grisenthwaite,
  P. Sewell, "Relaxed virtual memory in Armv8-A", European Symposium on
  Programming (ESOP), 2022, <https://arxiv.org/abs/2203.00642>.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/memory.md`, lines 155 to 236: allocation and
    ownership, and the staged page reservation;
  - `docs/features/kernel/memory.md`, lines 260 to 355: page tables and
    permissions, and the checks of the direct map;
  - `docs/pi5-bring-up.md`, lines 81 to 120: translation and bounded
    allocation;
  - `docs/pi5-kernel.md`, lines 225 to 250: translation and continuing
    interrupts;
  - `docs/kernel-state.md`, lines 92 to 109: the boundaries of the memory
    system and of applications;
  - `docs/features/platform/physical-entry.md`, lines 97 to 105: entry and
    translation, the memory attributes, the two 39-bit regions, the 2 MiB
    blocks of the direct map, `WXN` and the unmapped firmware reservations;
  - `docs/features/platform/physical-entry.md`, lines 138 to 161: the
    publication of executable bytes, boot storage outside the direct map.
