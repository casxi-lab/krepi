# Address-space contract

This page governs the code of the `address-space` component of the
[memory and address spaces](../README.md) domain: the address space of each
process, with the root of its lower tables in `TTBR0_EL1`, its ASID and the
CPUs that may hold its translations; the allocation, the release and the
reuse of ASIDs; the table pool from which the lower tables of every process
come; the layout of the virtual addresses of EL0 and the range check of user
buffers; the entry from EL0 and the return to it; the classes of the
exceptions taken from EL0 and of user faults; the creation of the first
process with its boot information, and the format of the boot-bundle
directory; the EL0 policy of the timers, the performance monitors, the
debug communications channel and the bits of `SCTLR_EL1` that govern EL0;
and the representation of kernel stacks and blocking calls. The tables
themselves are written by the entries of the
[page-tables](../page-tables/contract.md) component, and the saved user
context, with its layout, its validation and the save and restore of the
FP/SIMD and TLS registers, is the
[context](../../boot-platform/context/contract.md) component's. The
observable behaviour that these rules serve, with its evidence, is in the
[requirements](requirements.md), the other document of the component.

## Terms

- **Address space.** What a process holds of its own translation: the table
  set of its lower tables, a `page_tables::Tables` (planned), and its
  record `address_space::Space` (planned), which holds its ASID token and
  its CPU record. Both are fields of the process, kept in its process slot;
  neither is an object of its own
  ([records that are not objects](../../objects-capabilities/objects/contract.md#object-kinds-and-pools)).
- **Lower tables.** The table set of the lower region of a process, in the
  segment of its process slot: a private copy of the lower kernel set
  ([copying the kernel tables](../page-tables/contract.md#copying-the-kernel-tables)),
  with the pages that the process maps at EL0. Its root, table 0 of the
  segment, is what `TTBR0_EL1` holds while a thread of the process runs.
- **Table pool.** The held pages, carved once at boot, that hold the lower
  tables of every process: $P$ segments of $N$ tables, where $P$ is the
  process capacity of the capacity record and $N$ is `TABLES_PER_SPACE`,
  32.
- **Segment.** The $N$ tables of the table pool that belong to process
  slot $i$, from 0 to $P - 1$: those from `base` $+ 4096 N i$, where `base`
  is the start of the pool.
- **ASID.** The tag of the translations of an address space, which
  `TTBR0_EL1` carries with the root. ASID 0 is the kernel's, the tag with
  which the lower kernel set is loaded; processes take ASIDs from 1.
- **ASID capacity.** The number of ASIDs that processes can take: 255 with
  8-bit ASIDs and 65,535 with 16-bit ones.
- **ASID allocator.** `address_space::Asids` (planned): the ASIDs from 1 to
  its capacity, each with a slot that records whether it is held and its
  generation, a 64-bit counter.
- **ASID token.** `address_space::AsidToken` (planned): an ASID with the
  generation that its slot took when the ASID was taken.
- **CPU record.** The CPUs that may hold translations tagged with the ASID
  of an address space, a field of its `Space`.
- **Release plan.** `address_space::ReleasePlan` (planned): the token of a
  held ASID with the CPUs of the CPU record of its address space, on each
  of which the ASID is invalidated before it is released.
- **EL0 window.** The virtual addresses `[EL0_START, EL0_END)`,
  `[0x4000000000, 0x8000000000)` or $[2^{38}, 2^{39})$: the upper half of
  the lower region, its 1 GiB slots 256 to 511, where every page that a
  process maps at EL0 lies.
- **Boot bundle.** The read-only segment of the kernel image between the
  link symbols `__boot_bundle_start` and `__boot_bundle_end` (planned),
  page aligned at both ends and holding nothing else: the boot-bundle
  directory, the capacity record and the images of the root, the services
  and the workers
  ([boot and the resident root](../../../architecture.md#boot-and-the-resident-root)).
  The kernel learns of no other bundle and of nothing outside the image.
- **Boot-bundle directory.** The table at the start of the boot bundle that
  names its entries ([Boot-bundle directory](#boot-bundle-directory)).
- **Root.** The first process, which the kernel creates at boot from the
  root's segment entries of the directory.
- **Boot information.** The page at `BOOT_INFO` that the kernel writes for
  the root and maps for it read-only
  ([First process and boot information](#first-process-and-boot-information)).
- **Entry from EL0.** An exception taken from EL0 to EL1, through vector 8
  or 9 of the
  [exception vectors](../../boot-platform/boot/contract.md#exception-vectors):
  a system call, another synchronous exception or an IRQ.
- **Return to EL0.** The one-way exit of the
  [execution model](../../../architecture.md#system-calls-and-the-abi): it
  loads the address space of the thread that is to run, restores its saved
  context and executes `ERET`.
- **Current thread.** The thread that a CPU runs, whose context an entry
  from EL0 on that CPU saves; the record of the CPU names it (planned).
- **Composer of the return.** The module `dispatch` of the core (planned),
  which handles the pending interrupts, chooses the thread that is to run,
  has its saved context validated and gives the return plan; for the first
  return of the root, the boot wiring.
- **Return plan.** The address of the saved context of the thread that is
  to run, which has passed `validate`, with the value of `TTBR0_EL1` for its
  address space and the top of the kernel stack of the CPU.
- **Kernel stack.** The stack of a CPU with a guard below it on which every
  entry from EL0 runs; **emergency stack**, the second stack of each CPU, on
  which fatal diagnostics run.
- **Exception class.** One of the ten classes of
  [Exception classes](#exception-classes) of an entry from EL0;
  **cause class**, one of the nine classes of a user fault of
  [User faults](#user-faults).
- **Boot wiring.** The code of a board crate that runs on the boot CPU
  before the first entry from EL0, as in the
  [page-tables](../page-tables/contract.md#terms) and
  [objects](../../objects-capabilities/objects/contract.md#terms)
  contracts.
- **Token.** What an access to shared or per-process state holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.

## Entry points

The entries of the core are in the module `address_space` of
`krepi-kernel` (planned); the adapter is the module `el0` of `krepi-arch`
(planned), and each kernel image defines the Rust entry of an exception
from EL0.

| Entry point | Kind | Called by | Rules |
| --- | --- | --- | --- |
| `address_space::EL0_START`, `EL0_END`, `BOOT_INFO`, `ROOT_IMAGE_START`, `ROOT_IMAGE_END`, `ROOT_STACK_TOP`, `ROOT_STACK_PAGES`, `BUNDLE_WINDOW`, `BUNDLE_WINDOW_END`, `TABLES_PER_SPACE`, `MAX_ROOT_SEGMENTS`, `MAX_BOOT_CAPABILITIES`, `OWNER_TABLE_POOL` and `OWNER_ROOT_PAGES` (planned) | Constants, host-testable | The entries of this page; the boot wiring; the modules `creation` and `dispatch` of the core and the VM and loading components (planned), for the layout | [EL0 address layout](#el0-address-layout), [Table pools](#table-pools), [First process and boot information](#first-process-and-boot-information) |
| `address_space::asid_capacity`, `check_processes` and `check_kernel_ranges` (planned) | Functions that write nothing, host-testable | The boot wiring, once, before it carves storage | [Address spaces and ASIDs](#address-spaces-and-asids), [EL0 address layout](#el0-address-layout) |
| `TablePool::new`, `TablePool::pages` and `TablePool::segment` (planned), with the value type `address_space::TablePool` | Functions that write nothing, host-testable | `pages` and `new`: the boot wiring, which carves the pool; `segment`: the boot of the root and the modules `creation`, `lifecycle` and `dispatch` of the core (planned) | [Table pools](#table-pools) |
| `Asids::new` (planned), with the value types `address_space::Asids` and `AsidToken` | Function that writes nothing, host-testable | The boot wiring, once, after the checks of the capacity record | [Address spaces and ASIDs](#address-spaces-and-asids) |
| `Asids::choose` and `Asids::take` (planned) | A read entry and a write entry, host-testable | The module `creation` and the boot of the root (planned) | [Address spaces and ASIDs](#address-spaces-and-asids) |
| `Asids::release_plan` and `Asids::release` (planned), with the value type `address_space::ReleasePlan` | A read entry and a write entry, host-testable | The module `lifecycle` of the core (planned), in the reclamation of the address space of a process | [Address spaces and ASIDs](#address-spaces-and-asids) |
| `Space::new`, `Space::join` and `Space::ttbr0` (planned), with the value type `address_space::Space` | A function that writes nothing, a write entry and a value function, host-testable | `new`: the module `creation` and the boot of the root; `join` and `ttbr0`: the module `dispatch`, as the composer of the return, and the boot wiring, for the first return of the root (planned) | [Address spaces and ASIDs](#address-spaces-and-asids), [Entry and return](#entry-and-return) |
| `address_space::check_range` (planned), with the value types `address_space::Range` and `address_space::Error` | Function that writes nothing, host-testable | The user copies of the kernel and the system calls with buffer arguments (planned), in their checks | [EL0 address layout](#el0-address-layout) |
| `address_space::classify` (planned), with the value types `address_space::Exception` and `Cause` | Function that writes nothing, host-testable | The module `dispatch` of the core (planned), at each entry from EL0 | [Exception classes](#exception-classes), [User faults](#user-faults) |
| `Directory::parse`, `Directory::entry` and `Directory::capacity_record` (planned), with the value types `address_space::Directory` and `Entry` | Functions that write nothing, host-testable | `parse` and `capacity_record`: the boot wiring, once, before it carves storage; `entry`: the boot of the root and the loading component (planned) | [Boot-bundle directory](#boot-bundle-directory) |
| `Directory::root_plan` and `BootInfo::new` (planned), with the value types `address_space::RootPlan` and `BootInfo` | Functions that write nothing, host-testable | The boot of the root (planned) | [First process and boot information](#first-process-and-boot-information), [Table pools](#table-pools) |
| `__el0_entry` in `kernel/arch/src/el0.S` (planned) | Hardware entry, assembly | The CPU, through vectors 8 and 9 of the exception vectors, at an exception taken from EL0 | [Entry and return](#entry-and-return), [Kernel stacks and blocking](#kernel-stacks-and-blocking) |
| `el0_dispatch` of each kernel image (planned) | Rust entry, `extern "C" fn(u64, u64, u64) -> !` | `__el0_entry`, with the vector number, `ESR_EL1` and `FAR_EL1`, on the kernel stack and with every exception masked | [Entry and return](#entry-and-return) |
| `__el0_return` in `kernel/arch/src/el0.S` (planned) | Assembly routine that does not return | `el0_dispatch`, and the boot wiring for the first return of the root, each with a return plan of the composer | [Entry and return](#entry-and-return) |
| `krepi_arch::el0::write_controls`, `load_kernel_tables` and `invalidate_asid` (planned) | `unsafe` functions | `write_controls`: the boot wiring on the boot CPU and the start of each other CPU, once, before the CPU first enters EL0; `load_kernel_tables`: a CPU that has no thread to run, before it waits; `invalidate_asid`: `el0_dispatch`, on each CPU of a release plan that the dispatch of the core returns | [EL0 controls](#el0-controls), [Address spaces and ASIDs](#address-spaces-and-asids) |

## Extractability

The module `address_space` of the core (planned), in
`kernel/src/address_space.rs` (planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the
constants of the layout and of the pool, the ASID allocator, the
address-space record with its CPU record, the range check, the
classification of exceptions and user faults, the parsing of the
directory, the plan of the root and the boot information. It is in layer 1
of the [module order](../../../architecture.md#module-order-in-the-core)
and refers to no other module of the core: it holds values, constants and
the checks and computations that need no other module, and it names the
kinds of mappings by an access of its own, which its callers turn into the
kinds of `page_tables`. The operations that span several modules are
composed above it: the lower tables of a process are built and reset by the
modules `creation` and `lifecycle` with the entries of `page_tables`, the
root by the boot wiring through `creation`, and each return to EL0 by
`dispatch` (planned), each step by the module that this page names. Its
items are `pub(crate)` except the rows of the entry table that the
architecture crate or a board crate calls, with the value types that those
rows take and return
([provable core](../../../architecture.md#the-provable-core)). It touches
no register and defines no callback for a hardware action: the release of
an ASID gives a plan, which the architecture crate executes.

The adapter `el0` of `krepi-arch` (planned), in `kernel/arch/src/el0.rs`
with its assembly in `kernel/arch/src/el0.S` (planned), does not follow the
subset: it saves and loads the user registers at the entry from EL0 and the
return to it, writes `TTBR0_EL1`, invalidates the TLB entries of an ASID
and writes the EL0 controls. The assembly takes the offsets of the saved
context from the constants of the
[context](../../boot-platform/context/contract.md#layout) component. The
Rust entry of an exception from EL0 and the boot of the root are code of
the board crates. The contract is written before its code, so this section
lists no source paths; the change that adds the module writes its `paths`
block here.

## Address spaces and ASIDs

- **The root of an address space.** The lower tables of a process are the
  table set of the segment of its process slot
  ([Table pools](#table-pools)), and their root is table 0 of the segment.
  The module `creation` builds them when it creates the process:
  `Tables::new` on the segment and then `Tables::clone_kernel_from` with the
  lower kernel set as the source, with the plans that
  `krepi_arch::mmu::apply` executes. The pages that the process maps at
  EL0 are added afterwards, with the user kinds of the page-tables
  component and only in the EL0 window. The lower tables hold no other page
  of a kernel kind than the copy: no kernel page is private to one address
  space.
- **The lower kernel set is complete before the first copy.** The boot
  wiring writes the lower kernel set with `kernel_map` before it creates the
  root, and no plan fills it afterwards, so every copy holds the same kernel
  entries, all global.
- **ASID width.** The ASIDs are 16 bits wide when
  `ID_AA64MMFR0_EL1.ASIDBits` is `0b0010` and `TCR_EL1.AS` is 1, and 8 bits
  wide otherwise. `asid_capacity(asid_bits, tcr_as)` gives the ASID capacity
  from these two fields: 65,535 for 16 bits and 255 for 8. The Cortex-A76 of
  both boards reports `0b0010`, but `krepi_arch::mmu::enable` writes
  `TCR_EL1` with `AS` 0 and `A1` 0, so that the ASID is taken from
  `TTBR0_EL1` with 8 bits
  ([turning the MMU on](../page-tables/contract.md#write-plans-and-publication)):
  on both boards the ASIDs are 8 bits wide, the ASID capacity is 255, and
  processes take ASIDs 1 to 255. A change to 16 bits starts with a change of
  `enable`.
- **The process capacity at boot.** `check_processes(processes, capacity)`
  refuses a process capacity above the ASID capacity with `AsidCapacity`.
  The boot wiring runs it as the last check of the capacity record, after
  the checks of the
  [objects](../../objects-capabilities/objects/contract.md#capacity-record)
  component, and stops the boot with the error; it does not fall back to the
  defaults. `Asids::new(processes, capacity)` then gives the allocator of
  the ASIDs 1 to `processes`, every slot free at generation 0, and refuses a
  number of ASIDs of 0 or above the ASID capacity with `AsidCapacity`.
- **Allocation.** `choose` gives, without writing, the lowest ASID whose
  slot is free and whose generation is below $2^{64} - 1$. It refuses with
  `Exhausted` when every ASID is held, and with `GenerationExhausted` when
  the only free ASIDs have reached the last generation.
  `take(choice)`, under the token under which `choose` gave the choice,
  marks the slot held, raises its generation by one and gives the token of
  the ASID with the new generation; the first token of an ASID has
  generation 1.
- **Generations.** Each slot has its own generation, which grows by one at
  each take and never wraps: an ASID whose generation has reached
  $2^{64} - 1$ is not taken again before the next boot. A token of an
  earlier generation names no held ASID. These generations are not those of
  the object table, and no ASID or generation is an output to EL0.
- **Release.** The release of an ASID takes three steps, in this order,
  and the ASID stays held until the last:
  1. *Unload.* No CPU holds the root of the address space in its
     `TTBR0_EL1`, so its tables are unreachable from every `TTBR`. A CPU
     holds the address space of the process of its current thread, or the
     lower kernel set with ASID 0 when it has no thread to run, which
     `load_kernel_tables` loads before the CPU waits; the reclamation of a
     process whose threads have all ended therefore finds it loaded on no
     CPU, which its caller, the module `lifecycle`, vouches for.
  2. *Invalidate.* `release_plan(token)` checks the token, without
     writing, and gives the release plan: the ASID and the CPUs of the CPU
     record. On each CPU of the plan, `krepi_arch::el0::invalidate_asid`
     executes `TLBI ASIDE1` with the ASID in bits 48 to 63 of its operand,
     which removes from the TLB of that CPU the non-global entries and the
     entries of the levels above the last that carry the ASID, and then
     `DSB NSH`, which completes a TLB maintenance instruction that applies
     to one CPU. With one CPU, the record holds at most the executing CPU;
     the invalidation on another CPU, with its acknowledgement, belongs to
     the multicore domain.
  3. *Release.* `release(plan)` checks the token of the plan again, frees
     the slot and leaves its generation as it is.
- **Reuse.** The ASID is free for the next `choose` only after `release`.
  The plan of `Tables::reset` of the lower tables runs after the
  invalidation, since `reset` requires that no TLB holds a translation of
  the set ([after mapping](../page-tables/contract.md#after-mapping)), and
  the segment serves the next process of its slot only after both. A
  release that fails its check changes nothing, and an execution of the
  plan that has not been followed by `release` leaves the ASID and the
  segment held.
- **The CPU record.** `Space::new(token)` gives the record of a new address
  space with an empty CPU record. `Space::join(cpu)` adds a CPU, and the
  composer of the return calls it before that CPU first writes the root of
  the address space into its `TTBR0_EL1`. A CPU stays in the record after it
  loads another address space, since its TLB may still hold translations
  tagged with the ASID, and leaves it only with the release. When the
  release plan is made the process has no thread that runs, so no CPU joins
  afterwards and the set of the plan does not shrink
  ([reclamation](../../../conventions/smp.md#s3-reclamation-after-acknowledgement)).
- **Loading.** `Space::ttbr0(root)` gives the value of `TTBR0_EL1` for the
  address space: the physical address of the root, a multiple of 4096, in
  bits 1 to 47, `CnP`, bit 0, 0, and the ASID in bits 48 to 63. A switch
  of address spaces writes that value and executes `ISB` before the next
  access at EL0; it invalidates no TLB entry, since the entries of a
  process carry its ASID and the kernel's are global and the same in every
  copy.

## EL0 address layout

- **The EL0 window.** Every page that a process maps at EL0, with a user
  kind, lies in the EL0 window, `[EL0_START, EL0_END)`, from
  `0x4000000000` to `0x8000000000`. No entry of this component, of the VM
  component or of the loading component maps a page of a process outside
  it.
- **Why the upper half.** The lower tables of a process copy the lower
  kernel set, which maps the image, the device tree and the registers of
  the console and of the interrupt controller at their physical addresses
  ([kernel mappings](../page-tables/contract.md#kernel-mappings)). On QEMU
  virt these lie below `0x48000000`: the GICv2 from `0x08000000`, the PL011
  at `0x09000000`, and the RAM of 128 MiB from `0x40000000`. On the
  Raspberry Pi 5 the image starts at `0x80000` and the device tree at
  `0x10000000`
  ([the load layout](../../../architecture.md#boot-and-the-resident-root)),
  UART10 is at `0x107d001000` and the distributor of the GIC-400 at
  `0x107fff9000`. Every one of these is below $2^{38}$, so the EL0 window
  shares no 1 GiB slot with them.
- **The check at boot.** `check_kernel_ranges(ranges)` refuses, with
  `KernelLayout`, a range of the layout that the board gives `kernel_map`
  whose end is above `EL0_START`. The boot wiring runs it on that layout
  before it writes the lower kernel set, so no entry of the lower kernel set
  lies in a 1 GiB slot of the EL0 window.
- **The boot ranges.** These ranges of the EL0 window are fixed:

| Range | Pages | Mapped in |
| --- | --- | --- |
| `BOOT_INFO`, `0x4000000000+0x1000` | The boot information, `UserReadOnly` | The root alone |
| `ROOT_IMAGE_START` to `ROOT_IMAGE_END`, `0x4000001000+0x1ee000` | The root's segments, each with the access of its entry | The root alone |
| `0x40001ef000+0x1000` | The guard of the root's stack, never mapped | The root alone |
| `ROOT_STACK_TOP` less `ROOT_STACK_PAGES` pages to `ROOT_STACK_TOP`, `0x40001f0000+0x10000` | The root's initial stack of 16 pages, `UserReadWrite` | The root alone |
| `BUNDLE_WINDOW` to `BUNDLE_WINDOW_END`, `0x4000200000+0x1fe00000` | The boot bundle from its start, `UserReadOnly`, up to the end of its last page | The root alone |

- The first four rows lie in the first 2 MiB block of the EL0 window, the
  root block, and the bundle window starts at the 2 MiB block after it; all
  five lie in the first 1 GiB slot of the window.
- **Other ranges.** The image windows of the loading component and the
  windows of the VM component (planned), in which a process maps its
  segments, stacks and VM regions, lie in the EL0 window outside the boot
  ranges; their values and their checks belong to those components.
- **The bounds of a thread.** The composer of the return checks every
  saved context with the bounds of the EL0 window:
  `Bounds::new(EL0_START, EL0_END - EL0_START, EL0_START, EL0_END - EL0_START)`,
  the code range `[EL0_START, EL0_END)` and the stack range
  `[EL0_START, EL0_END]`, which passes the rules of
  [Bounds::new](../../boot-platform/context/contract.md#validation). So
  `validate` refuses a return address outside the EL0 window, and a stack
  pointer outside it other than `EL0_END`, the top of an empty stack that
  ends there, whichever stack the thread runs on, such as the stack of an
  upcall handler.
- **The range of a user buffer.**
  `check_range(address, length, lower, upper, limit)` checks the
  arithmetic of a buffer of a process before the kernel reads or writes it,
  with the window `[lower, upper)` that its caller gives, a part of the EL0
  window for the buffers of a process:
  1. a length above `limit` is refused with `TooLong`, whatever the
     address and the window;
  2. a length of 0 is accepted with no range, whatever the address and the
     window;
  3. otherwise the buffer is `[address, address + length)`, accepted as
     that `Range` when `address + length` fits in 64 bits, `address` is at
     least `lower` and `address + length` is at most `upper`, and refused
     with `Address` otherwise, an empty or reversed window among them.
- The length is checked before the address, as the order of errors of the
  [security model](../../../security.md#internal-choices) puts the form of
  the register arguments before the range of a user buffer. The check
  reads no memory; the copies themselves, the faults that they may take and
  Privileged Access Never, which keeps EL1 off the pages of EL0 outside the
  copies, belong to the user copies of the kernel (planned).

## Table pools

- **Capacity.** The table pool of every address space holds $N$ tables,
  `TABLES_PER_SPACE`, $N = 32$: the capacity of the pool of the lower kernel
  set ([Table pool](../page-tables/contract.md#table-pool)), since
  `clone_kernel_from` copies between two sets of one capacity.
- **Carving at boot.** `TablePool::pages(processes)` gives $32 P$, the
  pages of the pool for the process capacity $P$. The boot wiring carves the
  pool once, after the eight allocations of the
  [objects](../../objects-capabilities/objects/contract.md#storage-carved-at-boot)
  component, in one step of
  [zeroing before publication](../page-tables/contract.md#page-ownership):
  `Ownership::choose` of $32 P$ pages at an alignment of one page and a low
  placement without a window, then `krepi_arch::mmu::zero_frames` of the
  chosen range, then `Ownership::assign` with the owner identity
  `OWNER_TABLE_POOL`, a nonzero constant distinct from the owner identity of
  every other holder. When the page ownership table finds no range, the
  boot stops with its error. `TablePool::new(base, processes)` gives the
  pool, and `TablePool::segment(slot)` the base of the segment of a process
  slot, `base` $+ 4096 \cdot 32 \cdot \mathrm{slot}$, for a slot below
  $P$.
- **One holder.** The pool is one held range of one owner identity, so it
  adds at most two extents to the page ownership table, the held range and
  the rest of the free extent that it splits, and at most one at a low
  placement and an alignment of one page; the 160 extents of the table
  ([capacity](../page-tables/contract.md#page-ownership)) need no change.
  For $P = 64$ the pool holds 2,048 pages, 8 MiB; for $P = 255$, 8,160
  pages.
- **Fixed segments.** Segment $i$ belongs to process slot $i$ for the whole
  boot. The creation and the reclamation of a process take no page from the
  page ownership table and return none: the zeroing at the carving and the
  plans of `Tables::reset` keep every table that is not in use zero, as
  `Tables::new` requires
  ([zero storage](../page-tables/contract.md#table-pool)).
- **Quota.** The page-table pages of the quota record of a process count
  the $N$ tables of its segment from the occupation of its process slot to
  its release, and no entry charges or credits them
  ([metadata quotas](../../objects-capabilities/objects/contract.md#metadata-quotas)).
- **The tables of a process.** A process uses $K + |G| + |P_2|$ tables of
  its $N$: $K$, the tables of the copy of the lower kernel set; $G$, the
  1 GiB slots of the EL0 window that its pages touch, one level 2 table
  each; and $P_2$, the 2 MiB slots that it maps in part with pages, one
  level 3 table each. A mapping that would need more fails with
  `OutOfTables` in its check, before any write
  ([errors](../page-tables/contract.md#errors-of-table-sets)).
- **The lower kernel set.** On both boards
  $K = 6 + \lceil (o + S) / 2\,\mathrm{MiB} \rceil$, as the page-tables
  contract counts it: $S$ is the size of the image with its boot bundle,
  BSS, stacks and the pools of the kernel tables, and $o$ the offset of the
  start of the image in its 2 MiB block, `0x80000` on the Pi 5 and 0 on
  QEMU virt. An image within one 2 MiB block gives $K = 7$, which leaves 25
  tables to EL0.
- **The root.** The root maps the boot information, its segments and its
  stack in the root block, and the boot bundle from `BUNDLE_WINDOW`, all in
  the first 1 GiB slot of the EL0 window, so it needs
  $2 + \lceil S_b / 2\,\mathrm{MiB} \rceil$ tables beyond the copy, $S_b$
  being the size of the boot bundle: the level 2 table of that slot, the
  level 3 table of the root block and one for each 2 MiB block of the
  bundle window. `Directory::root_plan` refuses, with `RootTables`, a
  bundle for which $2 + \lceil S_b / 2\,\mathrm{MiB} \rceil > N - K$.
- **The limit of the image with its bundle.** With the kernel apart from
  its bundle at about 1 MiB, an inferred size, $S_b = S - 1\,\mathrm{MiB}$,
  and the root's condition holds while $o + S$ is at most 24 MiB:

| Board | $o$ | $S$ | $K$ | Tables left to EL0 | Tables of the root |
| --- | --- | --- | ---: | ---: | ---: |
| Raspberry Pi 5 | 0.5 MiB | 8 MiB | 11 | 21 | 6 |
| Raspberry Pi 5 | 0.5 MiB | 23.5 MiB, the largest | 18 | 14 | 14 |
| QEMU virt | 0 | 8 MiB | 10 | 22 | 6 |
| QEMU virt | 0 | 24 MiB, the largest | 18 | 14 | 14 |

- The lower kernel set alone fits 32 tables up to $o + S$ of 52 MiB; the
  limit that matters is the root's. The build compares the image with its
  bundle against the limit of the board (planned).

## Entry and return

A thread's user state is in one of two places: in the registers of the CPU
that runs it, while it executes at EL0, or complete in its saved context,
while it does not. An entry from EL0 moves it from the registers into the
saved context of the current thread; a return to EL0 moves the saved
context of the thread that is to run into the registers. No code reads or
writes the saved context of a thread while the thread executes at EL0
([state fields](../../boot-platform/context/contract.md#state-fields)).

**The entry.** At an exception taken from EL0, the CPU runs on `SP_EL1`,
which every return to EL0 left at the top of the kernel stack of the CPU,
with D, A, I and F set in `PSTATE`, and takes vector 8 or 9 of the
[exception vectors](../../boot-platform/boot/contract.md#exception-vectors):

1. the vector stores `x0` and `x1` on the kernel stack, below its top, and
   branches to `__el0_entry` with its number; `__el0_entry` reads the
   address of the saved context of the current thread from the record of
   the CPU (planned), stores `x2` to `x30` into it, then `x0` and `x1` from
   the stack, then `SP_EL0`, `ELR_EL1` and `SPSR_EL1`;
2. it calls `__fpsimd_save` of the
   [context](../../boot-platform/context/contract.md#fpsimd-and-tls-state)
   component with that address;
3. it calls `el0_dispatch` with the vector number, `ESR_EL1` and `FAR_EL1`,
   at the top of the kernel stack;
4. `el0_dispatch` hands them to the module `dispatch` of the core, which
   takes the [exception class](#exception-classes) from `classify` and
   handles the entry by it: native dispatch for a system call, the end of
   the process for a user fault, the interrupt for an IRQ. The entry runs to
   completion with every exception masked: EL1 never clears a bit of `DAIF`
   ([execution model](../../../architecture.md#system-calls-and-the-abi)).

**The return.** The composer of the return:

1. after the entry has released every lock and every borrowed object,
   handles every interrupt that is pending, as for the class `Irq`, and
   then chooses the thread that is to run, by the rules of scheduling
   (planned);
2. runs `Context::validate` on the saved context of the thread with the
   bounds of the EL0 window; when it fails, the thread does not return to
   EL0, its process ends by a user fault
   ([a refused context](#user-faults)), and the composer starts again at
   step 1;
3. calls `Space::join` with the executing CPU, when the CPU record of the
   address space of the thread's process lacks it, and records the thread
   as the current thread of the CPU (planned);
4. gives the return plan: the address of the saved context, `Space::ttbr0`
   of the root of the address space, and the top of the kernel stack of the
   CPU.

The composer handles the pending interrupts itself, with every exception
masked, and does not leave them to be taken at EL0 after the `ERET`: when
the first instruction there takes a synchronous exception, as an `SVC`
does, the architecture leaves open whether a pending IRQ is taken first,
and the [internal choices](../../../security.md#internal-choices) put the
synchronous exception first. A call that stopped at a preemption point is
executed again only by its thread at EL0
([Kernel stacks and blocking](#kernel-stacks-and-blocking)), so its checks
run with the thread's own address space loaded.

`el0_dispatch`, or the boot wiring for the first return of the root, then
calls `__el0_return` with the plan, and `__el0_return`, with every
exception masked:

1. writes `TTBR0_EL1` with the value of the plan and executes `ISB`;
2. calls `__fpsimd_restore` with the address of the saved context;
3. loads `SP_EL0`, `ELR_EL1` and `SPSR_EL1` from the saved context;
4. sets `SP_EL1` to the top of the kernel stack of the plan;
5. loads `x0` to `x30` from the saved context and executes `ERET`.

**Vectors.** Vectors 8 and 9, the synchronous exceptions and the IRQs from
EL0 in AArch64, take the entry above. Vectors 10 and 11, the FIQs and
SErrors from EL0, are masked at EL0 by F and A of every context that
`validate` accepts, and EL0 cannot change them, since `SCTLR_EL1.UMA` is 0
([EL0 controls](#el0-controls)); vectors 12 to 15, the exceptions from EL0
in AArch32, are never taken, since `validate` refuses an `SPSR` with
M[4] set and EL0 runs only in AArch64. These six keep the path of the
[boot](../../boot-platform/boot/contract.md#exception-vectors) component,
which reports the exception and halts.

The rules of the saved, restored and cleared state, each an
[open obligation](#open-obligations) with its test:

| Label | Statement |
| --- | --- |
| `entry-stack` | Every entry from EL0 starts at the top of the kernel stack of its CPU: `SP_EL1` holds that top when EL0 runs, and the entry uses no other stack. |
| `entry-save-general` | At every entry from EL0, `x0` to `x30` are stored into the saved context of the current thread with the values that EL0 left: `x0` and `x1` through the kernel stack, before the entry changes them, and the others before it uses them. |
| `entry-save-system` | At every entry from EL0, `SP_EL0`, `ELR_EL1` and `SPSR_EL1` are stored into the saved context of the current thread, and `ESR_EL1` and `FAR_EL1` are passed to `el0_dispatch`, before any instruction that may change them. |
| `entry-mask` | From the exception to the `ERET` of the return, D, A, I and F stay set: no code of the entry, of the dispatch or of the return clears a bit of `DAIF`. |
| `return-validate` | `__el0_return` is called only with the saved context of a thread for which `validate` passed, with the bounds of the EL0 window, after the last write of that context and before the restore. |
| `return-ttbr0` | Before the first load from the saved context, `TTBR0_EL1` holds the root of the lower tables of the thread's process with its ASID, followed by `ISB`, and the executing CPU is in the CPU record of that address space; no TLB entry is invalidated for the switch. |
| `return-load` | `SP_EL0`, `ELR_EL1`, `SPSR_EL1` and `x0` to `x30` are loaded from the saved context of the thread that is to run, the general registers last, and nothing changes them before the `ERET`. |
| `return-stack` | Before the `ERET`, `SP_EL1` is set to the top of the kernel stack of the CPU, so no kernel frame survives the return. |
| `return-no-kernel-value` | After the `ERET`, every register that EL0 can read holds a value of the thread's saved context, a value of the thread's own process, such as its ASID in `TTBR0_EL1`, which EL0 cannot read, or a value that the observable outputs allow, such as `CNTVCT_EL0`; none holds a value of the kernel or of another process. |

## Exception classes

`classify(vector, esr)` gives the class of an entry from EL0 from its
vector and, at vector 8, from the exception class `EC`, bits 26 to 31 of
`ESR_EL1`, as the Arm Architecture Reference Manual encodes it. The classes
are exactly these ten:

| Class | Vector | Condition | Handling |
| --- | --- | --- | --- |
| `Svc` | 8 | `EC` `0x15`: `SVC` in AArch64 state | Native dispatch; an immediate other than 0 returns `UNSUPPORTED_OPERATION` and is not a fault ([SVC immediate](../../../architecture.md#system-calls-and-the-abi)) |
| `DataAbort` | 8 | `EC` `0x24`: a Data Abort from a lower Exception level | A user fault, of the cause that its `DFSC` gives: `DataTranslation`, `DataPermission`, `Alignment` or `Other` |
| `InstructionAbort` | 8 | `EC` `0x20`: an Instruction Abort from a lower Exception level | A user fault, of the cause that its `IFSC` gives: `InstructionTranslation`, `InstructionPermission` or `Other` |
| `PcAlignment` | 8 | `EC` `0x22`: a PC alignment fault | A user fault, `Alignment` |
| `SpAlignment` | 8 | `EC` `0x26`: an SP alignment fault, which `SCTLR_EL1.SA0` 1 enables at EL0 | A user fault, `Alignment` |
| `TrappedAccess` | 8 | `EC` `0x18`: a trapped `MSR`, `MRS` or System instruction; or `EC` `0x01` with `TI`, bits 0 and 1 of the `ISS`, `0b00`: a trapped `WFI` | A user fault, `TrappedAccess` |
| `Breakpoint` | 8 | `EC` `0x3c`: `BRK` in AArch64 state | A user fault, `Breakpoint` |
| `Unknown` | 8 | `EC` `0x00`: an exception for an unknown reason, among them an access of EL0 to a register of EL1, `HVC` and `SMC` at EL0 and an instruction that the Cortex-A76 does not implement, such as one of SVE | A user fault, `Undefined` |
| `Other` | 8 | Any other `EC`, such as `0x07`, `0x0e` or `0x2c`, and `EC` `0x01` with another `TI` | A user fault, `Other` |
| `Irq` | 9 | An IRQ taken from EL0 in AArch64 state | The interrupt is handled; at the expiry of the timer the thread may be preempted, and the return goes to it or to another thread |

- The classes partition the entries from EL0: every value of `EC` at
  vector 8 falls in exactly one class, and vector 9 is `Irq`.
- `EC` `0x01` with another `TI`, a trapped `WFE`, does not occur, since
  `SCTLR_EL1.nTWE` is 1; the Cortex-A76 has no `WFIT` or `WFET`. The
  hardware breakpoints, watchpoints and software step of EL0 do not occur
  either, since `MDSCR_EL1.MDE` and `SS` are 0 ([EL0 controls](#el0-controls)).
- In one transition the synchronous exception of the current instruction
  comes first, and interrupts are taken only where the execution model
  takes them ([internal choices](../../../security.md#internal-choices)).

## User faults

A user fault is a synchronous exception of a thread at EL0 other than a
system call, every class of [Exception classes](#exception-classes) but
`Svc` and `Irq`, or a saved context that `validate` refuses at a return to
EL0. `classify` gives the cause class of an exception, and the composer of
the return that of a refused context; the cause classes partition the user
faults: every user fault has exactly one. The cause class is the class
that a later release passes to the fault handler of a thread with the
exception class bits of `ESR_EL1` and the user virtual address of
`FAR_EL1` ([fault handler](../../../architecture.md#futexes-and-upcalls)).
The fault status code, `DFSC` of a Data Abort or `IFSC` of an Instruction
Abort, is bits 0 to 5 of the `ISS`.

| Cause | Value | Condition | Case of the QEMU tests |
| --- | ---: | --- | --- |
| `DataTranslation` | 1 | `EC` `0x24` with a translation fault, `DFSC` `0b0001xx` | A read of the guard of a stack |
| `DataPermission` | 2 | `EC` `0x24` with a permission fault, `DFSC` `0b0011xx` | A write of a kernel sentinel through the kernel's mapping, after which the sentinel is unchanged |
| `InstructionTranslation` | 3 | `EC` `0x20` with a translation fault, `IFSC` `0b0001xx` | A branch to a page of the EL0 window that is not mapped |
| `InstructionPermission` | 4 | `EC` `0x20` with a permission fault, `IFSC` `0b0011xx` | An execution of a data page |
| `Alignment` | 5 | `EC` `0x22` or `0x26`, or `EC` `0x24` with an alignment fault, `DFSC` `0b100001` | A branch to an address that is not a multiple of 4 |
| `Undefined` | 6 | `EC` `0x00` | `UDF` |
| `TrappedAccess` | 7 | `EC` `0x18`, or `EC` `0x01` with `TI` `0b00` | A read of `PMCCNTR_EL0` |
| `Breakpoint` | 8 | `EC` `0x3c` | `BRK #0x76` |
| `Other` | 9 | Any other `EC`, and `EC` `0x20` or `0x24` with any other fault status code: an address size fault, an access flag fault, a synchronous External abort or a TLB conflict; and a saved context that `validate` refuses at a return | An FP/SIMD instruction after a test image has cleared `CPACR_EL1.FPEN` for the thread, `EC` `0x07`, which only a test image can cause |

- **Handling.** Release 0.1 has no fault handler of a thread, so every user
  fault ends the process of the thread as faulted, with a fault record, by
  the rules of the component that terminates processes (planned); the
  thread does not return to EL0. The fault record holds the cause class,
  the bits of `EC` of `ESR_EL1` and, for `DataTranslation`,
  `DataPermission`, `InstructionTranslation`, `InstructionPermission` and
  for `Alignment` from `EC` `0x24` or `0x22`, the user virtual address of
  `FAR_EL1`. For the other causes the record holds no address, even where
  `FAR_EL1` holds one, as for an access flag fault of `Other`. A user fault
  never ends another process.
- **The kernel sentinel.** The case of `DataPermission` writes, from EL0, a
  page that the lower kernel set maps writable at EL1, so the refused store
  shows the boundary between EL1 and EL0, not a read-only page.
- **A refused context.** A saved context that `validate` refuses at a
  return ([Entry and return](#entry-and-return)) is a user fault of the
  cause `Other`: the process of its thread ends as for every user fault,
  and its fault record holds `Other` with no bits of `EC` and no address,
  since EL0 took no exception for it.

## First process and boot information

The boot wiring creates the root once, after it has checked the directory,
the capacity record and the process capacity, carved the storage of the
objects component and the table pool, and built the object table, the ASID
allocator and the kernel root. Each step is taken by the module named:

1. `Directory::root_plan` checks the root's segment entries of the
   directory with the tables that the root needs
   ([Table pools](#table-pools)) and gives the root plan: the pages of the
   root's private allocation, and the mappings of the root, each with its
   virtual address, its source and its access.
2. The boot wiring takes the root's private allocation, in one step of
   [zeroing before publication](../page-tables/contract.md#page-ownership)
   with a low placement and an alignment of one page and the owner identity
   `OWNER_ROOT_PAGES`, a nonzero constant distinct from the owner identity
   of every other holder: one page for the boot information, the pages of
   the memory of each RW segment, and `ROOT_STACK_PAGES`, 16, for the
   stack. It adds at most one extent to the page ownership table. When no
   range is found, the boot stops with the error of the page ownership
   table. This page fixes the number of these pages; whether a quota item
   of the root counts them, and which, is a rule of the
   [objects](../../objects-capabilities/objects/contract.md#metadata-quotas)
   component (planned).
3. The module `creation` (planned) creates the root's process and thread
   as the boot of the root of the
   [objects](../../objects-capabilities/objects/contract.md#metadata-quotas)
   component states, takes the first ASID with `Asids::choose` and
   `take`, ASID 1 of generation 1, gives its record with `Space::new`, and
   builds its lower tables in the segment of its process slot with
   `Tables::new` and `clone_kernel_from`.
4. The boot wiring copies the file bytes of each RW segment from the bundle
   into its private pages, through the direct map, and writes the boot
   information that `BootInfo::new` gives into its page; the rest of these
   pages and the stack stay zero.
5. The module `creation` maps the pages of the root plan with `map_page`:
   the boot information at `BOOT_INFO`, `UserReadOnly`; each page of an RX
   segment, the page of the bundle that holds it, `UserReadExecute`; of an
   RO segment, `UserReadOnly`; of an RW segment, its private page,
   `UserReadWrite`; the stack, `UserReadWrite`, with its guard left
   unmapped; and each page of the bundle at the same offset from
   `BUNDLE_WINDOW`, `UserReadOnly`. The kernel installs these pages
   directly; they are not VM objects
   ([address spaces](../../../architecture.md#address-spaces-and-vm-objects)).
6. The boot wiring publishes the code of each RX segment with
   `krepi_arch::cache::invalidate_code_to_pou` of its pages, through the
   kernel's mapping of the image, before the root's first instruction; no
   CPU has written these pages, so no clean is needed
   ([cache and TLB maintenance](../../boot-platform/boot/contract.md#cache-and-tlb-maintenance)).
7. The thread's initial context is `Context::new(root_entry, ROOT_STACK_TOP)`
   of the [context](../../boot-platform/context/contract.md#initial-context)
   component, with the root entry of the directory header; `creation`
   checks it with `validate`.
8. The boot wiring calls `krepi_arch::el0::write_controls`, composes the
   first return as the composer of the return does, and calls
   `__el0_return`. The first return abandons the frames of the boot on the
   kernel stack.

- No page of the root plan is writable and executable: RX and RO pages are
  pages of the bundle, which the lower kernel set maps read-only and never
  executable, and RW pages are private pages that no executable mapping
  names ([W^X](../page-tables/contract.md#descriptors-and-attributes)).
- The root finds the boot information at `BOOT_INFO` and the bundle at
  `BUNDLE_WINDOW`, fixed addresses, so its initial registers hold no
  address.

**Boot information.** One page, written by the kernel and read-only at EL0,
little-endian, every field aligned to its width:

| Offset | Field | Bytes | Content |
| ---: | --- | ---: | --- |
| 0 | `magic` | 8 | The ASCII bytes `KREPIBI1` |
| 8 | `version` | 4 | 1 |
| 12 | `capability_count` | 4 | The number of entries of the initial capability table, at most `MAX_BOOT_CAPABILITIES`, 16 |
| 16 | `info_bytes` | 8 | The bytes of the boot information: 64 and 16 for each entry of the initial capability table |
| 24 | `bundle_address` | 8 | `BUNDLE_WINDOW`, the virtual address of the bundle in the root's address space |
| 32 | `bundle_bytes` | 8 | The size of the bundle in bytes, that of the directory header |
| 40 | `entry_count` | 4 | The number of entries of the directory |
| 44 | `capability_offset` | 4 | 64, the offset of the initial capability table in the page |
| 48 | `reserved` | 16 | 0 |
| 64 | The initial capability table | 16 each | `capability_count` entries; the rest of the page is 0 |

**Initial capability table.** Each entry names one capability that the
kernel puts into the root's capability table at boot, little-endian:

| Offset | Field | Bytes | Content |
| ---: | --- | ---: | --- |
| 0 | `kind` | 4 | The kind of the capability, a value that the component issuing it names (planned) |
| 4 | `reserved` | 4 | 0 |
| 8 | `handle` | 8 | The handle of the capability in the root's table, its slot number and generation, in the form of a handle of the ABI (planned) |

The kinds and the capabilities themselves, such as the root's control of
its own process, its creation right and its capability to the device
directory, belong to the components that issue them; this page fixes the
container and its limit. The prototype's spawn capability and profile flags
are not carried: the capabilities are entries of the table, and the root
has one profile.

## Boot-bundle directory

The bundle starts with the directory: a header of 64 bytes and, from byte
64, its entries of 48 bytes each, little-endian, every field of 4 or 8
bytes aligned to its width and the reserved field of 24 bytes to 8. The
boot wiring reads the bundle through the kernel's read-only
mapping of the image, from `__boot_bundle_start` to `__boot_bundle_end`
(planned), and `Directory::parse` checks it once, as untrusted input,
before any storage is carved; it writes nothing, and the boot stops at the
first check that fails with the fixed error of that check, without a
fallback.

**Header:**

| Offset | Field | Bytes | Content |
| ---: | --- | ---: | --- |
| 0 | `magic` | 8 | The ASCII bytes `KREPIBB1` |
| 8 | `version` | 4 | 1 |
| 12 | `entry_count` | 4 | The number of entries, at least 1 |
| 16 | `directory_bytes` | 8 | $64 + 48 \cdot$ `entry_count` |
| 24 | `bundle_bytes` | 8 | The size of the bundle, `__boot_bundle_end` less `__boot_bundle_start` |
| 32 | `root_entry` | 8 | The virtual address at which the root starts, in one of its RX segments |
| 40 | `reserved` | 24 | 0 |

**Entry:**

| Offset | Field | Bytes | Content |
| ---: | --- | ---: | --- |
| 0 | `kind` | 4 | The kind of the entry, of the table below |
| 4 | `access` | 4 | For a root's segment: 1 for RX, 2 for RO, 3 for RW; 0 for every other kind |
| 8 | `offset` | 8 | The start of the entry in the bundle, a multiple of 4096 |
| 16 | `file_bytes` | 8 | The bytes of the entry in the bundle, at least 1 |
| 24 | `memory_bytes` | 8 | For an RW segment, its bytes in memory, at least `file_bytes`, the rest zero; for every other entry, `file_bytes` |
| 32 | `address` | 8 | For a root's segment, its virtual address, a multiple of 4096; 0 for every other kind |
| 40 | `reserved` | 8 | 0 |

**Kinds:**

| Kind | Value | Entry | Who reads it |
| --- | ---: | --- | --- |
| Root segment | 1 | A segment of the root's image, which the kernel maps directly at boot | The boot of the root ([First process and boot information](#first-process-and-boot-information)) |
| Capacity record | 2 | The capacity record, whose fields belong to the objects component and to the VM and loading components | The boot wiring, with `Directory::capacity_record` ([capacity record](../../objects-capabilities/objects/contract.md#capacity-record)) |
| Service manifest | 3 | The manifest of the services, whose format belongs to the root | The root |
| Image | 4 | A static ELF image that the root reads and asks the kernel to load | The root and the loading component (planned), which checks it again |

**Checks.** `Directory::parse(bundle, length)` checks, in this order, and
returns the error of the first check that fails:

1. the bundle starts on a page boundary, its length is a multiple of 4096
   and it holds at least the 64 bytes of the header (`BundleRange`);
2. `magic` (`Magic`) and `version` (`Version`);
3. `entry_count` is at least 1, `directory_bytes` equals
   $64 + 48 \cdot$ `entry_count` and is at most the length, and
   `bundle_bytes` equals the length (`DirectoryRange`);
4. the reserved field of the header is 0 (`Reserved`);
5. then each entry, in the order of the directory: its kind is one of the
   four (`EntryKind`); its reserved field is 0 (`Reserved`); its `offset` is
   a multiple of 4096 and at least `directory_bytes` rounded up to a page,
   `file_bytes` is at least 1, `offset + file_bytes` fits in 64 bits and is
   at most the length, and its `offset` is at least the end of the previous
   entry rounded up to a page, so that the entries follow each other in the
   bundle and share no page (`EntryRange`); its `access` and `address` are
   0 and `memory_bytes` equals `file_bytes` unless it is a root's segment
   (`EntryForm`); for a root's segment, fewer than `MAX_ROOT_SEGMENTS`, 8,
   root's segments precede it, `access` is 1, 2 or 3, `address` is a
   multiple of 4096, `memory_bytes` equals `file_bytes` for RX and RO and
   is at least it for RW, and the range of `address` and `memory_bytes`,
   rounded up to a page, lies in `[ROOT_IMAGE_START, ROOT_IMAGE_END)` and
   shares no page with the range of an earlier root's segment (`Segment`);
6. the directory holds at least one root's segment, and `root_entry` is a
   multiple of 4 that lies in an RX segment (`RootEntry`);
7. it holds at most one capacity record (`CapacityRecords`).

- A directory without a capacity record makes the boot wiring use the
  default record of its board; the framing of a capacity record is that of
  its entry, and its bytes are checked by the
  [objects](../../objects-capabilities/objects/contract.md#capacity-record)
  component and by the VM and loading components after these checks.
- The limits of the size of the bundle and of the number of its entries
  are limits of the boot configuration, which the build checks against
  them (planned); this page fixes only the limits of the format.
- **The pages of the bundle.** The bundle shares no page with another
  section of the image. The board gives it to the boot memory map as a
  span of boot storage of its own
  ([boot memory map](../../boot-platform/fdt/contract.md#boot-memory-map)),
  so its pages are owned by boot storage and the rest of the image by the
  image, and none of them is in the direct map
  ([page ownership](../page-tables/contract.md#page-ownership)).

## EL0 controls

`krepi_arch::el0::write_controls` writes these registers on the executing
CPU, once, before the CPU first enters EL0: on the boot CPU before the first
return of the root, and on another CPU in its start. The fields of
`CNTKCTL_EL1`, `PMUSERENR_EL0` and `MDSCR_EL1` reset to unknown values, so
the kernel writes the whole registers; it then executes `ISB`. Each value
follows the observable outputs of the
[security model](../../../security.md#observable-outputs): EL0 reads
`CNTVCT_EL0` and `CNTFRQ_EL0`, and the default image traps EL0 access to the
other timers, to the performance monitors and to the debug communications
channel.

| Register | Value | Fields | Effect at EL0 |
| --- | --- | --- | --- |
| `CNTKCTL_EL1` | `0x2` | `EL0VCTEN`, bit 1, is 1; `EL0PCTEN`, bit 0, `EVNTEN`, bit 2, `EL0VTEN`, bit 8, and `EL0PTEN`, bit 9, are 0, and so are `EVNTI` and `EVNTDIR`; the higher bits are RES0 on the Cortex-A76 | A read of `CNTVCT_EL0` and of `CNTFRQ_EL0` does not trap, since `CNTFRQ_EL0` traps only when both `EL0VCTEN` and `EL0PCTEN` are 0; `CNTPCT_EL0`, the registers of the physical timer and those of the virtual timer trap with `EC` `0x18`; no event stream |
| `PMUSERENR_EL0` | `0x0` | `EN`, `SW`, `CR` and `ER` are 0; the other fields are RES0 on the Cortex-A76 | Every access to a register of the performance monitors traps with `EC` `0x18`, except an access to `PMUSERENR_EL0` itself: EL0 reads it, as 0, without a trap, and a write of it at EL0 is undefined, `EC` `0x00`; the Cortex-A76 of both boards, and of QEMU, implements them |
| `MDSCR_EL1` | `0x1000` | `TDCC`, bit 12, is 1; `SS`, bit 0, `KDE`, bit 13, and `MDE`, bit 15, are 0 | Every access to `MDCCSR_EL0`, `DBGDTR_EL0`, `DBGDTRRX_EL0` and `DBGDTRTX_EL0` traps with `EC` `0x18`; no hardware breakpoint, watchpoint or software step |

The virtual timer traps as well: it is not an output of EL0, and the kernel
uses it for preemption
([interrupts](../../boot-platform/boot/contract.md#interrupts)), which a
write of `CNTV_CTL_EL0` at EL0 would stop. The rules need
`HCR_EL2.{E2H, TGE}` other than `{1, 1}` where EL2 exists: QEMU virt in its
configuration has no EL2, and a board that enters at EL2 drops to EL1 with
`HCR_EL2.TGE` 0.

`write_controls` writes the eight bits of `SCTLR_EL1` that govern EL0 by a
read-modify-write that changes no other bit: it clears the bits of the mask
`0x0505c210` and sets those of `0x0404c010`. The values are those of
`INIT_SCTLR_EL1_MMU_ON` of Linux 6.12:

| Bit | Value | Effect at EL0 |
| --- | ---: | --- |
| `UMA`, bit 9 | 0 | An access to `DAIF` by `MRS` or `MSR` traps with `EC` `0x18`, so EL0 cannot mask an interrupt |
| `SA0`, bit 4 | 1 | An access with `SP` as its base checks the alignment of `SP` to 16 bytes and takes an SP alignment fault, `EC` `0x26` |
| `E0E`, bit 24 | 0 | The explicit data accesses of EL0 are little-endian |
| `UCT`, bit 15 | 1 | A read of `CTR_EL0` does not trap |
| `DZE`, bit 14 | 1 | `DC ZVA` does not trap |
| `UCI`, bit 26 | 1 | The cache maintenance by virtual address, `DC CVAU`, `DC CVAC`, `DC CVAP`, `DC CIVAC` and `IC IVAU`, does not trap |
| `nTWI`, bit 16 | 0 | A `WFI` that would wait traps with `EC` `0x01` |
| `nTWE`, bit 18 | 1 | `WFE` does not trap |

- These bits act only on EL0, and no code of EL1 depends on them before a
  CPU first enters EL0. `krepi_arch::mmu::enable` sets only `M`, `WXN`, `C`
  and `I`, which share no bit with these, so the order of the two writes
  does not change the result. Written by `el0`, the bits do not depend on
  the board or on the way it reaches EL1: on QEMU virt the CPU arrives with
  the reset value of `SCTLR_EL1`, `0x30c50838`, and on the Pi 5 with the
  value that the drop from EL2 writes.
- **Behaviour changes.** `UCT`, `DZE` and `UCI` differ from the reset value
  of QEMU's Cortex-A76, where they are 0, and `nTWI` too, which is 1 there.
  `SA0`, `UCT`, `DZE`, `UCI` and `nTWE` differ from the value that the
  prototype's drop from EL2 wrote, `0x30d00800`, where they are 0, and
  `MDSCR_EL1` from the prototype's 0, which did not trap the debug
  communications channel.

## Kernel stacks and blocking

The rules of the
[execution model](../../../architecture.md#system-calls-and-the-abi) hold;
this section states how this component represents them.

- **Kernel stacks.** Each CPU has one kernel stack with a guard below it
  and one emergency stack. The kernel stack of the boot CPU is the stack of
  the cold entry, `[__stack_bottom, __stack_top)`, 64 KiB with a guard of
  4 KiB below it
  ([cold entry](../../boot-platform/boot/contract.md#cold-entry)); the
  stacks of the other CPUs and the size and the probe of the emergency
  stacks belong to the components of multicore and of diagnostics and
  stacks (planned). The stacks are part of the image: no thread owns one,
  and no stack is mapped into the lower tables of a process other than
  through the copy of the lower kernel set, which gives EL0 no access to
  it.
- **Run to completion.** Every entry from EL0 starts at the top of the
  kernel stack of its CPU and ends with the return to EL0, which sets
  `SP_EL1` to that top again, so no frame of the kernel outlives an entry.
- **Blocking.** A call that blocks writes, after its checks, the wait record
  of its thread, in which the registers that its completion writes back are
  one of two forms: `x0` and `x1`, which the completer writes with
  `Context::set_return_values`, or `x0` to `x5`, which it writes with
  `Context::set_return_registers`
  ([results of a call](../../boot-platform/context/contract.md#results-of-a-call)).
  The record itself belongs to the waits component (planned). The thread
  blocks and the entry returns to another thread or waits.
- **Execution again.** A long operation that stops at a preemption point,
  where an interrupt is pending, stores its progress in its object and
  writes no result. The dispatch then moves the saved `elr` of its thread
  back by 4, from the address after the `SVC` to the `SVC` itself, while
  the executing CPU owns the saved context
  ([state fields](../../boot-platform/context/contract.md#state-fields));
  every other field stays as the entry saved it. The composer of the return
  handles the pending interrupt before it chooses a thread
  ([Entry and return](#entry-and-return)). When the thread next runs, it
  executes the `SVC` again at EL0, and the call repeats its checks and
  continues from the stored progress. The moved `elr` passes `validate`:
  the `SVC` lay in a page of the EL0 window from which the thread executed
  it. Whether a blocking call completes by its completer's write or by
  execution again is a rule of the contract of that call; one that
  completes by execution again moves `elr` back in the same way before its
  thread blocks.

## Check and execute

- The constants, `asid_capacity`, `check_processes`,
  `check_kernel_ranges`, `TablePool::pages`, `TablePool::new`,
  `TablePool::segment`, `Asids::new`, `Space::new`, `Space::ttbr0`,
  `check_range`, `classify`, `Directory::parse`, `Directory::entry`,
  `Directory::capacity_record`, `Directory::root_plan` and `BootInfo::new`
  write nothing; a refusal gives its error and nothing else.
- `choose` and `release_plan` write nothing. `take` and `release` are the
  write phases of an allocation and of a release: the caller takes the
  choice of `choose`, or the plan of `release_plan`, under the token of the
  allocator, and `release` checks the token of the plan again before its
  write, so neither write phase fails. An allocation or a release that a
  check refuses changes nothing.
- `Space::join` adds a CPU to the record and does not fail.
- The creation of a process completes `choose` before its first write; the
  boot of the root completes `root_plan` before it maps a page; a
  reclamation completes `release_plan` before it executes the plan.
- `__el0_entry`, `__el0_return`, `write_controls`, `load_kernel_tables` and
  `invalidate_asid` check nothing and do not fail. Their callers vouch that
  the address of a saved context is that of the current thread, or of the
  thread that is to run, aligned to 16 bytes and mapped for reads and writes
  at EL1; that the value of `TTBR0_EL1` is that of `Space::ttbr0` for the
  thread's address space, or the root of the lower kernel set with ASID 0;
  and that every exception is masked.

### Errors

`address_space::Error` (planned):

| Error | Rule broken | Entries | Order |
| --- | --- | --- | --- |
| `AsidCapacity` | A process capacity above the ASID capacity; a number of ASIDs of 0 or above it | `check_processes`, `Asids::new` | The last check of the capacity record, at boot |
| `Exhausted` | Every ASID is held | `choose` | Shared capacity |
| `GenerationExhausted` | The only free ASIDs have reached the last generation | `choose` | Shared capacity |
| `InvalidToken` | A token of ASID 0 or above the capacity, of a free ASID or of another generation | `release_plan`, `release` | Object state |
| `TooLong` | A buffer longer than its limit | `check_range` | The form of the register arguments |
| `Address` | A nonempty buffer that wraps or does not lie in its window | `check_range` | The range of user buffers |
| `KernelLayout` | A range of the kernel layout that ends above `EL0_START` | `check_kernel_ranges` | At boot, before `kernel_map` |
| `BundleRange` | A bundle that is not on page boundaries or shorter than the header | `Directory::parse` | Check 1 of the directory |
| `Magic` | Another magic | `Directory::parse` | Check 2 |
| `Version` | Another version | `Directory::parse` | Check 2 |
| `DirectoryRange` | No entry; a size of the directory that does not follow from its entries or exceeds the bundle; a size of the bundle other than that of the link | `Directory::parse` | Check 3 |
| `Reserved` | A reserved field that is not 0 | `Directory::parse` | Checks 4 and 5 |
| `EntryKind` | An unknown kind | `Directory::parse` | Check 5 |
| `EntryRange` | An entry that is not page aligned, is empty, ends beyond the bundle, starts in the directory or before the end of the previous entry | `Directory::parse` | Check 5 |
| `EntryForm` | An access, an address or a memory size where its kind has none | `Directory::parse` | Check 5 |
| `Segment` | A ninth root's segment, or a root's segment with another access, an unaligned address, a memory size that its access does not allow, or a range outside the root image range or sharing a page with another | `Directory::parse` | Check 5 |
| `RootEntry` | No root's segment, or a root entry that is not a multiple of 4 or lies in no RX segment | `Directory::parse` | Check 6 |
| `CapacityRecords` | More than one capacity record | `Directory::parse` | Check 7 |
| `RootTables` | A bundle whose mapping in the root needs more tables than its pool leaves after the copy of the lower kernel set | `Directory::root_plan` | At boot, before the root is mapped |

The errors of `check_range` are errors of the calls whose buffers it
checks, in the order of the
[security model](../../../security.md#internal-choices); the others stop the
boot or the operation that composes the entry. A context that `validate`
refuses at a return is no error of this page: the composer ends the
thread's process by a user fault of the cause `Other`
([a refused context](#user-faults)), and no call returns the error of
`validate`.

The errors of the prototype's ASID allocator, `Exhausted`,
`GenerationExhausted` and `InvalidToken`, and of its range check, `TooLong`
and `Address`, are kept; its `InvalidationFailed` is dropped, since the
invalidation of an ASID is a step of a plan that cannot fail, and a plan
that has not been followed by `release` keeps the ASID held instead. Of the
errors of its execution manager, `Asid` stands for the errors of the ASID
allocator, and `Capacity`, where the domains were full, for `Exhausted`
here and for the full process pool of the objects component;
`Preparation` and `Busy` no longer exist, since the lower tables come from
a plan that cannot fail and no code reaches a saved context while its
thread runs at EL0; the others belong to other components, as
[Legacy test vectors](#legacy-test-vectors) states for each vector.

## Work bounds

- `choose` scans at most the capacity of the allocator, at most 255 slots;
  `take`, `release_plan`, `release`, `Space::new` and `Space::ttbr0` take a
  fixed number of steps, and `Space::join` sets one bit of a set of at most
  the CPU count.
- `asid_capacity`, `check_processes`, `check_range`, `classify`,
  `TablePool::pages`, `TablePool::new`, `TablePool::segment` and
  `BootInfo::new` take a fixed number of steps; `BootInfo::new` writes at
  most `MAX_BOOT_CAPABILITIES` entries. `check_kernel_ranges` reads each of
  the at most 16 ranges of the layout once.
- `Directory::parse` reads the header once and each entry once, in the
  order of the directory: at most `entry_count` entries, which check 3
  bounds by the size of the bundle, and each of which takes at least one
  page of it. Since the entries follow each other, the check that they
  share no page compares each entry with the one before it; each root's
  segment is compared with the earlier ones, at most 7, since check 5
  refuses a ninth, so at most 28 comparisons in all.
- `Directory::root_plan` reads the at most 8 root's segments; the boot of
  the root maps at most the pages of the root block and of the bundle, one
  `map_page` each, and runs to its end at boot.
- `__el0_entry`, `__el0_return`, `write_controls`, `load_kernel_tables` and
  `invalidate_asid` run fixed sequences of instructions without a loop.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls. The reclamation of an address space
  is one step of the destruction of a process, a long operation of the
  lifecycle component (planned): `release_plan`, the execution of the plan
  on at most the CPUs of the record, `release` and the plan of `reset` of
  at most $N$ tables.

## Determinism

- **ASIDs.** An address space takes the lowest free ASID whose generation is
  not exhausted, the rule for slots of the security model's
  [internal choices](../../../security.md#internal-choices); ASID 0 is the
  kernel's.
- **Segments.** The segment of a process is that of its process slot, which
  the objects component chooses; this page makes no choice of tables.
- **Exceptions.** The synchronous exception of the current instruction
  comes first, and interrupts are taken only where the execution model
  takes them ([internal choices](../../../security.md#internal-choices)).
  When an IRQ becomes pending and the order in which the interrupt
  controller presents its numbers are
  [ND-02](../../../security.md#nd-02), and the arrival of the timer
  interrupt, which decides which instruction of EL0 an IRQ interrupts and
  where preemption happens, is [ND-01](../../../security.md#nd-01), of the
  register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism).
- **Requests.** With more than one CPU, the order in which CPUs take the
  token of the ASID allocator is the multicore interleaving of
  [ND-03](../../../security.md#nd-03); for each order, the rules of this
  page fix the result.
- **Boot.** The directory, the root plan, the boot information and the
  values of the EL0 controls follow from the bytes of the bundle and the
  constants of this page, so cold boots of one image give the same root.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The ASID allocator: whether each ASID is held, and its generation | Shared | The token of the allocator, a field of the kernel root; with one CPU, the executing CPU | The end of the write phase of `take` or `release`, in the transaction that composes it | Under the token, by the release of the lock that provides it once CPUs share it |
| The CPU record of each address space | Shared | The token of the record: a CPU joins it before it loads the address space and leaves it only with the release, after the invalidation | The end of `join`; the end of `release` | Under the token, before the CPU writes `TTBR0_EL1` |
| The record `Space` of each process, its ASID token | Per-process | The token of the process | The write-back of the creation that gives it, or of the reclamation that releases it | Under the token of the process |
| The table set of the lower tables of each process, its descriptors and its record of tables in use | Per-process | The token of the process; during `clone_kernel_from`, also the token of the kernel tables, for the source | The `Sync` that ends each plan | By that `Sync`; a CPU relies on the set only after its write of `TTBR0_EL1` and `ISB` |
| `TTBR0_EL1` | Per-CPU | The executing CPU: `__el0_return` and `load_kernel_tables` | The `ISB` after the write | `none`: each CPU has its own |
| `CNTKCTL_EL1`, `PMUSERENR_EL0`, `MDSCR_EL1` and the eight EL0 bits of `SCTLR_EL1` | Per-CPU | The executing CPU; only `write_controls` writes them, once | The `ISB` after `write_controls` | `none`: each CPU has its own |
| The current thread of each CPU, in the record of the CPU | Per-CPU | Its CPU: the composer of the return writes it, and `__el0_entry` reads it | The write of the composer before `__el0_return` | `none`: each CPU has its own |
| The kernel stack and the emergency stack of each CPU | Per-CPU | Its CPU | - | `none` |
| The directory, the capacity record and the boot information | Shared, read-only after boot | The boot CPU, which checks and writes them before the first entry from EL0 | The return of `Directory::parse`; the write of the boot information before its page is mapped | Once, before the secondary CPUs start; they never change afterwards |
| The table pool: its base and its segments | Shared, read-only after boot | The boot CPU, which carves it | The `assign` of the carving | Once, before the secondary CPUs start; the tables of a segment are fields of the process of its slot |

The saved context of a thread, with the FP/SIMD and TLS registers and
`CPACR_EL1`, is classified in the
[State fields](../../boot-platform/context/contract.md#state-fields) of the
context contract, the descriptors of the lower kernel set and the page
ownership table in those of the
[page-tables](../page-tables/contract.md#state-fields) contract, and the
TLB entries that an invalidation removes in those of the
[boot](../../boot-platform/boot/contract.md#state-fields) contract.

## Testing obligations

- The host tests of the module `address_space` (planned) hold the frozen
  vectors of [Legacy test vectors](#legacy-test-vectors) whose entry is on
  this page, each case with its expected output, and write their results
  ([host results](../../../formal-verification.md#host-results)).
- Host tests give each check of [Boot-bundle directory](#boot-bundle-directory)
  a directory that passes at its limit and one that fails by one beyond it,
  and, for each pair of consecutive checks whose errors differ, a directory
  that breaks both and gets the error of the earlier; they include a
  directory without a capacity record, one with 8 and one with 9 root's
  segments, and segments that share a page.
- Host tests give `classify` every value of `EC` at vector 8, with the
  fault status codes of [User faults](#user-faults) for `EC` `0x20` and
  `0x24`, and vector 9, and check that each gives the class and the cause of
  the two tables; `asid_capacity` its four combinations of inputs;
  `check_processes` 255 and 256 processes; `check_kernel_ranges` a range
  that ends at `EL0_START` and one that ends a page beyond it;
  `root_plan` a bundle whose root takes exactly the tables left and one
  that needs one more.
- A host test carves the table pool of 64 and of 255 processes from the
  page ownership table of the 8 GB Pi 5 and checks that it adds at most one
  extent, and that `TablePool::segment` gives disjoint segments.
- On QEMU virt, a test image takes each of the ten classes of
  [Exception classes](#exception-classes) once from EL0: `Svc` by
  `svc #0`; `DataAbort` by a read of the guard of a stack;
  `InstructionAbort` by an execution of a data page; `PcAlignment` by a
  branch to an address that is not a multiple of 4; `SpAlignment` by a
  load with `SP` as its base while `SP` is not a multiple of 16;
  `TrappedAccess` by a read of `CNTP_CTL_EL0`; `Breakpoint` by `BRK`;
  `Unknown` by `UDF`; `Other` by the FP/SIMD case of its cause; and `Irq`
  by an IRQ of the timer that interrupts a loop at EL0. It also takes the
  case of each cause of [User faults](#user-faults). For each it checks
  the class, and for each user fault the cause, the fault record and that
  the process does not run again.
- On QEMU virt, a test image reads `CNTVCT_EL0` and `CNTFRQ_EL0` at EL0
  without a trap, and an access at EL0 to the physical timer, to a register
  of the performance monitors and to `DBGDTR_EL0` each traps with `EC`
  `0x18`.
- On QEMU virt, the root of a test image reads its boot information and the
  directory through `BUNDLE_WINDOW`, and checks the registers of its first
  instruction, as the context contract requires.
- On QEMU virt, a test image creates and destroys more processes than the
  ASID capacity of its allocator, and checks that each reuse of an ASID
  follows the invalidation of its entries.
- Each rule of [Entry and return](#entry-and-return) has one test, a case
  of a QEMU suite or a self-check of a test image, which the change that
  adds the code names in the Test column of its row of
  [Open obligations](#open-obligations); one test may serve several rules.
- No test bounds the time that a step takes, and the tests of interrupts
  take their periods from the platform parameters.

## Open obligations

The page-table logic leaves the tables of an address space and their ASIDs
to this component
([page-tables obligations](../page-tables/contract.md#open-obligations)),
and the specification of the component is to come with the proof of
contexts, user copies and the private VM, by release 0.2. So the module
`address_space`, the adapter `el0` with its routines and its `unsafe`
sites, and each rule of the saved, restored and cleared state of the entry
and the return have a row here. The Rust entry `el0_dispatch` of an image
is code of its board crate, which the open obligations of that crate cover
by its path, as those of the
[boot](../../boot-platform/boot/contract.md#open-obligations) component do
for QEMU virt; the change that adds the entry gives its exported symbol a
row, as that component does for the dispatch of exceptions.

| Obligation | Kind | Verified state | Carrier | Stage | Test |
| --- | --- | --- | --- | --- | --- |
| `kernel/src/address_space.rs` (planned) | `code` | Neither | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/el0.S#__el0_entry` (planned) | `assembly` | Writes the saved user context that the context logic describes, its general registers, `SP_EL0`, `ELR_EL1` and `SPSR_EL1` | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/el0.S#__el0_return` (planned) | `assembly` | Reads the saved user context that the context logic describes, and writes `TTBR0_EL1` and the user registers | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/el0.S#entry-stack` (planned) | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#entry-save-general` (planned) | `register-state` | Writes the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#entry-save-system` (planned) | `register-state` | Writes the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#entry-mask` (planned) | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#return-validate` (planned) | `register-state` | Reads the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#return-ttbr0` (planned) | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#return-load` (planned) | `register-state` | Reads the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#return-stack` (planned) | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S#return-no-kernel-value` (planned) | `register-state` | Reads the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/el0.S` (planned) | `assembly` | Reads and writes the saved user context that the context logic describes | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/el0.rs` (planned) | `code` | Neither | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/el0.rs#load_kernel_tables` (planned) | `unsafe` | Neither (writes `TTBR0_EL1` with the root of the lower kernel set and ASID 0, then `ISB`) | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/el0.rs#invalidate_asid` (planned) | `unsafe` | Neither (executes `TLBI ASIDE1` with an ASID and `DSB NSH`) | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/el0.rs#write_controls` (planned) | `unsafe` | Neither (writes `CNTKCTL_EL1`, `PMUSERENR_EL0`, `MDSCR_EL1` and eight bits of `SCTLR_EL1`, then `ISB`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - |

## Legacy test vectors

The component freezes 33 vectors from the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`. A vector of this
page is one `#[test]` function of the prototype; in the vector file it is
the lines whose id starts with the id of the vector and a dot, one line for
each case, `<vector>.<n>` from 1 in the order of the test, where a case is
one call of an entry of this page that the test makes, with the output that
it asserts. The expected outputs below are the assertions of the test
bodies.

| File | Vectors |
| --- | ---: |
| `src/arch/aarch64/asid/tests.rs` | 7 |
| `src/execution/tests/creation.rs` | 7 |
| `src/execution/tests/layouts.rs` | 4 |
| `src/execution/tests/capacity.rs` | 3 |
| `src/userspace/tests.rs` | 10 |
| `src/arch/aarch64/address.rs` | 2 |

The prototype's `src/arch/aarch64/asid.rs` holds its tests in the first
file. The tests of its execution manager in the second to the fourth file
exercise address spaces together with objects, quotas, page allocations and
kernel stacks; its other tests are not vectors of this page.

**Notation.** Addresses, lengths, values and generations are written as
`0x` and lowercase hexadecimal digits without separators, zero also as 0;
counts and ASIDs in decimal; a range as `<start>+<length>`, and a token as
`<asid>:<generation>`. The output of a call is `ok`, followed by its
fields, or `err=<error>`, with the errors of this page. The prototype's
`AsidPool::<N>::new()` is `Asids::new(N, 255)`; its `allocate` is `choose`
followed by `take`; and its `release(token, invalidate)` is
`release_plan(token)`, the execution of the invalidation of the plan, and
`release(plan)`, so a release whose invalidation the test makes fail is a
plan that has not been followed by `release`. The prototype's
`check_range` is `check_range` with the same arguments; its output
`Ok(None)` is `ok none`, and `Ok(Some(range))` is `ok` and the range.

**The execution manager of the prototype.** A `Manager<D, N>` keeps up to
$D$ domains, each a process with one thread and its own ASID from an
allocator of capacity $D$, with a page allocator of $N$ extents over the
pages from `0x1000`. A creation passes a quota of pages and takes four page
allocations: tables, data, user stack and kernel stack, 2, 1, 1 and 2
pages in its default layout, which the test backend zeroes, prepares and
records as the events `Zero`, `Prepare`, `Cancel`, `Retire`,
`Invalidate(asid)` and `Scrub`. Its object pool has 4 processes and 4
threads unless a row says otherwise. The Entry column gives the case on this
page, and names the component where a part of the test belongs elsewhere.

**Vectors without a case.** A vector whose Entry column names no entry of
this page has no line in the vector file; its row gives the reason.

**Behaviour changes.** These rules differ from the prototype:

- The release of an ASID is a plan and its confirmation, and the
  invalidation of the plan cannot fail; the prototype's failed
  invalidation, which kept the ASID for a retry, is a plan that has not
  been followed by `release`, which keeps the ASID held as well
  (`as-02`, `as-18`), and `InvalidationFailed` does not exist.
- The capacity of the ASID allocator is the process capacity of the
  capacity record, checked at boot with a fixed error; the prototype's
  allocator panicked for a capacity of 0 or above 255 (`as-06`, `as-07`)
  and its execution manager refused it as an invalid layout (`as-08`).
- The tables of a process are the segment of its process slot in the table
  pool, carved once at boot and zeroed then and by `reset`; a creation
  takes no table pages, does not zero them and cannot fail to prepare its
  root, since `clone_kernel_from` executes a plan that its check fixed
  (`as-08` to `as-10`, `as-13`, `as-15`, `as-20`). Every process has $N$
  tables, so layouts with other table counts do not apply.
- Threads own no kernel stack, so the kernel-stack parts of the layouts of
  the prototype do not apply.
- The prototype's checks of layouts, quotas, object pools, page
  allocations, owner identities, handles and the states of domains belong
  to the objects component and to the components of creation, of the
  lifecycle of processes and of VM and loading (planned), whose rules take
  these assertions as inputs; `as-12`, `as-14` and `as-16` have no case on
  this page, and the other vectors keep only their cases of this page.
- The direct address and the value of `TCR_EL1` are rules of the
  page-tables component; this page relies on the value of `TCR_EL1` for the
  width of ASIDs, and `as-32` and `as-33` have their cases with the code of
  those rules.

### `src/arch/aarch64/asid/tests.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `as-01` | 4 | `pool_reserves_zero_and_enforces_capacity` | Capacity 2: two allocations give ASIDs 1 and 2; a third is `err=Exhausted` | `Asids::new`, `choose`, `take` |
| `as-02` | 12 | `invalidation_failure_retains_lease_until_successful_retry` | Capacity 1: the allocation gives `1:1`; its release with an invalidation of ASID 1 that fails is `err=InvalidationFailed` after one invalidation, and an allocation is then `err=Exhausted`; its release with an invalidation of ASID 1 that succeeds is `ok`, after two invalidations in all; the next allocation gives ASID 1 with another generation, `1:2`; a release of `1:1` is `err=InvalidToken` and invalidates nothing; an allocation is `err=Exhausted`; the release of `1:2` is `ok` | `release_plan` of `1:1` gives a plan of ASID 1; before its `release`, `choose` is `err=Exhausted`; after it, `choose` and `take` give `1:2`; `release_plan` of `1:1` is `err=InvalidToken` and gives no plan; `choose` is `err=Exhausted`; the release of `1:2` is `ok`. The failed invalidation is the plan before its `release` |
| `as-03` | 45 | `invalid_tokens_never_invoke_invalidation` | Capacity 2, with `1:1` allocated: the releases of `0:1`, `3:1`, `1:2` and `2:0` are each `err=InvalidToken` and invalidate nothing; the release of `1:1` is `ok`; a second release of `1:1` is `err=InvalidToken` and invalidates nothing | `release_plan`, which gives no plan for a refused token, and `release` |
| `as-04` | 79 | `exhausted_generations_never_wrap_or_prevent_other_slots_from_allocating` | Capacity 2, whose test sets the generation of ASID 1 to `0xfffffffffffffffe`: the allocation gives `1:0xffffffffffffffff`; its release is `ok`; the next allocation gives ASID 2; the next is `err=GenerationExhausted`, and the generation of ASID 1 stays `0xffffffffffffffff`; after the release of ASID 2, an allocation gives ASID 2 | `choose`, `take`, `release_plan`, `release`. The host test sets the generation of the slot as the prototype's test does, through the test support of the module |
| `as-05` | 94 | `full_eight_bit_asid_range_is_available` | Capacity 255: 255 allocations give ASIDs 1 to 255 in order; the next is `err=Exhausted` | `Asids::new`, `choose`, `take` |
| `as-06` | 104 | `zero_capacity_is_invalid` | Capacity 0: the construction panics with the message `ASID capacity must be 1..=255` | `Asids::new(0, 255)`: `err=AsidCapacity` |
| `as-07` | 110 | `capacity_cannot_exceed_eight_bit_asids` | Capacity 256: the construction panics with the same message | `Asids::new(256, 255)` and `check_processes(256, 255)`: `err=AsidCapacity` |

### `src/execution/tests/creation.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `as-08` | 4 | `malformed_layout_and_asid_capacity_are_rejected_without_panics` | A manager of 1 domain and 16 extents over 64 pages is `err=InvalidLayout` for a layout of 0 table pages, of 0 data pages, of 0 user-stack pages, of 0 kernel-stack pages and of `0xffffffffffffffff` table pages; managers of 0 and of 256 domains are each `err=InvalidLayout` | `Asids::new(0, 255)` and `Asids::new(256, 255)`: `err=AsidCapacity`. The layouts of data and stacks belong to the VM and loading components (planned); the table and kernel-stack cases do not apply |
| `as-09` | 44 | `every_zero_failure_rolls_back_all_pages_objects_and_asids` | Capacity 1. For each of the four page allocations of a creation with a quota of 6, a zeroing that fails at it gives `err=Page(ZeroFailed)`: the usage of the manager and of the objects is as before, there is no `Prepare`, `Cancel` or `Invalidate(1)`, and there is one `Scrub` for each allocation before the one that failed; a creation then gives ASID 1 and the process generation 1, and its destruction restores the usage | With capacity 1, `choose` gives ASID 1 before and after a creation that takes no ASID, and `take` then gives `1:1`. The page allocations, the zeroing and the generations of processes belong to the creation and objects components; the tables are not allocated or zeroed at creation |
| `as-10` | 77 | `prepare_failure_cancels_before_scrub_and_never_publishes_metadata` | Capacity 1: a creation whose preparation of the root fails is `err=Preparation`; the usage is as before; the events are four `Zero`, then `Prepare`, `Cancel` and four `Scrub`, 10 in all; the first 6 pages of the backing are zero; a creation then gives ASID 1 and the process generation 1 | As `as-09`, for its ASID. A root that fails its preparation does not exist: the lower tables come from `clone_kernel_from`, whose plan cannot fail, so `Preparation` does not exist |
| `as-11` | 108 | `quota_capacity_and_object_capacity_fail_before_touching_backing` | Capacity 1: a creation with a quota of 5 is `err=Quota`, with no change and no event; after a creation, another is `err=Capacity`, with no change and no event; after its destruction, a creation on an object pool of one process, already full, is `err=Object(PoolExhausted)`, with no change and no event | With the one ASID of capacity 1 held, `choose` is `err=Exhausted` and writes nothing. The quota and the object pool belong to the objects and creation components |
| `as-12` | 142 | `out_of_memory_and_metadata_exhaustion_restore_partial_allocations` | Managers of 1 domain over 1 to 5 pages are each `err=Page(OutOfMemory)` at a creation, with the usage as before and no process or thread; a manager of 1 domain and 2 extents over 64 pages is `err=Page(MetadataExhausted)`, with the usage as before | No case: the pages of data and stacks belong to the creation component and the page ownership table, and the tables take no page at creation |
| `as-13` | 166 | `successful_creation_charges_all_categories_and_one_mapping_obligation` | Capacity 2: after one creation, 1 domain, 1 ASID, 6 charged pages, 4 allocations and 6 allocated pages; tables of 2 pages and a kernel stack of 2 pages; the process holds 1 mapping obligation and its thread is ready; another thread of the process is `err=QuotaExceeded`; 5 events, the fifth `Prepare` | `choose` and `take` give `1:1`; the process uses the segment of its slot, $N$ tables. The charges, the mapping obligation and the thread belong to the objects and creation components; the kernel stack does not apply |
| `as-14` | 199 | `owner_generation_exhaustion_never_wraps_or_touches_backing` | With the next owner identity of the manager at `0xffffffffffffffff`, a creation and its destruction succeed; the next creation is `err=GenerationExhausted`, with no event | No case: the owner identities of page allocations belong to the creation component; the table pool has one owner identity for the whole boot |

### `src/execution/tests/layouts.rs`

Unless a row says otherwise, the managers keep 2 or 3 domains with 16
extents over 64 pages, and the large layout has 3 table, 4 data, 2
user-stack and 3 kernel-stack pages, 12 pages.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `as-15` | 20 | `mixed_layouts_charge_actual_pages_and_reclaim_out_of_order` | Capacity 3: a domain of the default layout and one of the large layout with a quota of 12: 6 pages for the default, 12 for the large, whose backing is 3, 4, 2 and 3 pages; 18 charged and 18 allocated pages; no range of the one overlaps a range of the other; after the destruction of the first, 12 charged and allocated pages; a new domain of the default layout takes the same backing as the first, with another handle; after the destruction of the large one, 6 charged pages, its ranges read 0, and its handle is `Stale`; after the last destruction, the usage of the start | The segment of a process slot serves the next process of that slot, with its tables zero after `reset`; the segments of two slots share no table. Every process has $N$ tables, so the table counts of the layouts do not apply; the data, the stacks and the handles belong to the creation, VM and objects components |
| `as-16` | 64 | `bad_layout_or_insufficient_quota_has_no_allocation_or_object_side_effects` | Capacity 2, with one domain: the large layout with 0 table, data, user-stack or kernel-stack pages, with `0xffffffffffffffff` data pages and with `0xfffffffffffff` data pages is each `err=InvalidLayout` with a quota of `0xffffffffffffffff`; the large layout with a quota of 11 is `err=Quota`; the state, the usage of the objects and the next owner identity are unchanged, with no event | No case: layouts and quotas belong to the creation and VM components, and threads own no kernel stack |
| `as-17` | 114 | `variable_allocation_failures_preserve_a_live_domain` | Capacity 2, with one domain whose backing the test fills with `0x4d`. For each of five stages, a creation of the large layout that fails at one of its four zeroings or at its preparation is `err=Page(ZeroFailed)` or `err=Preparation`; the usage is as before, the first domain and its backing are unchanged, and there is no `Retire` or `Invalidate`; a creation then gives ASID 2 and 18 charged pages, and the destructions restore the usage | With ASID 1 held, a creation that fails takes no ASID and leaves the token and the segment of the live process unchanged; `choose` then gives ASID 2. The page allocations belong to the creation component |
| `as-18` | 164 | `failed_invalidation_retains_exact_large_charge_until_retry` | Capacity 2, with a domain of the default layout and one of the large layout: the destruction of the large one with an invalidation that fails is `err=Asid(InvalidationFailed)`; the state is unchanged, the events are `Retire` and `Invalidate(2)`, the domain is `InvalidState`, a creation is `err=Capacity`, and its process holds 1 mapping obligation; with an invalidation that succeeds, its destruction makes `Invalidate(2)` first, 5 events in all, and leaves 6 charged and allocated pages; after the last destruction, the usage of the start | The release of ASID 2 in its order: the tables unreachable, `Retire`; the plan, `Invalidate(2)`, `TLBI ASIDE1` of ASID 2; then `release`. Before `release`, ASID 2 and the segment stay held, and with both ASIDs of capacity 2 held, `choose` is `err=Exhausted`. The failed invalidation is the plan before its `release`; the states and charges belong to the lifecycle and objects components |

### `src/execution/tests/capacity.rs`

The managers keep 4 domains with 32 extents over 64 pages, and each test
fills the data and stacks of its live domains with a tag of its own and
configures their contexts.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `as-19` | 95 | `fourth_domain_rollback_preserves_three_live_contexts_and_all_backing` | For each of five stages, with three live domains: a fourth creation that fails at one of its four zeroings or at its preparation is `err=Page(ZeroFailed)` or `err=Preparation`; the usage is as before, with no `Retire` or `Invalidate`, and the three domains keep their state, contexts, backing, threads and processes; a fourth creation then gives ASID 4, with 4 domains and 4 ASIDs; after the four destructions, the usage of the start, with no process or thread | With ASIDs 1 to 3 held, a creation that fails takes no ASID; `choose` then gives ASID 4, the lowest free, and the tokens and segments of the live processes are unchanged. The contexts, the backing and the objects belong to the context, creation and objects components |
| `as-20` | 177 | `four_domains_use_distinct_leases_and_fifth_rejection_has_no_backend_effects` | Four creations give ASIDs 1, 2, 3 and 4, and the ranges of their backing are pairwise disjoint; 16 allocations, 17 metadata entries in use and 24 charged pages; a fifth creation is `err=Capacity`, with no event, no zeroing and no change; the four domains keep their state and are destroyed, after which the usage is that of the start | ASIDs 1 to 4 are distinct and the segments of four process slots share no table; with the 4 ASIDs of capacity 4 held, `choose` is `err=Exhausted` before any write. The table pool is one holder carved at boot, so the counts of allocations and metadata entries differ here |
| `as-21` | 243 | `middle_domain_reuse_invalidates_only_its_lease_and_preserves_three_survivors` | Of four domains, the destruction of the second invalidates ASID 2 alone; 3 domains remain and keep their state; a new creation gives ASID 2 and the same backing, the same process and thread slots with other generations; its context is not configured, `InvalidState`; its data reads `0xa5` from its preparation and its stacks 0; the old handle is `Stale` for its state, its start and its destruction, with no change and no event; each of the other three runs and is suspended with its context and keeps its state; after the last destruction, the usage of the start | The release of the second address space invalidates ASID 2 alone; the next creation takes ASID 2, the lowest free, as `2:2`, with the segment of its process slot, the slot of the destroyed process. The slots, generations, contexts and handles belong to the objects and context components |

### `src/userspace/tests.rs`

Unless a row says otherwise, the window is `0x4000` to `0x8000` and the
limit `0x2000`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `as-22` | 8 | `empty_buffers_do_not_require_an_address_or_valid_bounds` | With the limit 0, a length of 0 at each address `0x0`, `0x4000`, `0x8000` and `0xffffffffffffffff`, in the window and in the reversed window `0x8000` to `0x4000`: `ok none` | `check_range` |
| `as-23` | 16 | `lower_boundary_is_inclusive` | `0x4000` of length 1: `ok 0x4000+0x1`; `0x3fff` of length 2: `err=Address` | `check_range` |
| `as-24` | 31 | `upper_boundary_is_exclusive_but_an_end_may_equal_it` | `0x7fff` of length 1: `ok 0x7fff+0x1`; `0x8000` of length 1 and `0x7fff` of length 2: `err=Address` | `check_range` |
| `as-25` | 50 | `address_addition_must_not_wrap` | In the window `0x0` to `0xffffffffffffffff`, `0xffffffffffffffff` of length 1 and `0xfffffffffffffffc` of length 4: `err=Address` | `check_range` |
| `as-26` | 60 | `transfer_limit_is_inclusive` | With the limit `0x1000`, `0x4000` of length `0x1000`: `ok 0x4000+0x1000`; of length `0x1001`: `err=TooLong` | `check_range` |
| `as-27` | 75 | `length_limit_takes_precedence_over_invalid_addresses` | With the limit 1, a length of 2 at `0x0`, `0x8000` and `0xffffffffffffffff`: `err=TooLong`; in the window `0x0` to `0xffffffffffffffff` with the limit 1, `0x0` of length `0xffffffffffffffff`: `err=TooLong` | `check_range` |
| `as-28` | 89 | `nonempty_buffers_fail_with_a_zero_limit` | With the limit 0, `0x4000` of length 1: `err=TooLong` | `check_range` |
| `as-29` | 97 | `crossing_a_page_boundary_is_a_valid_address_interval` | `0x4fff` of length 2: `ok 0x4fff+0x2` | `check_range` |
| `as-30` | 108 | `high_addresses_are_preserved_without_truncation` | In the window `0xffff000000000000` to `0xffffffffffffffff`, `0xffff000000001234` of length `0x11`: `ok 0xffff000000001234+0x11`; `0xfffffffffffffffe` of length 1: `ok 0xfffffffffffffffe+0x1` | `check_range` |
| `as-31` | 128 | `empty_or_reversed_windows_reject_nonempty_buffers` | In the window `0x4000` to `0x4000` and in the window `0x8000` to `0x4000`, `0x4000` of length 1: `err=Address` | `check_range` |

### `src/arch/aarch64/address.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `as-32` | 36 | `direct_spans_preserve_high_pa_and_reject_range_wrap` | The direct address of `0x0+0x1000` is `0xffffff8000000000`, of `0x100000000+0x2000` `0xffffff8100000000` and of `0x7ffffff000+0x1000` `0xfffffffffffff000`; `0x7ffffff000+0x2000` and `0x8000000000+0x1000` have none | No case on this page: `page_tables::direct_address` of the [kernel direct map](../page-tables/contract.md#kernel-direct-map), whose host test comes with the code of that rule |
| `as-33` | 49 | `both_walk_regions_have_matching_policies_and_ttbr0_asids` | For each physical size encoding 0 to 5, with the caches off and on: `T0SZ`, bits 0 to 5, and `T1SZ`, bits 16 to 21, are 25; `TG0`, bits 14 and 15, is `0b00` and `TG1`, bits 30 and 31, `0b10`, both 4 KiB; `SH0`, bits 12 and 13, and `SH1`, bits 28 and 29, are `0b11`; `IRGN0`, `ORGN0`, `IRGN1` and `ORGN1`, two bits each from bits 8, 10, 24 and 26, are `0b01` with the caches on and `0b00` off; `IPS`, bits 32 to 34, is the encoding; `EPD0`, bit 7, `A1`, bit 22, `EPD1`, bit 23, `AS`, bit 36, `TBI0`, bit 37, and `TBI1`, bit 38, are 0; the encoding 6 gives no value | No case on this page: the value of `TCR_EL1` that `krepi_arch::mmu::enable` writes ([turning the MMU on](../page-tables/contract.md#write-plans-and-publication)), whose host test comes with the code of that rule; [Address spaces and ASIDs](#address-spaces-and-asids) takes its `A1` and `AS` of 0 for the width of ASIDs, 8 bits from `TTBR0_EL1` |

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  `TTBR0_EL1` with its ASID and `CnP`; `TCR_EL1` with `AS` and `A1`, and
  `ID_AA64MMFR0_EL1` with `ASIDBits`; `TLBI ASIDE1` and the completion of
  TLB maintenance by `DSB NSH` for one PE; `ESR_EL1` with the exception
  classes `0x00`, `0x01`, `0x07`, `0x15`, `0x18`, `0x20`, `0x22`, `0x24`,
  `0x26` and `0x3c`, the `TI` field of a trapped `WF*` instruction and the
  fault status codes of Data and Instruction Aborts; `FAR_EL1`; the masking
  of asynchronous exceptions taken from EL0 by `PSTATE`; `SCTLR_EL1` with
  `UMA`, `SA0`, `E0E`, `UCT`, `DZE`, `UCI`, `nTWI` and `nTWE`;
  `CNTKCTL_EL1`, `PMUSERENR_EL0` and `MDSCR_EL1` with their traps of EL0;
  and the effect of `HCR_EL2.{E2H, TGE}` on them.
- Arm Limited, *Arm Cortex-A76 Core Technical Reference Manual*, revision
  r4p1, document 100798_0401_00_en, 2020,
  <https://documentation-service.arm.com/static/5f562083235b3560a01e03bc>:
  `ID_AA64MMFR0_EL1`, whose `ASIDBits` is `0b0010`, and the performance
  monitors of the core.
- The QEMU Project, QEMU 8.2.2, `target/arm/tcg/cpu64.c`,
  <https://gitlab.com/qemu-project/qemu/-/blob/v8.2.2/target/arm/tcg/cpu64.c>:
  the `ID_AA64MMFR0_EL1`, the `ID_AA64DFR0_EL1` and the reset value of
  `SCTLR_EL1` of the CPU `cortex-a76`.
- The Linux kernel, version 6.12, `arch/arm64/include/asm/sysreg.h`,
  <https://github.com/torvalds/linux/blob/v6.12/arch/arm64/include/asm/sysreg.h>:
  `INIT_SCTLR_EL1_MMU_ON`, whose bits that govern EL0 are those of
  [EL0 controls](#el0-controls).
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/user-execution.md`, lines 41 to 50: the layout of
    the address space of a domain, with its code, data, user stack and
    guard, and its private kernel stack and guard, which is not carried:
    the pages of a process lie in the EL0 window, where the device tree of
    the Pi 5 at `0x10000000` is not, and threads own no kernel stack;
  - `docs/features/kernel/user-execution.md`, lines 158 to 168: the nine
    user faults of the prototype's tests and their exception classes, which
    give the cases of the QEMU tests of [User faults](#user-faults); its
    seventh, an FP/SIMD instruction in a domain without FP/SIMD, does not
    apply, since every thread at EL0 has FP/SIMD access;
  - `docs/features/services/static-bootstrap.md`, lines 44 to 48: the boot
    information page of eight words and the addresses of that page and of
    the bundle, both read-only and never executable at EL0, which the
    fields of [First process and boot information](#first-process-and-boot-information)
    replace.
