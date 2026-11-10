# Architecture

This page describes the target architecture of krepi. Only a small part of
it is implemented in this repository; the [feature index](features/README.md)
lists what the system provides. Rules that are already fixed are stated as
rules. Questions that are still open are listed under
[open design questions](#open-design-questions) and are not answered here.

## Protection domains

A protection domain is an address space with a set of authorities and a fault
boundary. It is a run-time notion: a domain is neither a Git repository, a
crate nor a job.

```text
EL0   root (supervisor and process manager)
      file service, read-only image service, file system services
      block driver, stream service, UART service
      job service, display and input services, device drivers
      worker processes: CAS, plotting, Python, proof compile/run/check
      POSIX environments: a process service and its POSIX processes
      Linux processes, each with its compatibility runtime
        |  SVC, IPC, notifications, shared pages (all authorized)
EL1   kernel: threads, budgets, address spaces, capabilities, IPC, IRQs
        |
HW    CPUs, MMU, GIC, timers, platform protection
```

| Domain | Holds | When it fails |
| --- | --- | --- |
| Kernel (EL1) | Kernel objects, page tables, scheduling, GIC and timers, hardware protection operations | A kernel fault is a system fault: minimal diagnostics, then halt or controlled restart |
| Root | Initial resources, creation, termination and granting of authority, the service manifest and recovery policy | A root failure is a system failure; the root does not claim to restart itself |
| File service | The authorized namespace of each environment with its mounts, path resolution, files and directories, the read-only boot bundle and tmpfs with quotas; its sessions with the storage back ends, and at first the session of the block service that holds its persistent namespace | Open file sessions fail; data held only in memory, tmpfs included, may be lost and writes are not replayed; the back ends keep their committed state |
| Read-only image service | The read-only system image: its manifest and the files that it lists, each block checked against the hash tree of its file whenever it is read, and the execute right of the files that the manifest marks executable; the contents of installed packages, checked in the same way against the roots recorded when they were installed | Only the sessions of its mounts fail; it holds no state beyond its caches |
| File system service | One writable volume, its commits and its quotas | Only the sessions of its mounts fail; writes that were not committed are lost, and recovery returns the last commit |
| Block driver | Granted MMIO, IRQ and DMA buffers; ranges of blocks, each granted to one client, so that only the updater writes the A/B slots and the approval records | The device is stopped and in-flight operations drained before memory is reclaimed |
| Workers | Private heap and stack, an input snapshot, limited file, stream and result rights | Each non-cooperative job runs in a process that can be killed as a whole |
| Process service | The process IDs, parent relations, exit statuses, process groups and sessions of one POSIX environment, and the creation right and quota from which it creates every process of that environment | Every process of the environment is destroyed with it; other environments continue |
| Linux process | An unmodified Linux program and the compatibility runtime that loading places in its address space, with the authority of that process only | Only that process is affected, also when the program damages its runtime |

The kernel keeps only the mechanisms that need EL1. Drivers, file systems,
general executable loading and application policy run in EL0. The kernel does
not parse file systems or arbitrary ELF files. The POSIX layer and Linux
compatibility run in EL0 as well: the kernel keeps no process IDs, signal
dispositions or other POSIX state and implements no Linux system call
([processes](#processes-posix-and-linux-compatibility)).

## Boot and the resident root

1. The firmware hands control to the kernel entry. The kernel checks the
   exception level, memory and reserved ranges and the device tree, then
   initializes exceptions, memory, timers, interrupts and scheduling.
2. The kernel maps exactly one root task from a segment description that the
   build validated and fixed in the image, and hands it typed boot
   information and its initial capabilities. This path performs only bounded
   mapping and entry checks.
3. The root reads the service manifest from the read-only boot bundle,
   which is part of the kernel image, validates restricted static ELF
   images and asks the kernel to create domains, pages, mappings and
   threads. Starting the file service from the read-only bundle avoids a
   loader that needs a file service that does not exist yet.
4. Services receive their endpoints and complete a version handshake and a
   readiness protocol. A service that does not become ready fails with a
   timeout and a diagnostic, so services never wait for each other in a
   cycle.
5. The root grants each domain the least authority it needs. Later worker
   processes are created through the process manager, which also starts the
   process service of each POSIX environment; the processes of that
   environment are created through its process service.

A cold boot reaches the resident root without reading the serial port. The
first service topology is the root with a file, a block, a stream and a UART
service.

The boot bundle holds the boot-bundle directory with its capacity record
and the images of the root, the services and the workers. It is a
read-only segment of the kernel image, page aligned and holding nothing
else, and neither board delivers it in another way: on QEMU virt it is a
read-only segment of the ELF image that QEMU's loader loads, and on the
Pi 5 the firmware loads it with the image. The kernel finds the bundle from
the symbols of its link and gives its place and size to the root in the
boot information; the root reads the images from there, so the kernel image
binds them and the root compares no digest at run time. The bundle shares
no page with kernel data, and the kernel maps it for itself read-only and
never executable. Each board has one image file, and the digest of the
image covers the bundle and its workers. The build checks the size of the
bundle and the number of its entries against limits of the boot
configuration, and the image with its bundle has to fit the load layout of
the board.

Boot facts that the prototype established and that the design accounts for:

- The Pi 5 firmware enters at EL2 with the MMU off. The boot protocol that
  it follows allows the instruction cache to be on, so the entry checks both
  caches; the prototype found them off. UART10 must keep the divisor that
  the firmware set.
- The BCM2712 uses a GIC-400, not a GICv3. Group 1 routing of INTID 30 can
  only be configured by the firmware.
- The device tree that the Pi 5 firmware ships has 334 properties in its
  symbol node and property names of up to 32 characters. Its reservation for
  the Linux contiguous memory allocator is dynamic, a size and an allowed
  range rather than an address; the kernel checks and records it but does
  not treat it as a reserved range. The memory node of the device tree that
  Raspberry Pi ships is a placeholder of 640 MiB that the firmware replaces.
  On the 8 GB model the firmware describes three banks with a hole of 4 MiB
  below 1 GiB, as the prototype measured; the banks of the 1, 2, 4 and 16 GB
  models are inferred from that measurement. Using all of the RAM needs
  block mappings and a kernel direct map
  ([physical memory ranges](domains/boot-platform/README.md#physical-memory-ranges)).
- PSCI uses SMC on the Pi 5 and HVC on QEMU virt. The Pi 5 CPU affinities are
  `0`, `0x100`, `0x200` and `0x300`.

The firmware coherence convention is a trusted item. Before it enters the
kernel, the firmware writes the image, the device tree and any other file
that it loads for the kernel to the point of coherency and leaves no line
of these ranges dirty in a cache. Afterwards nothing writes memory except
the CPUs, the DMA of trusted drivers ([devices and DMA](#devices-and-dma)),
the firmware when it answers a mailbox request in the buffer of that
request, and the firmware in its reserved memory. A scan-out that the
firmware leaves running reads only memory that the device tree reserves or
leaves out of its memory nodes, until the display driver stops it or takes
it over; other memory that it may read stays quarantined. Before it turns
the caches on, the entry code invalidates by address the data cache lines
from the start of the image to the end of the boot bundle, which is the
whole image, and then the instruction cache of its CPU; it relies on no
other cache state that the firmware leaves. The kernel cannot check the
convention at run time: tests with the caches on check it on the board for
each firmware version, and again after every firmware update.

On the Pi 5 the configuration of the firmware loads the image at `0x80000`
and the device tree at `0x1000_0000`, with 2 MiB of room for the device
tree, and loads no initial RAM disk; the kernel takes the address of the
device tree from `x0` and does not assume it. The image with its boot
bundle may take up to 255.5 MiB, from `0x80000` up to the device tree, on
every RAM size of the board. The build refuses an image that would reach
the device tree, and the part of that range that the image leaves free
stays usable RAM. The reserved memory of the firmware lies below the image
and, on the 8 GB model, in the hole below 1 GiB, and the dynamic
reservation does not constrain this layout. On every model the image, its
boot bundle and the device tree lie in the first bank, outside the kernel
direct map. The layout is not yet confirmed on the board: cold boots with
an image of the largest size are to confirm it.

The rules on the boot bundle and the load layout leave the fields of the
boot information and of the boot-bundle directory to the contracts of the
components below [subject domains](domains/README.md), and they do not
state the values of the limits that the boot configuration sets on the
bundle.

## Kernel objects and capabilities

At first the kernel provides the eight object kinds of the table, and EL0
holds every kind except VM regions through capabilities. The creation right
is a right on a process, and an object that a process creates is charged to
that process; a thread is created and charged together with its process.
Replies and the device directory, which the kernel creates, are charged to
no process, and the pages committed in a VM region count against the commit
limit of its process. Where this page does not fix them, the layouts and
widths of fields and the error codes with their values are left to the
contracts of the components below [subject domains](domains/README.md).

| Kind | Contents | Created by |
| --- | --- | --- |
| Process | The root of an address space, a capability table, a quota record and a lifetime state; its rights include control and observation of the process and the creation right | The kernel at boot for the root, afterwards a holder of the creation right |
| Thread | The saved user context, the scheduling state, and the wait and reply records embedded in it | Together with its process; a process has one thread at first |
| Endpoint | The queues of `call`, `receive` and `reply` | A holder of the creation right |
| Reply | A one-shot reply right with a generation | The kernel when a call is received, in the reply record of the calling thread |
| Notification | A coalescing notification word | A holder of the creation right |
| VM region | A range of the caller's own address space with the private anonymous object behind it; no capability to it is issued | `reserve` |
| Device directory | The devices that the kernel exposes, at first the PL011 and the VirtIO-mmio slots in use on QEMU virt and UART10 on the Pi 5 | The kernel at boot; only the root holds it |
| Device grant | An MMIO window and an IRQ binding | The root, through its capability to the device directory |

Capability table entries, the wait records and wait-set registrations
embedded in threads, ASID records, per-CPU records and the progress of
revocation and destruction are kernel records, not objects, even where they
carry a generation or progress; at first a wait set is not an
object that can be created. A kind added later gets a pool and a quota item
of its own, and identities keep their structure. Processes, threads and jobs
are distinct identities: a job, EL0 work with its input version and result,
is a service-level object, and running one thread per process at first is a
limit of the implementation that does not merge processes and threads. The
threads of one process form its POSIX thread group. Process IDs, process
groups and sessions are records of a process service, not kernel identities,
and a job of POSIX job control, a process group of a session, is not a job
of the platform ([processes](#processes-posix-and-linux-compatibility)).

- **Object table.** Each kind has a pool of fixed size that the kernel carves
  out of memory once at boot. No object memory is allocated after that, and
  a full pool does not borrow the slots of another kind. The capability table
  and the VM region table of each process have a fixed size.
- **Capacities.** A typed capacity record in the boot-bundle directory sets
  the capacity of each pool, the capability slots and VM regions of each
  process, the control reserves and the limits of VM and loading. Without
  the record the kernel uses the defaults of the board, which provide at
  least 64 processes and 256 threads, and a commit limit of at least 1 MiB
  for each process. The kernel validates the record with the directory, once
  and as untrusted input, before it carves out the pools, and the record is
  read-only afterwards. Every capacity is at least 1 and fits the width of a
  slot number, there are no more processes than ASIDs and at least as many
  threads as processes, each control reserve fits its pool, and the pools,
  capability tables, per-CPU stacks and write-set buffers fit into the
  memory left after the kernel image, the boot bundle and the page tables. A
  record that fails a check stops the boot with a fixed error; the kernel
  does not fall back to the defaults.
- **Capability tables and handles.** Each process has a capability table. A
  handle is a 64-bit value made of a slot number of the caller's table and
  the generation of that slot. The value 0 is never a valid handle, and the
  rights live in the table entry, not in the handle. An entry records the
  type, the rights, the object reference and the derivation links, and an
  entry for an endpoint also records the sender badge. A lookup checks type,
  rights, slot generation and liveness; a lookup that fails returns a fixed
  error and changes no state. Copying or delegating a capability can only
  reduce its rights.
- **Generations.** Inside the kernel, objects refer to each other by pool,
  slot and generation; pools are fixed at boot, and their numbers are never
  reused. Every slot of a pool or of a capability table has a generation
  that increases by one each time the slot is freed. A slot whose generation
  reaches its maximum retires and is not allocated again before the next
  boot. Generations never wrap, so a stale handle or reference never matches
  again. The generations in internal references are 64 bits wide; how a
  handle divides its 64 bits between slot number and generation is left to
  the contracts. Retired slots are counted apart: free, allocated and
  retired slots add up to the capacity. ASIDs are not object identities and
  are not covered by this rule.
- **Dangling references.** A capability in EL0 goes stale lazily. Its entry
  can outlive the object, every lookup compares generations, and a stale
  entry keeps its slot until its holder closes it. Waits and queue links
  inside the kernel are completed or removed when their object is destroyed,
  and each waiter receives an explicit reason. Capabilities are counted per
  pool, slot and generation, so the last capability of an object is the last
  one of its current generation. No reference dangles: its generation is at
  most the current generation of its slot, and where the two are equal, the
  slot holds a live object of the expected type.
- **Quotas.** The calling domain of an operation is the process of the
  calling thread, and every object that a process creates records that
  process as its owner. The quota record of a process holds a limit and a
  usage for child processes, endpoints, notifications, capability slots,
  committed VM pages, private pages of loaded images and page-table pages.
  Creation checks the quota and a free slot before it writes anything and
  takes both in one write set. Ordinary creation never uses the control
  reserve of a pool, which serves only the root and the stop,
  fault-notification and cleanup paths. The limits of a child are carved out
  of what its parent has left and return to the parent when the child is
  reaped. Endpoints and notifications are freed when the last capability of
  their current generation is deleted, processes and threads when they are
  reaped. When an owner is destroyed, its objects other than processes are
  destroyed in bounded steps, and then its child processes, as process
  lifetime below states. The usages of different calling domains never
  overlap and add up to what is allocated, also while processes are
  destroyed: a parent is reaped only after its children, so their limits
  return to it before its own limits return to its owner, and no ownership
  or quota is transferred to another owner.
- **Transactions.** An entry first makes all its checks and determines its
  write set, and it writes no state while it checks. The write set holds the
  object slots, capability entries, quota records and queue links that the
  entry changes, each slot once, and the contract of the entry lists it. The
  entry then copies the write set into the write-set buffer of its CPU,
  changes the copies and writes them back. The write-back stores distinct
  slots, in any order, and cannot fail; an entry that changes a single slot
  and has no failure point may write in place. After the checks, only the
  capacity and quota failures that the contract lists and the fault-injection
  points of test builds can occur; a failure discards the buffer and leaves
  the state as it was. No operation copies the whole kernel state.
- **Revocation.** `close` drops one reference; `revoke` withdraws a grant and
  everything derived from it in two phases. While pending, new derivations
  and operations are refused and affected execution is paused; mappings are
  then removed in bounded batches, TLB invalidation and CPU references are
  drained, and only then is revocation complete. Memory reached by DMA that
  has not drained stays pending or quarantined.
- **Process lifetime.** A process moves through alive, dying, dead and
  reaped, and its exit reason is exited, killed or faulted. A dying process
  destroys its objects other than processes and then its child processes,
  children before their parents and siblings in the order in which they were
  created, as cascading revocation walks its tree; each step stays within
  its bound and stores its progress in the dying process, which reaps its
  children itself. A process becomes dead only once its objects other than
  processes are destroyed and its children reaped, and only its owner, which
  holds the control right, reaps it after that; its exit reason and exit
  code stay readable until it is reaped. A process that is destroyed because
  its owner is destroyed exits as killed; when its own exit and the
  destruction of its owner compete, the first to arrive decides
  ([internal choices](security.md#internal-choices)). Reclaiming a thread
  frees its context and its wait records, and happens only after the thread
  runs on no CPU.

Service-level objects, such as files, jobs and surfaces, are validated by the
service with its instance generation and session authority. A service ID is
never a kernel capability. The kernel gives each service an identity of its
peer that a request body cannot forge.

## System calls and the ABI

Every native system call enters through one SVC dispatch table. A call
passes the major ABI version that it was built for in `x7` and the operation
number in `x8`. The operations are listed in a committed inventory with
their operation number, the major version that added them, their arguments
and their error codes, and the dispatch table is generated from the
inventory, keyed by major version and operation number. EL0 creates
endpoints, notifications and child processes only by presenting a
capability that authorizes it. The system calls of a Linux program never
enter this table: the kernel hands each of them to the compatibility runtime
in the calling process as an upcall
([Linux programs](#processes-posix-and-linux-compatibility)).

- **Operation numbers.** The low 16 bits of `x8` hold the operation number,
  and the bits above them are zero. Number 0 is not used. Production
  operations take numbers from `0x0001` to `0x7FFF` and diagnostic
  operations from `0x8000` to `0xFFFF`; the inventory assigns the numbers
  within each range. The dispatch table of the default image has no entry in
  the diagnostic range, and diagnostic operations are registered only in
  test builds. A stable ABI contract freezes only the production range.
- **Versions.** The first kernel ABI is version 1, the only version that the
  kernel accepts at first; version 0, the experimental ABI of the prototype
  tree, is rejected. A new operation takes a new number and leaves the
  version unchanged. Arguments are extended by flags that must be zero and
  by structures that carry their size, so there is no minor version and
  nothing to negotiate; a query of features and limits, once one is added,
  is an ordinary production operation. An incompatible change takes a new
  number and deprecates the old one, or raises the major version. The kernel
  serves the current major version and the one before it.
- **Rejection.** A call with an unsupported version in `x7` returns
  `UNSUPPORTED_VERSION`. A call whose `x8` has no entry in the dispatch table
  of the running image, which includes every diagnostic number in the
  default image and every value beyond 16 bits, returns
  `UNSUPPORTED_OPERATION`. Both checks come before the checks of reserved
  registers, arguments and rights; the remaining checks follow one fixed
  order that every contract applies to its operations, and a rejected call
  changes no state.
- **Deprecation.** Operation numbers are never reused. A deprecated
  operation keeps its meaning within its major version and is removed only
  with a new major version, after which its number returns
  `UNSUPPORTED_OPERATION`. A major version is retired only at a release
  boundary of the stable ABI, after which it returns `UNSUPPORTED_VERSION`.
- **SVC immediate.** Native calls use `svc #0`, and in native dispatch any
  other immediate returns `UNSUPPORTED_OPERATION` without terminating the
  caller. Exit and yield are production operations with numbers of their
  own, not SVC immediates. Loading fixes an ABI attribute, native or Linux,
  for each process, and for a Linux process one code range, the code of its
  compatibility runtime, which lies in an RX segment that the kernel has
  validated. In a native process every SVC takes native dispatch. In a
  Linux process an SVC whose exception return address in `ELR_EL1` lies
  outside that range takes the Linux path whatever its immediate, as Linux
  dispatches by exception class and ignores the immediate; inside the range
  the SVC takes native dispatch. A Linux program that jumps into the range
  makes native calls with the authority of its own process only. Dispatch
  compares the attribute, the range and the immediate, and the attribute
  and the range do not change after loading
  ([Linux programs](#processes-posix-and-linux-compatibility)).

Every entry into EL1 follows one execution model:

- **Kernel stacks.** Each CPU has one kernel stack with a guard and one
  emergency stack, and threads own no kernel stack. An entry from EL0, by a
  system call, an exception or an interrupt, starts at the top of the kernel
  stack of its CPU and saves the user context in the current thread.
- **Run to completion.** An entry runs to completion and releases every lock
  and every borrowed object before it returns to EL0, so no kernel frame
  survives a switch to another thread. The return to EL0 restores a user
  context and executes `ERET`: it is a one-way exit, not a return to a
  kernel caller. The prototype tree entered EL0 by a call that returned into
  the kernel; that entry code is rewritten for the one-way exit, not ported
  as it is.
- **Interrupts and preemption.** EL1 runs with IRQs masked and handles
  interrupts and scheduling only before it returns to EL0 and at the
  explicit preemption points of long operations. A synchronous exception in
  EL1 is fatal unless it is a fault at a registered user-copy point, which
  makes its call fail or execute again. At first no user-copy point is
  registered, so every synchronous exception in EL1 is fatal. The kernel is
  not fully preemptible: an interrupt waits at most for the longest step
  between two preemption points.
- **Blocking.** A call that blocks writes, after its checks, a wait record
  in its thread: the pool, slot and generation of the object that it waits
  on, the generation of the wait, its deadline and the registers that
  completion writes back. The thread blocks and the entry returns. The
  sender, signaller, timer or forced kill that completes the wait writes the
  result into the saved context of the thread, in its own transaction, and
  makes the thread ready. Only the first completion takes effect, and a
  forced kill, a timeout or a thread interrupt cancels a wait by completing
  its record; an asynchronous upcall to a blocked thread also completes its
  wait, with an interrupted result, before it is delivered
  ([upcalls](#futexes-and-upcalls)). `receive`, a `call` that waits for its
  reply, waits on notifications, wait sets and futexes, and sleeps block
  this way.
- **Long operations.** Cascading revocation, process destruction and the
  release of a VM object have preemption points that their contracts state.
  When an interrupt is pending at such a point, the operation stores its
  progress in the object and returns; the interrupted call is dispatched
  again from the saved user registers, repeats its checks and continues from
  the stored progress. The progress belongs to the object: another operation
  of the same kind that passes its checks continues the same work, other
  operations on the object are refused while the work is pending, and a
  caller that finds the work done returns the result that its contract
  states.
- **User memory.** The kernel reaches user buffers only through checked
  user-copy paths. It reads user memory only while it checks a call, and in
  the execution phase it writes only user pages that it has found present. A
  call that meets an uncommitted page, or a page that a pager has not
  supplied, returns the fixed error that its contract states, or registers a
  wait for the page and is executed again from the start once the page is
  present.

The contract of each blocking call states whether it completes by
continuation, its completer writing the result into the saved context, or
by execution again from the saved user registers. Sequential proofs assume
this model on one CPU: no nested interrupts in EL1, entries that run to
completion and scheduling only at the points above
([formal verification](formal-verification.md)).

## IPC, notifications and waits

- **Calls.** `call`, `receive` and `reply` exchange short messages. When a
  call is received, the kernel creates a one-shot reply right with a
  generation. Reply, timeout, cancellation, revocation and peer death
  compete, and exactly one of them completes the wait; a thread interrupt
  counts as a cancellation
  ([internal choices](security.md#internal-choices)).
- **Budget lending.** A synchronous call lends the caller's remaining budget
  to the server within an authorized priority ceiling. A budget has at most
  one active holder and is never duplicated. When a call ends, the loan is
  withdrawn from the server and the downstream chain first, and the caller is
  woken after that settlement.
- **Notifications.** A notification is a coalescing signal to check a queue;
  messages are counted by the queue state.
- **Timeouts and wait sets.** Waits have deadlines and can be grouped in wait
  sets. A timeout means the caller stopped waiting; it does not mean that the
  server did not act. A futex key can be a source of a wait set; when the
  region of the key is released, the source is removed and the wait set
  reports a fixed reason ([futex keys](#futexes-and-upcalls)).
- **Capability transfer.** Copy and move are distinct. Receive slots are
  reserved before sending, and message data and capabilities become visible
  together at the commit point; failure before that restores a moved source.

Large data goes through pre-authorized shared buffers. Shared indices and
descriptors are read into a private snapshot and validated before use.

## Scheduling and budgets

Threads run from bounded priority queues with round robin within a priority,
per-domain CPU budgets with replenishment periods, and preemption by the
timer. Admission first sets aside control capacity and the kernel and IRQ
overhead, so guaranteed budgets never exceed the CPU. A child domain's budget
is cut from its parent's. Background and control classes keep a minimum
share. The run queues and budget records are per-CPU data structures from
the start, even while the system schedules one CPU.

## Address spaces and VM objects

Page allocation, page tables, ASID allocation and reuse, mapping changes and
code publication each have their own invariants. W^X holds for every alias,
and each VM object counts its writable and executable mappings to keep it.
Code written at run time is published with the needed instruction-cache
maintenance before it becomes executable. Unmapping a page does not make it
reusable: reuse waits for TLB invalidation, CPU references and DMA to finish.

The kernel provides VM objects, address-space regions and a pager port
through which EL0 pagers supply pages. A VM object is memory that can be
mapped into several address spaces, and a region is a range that `reserve`
establishes in an address space; the regions of one address space never
overlap. An anonymous object takes zero-filled pages on `commit`, and
`decommit` returns the pages and keeps the range. A copy-on-write object is
a child object whose chain depth and work per step are bounded, and a shared
object is one object mapped into several address spaces. A file-backed
object receives its pages from an EL0 pager through the pager port; when the
pager fails or dies, a thread that accesses such a page through a mapping
takes a page fault that the kernel cannot resolve. The fault goes to the
fault handler of the thread when one is registered, and otherwise
terminates the process as faulted ([upcalls](#futexes-and-upcalls)).

The first VM objects are the private anonymous objects of a single thread,
with `reserve`, `commit`, `decommit`, `mprotect` and `release`. `reserve`
acts only on the caller's own address space, and the commit limit of each
process comes from the capacity record. `release` works in two phases: once
it is pending, new accesses are refused at once, and it reports completion
only after unmapping, TLB invalidation and the draining of references.
`mprotect` cannot make these objects executable. Copy-on-write, shared and
file-backed objects and EL0 pagers are not provided at first.

Some mappings are not VM objects, and VM operations do not apply to them:
the RX, RO and boot-information pages of the boot bundle, the RW segments
and stack pages that loading creates, and the MMIO pages of a device grant.
The kernel installs them directly, from an entry of the boot-bundle
directory, from a loading request that it has validated again or from a
device grant, and records them in the address space. RW segments and stack
pages are charged to the quota of their process. The fixed DMA region that
EL1 holds is never mapped into EL0 and is not a VM object.

The pages of a VM object return to the allocator, and their quota to the
owner, only after its `release` has completed; the pages of a shared object
only after its last mapping and reference, DMA included, are confirmed to
have ended. A timeout is never taken as that confirmation.

The execute right is a right of a VM object and comes with the full VM
object model: at first no VM object carries it, and executable pages come
only from the boot bundle. Mapping a VM object executable requires that
right. Which processes may add the right, and how it is withdrawn, belong to
the [integrity policy](security.md#integrity-policy) for `exec`.

## Processes, POSIX and Linux compatibility

The kernel provides processes and threads. POSIX processes with their
relations and state, and the compatibility of Linux programs, are built on
them in EL0: by a process service for each POSIX environment, by the native
C library, a port of the GNU C Library (glibc), in each process, and for a
Linux program by a compatibility runtime in its process.

- **Environments.** A POSIX environment is an interactive shell session, or
  the worker environment of a job that hosts POSIX processes. The process
  manager starts one process service for each environment, and the service
  creates every POSIX process of the environment with its creation right. It
  is the kernel owner of these processes, their limits are carved out of
  what it has left, and a POSIX parent holds no kernel capability to its
  children. The processes of an environment trust its process service for
  their process relations, as clients trust a service for the semantics of
  that service ([threat model](security.md#threat-model)); the process
  service is not part of the trusted base.
- **Identities.** The thread group of a POSIX process is the set of threads
  of one kernel process, and its ID is the process ID. Process groups and
  sessions are records of the process service: a session holds process
  groups, and a process group holds processes. The pseudo-terminal service
  binds a controlling terminal to a session. A job of POSIX job control is a
  process group of a session, which the process service and the
  pseudo-terminal service move between foreground and background. A job of
  the platform is a service-level object, distinct from POSIX jobs,
  processes and threads, and the worker of such a job can host a POSIX
  environment.
- **Process IDs.** Process IDs, parent relations, exit statuses and
  resource limits are records of the process service and mean something
  only within its environment. A process learns its own process ID from its
  start message. The kernel assigns no global process ID and identifies
  processes to EL0 only by handles.
- **Fork.** The C library sends `fork` to the process service as a call.
  The service creates the child, asks the kernel to copy the address space
  of the caller, and writes the saved context of the calling thread, its
  floating-point state included, as the context of the only thread of the
  child. The child returns 0 from `fork`, and the parent receives the
  process ID of the child in the reply.
- **Spawn.** For `posix_spawn` the service creates the child directly: the
  EL0 loader loads its image, the kernel validates the image again, and no
  address space is copied. The file actions apply, in the order in which
  they were added, to the set of descriptors that the child receives, and
  the attributes are set before the child starts. The process service
  checks the permissions of both `fork` and `posix_spawn`.
- **Exec.** The EL0 loader loads the new image and the kernel validates it
  again; the execute right follows the exec rule of the
  [integrity policy](security.md#integrity-policy). The process ID and the
  records of the service stay as they were. The service may create a new
  process for the new image, give it the process ID and destroy the old
  process, so the kernel needs no operation that rebuilds an address space
  inside a process.
- **Orphans, zombies and waits.** An orphan is recorded in the service as a
  child of the adopting process of its environment, the implementation-defined
  system process of POSIX `_exit`; its kernel owner does not change. Once the
  service has read the exit reason and exit code of a process, it can reap the
  kernel process. A zombie is a record of the service that stays until its
  parent waits for it, and it takes no kernel process slot or quota; `waitid`
  with `WNOWAIT` reads the record and leaves it.
- **Cancellation and failure.** When a job of the platform is cancelled,
  the root or the job service destroys the process service of its
  environment, and every process of the environment is destroyed with it,
  as [process lifetime](#kernel-objects-and-capabilities) states. A failure
  of a process service likewise affects only its own environment.
- **Order.** The process service handles `fork`, `wait`, `kill` and
  `setpgid` in the order in which it receives them. The only ordering rule
  that this process model adds to the kernel is the order of a cascading
  destruction.
- **POSIX state.** The C library keeps the POSIX state of each process
  inside the process: the descriptor table, each entry a capability to a
  file, pipe, pseudo-terminal or socket session with library state such as
  an offset; the signal dispositions of the process; the signal mask and the
  pending signals of each thread; the working directory, a capability to a
  directory session; the umask and the environment variables. The C library
  allocates descriptor numbers, which are not kernel identifiers. Process
  relations and the POSIX operations across processes, `fork`, `wait`,
  `kill`, `setpgid`, `setsid` and resource limits, belong to the process
  service, and the file, pseudo-terminal and network services are ordinary
  services that every environment shares.
- **Signals.** `kill` goes to the process service, which checks the
  permission and requests an [asynchronous upcall](#futexes-and-upcalls) to
  the thread that the target process registered to receive signals. The C
  library chooses the thread that takes a signal directed to its process
  and keeps the masks and pending signals; the kernel keeps no signal
  dispositions or masks. `pthread_kill` requests an upcall to a thread of
  its own process directly, and when a child dies, the process service
  sends `SIGCHLD` to its parent. The upcall entry of the C library takes the
  pending signals, selects by the mask, writes the saved context as a
  `ucontext_t` on the stack of the thread or its `sigaltstack` and calls the
  handler; `sigreturn` returns from the upcall with the context that the
  handler may have changed.
- **Linux programs.** The EL0 loader recognizes a Linux program by the
  interpreter path and the attributes of its ELF file, and loading fixes the
  ABI attribute of its process as Linux; the Linux ABI is kept apart from
  the native one, and neither poses as the other. The loader also places a
  native compatibility runtime in a reserved range of the same address
  space, registers the code range of the runtime for
  [SVC dispatch](#system-calls-and-the-abi) and registers the runtime as the
  handler of the Linux system calls of the process.
- **Linux system calls.** The kernel delivers every Linux system call of a
  Linux process to its compatibility runtime as a synchronous upcall, and
  the call returns as an [upcall](#futexes-and-upcalls) returns. The runtime
  implements Linux semantics with native calls and services, and when it
  returns from the upcall, it writes the result into the registers of the
  caller. The kernel implements no Linux semantics and has no entry of its
  own for Linux system calls.
- **Linux on native POSIX.** The runtime maps a `clone` that creates a
  thread to native thread creation, `fork` and `vfork` to the `fork` of the
  process service, with `vfork` behaving as `fork`, and `mmap` to native VM
  operations. A Linux futex is a native futex, keyed as
  [futex keys](#futexes-and-upcalls) state, and its private flag is only a
  hint. The runtime writes Linux signal frames in EL0 in the format
  of `rt_sigframe`; `rt_sigreturn` is a Linux system call, which the runtime
  completes by returning from the upcall with the context of the frame.
  Linux processes use the native process, file and pseudo-terminal
  services.
- **Authority and failure.** The runtime holds only the authority of its
  process. A Linux program that damages its runtime affects only itself,
  and the boundary that the kernel enforces stays the process.
- **Reserved range.** The runtime occupies a reserved range of the address
  space of a Linux process. A Linux `mmap` with `MAP_FIXED` into that range
  fails and replaces no mapping, unlike on Linux.
- **Linux-only interfaces.** The native C library provides no epoll,
  eventfd, timerfd, pidfd or mount interface: it installs no `sys/epoll.h`,
  `sys/eventfd.h`, `sys/timerfd.h`, `sys/pidfd.h` or `sys/mount.h`, defines
  no `EFD_` or `TFD_` constant and none of `PIDFD_NONBLOCK`, `P_PIDFD` and
  `CLONE_NEWNS`, and a configure probe against an isolated native sysroot
  finds them missing. Native programs use `poll` and
  `waitid(P_PID, pid, WEXITED | WNOWAIT)`; the process service accepts no
  namespace flag, and its `fork` copies only native descriptors. On the
  Linux path the compatibility runtime provides the five interfaces: epoll
  on native wait sets and the readiness notifications of the file service;
  eventfd as a notification with a count word; timerfd with native waits
  that have deadlines; a pidfd as an observation handle that the process
  service issues, with `waitid(P_PIDFD)` and `pidfd_send_signal` going
  through that service; and mounts and mount namespaces through the file
  service, mapped to the authorized VFS namespace of the environment, so
  that a namespace belongs to an environment, not to a kernel process. A
  Linux `fork` also goes through the process service, and the epoll state
  and eventfd counts that a parent and its child share under Linux
  semantics live in a shared VM object.
- **Baselines.** The native POSIX layer follows POSIX.1-2024 (IEEE Std
  1003.1-2024, Issue 8) with XSI conformance. It provides the options that
  glibc 2.42 declares as supported, and the other options of Issue 8 are
  stated as not provided. The GNU extensions are the interfaces that the C and
  math libraries of glibc 2.42, libc and libm, export for AArch64 Linux, at
  the default version of each symbol, beyond POSIX and the five Linux-only
  interfaces; those that the native layer does not provide are stated as such,
  and Linux programs get them from the Linux user-space libraries. Linux
  compatibility follows the user-space API and the semantics of Linux 6.18.55
  with glibc 2.42. The shell and the base tools, which run with it in
  pipelines, redirections and job control, are all programs of bash 5.3 with
  its patches up to 020, coreutils 9.12, grep 3.12, sed 4.10, gawk 5.4.1,
  findutils 4.11.0 and diffutils 3.12, each built in its default
  configuration, with coreutils also installing `arch` and `hostname`; bash
  provides `/bin/sh`. The upstream test suites are LTP 20260930, the tests of
  glibc and the tests that bash and coreutils include.
- **Not covered here.** These rules do not state the semantics of POSIX and
  Linux signals or of each Linux system call, the priority-inheritance,
  robust and requeue operations of Linux futexes, how `/proc` and `/sys`
  are provided, copy-on-write and the copy of an address space, the
  implementation of threads, POSIX threads and TLS, what the native C
  library provides for priority-inheritance mutexes, CPU affinity and
  real-time scheduling policies, the design of the job service, or the
  operations and errors of process lifetime. Nor do they give the
  machine-readable lists of the interfaces and tests of the baselines, or
  name the network and TLS libraries and the native toolchain of the
  system. The components of the compatibility personalities, memory and
  address spaces, runtime ABI and SDK, EL0 services and storage, kernel
  objects and capabilities, and application platform services domains
  ([subject domains](domains/README.md#domains)) state them.

## Futexes and upcalls

A futex lets threads wait on a word of their memory, and an upcall lets the
kernel run a handler of a thread in EL0 with the context that it
interrupted. At first a process has one thread and the kernel provides
neither: every user fault of a thread in EL0 terminates its process as
faulted.

- **Futex keys.** The key of a futex word decides whether a wait and a wake
  name the same futex. It follows from the memory that holds the word, not
  from a flag of the operation; a private flag, also `FUTEX_PRIVATE_FLAG` of
  Linux, is only a hint.
- **Private keys.** A word in private anonymous memory, copy-on-write child
  objects included, has a private key: the address space, identified by the
  pool, slot and generation of its process; the VM region that holds the
  word, by the slot and generation of the region; and the offset of the
  word in the region.
- **Shared keys.** A word in a shared object has a shared key: the VM
  object, by its pool, slot and generation, and the offset of the word in
  the object. Every address space that maps the object reaches the same
  key.
- **Mappings that the kernel installs.** A word in a mapping that the
  kernel installs directly, a loaded RW segment, a stack page or a page of
  the boot bundle, has a key made of the address space, the record of the
  mapping in the address space and the offset of the word in the mapping.
  VM operations do not apply to these mappings, and they stay until their
  process is destroyed, so no other mapping takes their address while the
  process lives and the record carries no generation. Waits on such a key
  complete when the process is destroyed, as waits on a destroyed object
  do. A futex operation on an MMIO page of a device grant fails with a
  fixed error.
- **Unmapping.** When `release` of a region completes, every wait on a key
  of that region completes with a fixed error, by the rule that completes
  the waits on a destroyed object. The kernel completes them one by one
  along the chain of waiters on the region, in bounded steps whose progress
  it stores in the region, and such a completion competes with the other
  completions of a wait as a revocation does. A shared key lives as long as
  its object, and its waits complete when the object is destroyed.
- **Reuse of an address.** A new region at the address of a released one
  has another slot or generation, so its keys never match the old keys;
  the waits on the old keys ended when the `release` completed.
- **After fork.** The regions of the child are new entries of its own
  region table, so the private keys of a parent and its child differ and
  their private futexes never wake each other; the same holds for the
  mappings that the kernel installs in the child. A word in a shared object
  has one key in both.
- **Shared operations on private memory.** A shared operation on a word in
  private memory takes the private key, as a private operation on the word
  does. This gives the robust mutexes of the C library the shared wait and
  wake semantics that they need also when they are private to a process. A
  Linux program that mixes private and shared operations on one word uses
  one key and so sees at most spurious wake-ups, after which a caller checks
  the value again as usual.
- **Order.** A wake of n threads wakes the n waiters registered first, and
  waits whose deadlines expire in the same transition settle as timeouts
  before a wake in that transition takes effect. A forced kill, a timeout
  or a thread interrupt cancels a futex wait by completing its record
  ([internal choices](security.md#internal-choices)).
- **Storage and outputs.** A futex wait is a wait record embedded in its
  thread, with the key in place of an object, and the chains of waiters
  hang on the regions, mapping records and objects of their keys, so no
  wait allocates memory
  ([no allocation at run time](conventions/provable-subset.md#2-no-allocation-at-run-time)).
  Keys are never visible to EL0: a wait and a wake return only their result
  and the number of threads woken, and no error code carries a slot number
  or a generation. Lookup structures and capacities are left to the
  contracts.
- **Region generations.** Each slot of the VM region table of a process
  follows the rule for the [generations](#kernel-objects-and-capabilities)
  of object slots: its generation increases by one each time the slot is
  freed, a slot whose generation reaches its maximum retires until the next
  boot, generations never wrap, and free, allocated and retired slots add
  up to the capacity of the table. Region slots gain generations together
  with futexes; before that a region table has none, and `release` has no
  futex waits to complete.
- **Upcall areas.** A thread takes upcalls only through an upcall area that
  it registers: the entry of its handler, a stack for the handler and a
  fixed number of save slots, up to a limit that the capacity record sets.
  The kernel checks that these pages are committed when the area is
  registered and keeps them while it is: `decommit` and `release` of them
  fail with a fixed error. Delivery writes no other user pages.
- **Saved context.** Each delivery writes the complete user context that it
  interrupts, `x0`–`x30`, SP, PC, PSTATE, `q0`–`q31`, FPCR and FPSR, bit for
  bit into the next free save slot, in the layout of the saved user context
  of a thread. The return from an upcall reads the context back from its
  slot, checks PC, SP and PSTATE as every saved context is checked before it
  is restored, restores it and frees the slot.
- **Fault handler.** A synchronous exception of a thread in EL0 that is a
  user fault goes to that thread at the faulting instruction. The kernel
  writes the context and the cause, that is the cause class, the exception
  class bits of `ESR_EL1` and the user virtual address of `FAR_EL1`, into a
  slot and enters the handler at its registered entry and stack, with the
  cause and the number of the slot in argument registers. When the handler
  returns, the faulting instruction executes again, or execution continues
  at a PC that the handler wrote into the slot. A thread without an upcall
  area, without a free slot or with an invalid entry has no handler, and
  the fault terminates its process as faulted with a fault record. A fault
  that a handler takes leaves no fault record, and a fault of the handler
  itself goes into the next slot. A page fault that the kernel cannot
  resolve, such as an access to a page whose pager has failed, goes to the
  handler in the same way. A synchronous fault never terminates another
  process ([fault isolation](security.md#isolation)).
- **Asynchronous upcalls.** A holder of the corresponding right to a thread
  requests an asynchronous upcall, which reaches the thread when it next
  returns to EL0. When the thread is blocked, its wait record first
  completes with an interrupted result; then the kernel writes a slot and
  enters the handler. Pending requests are bits in a fixed bitmap of the
  thread, one for each kind, so repeated requests of one kind coalesce. The
  blocking call that the upcall interrupted returns the interrupted result,
  and EL0 decides whether to restart it, as the C library does for
  `SA_RESTART`; the kernel never restarts a call that an upcall
  interrupted. A request to a thread that has registered no upcall area
  fails with a fixed error, leaves the thread unchanged and sets no pending
  bit.
- **Thread interrupts.** A thread interrupt writes no slot and runs no
  handler. When the thread is blocked, its wait record completes with an
  interrupted result; when it runs, a pending bit makes its next blocking
  call return the interrupted result at once. There is no upcall return:
  the thread goes on in its own context, into which only the interrupted
  result of its blocking call is written.
- **Bounds.** The bitmap and the number of slots are fixed when the area is
  registered, so a flood of requests does not grow kernel memory. Upcalls
  nested deeper than the number of slots terminate the process as faulted
  with a fault record.
- **Order of delivery.** In one transition the synchronous exception of the
  current instruction comes first; a thread interrupt settles before
  asynchronous upcalls, and asynchronous upcalls of several kinds are
  delivered in ascending order of kind. A thread interrupt counts as a
  cancellation among the completions of a wait. Of a forced kill and a
  pending upcall, the first to arrive takes effect, and a forced kill
  discards the upcalls not yet delivered
  ([internal choices](security.md#internal-choices)).
- **Outputs.** A handler sees the cause class, the exception class bits of
  `ESR_EL1` and the user virtual address of `FAR_EL1`, never a physical
  address or a slot number or generation of the object table or a region
  table. The sender of an asynchronous upcall appears as a badge or as a
  handle of the receiver's table
  ([observable outputs](security.md#observable-outputs)).
- **Uses.** A Linux system call of a Linux process is a synchronous upcall,
  as a user fault is: it goes to the compatibility runtime that loading
  registered as its handler, and its delivery and return follow the rules
  above ([Linux system calls](#processes-posix-and-linux-compatibility)).
  POSIX signals and Linux signals ride on asynchronous upcalls, and the
  compatibility runtime writes a Linux signal frame from the saved context.
  The signal safe points and asynchronous preemption of the Go runtime use
  asynchronous upcalls. The cooperative cancellation of a job in the middle
  of an evaluation uses a thread interrupt for a blocked worker and an
  asynchronous upcall for a running engine, which checks a cancellation
  flag at its safe points.
- **Not covered here.** These rules do not state the semantics of POSIX and
  Linux signals; futex operations other than wait and wake, such as
  requeue, priority inheritance and robust lists; the capacities of futexes
  and upcalls; how they work across CPUs; the proofs of these mechanisms;
  or the operations and errors of their kernel entries. The components of
  the IPC and waits domain, which holds futex-style waits, of the multicore
  domain, of the runtime ABI and SDK and of the compatibility personalities
  ([subject domains](domains/README.md#domains)) state them in their
  contracts.

## Multicore by design

SMP and parallel applications are required. The design rules apply from the
first line of kernel code, also while the system runs one CPU.

Every piece of kernel state has one owner at a time. Its class follows from
that owner and from the way ownership moves, and the class decides the token
that an access holds:

| Class | Owner and token | Kernel state |
| --- | --- | --- |
| Per-CPU | Its CPU, which alone reaches it; another CPU asks for a change through the pending queue of that CPU, which applies it. The token is running on that CPU | The run queue; the current thread, the reschedule flag and the CPU-local continuation head; the kernel and emergency stacks; the timer deadline; the write-set buffer, empty before and after every entry; the budget ledger, except its lending and cross-CPU settlement fields |
| Per-thread | The CPU that runs the thread, the CPU whose run queue holds it while it is ready, or the object it waits on while it is blocked; the state moves with the thread | The saved context and the scheduling state; the wait records, which hold the deadline of a sleep, the reply records and the wait-set registrations |
| Per-process | A transaction that holds the token of the process, run by one of its threads or by an operation that acts on it through a capability: delegation into its table, cascading revocation, a forced kill or reaping | The capability table and its derivation links; the address space with its page tables, VM regions, anonymous objects, commit counts, and loaded and device mappings |
| Shared | No single owner: every access holds the token of the state and has a stated linearization point, and state that is read-only after boot is read without a token | The pending queues; the audit counters, one per CPU and increased only by that CPU; the quota records; the slots of the object tables, endpoint queues and notification words; process lifetime states; free-slot selection; the physical page allocator; the device directory, device grants and IRQ routing; the lending and cross-CPU settlement fields of budget ledgers; the ASID allocator and the CPU record of each address space; the capacity record and the boot-bundle directory, read-only after boot |

A handover of ownership is a publication, and the fields of a compound record
are classified one by one. A completion writes the result of a wait in a
transaction that holds the token of the object waited on. That write is the
linearization point of the single result, and the thread then goes to the
CPU chosen for it, through the pending queue of that CPU when it is another
one. A transaction takes the tokens of the state in its write set that is
not per-CPU during its checks and releases them after its write-back. The
progress of a revocation or destruction has the class of the object that
holds it. The CPU record of an address space lists the CPUs that may hold its
translations: a CPU joins it before it loads the address space and leaves it
after it has unloaded the address space and invalidated its own TLB entries.
An ASID is reused only after invalidation has reached every CPU of the record
and none of them still has the ASID loaded.

A token models ownership in the specification; it is not a per-object lock.
While one CPU runs, that CPU holds every token. Which locks provide the
tokens on several CPUs, how many there are and the order in which they are
taken are fixed before CPUs share kernel state.

The other design rules are:

- The boot CPU performs shared initialization once. Secondary CPUs have their
  own entry and boot stack and do not clear BSS again.
- Atomics, memory attributes, cache coherence and barriers form one
  publication contract. Local IRQ masking, `volatile` and `UnsafeCell` are not
  cross-CPU synchronization.
- A thread changes CPU only while it does not run, so no kernel frame moves
  with it. Migration preserves integer, TLS, FP/SIMD, address-space and
  budget state.
- Unmapping, ASID reuse and page reclamation wait until every relevant CPU has
  acknowledged invalidation and dropped its references. A timeout is never
  taken as an acknowledgement.

The [SMP design rules](conventions/smp.md) state what code does to meet them.

QEMU with one, two and four vCPUs checks function. A fixed instruction count
reproduces function only; races are tested with multi-threaded TCG and then on
the Pi 5. Four boot messages from four CPUs do not show that SMP works.

## Storage

Storage is served in EL0. Clients reach it through the file service, which
holds the namespaces and resolves paths; the one exception is the loader
under **Verification** below. Each storage back end runs in a domain of its
own: the read-only image service for the system image, and a file system
service for each writable volume. The file service reaches the back ends
through sessions of its own, apart from that loader no client holds a
capability to a back end, and the back ends reach the medium through the
block driver.

- **Read-only system image.** The system image is a read-only volume. Its
  manifest lists each file with its path, size and kind, whether it is
  executable, and the root of a SHA-256 hash tree over the 4 KiB blocks of
  the file; the manifest is stored in 4 KiB blocks with a hash tree of its
  own, whose root is the root digest of the volume. Each volume slot is a
  partition of the GPT that holds a header, the manifest with its tree, and
  the contents and trees of the files; the header decides nothing about
  acceptance. The build writes the root digest into a trusted part of the
  kernel image, so a kernel image and its volume are released and updated
  as a pair: each A/B slot of the kernel image has a volume slot of its
  own, approved and selected with it, and every read of a volume that does
  not match its kernel image fails. The system never writes the active
  volume: until the updater writes volumes on the device, a host writes the
  volume to the medium, and the updater then writes only the inactive
  volume slot.
- **Verification.** The read-only image service, in the block layer above
  the block driver, checks the manifest against the root digest from the
  kernel image, looks files up by path and checks every block that it reads
  against the hash tree of its file, also when a page is read again after
  it was evicted; a block that does not verify is never returned. It
  provides each file as a read-only memory object that carries its path,
  and it gives the execute right to the files that the manifest marks
  executable, so integrity and the execute right are both kept per file. A
  loader takes an object in one of two ways: it asks the read-only image
  service for the object by path, the one case in which a client other than
  the file service holds a session with a back end, or it receives the
  object through the file service and checks the path that the object
  carries. The contract of the loader (planned) fixes which of the two it
  uses. The file service builds the directory tree from the manifest and
  passes the objects on: it could misreport a directory listing, but it
  cannot change the contents or the path of an object. Large images are
  loaded page by page from verified blocks, and the kernel maintains the
  instruction cache before a page becomes executable, so their size is
  bound only by the limits of VM and loading in the capacity record, not by
  entry cache maintenance.
- **Installed packages.** Installed packages are stored in the same format.
  The signature of a package manifest is verified when the package is
  installed, and the roots of the hash trees of its files are recorded then.
  The read-only image service checks every read of an installed package
  against those roots and never returns a changed block, so what any client
  receives equals what was checked at installation. The file system service
  that stores the packages marks them immutable but is not trusted for it:
  if it changes or removes them, reads fail.
- **Namespaces and mounts.** Each environment has one namespace, which the
  file service records. The process manager obtains for an environment a
  directory handle to the root of its namespace, a session capability of
  the file service whose badge names the environment, and the processes of
  the environment receive only directory handles derived from it. A path is
  resolved from a directory handle and never leads out of the directory
  that the handle names, through an absolute path, `..` or a symbolic link.
  A mount binds a volume or a directory of a back end at a path of one
  namespace, and only a holder of the authority to mount in that namespace
  makes it; Linux mounts and mount namespaces map onto these mounts
  ([processes](#processes-posix-and-linux-compatibility)). A rename or a
  replacement across volumes is refused.
- **Files and quotas.** Directory hierarchy, hard and symbolic links and
  POSIX permission metadata are kept by the format of a back end and passed
  on by the file service. The file service orders the requests of its
  clients and enforces their quotas of bytes, files, handles and requests
  in flight, and a back end accounts each request to the principal that the
  file service names.
- **Writable file system.** A file system service keeps one writable volume
  in a copy-on-write format of krepi's own: directories and files are
  copy-on-write trees, and each of two superblock slots carries a
  generation that only increases and a commit identity. A write changes
  only the working view. A commit writes the new blocks, completes a write
  barrier, writes the other superblock slot with a higher generation and a
  new commit identity, and completes a second barrier; only then is it
  reported durable. `fsync` and a rename within a volume are each one
  commit and become visible atomically, and the completion of a write, its
  atomic visibility and its durability are reported apart. Recovery reads
  both superblocks and takes the newest valid one, so it reads a fixed
  number of blocks; the map of free space is saved with each commit, not
  rebuilt. The result of a commit whose reply was lost can be queried by
  its commit identity, and without enough evidence its outcome is reported
  as unknown, never assumed to be success. Quotas of bytes and files are
  kept in the metadata. A writable volume cannot be read or written
  directly on a PC.
- **SD cards.** A card is written only while its write cache is absent or
  off; a card whose write cache is on is not used for writing, and the
  cache flush of `CMD49` is not used. A write barrier is the completion of
  the transfer, with `DAT0` ready and `CMD13` reporting the transfer state
  and `READY_FOR_DATA`, and every commit takes two barriers. Large reads and
  writes go through DMA buffers ([devices and DMA](#devices-and-dma)).
- **FAT.** FAT32 remains only on the path of the prototype, for exchange
  with a host and for the boot partition. The Pi 5 firmware reads its
  configuration, the device tree and the kernel from a FAT boot partition,
  so the boot partition and the A/B slots that the firmware selects by
  partition stay FAT, and the updater writes them whole, not through a file
  system service.
- **Failure.** When the file service fails, all its sessions fail and the
  back ends keep their committed state. When a back end fails, only the
  sessions of its mounts fail, and a fault of a writable volume does not
  affect the read-only image. Once the back ends run in domains of their
  own, the file system services are the only storage services that write
  blocks: neither the file service nor the read-only image service writes
  the medium.
- **Integrity roles.** Of the storage components that code and update
  integrity rely on ([integrity policy](security.md#integrity-policy)), the
  read-only image service is the component that verifies the read-only
  system image, and also the storage component that keeps installed
  packages immutable, since it checks their contents whenever it reads
  them. The block driver is the storage path that alone writes the A/B
  slots and the approval records: they lie in partitions of their own,
  outside every writable volume, and the block driver grants writes to them
  only to the updater; it grants every range of blocks to one client only.
  No file service passes worker images from the boot bundle to the loader,
  because the root reads them from the kernel image; a file service that
  passed images to a loader would be trusted for that as well. The file
  service and the file system services are not trusted for integrity.
- **At first.** At first the file service is the only storage service. It
  serves the boot bundle as read-only files and keeps its persistent
  namespace as a whole through a session of the block service, committing
  it as a snapshot to one of two slots in the format of the prototype,
  whose CRC detects accidental damage only; until the back ends run in
  domains of their own, it holds the session of the block service that
  writes.
- **Not covered here.** These rules do not state the entries, path
  encoding and limits of the manifest, the fields and limits of the
  writable format, its points of power loss, the capacities of volumes,
  the limit of large images, the identification of SD cards and the SD host
  driver, signed packages and updates with their keys, or recovery media.
  The EL0 services and storage, devices and DMA, and security and lifecycle
  domains ([subject domains](domains/README.md#domains)) and the
  [integrity policy](security.md#integrity-policy) state them.

## Devices and DMA

A driver in EL0 that does not program DMA receives only the register
ranges and interrupts that its manifest grants, as device grants that the
root issues from the device directory; a driver that programs DMA also
holds the DMA authority of its devices and their DMA buffers. Drivers
cannot map other physical memory or configure the GIC.

On the Pi 5, PCIe and RP1 bring-up uses the independent reset controller
(the reset inside the root complex reads back `0xdeaddead`), RESCAL, the PHY
and Gen2 x4 link training, and hands EL0 a baseline with all BARs zero and
bridge windows closed. RP1 interrupts are demultiplexed by masking `INT_STAT`
with the `ENABLE` bit of each vector. The shared INTA line also carries an
Ethernet interrupt source that krepi does not own.

- **MMIO.** Every window of the device directory is aligned to 4 KiB pages.
  The kernel maps the window of a grant into the address space of the
  driver as whole pages of Device-nGnRnE memory that are not global,
  readable and writable at EL0 and never executable; EL0 never names a
  physical address, a size or memory attributes, and a futex operation on
  these pages fails with a fixed error. The driver then accesses its
  registers without the kernel. A page that holds registers of more than
  one device is granted whole to one domain, and the directory entry states
  that this domain holds the authority of each of those devices; the grant
  does not isolate them from each other. Registers that drivers of
  different domains need, such as the clocks, resets and pin multiplexing
  of RP1, are changed on request by the domain that holds their page.
- **First grants.** At first the device directory holds the PL011 on QEMU
  virt and UART10 on the Pi 5, each mapped to its driver in this way, and
  the VirtIO-mmio slots in use on QEMU virt. Those slots are the exception:
  eight of them share a page, and their registers set the addresses of the
  queues that the device reads, so at first the kernel does not map them
  into EL0, and the driver reaches their registers and its DMA only through
  the kernel, which checks each access. Once DMA buffers exist, the VirtIO
  block driver uses them as every driver that programs DMA does, and its
  slot is mapped to it; a page that would hold slots of drivers in
  different domains stays behind the kernel.
- **Interrupts.** An interrupt binding is part of a device grant and names
  one bit of a notification. A binding delivers nothing before its first
  arm. When the interrupt is taken, the kernel identifies it, records the
  sequence number of the event and the time it was taken, and sets the
  bit; the driver waits on the notification, handles the device and
  acknowledges the event with the epoch and sequence number of its binding.
  Epochs and sequence numbers never wrap. At most one event of a binding is
  pending at a time and the line stays masked until it is acknowledged, so
  a device stuck at an active level is delivered once, and edges that
  arrive while an event is pending are merged into it. The kernel masks a
  level-triggered source at the distributor before it ends the interrupt,
  so the CPU interface can take other interrupts; the driver clears the
  cause at the device before it acknowledges, and the kernel clears the
  pending state at the distributor before it unmasks the line. The
  interrupt path allocates nothing and changes only the routing record and
  one notification word. Sources that share a line, such as those of RP1
  on its shared line, each have a binding of their own, masked at their own
  enable bit, and the kernel demultiplexes them.
- **Revocation.** Revoking a grant, or the death of its holder, masks and
  drains its interrupts: a pending event is discarded and the epoch
  changes, so an acknowledgement with the old epoch and a repeated arm are
  refused, and a new holder starts with an arm after it has cleared the
  cause at the device. The kernel then removes the mappings, waits until
  the TLB invalidation has completed, and only then releases the
  references. DMA buffers are drained as below.
- **DMA buffers.** Device authority covers MMIO, interrupts, DMA buffers,
  clocks and resets, and buffers in flight. A driver that holds DMA
  authority gives its device memory only through DMA buffers, kernel
  objects of a kind of their own with a pool and a quota item, whose pages
  come from the quota of the driver and can be physically contiguous and
  aligned as the device needs. The pages stay resident and are never
  evicted or moved, and a buffer can be mapped into other processes as a
  shared VM object is. Before a buffer is given to a device it is sealed:
  while the device holds it, no mapping is added, its memory attributes do
  not change and it cannot be released, and unsealing first drains the
  device. A bus address is a type of its own, which the kernel computes
  from the physical address with the `dma-ranges` of the device tree. Only
  the driver that holds the DMA authority receives it, as part of that
  authority; no process receives the CPU physical address, and the other
  holders of mappings of the buffer receive no bus address. Where the path
  of a device is treated as not coherent, as the paths of the SD host and
  PCIe on the Pi 5 are, the driver asks the kernel to clean or invalidate
  ranges of its buffers, or creates them as Normal Non-cacheable memory;
  the VirtIO devices of QEMU virt are coherent.
- **Draining.** Unmapping memory from the CPU does not stop DMA. When a
  grant is revoked or its driver dies, its DMA buffers become pending:
  their CPU mappings are removed and their pages are not reclaimed. A
  trusted party that keeps control of the device, the restarted driver or a
  recovery component of the root, stops the device and reads back that it
  has stopped, and only once the drain is confirmed are the pages
  reclaimed. A timeout is not a confirmation: pages whose drain cannot be
  confirmed stay quarantined and are not allocated again before the next
  boot, and the device stays disabled.
- **Trusted base.** No device path has an IOMMU or an equivalent constraint
  that is verified; the IOMMUs of the BCM2712 and the inbound windows of
  PCIe are not used for isolation. Every EL0 driver that programs DMA is
  therefore part of the trusted base as a whole process, with its code, its
  data and its grants, and is trusted only to let its devices reach the DMA
  buffers that it holds; otherwise it counts as an untrusted driver. On the
  Pi 5 these are the display driver, the drivers of the USB host
  controller, the SD host and Ethernet, and the component that sets the
  inbound windows of PCIe and enables bus mastering; on QEMU virt they are
  the VirtIO block driver once it uses DMA buffers and, if QEMU virt shows
  its display through a VirtIO device, the driver of that device. Drivers
  that do not program DMA, such as those of the UARTs and GPIO, are not
  part of it. Each of these drivers is held to an executable specification
  of its own; for one that runs before that specification is complete, the
  release declaration says how far it is checked. Running a driver in EL0
  gives only partial isolation against CPU faults. At first the only DMA is
  that of the VirtIO block device on QEMU virt, through a fixed region that
  the kernel holds and never maps into EL0: the kernel checks each
  descriptor before it publishes it to the device, and the driver names no
  address.
- **Firmware mailbox.** Only the firmware mailbox service holds the grant of
  the mailbox of the Pi 5 and its interrupt, and it alone owns the buffer
  of the requests, a DMA buffer of its own whose cache it maintains before
  and after each request. Clients, such as the power and thermal services
  for frequencies and temperatures and the display driver for its clocks,
  send it requests through an endpoint. The service manifest of the root
  lists the tags of each client, and the service checks each tag with its
  arguments, such as the clocks and the ranges of frequency that a client
  may set. It refuses to every client the tags that return or take bus
  addresses of memory, those that call code at a bus address and those
  that allocate a frame buffer; the tags that change the persistent state
  of the firmware, such as its OTP memory and its boot and reboot flags,
  are listed only for the root itself. The mailbox passes only the
  bus address of the request buffer, and the firmware reads the request
  there and writes the response back, so whoever writes the mailbox
  registers can make the firmware write any memory that it names. The
  service is therefore part of the trusted base under the rule for drivers
  that program DMA, trusted only to let the firmware reach no buffer but
  those of the requests that it forwards. At first there is no mailbox
  service.
- **Display.** The display device service runs in the process of the
  display driver. It allocates every buffer that a display scans out as a
  DMA buffer, with the contiguity and memory attributes that the controller
  needs, and grants mappings of it to its holders: the kosmo display server
  and, as a second holder, a minimal recovery client of krepi that shows
  only prerendered images and status codes. A holder never supplies the
  pages that a device scans out. A holder that dies loses only its
  mappings; the buffers stay with the service, the scan-out goes on and the
  last frame stays on the display. The display driver holds the DMA
  authority of these buffers and stops the scan-out of a buffer, or moves
  it to another one, before the buffer is reclaimed. On the Pi 5 the
  registers of the HVS, the pixel valves and HDMI are mapped to the display
  driver, and a page that HDMI shares with another block is granted whole
  to it; the driver programs the scan-out addresses, and the register
  writes of each frame do not go through the kernel. Its completion and
  vertical blanking interrupts each have a binding, it sets the HDMI and
  HVS clocks of a mode through the mailbox service, and it never takes a
  scan-out buffer from the firmware. The holders only write pixels, program
  no DMA and are not part of the trusted base.
- **Not covered here.** These rules do not state the operations and errors
  of device grants, interrupt bindings and DMA buffers, how the time at
  which an interrupt was taken reaches the driver, the list of mailbox
  tags, how display and input device services pass events to their holders
  and the rest of their interfaces, the forms of the display and input
  drivers, the inbound windows, bus mastering and first interrupt
  configuration of PCIe, the management of the shared registers of RP1,
  the programming of an IOMMU, or the policy of power, frequency and
  temperature. The devices and DMA and the boot and platform domains
  ([subject domains](domains/README.md#domains)) state them, and the
  [trusted boundary](formal-verification.md#trusted-boundary) lists what a
  release declaration trusts.

## Floating-point state

EL0 uses hardware floating point; the kernel is built softfloat. Binary64
addition, subtraction, multiplication, division, square root and fused
multiply-add are the hardware's correctly rounded instructions. The kernel
creates every new process and thread with the default FPCR: round to nearest
even, FZ clear, all trap enables clear, and the FEAT_AFP bits AH, FIZ and NEP
clear. Where POSIX makes a new thread inherit the environment of its
creator, EL0 sets the inherited environment when it creates the thread: the
only thread of the child of `fork` takes the saved context of the calling
thread, FPCR and FPSR included, and the thread library sets a new POSIX
thread to the environment of its creator before the thread starts. A new
program image after `exec` starts with the default, and so does a CAS worker
thread, whose creation path sets the default. FPCR, FPSR and `q0`–`q31`
survive preemption, yield, system calls and IPC, signal delivery and return,
and migration; signals are delivered as [upcalls](#futexes-and-upcalls),
whose delivery and return save and restore these registers bit for bit. The
floating-point environment belongs to the thread, and the system never
changes the environment of a worker thread.

## Diagnostics and stacks

Fault records carry the domain, thread, service generation, PC, SP and
exception registers. A fault that a registered fault handler takes leaves no
fault record; a fault that terminates its process leaves one
([upcalls](#futexes-and-upcalls)). Frame-pointer backtraces are bounded and
check range, alignment and monotonic progress. The build reports an upper
bound of the stack used by every EL1 entry. Besides its guarded kernel
stack, each CPU has an emergency stack, so fatal diagnostics still run when
the kernel stack of that CPU is damaged or has overflowed into its guard.
IRQ and fatal-diagnostic paths do not allocate.

## Security model

The [security model](security.md) states the threat model, the security
properties with the rules for internal choices, the observable outputs and
the permitted nondeterminism that component contracts cite, and the
integrity policy for loading, `exec`, packages and updates.

## Verification boundary

Verification of the kernel is organized in layers: requirements and
security properties, an abstract state machine, refinement of the actual Rust
code, composition of modules, concurrency, and the correspondence of
architecture paths and the delivered binary. See [formal verification](formal-verification.md) for how
each layer is organized and what remains trusted.

## Open design questions

These questions are being decided and the rules they produce will be stated on
this page when they are made:

- the GUI, display and input stack with its rendering path, and the
  connections the device offers (Ethernet, Wi-Fi and Bluetooth, USB device
  mode);
- power management: battery, charging, backlight, sleep and saving before a
  low-battery shutdown.

The [SMP design rules](conventions/smp.md) and the
[provable Rust subset](conventions/provable-subset.md) are stated in the
conventions.

## Source layout

The repository holds the kernel and user-space Cargo workspaces, the proof
project, and the repository tasks and the host tooling crate, which are
Cargo workspaces of their own, each in its own directory:

| Path | Contents |
| --- | --- |
| `kernel/` | The kernel workspace: the EL1 kernel, board support, the ABI crate and the operation inventory; the input of proof extraction. Its root package is the provable core `krepi-kernel` (planned), with its sources in `kernel/src/`. It holds the ABI crate `kernel/abi` (`krepi-abi`), which defines no interface yet, the architecture crate `kernel/arch` (`krepi-arch`) and one crate per board below `kernel/boards/`: the QEMU virt board crate `kernel/boards/qemu-virt` (`krepi-qemu-virt`) and the Raspberry Pi 5 board crate `kernel/boards/pi5` (planned). The [kernel workspace crates](#kernel-workspace-crates) are described below. |
| `tools/` | The host tooling crate `krepi-tools`, a Cargo workspace of its own: a bounded ELF64 reader, the JSON values of tool reports, the serial port transport, the serial capture behind `cargo xtask serial-capture`, the serial link over the standard streams of a guest's process with the process helpers it uses, the QEMU virt command with the serial capture of a guest on QEMU or behind a board's serial port, the QEMU runner behind `cargo xtask qemu` and the test image that its tests boot, the QEMU boot suite behind `cargo xtask qemu-boot`, the line matchers and record parsers of a guest's serial output, and the time values of these tools per platform |
| `user/` | The user-space workspace: the resident root, services, drivers, the SDK and workers, which are members outside `default-members`. It holds the SDK crate `user/sdk` (`krepi-sdk`). |
| `verification/` | The Lean proof project and its registries, and the definition of the proof tools: their manifest, the reviewed patches and the recipe of the image that holds them, kept beside the proof project that the tools check ([formal verification](formal-verification.md#tools)) |
| `xtask/` | The `cargo xtask` commands, a Cargo workspace of its own; it depends on the host tooling crate, which implements `cargo xtask serial-capture`, `cargo xtask qemu` and `cargo xtask qemu-boot` |

Each workspace has its own `Cargo.lock`. Neither workspace directory contains
the other or is the repository root, and `xtask` and host tool crates live
outside both. Crates of the kernel workspace use no external crate
([dependencies](../CONTRIBUTING.md#dependencies)), reach only paths inside
`kernel/` and are all members of the kernel workspace, and tracked Cargo
configuration that applies to the kernel workspace passes rustc no crate.
User-space crates reach the kernel workspace only through the ABI crate.
Every crate is licensed MIT, and both workspaces build releases with
`overflow-checks = true`. `cargo xtask check` checks these rules as
[testing](conventions/testing.md#entry-points) describes, which also names
what the check does not cover. The crates of the kernel workspace and the
modules of its core follow the rules below; the crates and modules of the
user-space workspace are described here as they land.

The kernel workspace builds for the host, where the repository checks
format, lint and test it, and for the bare-metal target
`aarch64-unknown-none-softfloat`, which `rust-toolchain.toml` installs with
the toolchain. Code that means something only on that target, such as
assembly, register accesses, MMIO and image entry points, is compiled in
whole modules under `cfg(all(target_arch = "aarch64", target_os = "none"))`;
everything else is plain code that the host tests run. The checks format
the modules of the bare-metal target and lint them for that target, but test
only the host build; `cargo xtask qemu-boot` builds them into the images
and runs those.
Images are built with Cargo in `kernel/`, or at the repository root with
`--manifest-path kernel/Cargo.toml`, and the command names the board crate
of the image with `-p`, such as `-p krepi-qemu-virt`, and a test image with
`--example`. The
`.cargo/config.toml` of the repository root gives the target its flags: a
GNU build-id note of SHA-1, the static relocation model and frame pointers.

The image build follows a rule for every Cargo command that selects
packages, such as `build`, `check`, `test`, `clippy`, `run` and `doc`, when
it acts on the kernel workspace, in `kernel/` or with
`--manifest-path kernel/Cargo.toml`: it names its packages with `-p` or
takes `--workspace`, because once the core is the root package of
`kernel/`, a command with neither acts on the core alone. `cargo fmt`, which
has no `--workspace`, takes `--all`. The one exception is the extraction of
the proof gate, which names no package and so extracts the root package
([extraction](formal-verification.md#extraction)). A unit test of
`cargo xtask check` is to check its command steps against this rule
(planned), and a test of the QEMU boot suite checks the command with which
`cargo xtask qemu-boot` builds the default image; review checks the
commands in CI, in documents and in the other `cargo xtask` commands.

### Kernel workspace crates

The kernel workspace has four kinds of crate:

- The provable core `krepi-kernel` (planned) is the root package of the
  workspace: `kernel/Cargo.toml` holds both its `[package]` and the
  `[workspace]`, its library `krepi_kernel` is in `kernel/src/` and its
  integration tests are in `kernel/tests/`. It has one module per component,
  and every module that the
  [provable Rust subset](conventions/provable-subset.md#scope) lists is one
  of them. It depends on no crate, forbids `unsafe` code, is `no_std`
  without a condition and has no `cfg` other than `#[cfg(test)]` on a
  module, so it holds no code for the bare-metal target alone; its test
  modules write `extern crate std;`.
- The architecture crate `kernel/arch` (`krepi-arch`) holds the assembly,
  the system registers, the cache and TLB primitives, the ARM interrupt
  controller and timer that the boards share, and the adapters around the
  core, such as enabling the MMU and storing into live translation tables,
  the per-CPU records with the masking of interrupts, and the entry of a
  system call that hands the kernel root to the dispatch of the core.
- Each board has one crate, `kernel/boards/<board>` named
  `krepi-<board>`, with the wiring, the platform values and the one image of
  that board.
- The ABI crate `kernel/abi` (`krepi-abi`) holds only the data of the EL0
  ABI.

These are the only dependencies allowed between them, of every kind,
normal, build and development, and for every target:

| Crate | Depends only on |
| --- | --- |
| `krepi-kernel` (planned) | No crate |
| `krepi-abi` | No crate |
| `krepi-arch` | `krepi-kernel` |
| A board crate | `krepi-arch` and `krepi-kernel` |

So no board crate depends on another board crate or on `krepi-abi`, and no
crate depends on a board crate. The core does not depend on `krepi-abi`
either: the dispatch table of the core and `krepi-abi` are each to hold
the operation numbers and error codes, and a check of `xtask` is to keep
both equal to the operation inventory (planned). The `manifests` step of
`cargo xtask check` and the proof gate are to check these edges (planned)
in what `cargo metadata` reports, by the directory of each package: the
core is `kernel/` itself, the ABI crate `kernel/abi`, the architecture
crate `kernel/arch` and a board crate a directory directly below
`kernel/boards/`. A package in any other directory fails the check.

`kernel/Cargo.toml` keeps one shape, which the `manifests` step of
`cargo xtask check` and the proof gate check in the manifest, in the
crate attributes of the root package's library and in the targets that
`cargo metadata` reports for that package
([testing](conventions/testing.md#entry-points)). It holds only these
tables and keys: `package` with `name`, `version`, `edition`, `license`,
`publish`, `description` and `rust-version`; `workspace` with `resolver`,
`members` and `package`; `lints` with `rust`; `profile` with `release`;
and `lib` with `path`, or no `lib`. It must not have:

1. a dependency table of any kind, including those by target and
   `[workspace.dependencies]`;
2. `target`;
3. `features`;
4. `patch`;
5. `replace`;
6. `bin`;
7. `example`;
8. `bench`;
9. `package.metadata`;
10. `workspace.default-members`;
11. `profile.dev`;
12. `kernel/build.rs`.

The root package has only library and test targets, read from
`cargo metadata`, so the targets that Cargo discovers by itself count as
well: `kernel/build.rs` under 12, `src/main.rs` and `src/bin/` under 6,
`examples/` under 7 and `benches/` under 8. Two items are required:
`lints.rust.unsafe_code = "forbid"`, and an unconditional `#![no_std]`
among the crate attributes of the library, which
`#![cfg_attr(..., no_std)]` does not satisfy. A `kernel/Cargo.toml` without
`[package]`, a virtual workspace, passes the check, and with `[package]`
the package is named `krepi-kernel`. Kernel targets are extracted from that
package, so the proof gate refuses a run that extracts one while the
workspace has none ([gate run](formal-verification.md#gate-run)).

| Crate | Modules |
| --- | --- |
| `kernel/` (`krepi-kernel`) (planned) | The provable core, the root package of the kernel workspace: its library in `kernel/src/`, with one module per component in the [module order](#module-order-in-the-core) below and the kernel root in `lib.rs`, and its integration tests in `kernel/tests/`. |
| `kernel/arch` (`krepi-arch`) | The AArch64 processor layer with the ARM interrupt controller and timer that the boards share: `boot`, the cold entry `_start` of an image in `boot.S`; `cache`, the cache and TLB maintenance of the executing CPU by address; `cache_range`, the cache-line walks of a range; `cpu`, the processor registers that EL1 code reads and the halt of a CPU; `exception`, the exception vectors of EL1 in `exception.S`, the frame that they save and the class of an exception; `gic`, the GICv2 driver; and `timer`, the generic timer. The boards give the addresses, interrupt IDs and timers that they use. `boot`, `cache`, `cpu`, `gic`, `timer` and the vectors are compiled only for the bare-metal target; the frame, the classes and the cache-line walks are plain code. |
| `kernel/boards/qemu-virt` (`krepi-qemu-virt`) | The QEMU virt board support, its default image and its test images. The library holds `console`, the host-testable bounded writes of the serial console with `console::polled` and `console::emitter`, `fault`, the host-testable exception record, the PL011 driver `uart`, `irq`, the wiring of the GICv2 and the virtual timer, and the addresses and platform parameters of the board. The binary `krepi-qemu-virt`, from `src/main.rs`, is the default image, with the Rust entry `kernel_main`, the CPU check and the exception dispatch; the examples in `examples/` are the test images of the QEMU boot suite; `build.rs` hands the linker `link.ld`, the layout of the images, for the bare-metal target. |

### The provable core

Items of the core are `pub(crate)` by default. Only the entries that the
architecture crate and the board crates call are `pub`, with the value
types that those entries take and return. The `pub` entries are the rows
of the entry tables of the component contracts that those crates call, and
review checks that the two agree. The constructor of a handle stays in
the module that defines the handle
([rule 6](conventions/provable-subset.md#6-compile-time-guards)). The core
defines no callback for a hardware action: an entry that changes
translation tables or other hardware state returns a write plan, which the
architecture crate carries out.

### Module order in the core

The modules of the roles that the
[provable Rust subset](conventions/provable-subset.md#scope) lists, one
module each, and the kernel root are ordered in layers. A module refers
only to modules of lower layers, never to a module of a higher layer or to
another module of its own layer. An operation whose effect spans several
modules, such as revocation, the release of a region or the destruction of
a process, is composed by a module above all of them or by its entry in
`dispatch`; each of those modules provides only the checks and the writes
of its own part. The module names are planned and differ from the names
of the modules of the other kernel crates
([porting records](conventions/porting.md#porting-records)). From the lowest
layer:

| Layer | Item (planned) | Role |
| --- | --- | --- |
| 1 | `fdt` | fdt |
| 1 | `objects` | Objects |
| 1 | `context` | Context `validate` |
| 1 | `loader` | Loader `validate` |
| 2 | `page_tables` | Page-table logic |
| 3 | `KernelRoot` in `lib.rs` | The kernel root |
| 4 | `capabilities` | Capabilities |
| 4 | `ledger` | Scheduling ledger |
| 5 | `vm` | VM |
| 5 | `waits` | Waits and notifications |
| 6 | `ipc` | IPC |
| 7 | `lifecycle` | Lifecycle state machine |
| 8 | `creation` | Creation |
| 9 | `dispatch` | ABI dispatch |

The kernel root holds the state that the entries of the core share. The
modules below it never refer to it and work on the values and the parts of
the state that their callers pass them; `fdt` and `page_tables` also run at
boot, before the root exists, and `page_tables` takes the boot memory map
from `fdt` as values. Every handler entry of a module above the root
receives the one `&mut KernelRoot`
([rule 3](conventions/provable-subset.md#3-flat-relations-and-one-kernel-root)).
The root is the one item that refers upwards: its fields hold the state of
the modules above it as well as of those below it. Review checks the order;
no mechanical check reads it.

### Splitting the core

A module leaves the core for a crate of its own only when three conditions
hold together:

1. no registered target reaches it, apart from targets that extract the
   module itself;
2. it exchanges only values with the rest of the core and touches neither
   the kernel root nor the inside of a handle;
3. a measurement gives a reason, or a consumer outside the core has to use
   the module on its own.

The measurement is the wall clock of one Charon run on `krepi-kernel`,
each value the median of three runs; a value above about 6 s, a
provisional threshold, is such a reason. A split is decided before the
next target that reaches the module is registered.
