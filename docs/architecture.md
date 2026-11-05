# Architecture

This page describes the target architecture of krepi. None of it is
implemented in this repository yet; the [feature index](features/README.md)
lists what the system provides, and it is empty. Rules that are already fixed
are stated as rules. Questions that are still open are listed under
[open design questions](#open-design-questions) and are not answered here.

## Protection domains

A protection domain is an address space with a set of authorities and a fault
boundary. It is a run-time notion: a domain is neither a Git repository, a
crate nor a job.

```text
EL0   root (supervisor and process manager)
      file service, block driver, stream service, UART service
      job service, display and input services, device drivers
      worker processes: CAS, plotting, Python, proof compile/run/check
        |  SVC, IPC, notifications, shared pages (all authorized)
EL1   kernel: threads, budgets, address spaces, capabilities, IPC, IRQs
        |
HW    CPUs, MMU, GIC, timers, platform protection
```

| Domain | Holds | When it fails |
| --- | --- | --- |
| Kernel (EL1) | Kernel objects, page tables, scheduling, GIC and timers, hardware protection operations | A kernel fault is a system fault: minimal diagnostics, then halt or controlled restart |
| Root | Initial resources, creation, termination and granting of authority, the service manifest and recovery policy | A root failure is a system failure; the root does not claim to restart itself |
| File service | Authorized namespaces, files and directories, the read-only boot bundle; the endpoint of the block service | Open file sessions fail; data held only in memory may be lost and writes are not replayed |
| Block driver | Granted MMIO, IRQ and DMA buffers | The device is stopped and in-flight operations drained before memory is reclaimed |
| Workers | Private heap and stack, an input snapshot, limited file, stream and result rights | Each non-cooperative job runs in a process that can be killed as a whole |

The kernel keeps only the mechanisms that need EL1. Drivers, file systems,
general executable loading and application policy run in EL0. The kernel does
not parse file systems or arbitrary ELF files.

## Boot and the resident root

1. The firmware hands control to the kernel entry. The kernel checks the
   exception level, memory and reserved ranges and the device tree, then
   initializes exceptions, memory, timers, interrupts and scheduling.
2. The kernel maps exactly one root task from a segment description that the
   build validated and fixed in the image, and hands it typed boot
   information and its initial capabilities. This path performs only bounded
   mapping and entry checks.
3. The root reads the service manifest from the read-only boot bundle,
   validates restricted static ELF images and asks the kernel to create
   domains, pages, mappings and threads. Starting the file service from the
   read-only bundle avoids a loader that needs a file service that does not
   exist yet.
4. Services receive their endpoints and complete a version handshake and a
   readiness protocol. A service that does not become ready fails with a
   timeout and a diagnostic, so services never wait for each other in a
   cycle.
5. The root grants each domain the least authority it needs. Later worker
   processes are created through the process manager.

A cold boot reaches the resident root without reading the serial port. The
first service topology is the root with a file, a block, a stream and a UART
service.

Boot facts that the prototype established and that the design accounts for:

- The Pi 5 firmware enters at EL2 with the MMU and caches off, loads the
  image at `0x80000` and the device tree at `0x200000`. UART10 must keep the
  divisor that the firmware set.
- The BCM2712 uses a GIC-400, not a GICv3. Group 1 routing of INTID 30 can
  only be configured by the firmware.
- The firmware device tree has 334 symbol properties, 32-character vendor
  names and a dynamic `linux,cma` reserved range. The upstream memory node is
  a 640 MiB placeholder; the 8 GiB of the board come in three banks with a
  4 MiB hole, and using all of it needs block mappings and a kernel direct
  map.
- PSCI uses SMC on the Pi 5 and HVC on QEMU virt. The Pi 5 CPU affinities are
  `0`, `0x100`, `0x200` and `0x300`.
- With caches on, the prototype's entry code invalidated only its own image
  range and relied on a firmware coherence convention that is not proved.
  That convention is a trusted item.

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
limit of the implementation that does not merge processes and threads.

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
  destroyed in bounded steps. The usages of different calling domains never
  overlap and add up to what is allocated. What happens to the children of a
  destroyed process, and what gates reaping, belong to the process model, an
  [open design question](#open-design-questions), and to the contract of
  process lifetime.
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
  reaped. Reclaiming a thread frees its context and its wait records, and
  happens only after the thread runs on no CPU.

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
capability that authorizes it.

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
- **SVC immediate.** Native calls use one SVC immediate, and any other
  immediate returns `UNSUPPORTED_OPERATION` without terminating the caller.
  Exit and yield are production operations with numbers of their own, not
  SVC immediates. Linux system calls have a dispatch table of their own.
  The native immediate is 0, as in `svc #0`, and an ABI attribute that
  loading fixes for each process decides whether its calls reach the native
  or the Linux table. Both hold until the approach to Linux compatibility,
  an [open design question](#open-design-questions), confirms or replaces
  them.

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
  forced kill or a timeout cancels a wait by completing its record.
  `receive`, a `call` that waits for its reply, waits on notifications and
  wait sets, and sleeps block this way.
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
  compete, and exactly one of them completes the wait
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
  server did not act.
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
takes a fatal page fault.

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
the integrity policy for `exec`, an
[open design question](#open-design-questions).

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

## Devices and DMA

Drivers in EL0 receive only the register ranges and interrupts that their
manifest grants. They cannot map arbitrary physical memory or configure the
GIC. The kernel identifies an interrupt, masks or completes it at the
controller as the protocol requires and notifies the driver; the driver
clears the device cause and re-enables the line through its binding.

Device authority covers MMIO, IRQs, DMA address ranges, clocks and resets, and
buffers in flight. Unmapping memory from the CPU does not stop DMA. When a
process dies, its device is stopped, drained or reset before memory is
reclaimed; when that cannot be confirmed, the memory stays quarantined and the
device disabled. Without a verified IOMMU constraint, a driver that programs
DMA is part of the trusted base; running it in EL0 gives only partial
isolation against CPU faults.

On the Pi 5, PCIe and RP1 bring-up uses the independent reset controller
(the reset inside the root complex reads back `0xdeaddead`), RESCAL, the PHY
and Gen2 x4 link training, and hands EL0 a baseline with all BARs zero and
bridge windows closed. RP1 interrupts are demultiplexed by masking `INT_STAT`
with the `ENABLE` bit of each vector. The shared INTA line also carries an
Ethernet interrupt source that krepi does not own.

## Floating-point state

EL0 uses hardware floating point; the kernel is built softfloat. Binary64
addition, subtraction, multiplication, division, square root and fused
multiply-add are the hardware's correctly rounded instructions. Every new
process and thread starts with the default FPCR: round to nearest even, FZ
clear, all trap enables clear, and the FEAT_AFP bits AH, FIZ and NEP clear.
FPCR, FPSR and `q0`–`q31` survive preemption, yield, system calls and IPC,
signal delivery and return, and migration. The floating-point environment
belongs to the thread, and the system never changes the environment of a
worker thread.

## Diagnostics and stacks

Fault records carry the domain, thread, service generation, PC, SP and
exception registers. Frame-pointer backtraces are bounded and check range,
alignment and monotonic progress. The build reports an upper bound of the
stack used by every EL1 entry. Besides its guarded kernel stack, each CPU has
an emergency stack, so fatal diagnostics still run when the kernel stack of
that CPU is damaged or has overflowed into its guard. IRQ and
fatal-diagnostic paths do not allocate.

## Security model

The [security model](security.md) states the threat model, the security
properties with the rules for internal choices and the permitted
nondeterminism that component contracts cite, and the integrity policy for
loading, `exec`, packages and updates.

## Verification boundary

Verification of the kernel is organized in layers: requirements and
security properties, an abstract state machine, refinement of the actual Rust
code, composition of modules, concurrency, and the correspondence of
architecture paths and the delivered binary. See [formal verification](formal-verification.md) for how
each layer is organized and what remains trusted.

## Open design questions

These questions are being decided and the rules they produce will be stated on
this page when they are made:

- the process model, the architecture of the POSIX layer, the approach to
  Linux compatibility and the POSIX, GNU and Linux baselines;
- the storage architecture (read-only system image, VFS, writable file system
  back end) and the trust model for devices without an IOMMU;
- the GUI, display and input stack with its rendering path, and the
  connections the device offers (Ethernet, Wi-Fi and Bluetooth, USB device
  mode);
- power management: battery, charging, backlight, sleep and saving before a
  low-battery shutdown.

The [SMP design rules](conventions/smp.md) and the
[provable Rust subset](conventions/provable-subset.md) are stated in the
conventions.

## Source layout

The repository holds two Cargo workspaces, the proof project and the
repository tasks, each in its own directory:

| Path | Contents |
| --- | --- |
| `kernel/` | The kernel workspace: the EL1 kernel, board support, the ABI crate and the operation inventory; the input of proof extraction. It holds the ABI crate `kernel/abi` (`krepi-abi`), which defines no interface yet. |
| `user/` | The user-space workspace: the resident root, services, drivers, the SDK and workers, which are members outside `default-members`. It holds the SDK crate `user/sdk` (`krepi-sdk`). |
| `verification/` | The Lean proof project and its registries ([formal verification](formal-verification.md)) |
| `xtask/` | The `cargo xtask` commands, a Cargo workspace of its own |

Each workspace has its own `Cargo.lock`. Neither workspace directory contains
the other or is the repository root, and `xtask` and host tool crates live
outside both. Crates of the kernel workspace reach only paths inside
`kernel/`: path dependencies of every kind, tracked symbolic links and the
literal paths of `include!`, `include_bytes!`, `include_str!` and `#[path]`
stay inside it. User-space crates reach the kernel workspace only through the
ABI crate. Every crate is licensed MIT, and both workspaces build releases with
`overflow-checks = true`. `cargo xtask check` enforces these rules
([testing](conventions/testing.md#entry-points)). The crates and modules inside
each workspace are described here as they land.
