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

`Process` (an address space, a capability table and resource ownership),
`Thread` (registers, user and kernel stacks, TLS, wait and scheduling state)
and `Job` (EL0 work with its input version and result) are distinct
identities. Running one thread per process at first is a limit of the
implementation and does not merge them.

- **Object table.** Kernel objects live in tables whose capacities are fixed
  by a configuration read at boot, by default at least 64 processes and 256
  threads. Every slot has a generation; a stale handle is rejected, an
  exhausted generation retires the slot, and generations never wrap. Object
  creation first reserves the caller's metadata quota.
- **Transactions.** An operation that changes several objects commits its
  write set. It does not copy the whole kernel state, and a failure leaves no
  partial change visible.
- **Capability tables.** Each process has a capability table. A lookup checks
  type, rights, slot generation and liveness. Copying or delegating a
  capability can only reduce its rights.
- **Revocation.** `close` drops one reference; `revoke` withdraws a grant and
  everything derived from it in two phases. While pending, new derivations
  and operations are refused and affected execution is paused; mappings are
  then removed in bounded batches, TLB invalidation and CPU references are
  drained, and only then is revocation complete. Memory reached by DMA that
  has not drained stays pending or quarantined.
- **Process lifetime.** A process moves through alive, dying, dead and
  reaped. A thread never frees the kernel stack it is running on.

Service-level objects, such as files, jobs and surfaces, are validated by the
service with its instance generation and session authority. A service ID is
never a kernel capability. The kernel gives each service an identity of its
peer that a request body cannot forge.

## System calls and the ABI

Every system call enters through one SVC dispatch table. The operations of ABI
v1 are listed in a committed inventory with their operation number, version,
arguments and error codes. Production and diagnostic operations have
separate numbers, and the default image registers no diagnostic operation.
EL0 creates endpoints, notifications and child processes only by presenting
a capability that authorizes it. The kernel reaches user buffers only through
checked user-copy paths.

## IPC, notifications and waits

- **Calls.** `call`, `receive` and `reply` exchange short messages. A call
  creates a one-shot reply right with a generation. Reply, timeout,
  cancellation and peer death compete, and exactly one of them completes the
  wait.
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
and code written at run time is published with the needed instruction-cache
maintenance. Unmapping a page does not make it reusable: reuse waits for TLB
invalidation, CPU references and DMA to finish.

The first VM objects serve a single thread: `reserve`, `commit`, `decommit`,
`mprotect` and `release`, with revocation reported in two phases and a commit
limit of at least 1 MiB. The VM object model that is being decided covers
anonymous, copy-on-write, shared and file-backed objects and EL0 pagers.

## Multicore by design

SMP and parallel applications are required. The design rules apply from the
first line of kernel code:

- Every piece of state is classified as per-CPU, per-thread, per-process or
  shared, and its concurrent ownership is stated.
- The boot CPU performs shared initialization once. Secondary CPUs have their
  own entry and boot stack and do not clear BSS again.
- Atomics, memory attributes, cache coherence and barriers form one
  publication contract. Local IRQ masking, `volatile` and `UnsafeCell` are not
  cross-CPU synchronization.
- Migration preserves integer, TLS, FP/SIMD, address-space and budget state.
- Unmapping, ASID reuse and page reclamation wait until every relevant CPU has
  acknowledged invalidation and dropped its references. A timeout is never
  taken as an acknowledgement.

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
stack used by every EL1 entry, and each CPU has an emergency stack that does
not depend on a damaged task stack. IRQ and fatal-diagnostic paths do not
allocate.

## Verification boundary

Verification of the kernel is organized in layers: requirements and
security properties, an abstract state machine, refinement of the actual Rust
code, composition of modules, concurrency, and the correspondence of
architecture paths and the delivered binary. See [formal verification](formal-verification.md) for how
each layer is organized and what remains trusted.

## Open design questions

These questions are being decided and the rules they produce will be stated on
this page when they are made:

- the threat model, the security properties and the integrity policy for
  loading, `exec`, packages and updates;
- the remaining details of the kernel object model, the ABI versioning
  policy and the VM object model;
- the process model, the architecture of the POSIX layer, the approach to
  Linux compatibility and the POSIX, GNU and Linux baselines;
- the storage architecture (read-only system image, VFS, writable file system
  back end) and the trust model for devices without an IOMMU;
- the GUI, display and input stack with its rendering path, and the
  connections the device offers (Ethernet, Wi-Fi and Bluetooth, USB device
  mode);
- power management: battery, charging, backlight, sleep and saving before a
  low-battery shutdown;
- the SMP design rules in detail and the provable Rust subset.

## Source layout

There is no source tree yet. The layout of crates and modules is described
here once the first code lands.
