# Subject domains

The target scope of krepi is divided into subject domains. Each domain page
is to describe the complete feature set of its domain: what every feature
does, the design background, which services and applications build on it, its
interface, what it builds on, engineering notes and how it is verified. The
[feature documents](../features/README.md) state the interface, tested
examples and status of each capability that krepi provides. Repository-wide
rules are in the [documentation](../conventions/documentation.md) and
[testing](../conventions/testing.md) conventions.

A domain page is written when the first work in its domain starts, and a
component directory, with its `requirements.md` and `contract.md`, when the
first work on that component starts; its `specification.md` and `proof.md`
are added when specification work on the component starts. The directory
names below are the names that the pages use, and the Domain column links
each page that exists.

## Domains

| Domain | Directory | Scope |
| --- | --- | --- |
| [Boot and platform](boot-platform/README.md) | `boot-platform` | Firmware handoff, EL1 entry, exception vectors, cache and TLB maintenance, device-tree parsing, physical memory ranges, QEMU virt and Pi 5 board support, interrupt controllers, PCIe and RP1 links, CPU errata, fault symbolization |
| Memory and address spaces | `memory` | Physical page ownership, page tables and the kernel direct map, ASIDs, VM objects and their kinds, user-buffer access, W^X and code publication, reclamation barriers |
| Kernel objects and capabilities | `objects-capabilities` | The object table, boot-time capacities, generations, metadata quotas, write-set transactions, process and thread lifetimes, per-process capability tables, delegation and revocation |
| IPC and waits | `ipc-waits` | Call, receive and reply, one-shot replies, capability transfer, shared buffers, notifications, timeouts, wait sets and futex-style waits |
| Scheduling and budgets | `scheduling` | Priority classes, budgets and replenishment, preemption, synchronous budget lending, reserved control capacity, admission |
| Multicore | `multicore` | Secondary CPU startup, per-CPU state, migration, cross-CPU IPC, waits and budgets, acknowledged TLB invalidation and reclamation, parallel jobs |
| Devices and DMA | `devices-dma` | Device authority for EL0 drivers, interrupt delivery protocols, DMA authorization and draining without an IOMMU, bus authority, the firmware mailbox, input, display, power and thermal devices |
| EL0 services and storage | `services-storage` | The resident root and service topology, process creation authority, the file, block, stream, UART and job services, the read-only system image, VFS, writable file systems, service recovery |
| Runtime ABI and SDK | `runtime-sdk` | System-call dispatch and the operation inventory, application entry and CRT, sysroots, Rust `std`, C and C++ libraries, threads, TLS and the floating-point environment, the Go runtime, SDK packages |
| Security and lifecycle | `security-lifecycle` | The threat model of the [security model](../security.md), integrity of loading, `exec`, packages and updates, keys, signed boot and updates, restricted use mode, release profiles and trusted-base declarations |
| Compatibility personalities | `compatibility` | Native POSIX and GNU interfaces, the shell and terminal, dynamic loading and `dlopen`, Linux system-call and binary compatibility |
| Application platform services | `application-services` | Document and job services for applications, GUI, display and input stacks, networking and TLS, CPython, Lean and Lake, desktop frameworks, host companion and data exchange |
| Cross-cutting components | `cross-cutting` | Components that several domains build on, with their requirements, contracts, specifications and proof paths |

## Shared conventions

Every subject domain follows these rules. A domain page states which apply to
its features and adds only rules of its own.

- **Authority.** An operation acts only with the authority of a capability or
  a service session that the caller holds. Rights can only be reduced when
  passed on, and no request body can forge the identity of its sender.
- **Bounded paths.** Kernel paths are bounded. IRQ and fatal-diagnostic paths
  do not allocate. Long cleanup runs in bounded batches.
- **Explicit failure.** Errors are distinct from result states. A timeout
  means that the caller stopped waiting; an operation whose effect is unknown
  reports its outcome as unknown.
- **Reclamation after acknowledgement.** Memory, objects and devices are
  reused only after every mapping, CPU reference and DMA access has been
  confirmed to end. A timeout is never taken as a confirmation.
- **Multicore by design.** Every piece of state is classified as per-CPU,
  per-thread, per-process or shared, also while the system runs one CPU, as
  the [SMP design rules](../conventions/smp.md) state; the `State fields` of
  each component's contract hold the classification.
- **One image.** Features of different domains run together in one image per
  board; no feature requires an image that excludes another.
- **Evidence by environment.** Host, QEMU and board evidence are stated
  separately, and each names its configuration.

## Out of scope

The following lie outside every domain of this repository:

- the algorithms of the computer algebra system, which belong to kalyx;
- reusable UI components and the graphical shell, which belong to kosmo;
- the electrical and mechanical design of the device;
- the internal logic of language runtimes and proof checkers, beyond their
  integration with the system.

## Component documents

A component has a directory with `requirements.md` (observable behaviour)
and `contract.md` (the rules code and tests follow), and, from the start of
its specification work, `specification.md` (the Lean specification and its
correspondence) and `proof.md` (targets, obligations and trusted items). The
[documentation conventions](../conventions/documentation.md#component-documents)
define their sections. Requirement IDs such as `IPC-R03` are never renumbered
or reused.
