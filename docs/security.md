# Security model

This page states the threat model, the security properties of the kernel,
the rules for its internal choices, its observable outputs, the
nondeterminism that its specification permits, and the integrity policy for
code and updates.

The [architecture](architecture.md) describes the system that these rules
apply to. Like that page, this one states the target design: none of it is
implemented in this repository yet.

## Threat model

**Assets.** Kernel state; authority state, including derivations,
generations and badges; the execution state of each process; the root's
initial resources, grants, service manifest and recovery policy; system code:
the kernel image, the boot bundle and, once it exists, the read-only system
image; user data, including code compiled on the device; the
authenticity of proof-checking results; CPU budgets and quotas; release
artifacts and receipts; and, once they exist, the update state, the state of
the restricted use mode and keys.

**Adversaries.**

- Untrusted EL0 programs, alone or in collusion, issue any system call with
  any arguments, including forged and stale handles, fault on purpose and
  exhaust their own quotas. They cannot enter EL1, reach memory that is not
  mapped to them or program DMA.
- Services and drivers outside the trusted base may lie about service-level
  results but cannot forge kernel identities or capabilities.
- Content, including package and update payloads and the device tree, may be
  malicious; it carries no authority.
- Once the device has networking and data exchange, adversaries on those
  paths may read, change, inject and replay traffic and offer old or
  malicious content.
- A person may rewrite the storage medium while the device is off, and the
  build and supply chain may be compromised.

**Trusted.** The kernel, the root, drivers that program DMA, the firmware
mailbox service, the firmware, the hardware, the pinned toolchain and CI,
and the components that the [integrity policy](#integrity-policy) trusts.
The proof checker is the logical trusted base of proof-checking results.

**Trust boundaries.**

- EL0 and EL1: the kernel reaches user memory only through checked user
  copies, copies before it validates, and clears registers on the return.
- Processes, which do not trust each other: the kernel mediates every
  exchange ([IPC](architecture.md#ipc-notifications-and-waits)), and no
  request body can forge the identity of its sender.
- The root and other EL0 processes: the root grants least authority.
- Services and clients: a service is trusted only for the semantics of its
  own service ([service-level
  objects](architecture.md#kernel-objects-and-capabilities)).
- Drivers and devices: that a device behaves as specified is a hardware
  assumption; a driver that does not program DMA holds only the registers
  and interrupts that its manifest grants
  ([devices](architecture.md#devices-and-dma)).
- Firmware and kernel: the firmware is trusted, including the coherence
  convention that the kernel relies on at entry
  ([boot](architecture.md#boot-and-the-resident-root)) and the services
  behind its mailbox ([devices](architecture.md#devices-and-dma)), but the
  kernel parses the device tree as untrusted input, with bounds.
- Storage: only bytes that the integrity policy verifies or authenticates are
  trusted.
- Build and device: artifacts are taken by their SHA-256 digest.
- Network and host companion: only the trust anchors in the image are
  trusted.
- A language runtime and the user code in its process: the runtime's import
  authorization holds only while the process holds no executable-memory
  capability and runs no untrusted native code. The kernel enforces the
  boundary between processes, not this one.

## Security properties

The properties are stated over the abstract state machine of the kernel. A
transition is the change of state from an entry into the kernel to the
return to EL0 or a switch to another thread; a subject is an EL0 thread with
its process; the authority of a subject is the capabilities and mappings
that it holds and the wait, loan and derivation relations between kernel
objects. Authorized changes and confinement are stated for the whole system,
and each component's specification gives its part. The kernel specification
states the properties within the limits given here, and the requirements of
the security and lifecycle [domain](domains/README.md#domains) derive from
them.

### Isolation

- **Authorized changes.** A transition that a subject starts changes the
  state of other subjects and the kernel's private state only as the
  subject's authority allows. The allowed changes are listed for each kind of
  authority, and the contracts of interrupts and timers list the changes that
  those cause.
- **Spatial isolation.** A page is mapped into a subject only through
  authority that it holds, with no more access than that authority grants.
  Every page has exactly one owner, no page is writable through one mapping
  and executable through another, and kernel memory is never mapped to EL0.
- **Fault isolation.** A synchronous fault terminates only the process of
  the faulting thread. Other subjects learn of it only from an authorized
  death notification, a query under observe authority or the result of an
  operation on that process's objects.

### Unforgeable authority

- **Confinement.** A subject gains authority only when a holder of grant
  authority passes it over a channel they share, when the subject creates an
  object with its own creation right and quota, or when, as the receiver on
  an endpoint, it gets from a `call` a one-shot reply right to the caller and
  the caller's lent budget. A policy that lists the authority each process
  may hold and is closed under these three ways stays satisfied after every
  transition that a subject outside the trusted base starts; the
  specifications of trusted components keep their grants within it.
- **Attenuation.** Derivation and transfer only reduce rights.
- **Handles.** An operation whose handle does not name a live slot of the
  caller's table with the expected generation, type and rights fails and
  changes no state.
- **Sender identity.** The badge that a receiver sees, the value set on an
  endpoint send capability when it was minted, depends only on the
  capability used to send.

### Effective revocation

After the transition that makes a revocation pending, every operation that
resolves to a capability of the revoked subtree fails, the subtree derives
nothing more and affected execution is paused. When the kernel reports the
revocation complete, the subtree holds no usable capability, no page table
holds a mapping derived from it, and every relevant CPU has acknowledged the
TLB invalidation and holds no reference. Memory that undrained DMA may reach
stays pending or quarantined; a timeout is not an acknowledgement. The
property sets no bound on the time until completion.

### Information-flow boundary

- **Determinism.** A transition is a function of its inputs: the state before
  it, the arguments of the subject that starts it, including the bytes that
  the kernel reads from that subject's memory, and the
  [permitted nondeterminism](#permitted-nondeterminism). Internal choices
  follow the rules under [internal choices](#internal-choices).
- **Output sources.** Each [observable output](#observable-outputs) that a
  transition gives a subject depends only on the subject's own state and the
  inputs of the transition, the objects that the subject may observe, the
  rules for internal choices and the permitted nondeterminism. Two declared
  global flows are exempt: scheduling, that is who runs when, and errors of
  shared capacity.
- **Internal identifiers.** Object table slots, global generations, ASIDs,
  internal tokens and queue positions are not observable outputs.

These rules are premises that a proof of confidentiality would need; they
are not a confidentiality theorem. The kernel specification states
determinism, the internal identifiers and the observable outputs, with the
permitted nondeterminism as explicit inputs; instead of a theorem of output
sources, it gives the source of every output.

### What the properties do not cover

The properties claim no confidentiality; no availability, time bound or
moment of completion; nothing about authority that flows along a legitimate
chain of grants; no secrecy of handle values; no undoing of effects that
already happened, such as delivered messages, copied data and the side
effects of a server; and nothing about the semantics, authority and
revocation of service-level objects. They hold only for code that registered
proof targets cover, and only under the assumptions that those targets and
the [trusted boundary](formal-verification.md#trusted-boundary) state;
elsewhere they are design rules that tests check. The EL0 policies for
packages, updates and grants of execution are specified for the EL0
components that apply them, not in the kernel specification. The threat
model does not cover:

- physical attacks;
- fault injection, including disturbance of DRAM that software can trigger;
- side channels: timing, including the order of scheduling and the duration
  of system calls; caches and TLBs; branch prediction and speculative
  execution; power, electromagnetic emanation, temperature and the fan;
- an offline rewrite of the storage medium, and a rewrite of the boot medium
  after a run-time compromise that persists across reboots;
- malicious or defective firmware;
- DMA without an IOMMU: the kernel quarantines the memory that DMA may reach
  but does not guarantee that the device stops accessing it;
- the toolchain and the supply chain;
- misuse of authority by the subjects that hold it, including the trusted
  base, and the correctness of the root's initial grants;
- denial of service beyond what the budget and quota rules prevent;
- hardware state that the kernel neither reads nor writes.

## Internal choices

Every internal choice of the kernel follows a fixed rule or is made by the
caller. On one CPU, transitions are totally ordered, as EL1 does not nest
interrupts; on several CPUs, the order in which they gain exclusive access to
a shared object is [ND-03](#nd-03). A transition reads the time source once,
on entry, and judges every deadline by that time ([ND-01](#nd-01)). A result
is written into its object in the transition that causes it and never
changes; a woken thread only collects it. Events are simultaneous when they
occur in one transition.

- **Requests.** Requests that contend for an object take effect in the order
  in which they enter the kernel; each completes in one transition or stores
  its progress in the object and continues from there. The first cause to
  arrive decides why a process exits.
- **Slots.** An object takes, in the range of its allocation class, the
  lowest free slot whose generation is not exhausted: the reserved tail of
  its table first for a control allocation, and the rest of the table for
  any other. An address space takes the lowest free ASID whose generation
  is not exhausted; ASID 0 is the kernel's. A capability that an operation
  creates, copies, derives or receives goes to the slot of the caller's own
  table that the caller names, and the kernel only checks that the slot is
  free; an initial capability of a child, which the creation of the child
  puts into the child's table before the child first runs, goes to a slot
  that the rules of creation fix or that its creator names, and the kernel
  likewise only checks that the slot is free.
- **Identifiers.** An identifier that the kernel assigns and returns to EL0
  depends only on the caller's own state: a handle, also one that carries a
  reply right, names a slot of the caller's own table
  ([handles](architecture.md#kernel-objects-and-capabilities)). Admission
  tokens, queue positions and global counters are never returned. The party
  that mints an endpoint send capability, the root or a service, chooses its
  badge, which the kernel stores and derivation keeps.
- **Queues.** Each priority has one FIFO run queue. A thread that becomes
  ready (woken, created, out of time slice or resumed after replenishment)
  joins the tail; a thread preempted with time slice left returns to the
  head; dispatch takes the first thread with budget at the highest non-empty
  priority. When one transition wakes several threads, those woken by
  timeouts are queued first, earliest deadline first with ties in registration
  order, and those woken by events follow in registration order. Calls
  queued on an endpoint are delivered in queue order. Of several waiters
  for one event, the first registered wins and the others keep waiting. A
  wait set holds at most the number of sources that its contract states,
  and it reports every source ready in the transition that wakes it, as
  one set in registration order.
- **Deadlines.** Expiry comes first. A wait whose deadline is not later than
  the transition time settles as a timeout before the operation of the
  transition runs; the event of that operation does not complete the wait
  and is kept as its object defines: a notification bit stays for the next
  wait, and a reply to a caller that timed out fails with a fixed error. A
  wait whose deadline is not later than the time of its admission times out
  at once, consumes no pending state and reserves nothing; a wait for a
  thread to exit is the exception and still sees an exit already published.
  Deadlines that expire together all settle as timeouts, in a loop that the
  contract bounds by the thread capacity.
- **Completion.** Reply, timeout, cancellation, revocation and peer death
  compete for a waiting call, and the first transition wins. When one
  transition brings several, the call reports the first of timeout,
  cancellation, revocation, peer closed and reply. A call that waits through
  a capability under revocation settles as revoked, with an error of its
  own, when the revocation becomes pending, and its thread is paused. Peer
  death and endpoint closure report the same peer-closed error. A
  [budget loan](architecture.md#ipc-notifications-and-waits) settles as a
  whole within one transition.
- **Exceptions.** The synchronous exception of the current instruction comes
  first. Interrupts are taken only where the
  [execution model](architecture.md#system-calls-and-the-abi) takes them.
  Each interrupt number is handled in a fixed way; the order in which the
  controller presents numbers is [ND-02](#nd-02).
- **Cascading revocation.** Revocation walks the derivation tree in
  post-order, children before parents and siblings in the order in which
  their derivations were made. Each step stays within the bound of its
  contract and stores its progress in the object.
- **Errors.** When several checks fail, the first in this order decides the
  error, and the failure changes no state: the operation number and
  version; the form of the register arguments (reserved bits, ranges,
  alignment, length overflow); handle resolution (range, empty slot,
  generation, type, liveness); rights; the range and permissions of user
  buffers, then the form of the argument structures copied in; object state,
  such as a wait in progress or a pending revocation; the caller's quota;
  shared capacity. Each contract applies this order to its operations.

## Observable outputs

An observable output is a value that an EL0 subject obtains from the kernel;
the specification of each operation lists its outputs. They are:

- the result registers of a system call, unused ones cleared or kept as the
  contract states;
- error codes, by the order of checks above;
- the state that EL0 can read architecturally after the return, which holds
  no value of the kernel or another process beyond the results and the
  thread's own values;
- changes of the subject's user memory and own mappings;
- the messages, capabilities and badges it receives, and their order;
- wait results and sets of ready sources;
- the order in which it is woken;
- readings of `CNTVCT_EL0` and `CNTFRQ_EL0`;
- for a process that it may observe: the state, exit cause, exit code and
  CPU time used, the death notification, delivered once, and fault records,
  which name processes and threads by the observer's handles;
- quota and capacity errors.

Output sources cover all of them except the order of wake-ups and the CPU
time used, which scheduling decides, and errors of shared capacity. Time
(instants, durations and where preemption happens), microarchitectural state
including performance counters, power, electromagnetic emanation,
temperature and the fan, physical addresses other than the bus addresses of
a DMA driver's own buffers, and the serial diagnostics of a fault are not
observable outputs. Neither are kernel-internal identifiers and orders: an
operation that is to return one first adds it to the outputs, with a
reviewed rule for its value. The default image traps EL0 access to the
performance monitors and the debug communications channel, alongside the
EL0 timer policy that `CNTKCTL_EL1` sets.

## Permitted nondeterminism

The kernel specification leaves open only the choices registered here. It
takes each as an explicit input, and for every value of these inputs a
transition has one result. Entries are numbered from ND-01 in steps of one,
and a number is never changed or reused. Component contracts cite an entry
by its number and link its anchor on this page, such as `#nd-01`. A contract
adds no entry: a choice that it cannot fix by a rule is raised for review,
and only a reviewed change of this register admits it.

### ND-01

**Location.** Time: the time of each transition, which decides the
admission and settlement of waits, the charging and replenishment of
budgets, and preemption; the arrival of timer interrupts; the counter values
that EL0 reads and the CPU time it is told it used. **Reason.** Time comes
from the hardware counter or an injected time source; the kernel does not
choose it.

### ND-02

**Location.** Device interrupts: when an IRQ becomes pending, and the order
in which the interrupt controller presents interrupt numbers. **Reason.**
The devices and the controller decide this; the kernel handles each
interrupt number in a fixed way.

### ND-03

**Location.** Multicore interleaving: the order in which several CPUs gain
exclusive access to the same shared object, in cross-CPU IPC, waits,
revocation and reclamation; it occurs only with more than one CPU.
**Reason.** The hardware interleaving decides this order; for each order,
the rules for internal choices fix the result.

## Integrity policy

Where the integrity or origin of bytes decides their acceptance, only two
checks count: verification, which compares a cryptographic digest with an
expected value from an already trusted source, namely a digest or root digest
bound into the image; and authentication, which checks a signature against a
public key in the image, together with rollback protection. CRC and other
non-cryptographic checksums detect accidental damage only and never decide
acceptance; CRC fields in formats taken from the prototype tree keep that
meaning. The only trust anchors are the public keys and digests in the image,
and verification on the device uses no private key.

- **Loading.** The boot bundle is part of the kernel image, and the root
  reads its images from there, so the kernel image itself binds them and
  the root compares no digest at run time. Once the read-only system image
  exists, its root digest is published with the kernel image, and the
  read-only image service of the block layer verifies every block that it
  reads against the hash tree of its file, with an expected value that
  comes from the kernel image, never from the caller of a load, so that the
  file service stays outside the trusted base
  ([storage](architecture.md#storage)); the volume is updated together with
  the kernel image, with one volume slot for each A/B slot. Loading only
  verifies: the root parses no signature and uses no key, and
  authentication covers the whole image when an update is installed.
- **Exec.** A page is mapped executable only from a memory object with the
  execute right; the kernel checks that right and W^X and parses no file or
  ELF. Objects from a verified read-only source, that is the boot bundle,
  the read-only system image and the immutable contents of installed
  packages, get the right from the component that provides them. Writable
  files, anonymous memory and code generated at run time get it only from a
  process that holds the executable-memory capability, which the supervisor
  grants per session, workspace or job and the restricted use mode
  withdraws. An execute right added this way is a derivation of that
  capability, so withdrawing the capability revokes, in two phases, the
  right and every executable mapping made with it. The worker that checks
  proofs never holds the capability. Code that runs in a session holding the
  executable-memory capability claims no integrity or origin. Scripts are
  data: a policy checkpoint that all entry points share and the import
  authorization of the runtime limit what an interpreter runs. The first
  release has neither the capability nor memory objects with the execute
  right, so executable pages come only from the boot bundle (see
  [VM objects](architecture.md#address-spaces-and-vm-objects)).
  The execute right, and the kernel specification of this check, come with
  the full VM object model.
- **Packages.** A package carries a manifest of its package ID, version, the
  digest of each file and the permissions it requests, signed with the
  publisher's key. The installer verifies the signature with a trust anchor
  in the image, checks the digest of every file and refuses a version that
  is not higher than the installed one. An update of a package needs the
  same key or a proof of its rotation, and only an authenticated system
  update rotates trust anchors or resets version records. Installed contents
  are stored as immutable files with checked digests. Withheld newer
  versions go unnoticed. Packages of language ecosystems, such as Python
  wheels and Lake dependencies, are workspace code under the exec rule; the
  ecosystem's own means, such as TLS to the package index and locked
  digests, check their origin.
- **Updates.** The trusted EL0 updater, which is the root, authenticates a
  signed update bundle when it installs it. The bundle lists the digests and
  versions of the kernel image, the boot bundle, the read-only system image
  and the firmware and EEPROM images, in the manifest format of packages, and
  the same verification component checks both. An image is approved once it
  has passed authentication and the rollback check and the updater has
  recorded its digest and version, before it is written to the inactive
  slot; firmware and EEPROM images take the same path, and each write of
  them needs its own authorization. The slot then moves through staged,
  trial and confirmed, and a failed health check returns to the confirmed
  slot. Boot selection and fallback choose only among slots with an approval
  record. Confirming a slot raises the version floor and withdraws the
  approval of the image it replaces; the root's check after boot and every
  fallback refuse an image below the floor. Only the updater writes the
  slots, the selection state and the approval records, which ordinary
  applications can neither read nor write; version records only increase,
  and the sequence numbers and generations of stage transitions never wrap.
  The firmware does not authenticate what it boots; that would need
  tamper-resistant storage for the version floor and a one-time write of the
  board's OTP memory.
- **Trusted base for integrity.** Besides the kernel and the root, code and
  update integrity rely on the verification component, which also keeps the
  approval records; the component that verifies the read-only system image;
  the storage component that keeps installed packages immutable; the storage
  path that alone writes the A/B slots and approval records; and a file
  service that passes worker images from the boot bundle to the loader, if
  one does. They are trusted for these two properties only and count as
  untrusted services otherwise. Each is held at least to an executable
  specification of its own, and the [storage rules](architecture.md#storage)
  name the storage components among them.

Packages, updates, keys and the restricted use mode come after the first
release. Until then there is no update path, and A/B logic taken from the
prototype tree only selects among images already present in the boot
directory.
