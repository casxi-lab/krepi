---
features: none
---

# Creation requirements

The observable behaviour of the `creation` component of the
[kernel objects and capabilities](../README.md) domain: the creation of
endpoints, notifications and child processes with the creation right, the
staged creation of a child with the loading of its image, the initial
capabilities of a child, the quotas and the admission of every creation,
the first capabilities of new objects and the boot of the root. The rules
that its code and tests follow are in the [contract](contract.md). No
feature document covers the component, so the metadata lists none.

## Sources

- The checks of capacities and quotas before a process and its first thread
  are published together, a failed creation that consumes no slot, staging
  that owns no pages and whose commit checks the authority again, the abort
  that stays possible after a revocation, and the endpoint and notification
  pools take the rules of the prototype's object pool and spawn controller,
  which the [references](contract.md#references) of the contract list, with
  the host tests of its endpoints and notifications as the frozen
  [vectors](contract.md#legacy-test-vectors).
- The creation right on the caller's own process, the staging record of
  each process with its commit in one write set, the initial capabilities
  of a child in its fixed slots and its grants, the shares that a creator
  splits to its child, the private pages of a child from the page pool, the
  plans of a commit and the boot of the root as one entry are new, from the
  kernel's
  [objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities),
  its [execution model](../../../architecture.md#system-calls-and-the-abi)
  and its [processes](../../../architecture.md#processes-posix-and-linux-compatibility);
  the [current deviations](contract.md#current-deviations) of the contract
  list where they differ from the prototype.
- The order of errors, the choice of slots and the observable outputs
  follow the [security model](../../../security.md#internal-choices), the
  ways in which a process gains authority its
  [unforgeable authority](../../../security.md#unforgeable-authority), and
  the source of images its
  [integrity policy](../../../security.md#integrity-policy); the classes of
  state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The pools, owners, quotas and write sets are those of the
  [objects](../objects/requirements.md) component; the tables, rights,
  lookups and transfers of capabilities those of the
  [capabilities](../capabilities/requirements.md) component; the binding
  of an endpoint that of the [IPC](../../ipc-waits/ipc/requirements.md)
  component; the admission of a thread that of the
  [scheduler](../../scheduling/scheduler/requirements.md) and the
  [budget ledger](../../scheduling/budget-ledger/requirements.md); the page
  pool and the VM head those of the [VM](../../memory/vm/requirements.md)
  component; the ASIDs, the table pool, the directory and the first process
  those of the [address-space](../../memory/address-space/requirements.md)
  component; and the states of processes those of the
  [lifecycle](../lifecycle/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host, booted with the default capacity record of the board.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release
  0.1, with one of its four Cortex-A76 cores running and the default
  capacity record of the board.
- **Host.** The host tests of the module `creation` of the core (planned)
  run on the development host and in CI, with the frozen vectors and the
  tests that the [contract](contract.md#testing-obligations) adds, each
  with the capacity record, the page pool and the plans that it passes.
- One CPU. The staging records are per-process and the chains of children
  shared state under the tokens of their process slots, also while one CPU
  runs; no requirement here covers the order in which several CPUs take
  those tokens, a child that another CPU could choose before its creation
  ends, or the locks that provide the tokens.

## Requirements

### CREA-R01

**The creation right.** A process creates endpoints, notifications and child
processes only through a capability to its own process with CREATE, and
every object that it creates is owned by it and charged to it. CREATE on a
capability to another process is refused with `NotOwnProcess`, and a
capability without CREATE with `PermissionDenied`; each refusal changes
nothing. A child holds CREATE only when its creator gives it through the
mask of its fixed slot, and the creator withdraws it by a revocation of the
capability from which it was derived. The criterion: a creation through a
capability to the caller's process with CREATE succeeds and records the
caller as the owner; one through a capability to another process with CREATE
and one through a capability without CREATE are refused with their errors
and change nothing; a child without CREATE cannot create, and a child with
it creates within its shares until its creator revokes the capability that
it gave.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::create_endpoint`,
  `creation::create_notification`, `creation::spawn_begin` and
  `creation::spawn_commit` (planned).
- **Contract.** [Rights](contract.md#rights).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `endpoints-admission-2` as a host test,
  and the host tests of the errors and of the initial capabilities of the
  [contract](contract.md#testing-obligations), among them the creation
  through a capability without its right of each kind of creation. The
  operations that the creation right of a process authorizes, which
  [CAPS-R02](../capabilities/requirements.md#caps-r02) leaves to this
  component, are shown here.

### CREA-R02

**Endpoints.** `create_endpoint` creates an endpoint bound to a thread
that the caller names through a capability with CONTROL, also a thread of
another process, and puts its first capability, with SEND, RECEIVE, GRANT
and REVOKE, into the slot of the caller's table that the caller names. A
thread whose process is not alive is refused with `ProcessNotAlive`. The
creation writes nothing into the bound thread: the endpoint holds back the
reclamation of neither the thread nor its process, and it is released when
its last capability is deleted or its owner destroyed. The criterion: a
creation with a thread capability with CONTROL alone succeeds; one with
OBSERVE alone and one after the process of the thread has left Alive are
refused and change nothing; the bound thread and its process are reaped
while the endpoint lives; and the frozen vectors of endpoints hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::create_endpoint` (planned).
- **Contract.** [Endpoints](contract.md#endpoints) and
  [Capabilities of new objects](contract.md#capabilities-of-new-objects).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `endpoints-admission-1`,
  `endpoints-admission-2`, `endpoints-admission-6`, `endpoints-lifetime-1`
  and `endpoints-lifetime-2` as host tests, with `ipc-admission-7` of the
  [IPC contract](../../ipc-waits/ipc/contract.md#legacy-test-vectors), and
  the QEMU test of the creation of an endpoint from EL0 of the
  [contract](contract.md#testing-obligations), which shows the creation
  from EL0 that [IPC-R01](../../ipc-waits/ipc/requirements.md#ipc-r01)
  leaves to this component.

### CREA-R03

**Notifications.** `create_notification` creates a notification with the
word 0 and no waiter, which has no recipient, and puts its first
capability, with SIGNAL, WAIT, GRANT and REVOKE, into the slot of the
caller's table that the caller names. The state of no other process is a
check of it, and the notification is released when its last capability is
deleted or its owner destroyed. The criterion: a creation gives a
notification whose word is 0 and whose queues are empty, a creation after
another process has left Alive succeeds, and the frozen vectors of
notifications hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::create_notification` (planned).
- **Contract.** [Notifications](contract.md#notifications) and
  [Capabilities of new objects](contract.md#capabilities-of-new-objects).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `notifications-admission-1`,
  `notifications-admission-2`, `notifications-admission-6`,
  `notifications-lifetime-1` and `notifications-lifetime-2` as host tests,
  and the QEMU test of the creation of a notification from EL0 of the
  [contract](contract.md#testing-obligations).

### CREA-R04

**Staged creation of a child.** A child is created by `spawn_begin`, any
number of `spawn_segment` and at most four `spawn_grant`, and then
`spawn_commit`, each call with its arguments in registers; `spawn_abort`
discards what is staged. A process stages at most one creation at a time,
and what it stages holds no slot, page or ASID. The commit makes every
check of the staging again, among them the creation right, the slots of
the creator's table, the shares and the sources of the grants, and creates
the child and its thread in one write set, admitted and alive. The
criterion: a second `spawn_begin` with a creation staged is refused with
`Staged`, and every other call of a child without one with `NotStaged`; a
commit after the revocation of the creation right, after another creation
has used the shares, after a slot has been filled and after the revocation
of the source of a grant is refused with the error of its check and keeps
the staging; and a commit of the same staging then succeeds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::spawn_begin`, `creation::spawn_segment`,
  `creation::spawn_grant`, `creation::spawn_commit` and
  `creation::spawn_abort` (planned).
- **Contract.** [Child processes](contract.md#child-processes) and
  [Rights](contract.md#rights).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of staging and of the errors of the
  [contract](contract.md#testing-obligations). No frozen vector covers the
  calls of a child: the prototype's tests of its spawn controller are not
  vectors of this component.

### CREA-R05

**The image of a child.** A commit maps the image that its staging names,
an entry of the boot bundle of the kind Image, whose segments the loading
component has accepted: the pages of its RX segments, mapped readable and
executable, and of its R segments, mapped read-only, are pages of the boot
bundle; the pages of its RW segments are frames of the page pool that
hold the bytes of the file and zero beyond them, mapped writable; its
initial stack is zero and writable below the top of the image window,
with an unmapped guard below it; and its thread starts at the entry, in
an RX segment, with the initial context. No page of a child is writable
and executable. The criterion: an image whose segments are refused
creates no child; after the commit of an image that is accepted, every
page holds the bytes and the kind of the rules, the stack reads 0, and the
child runs its entry on QEMU virt.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::spawn_segment`, `creation::spawn_commit`
  and `creation::acknowledge` (planned).
- **Contract.** [Child processes](contract.md#child-processes).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of images of the
  [contract](contract.md#testing-obligations), one with an image that the
  loading component refuses and one with an image that it accepts, and its
  QEMU test of a child that runs its entry and reads its RW data and its
  stack, with `as-16` of the
  [address-space contract](../../memory/address-space/contract.md#legacy-test-vectors)
  for the refused layouts. The host tests show the plans and the frames;
  the QEMU test the mappings on QEMU virt.

### CREA-R06

**Initial capabilities.** A child starts with the capabilities that its
creator gives it, and no others: in slot 0 a capability to itself and in
slot 1 one to its thread, each with the rights of a mask that the creator
gives, none for the mask 0; and up to four copies of capabilities that the
creator holds with GRANT, each with at most the rights of its source and
the badge of its source, in slots that the creator names, distinct from
each other and from slots 0 and 1. Each is a descendant of the creator's
capability that it came from, and a revocation of that capability or of an
ancestor withdraws it. The kernel chooses no slot and returns no slot of
the child. The criterion: for each mask, the fixed slots hold exactly the
requested rights or are empty; four grants arrive with their rights and
badges, and a fifth is refused with `GrantsFull`; a revocation of each
source removes the child's capability; and the child obtains its start
information by calls on a granted endpoint.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::spawn_begin`, `creation::spawn_grant` and
  `creation::spawn_commit` (planned), with the constants
  `creation::SPAWN_GRANTS`, `PROCESS_SLOT` and `THREAD_SLOT` (planned).
- **Contract.** [Initial capabilities](contract.md#initial-capabilities).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of the initial capabilities of the
  [contract](contract.md#testing-obligations), and its QEMU test of a child
  that calls a granted endpoint for its start information. No frozen vector
  covers them: the prototype gave a child no capability through its
  creation.

### CREA-R07

**Quotas and admission.** A creation checks the caller's quota before the
shared capacity and before its first write. An endpoint and a notification
are charged to the caller; a child is charged, with its thread, to the
child processes of its creator, receives the five shares that its creator
splits to it from what it has left, and is charged its private pages
within its own share. The thread of a child is admitted with the class,
the ceiling and the amounts of its commit, from the creator's holdings, at
the tail of the queue of its class. A creation beyond a limit is refused
with `QuotaExceeded`, `ImageShare` or `AdmissionRejected`, and one beyond
the shared capacity with `PoolExhausted`, `Exhausted` or `OutOfPages`, in
the order of the contract. The criterion: creations at each limit succeed
and one beyond each is refused; a creation that breaks two limits gets the
error of the earlier; the limits and usages hold against an independent
model over a tree of processes; and the frozen vectors of capacity hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::create_endpoint`,
  `creation::create_notification`, `creation::spawn_begin` and
  `creation::spawn_commit` (planned).
- **Contract.** [Quotas and admission](contract.md#quotas-and-admission)
  and [Errors](contract.md#errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `endpoints-admission-3` and
  `notifications-admission-3` as host tests, with `as-12` of the
  [address-space contract](../../memory/address-space/contract.md#legacy-test-vectors),
  and the host tests of quotas and of the errors of the
  [contract](contract.md#testing-obligations), among them a creation of
  each kind whose quota is used up. The creation of objects through the ABI
  that [OBJ-R07](../objects/requirements.md#obj-r07) and the creation call
  that composes admission that
  [SCHED-R08](../../scheduling/scheduler/requirements.md#sched-r08) leave
  to this component are shown here.

### CREA-R08

**No change on failure.** Every creation makes all its checks before its
first write; a refused creation, a failure of its write phase at a
fault-injection point of a test build and a refused call of a child leave
every field of the kernel state as it was, the staging of a child
included, take no slot, ASID, table or frame and give no plan. A commit
that has passed its checks cannot fail: its mappings and copies follow its
write-back and cannot fail. The criterion: for each error of the contract,
a call that gives it leaves every field compared before and after
unchanged; for each pair of consecutive checks whose errors differ, a call
that breaks both gets the error of the earlier; a creation of each kind
that meets each fault-injection point leaves the state from before it; and
the frozen vectors of refusals hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `endpoints-admission-2`,
  `endpoints-admission-3` and `notifications-admission-3` as host tests,
  with `as-12` and `as-16` of the
  [address-space contract](../../memory/address-space/contract.md#legacy-test-vectors),
  and the host tests of the errors and of the write sets of the
  [contract](contract.md#testing-obligations), among them the failure in
  the write phase of each kind of creation.

### CREA-R09

**New objects and their identities.** A new endpoint, notification,
process or thread takes the lowest free slot of its pool, at the
generation of that slot, and a slot whose generation is exhausted is never
taken again; its first capability goes to the slot of the caller's table
that the caller names, and the result of a creation is only handles of the
caller's own table. An endpoint or a notification whose last capability is
deleted is released, its slot free at the next generation, so its pool
returns to its counts of before. The criterion: the frozen vectors of slot
reuse and of exhausted generations hold; a handle of a released object
goes stale; and three rounds of creating endpoints and notifications and
deleting their last capabilities leave the counts of the pools and the
usages as at the start.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::create_endpoint`,
  `creation::create_notification` and `creation::spawn_commit` (planned).
- **Contract.** [Capabilities of new objects](contract.md#capabilities-of-new-objects)
  and [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `endpoints-admission-3`,
  `endpoints-admission-4`, `notifications-admission-3` and
  `notifications-admission-4` as host tests, and the host test of three
  rounds of creation and release of the
  [contract](contract.md#testing-obligations).

### CREA-R10

**The boot of the root.** The boot creates the root's process and thread
once, as a control allocation of the kernel domain, with its starting
limits from the capacity record; puts its capability to itself, with
CREATE, into slot 0 and its capability to its thread into slot 1, which the
boot information names; charges the pages of its RW segments and its stack
to its item of private pages of loaded images; admits its thread in the
class control; and maps its image, its stack, the boot information and the
boot bundle. A capacity record whose table of capabilities has fewer slots
than the root's fixed slots, the two of this page and any that the
device-authority rules add (planned), stops the boot. The criterion: after
the boot, the record of the kernel domain counts the root's pair, the
root's limits and usages are those of the rules for records of several
values, its first capabilities are `0@1` and `1@1` with their rights, and a
record with one slot stops the boot with `RootSlots`; the root runs on QEMU
virt and on the 8 GB Pi 5.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `creation::boot_root` and `creation::acknowledge`
  (planned).
- **Contract.** [The boot of the root](contract.md#the-boot-of-the-root).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of the boot of the root of the
  [contract](contract.md#testing-obligations), with `cx-12` of the
  [context contract](../../boot-platform/context/contract.md#legacy-test-vectors)
  for the initial context of a thread, and the QEMU tests of the contract,
  each of which boots the root. No frozen vector covers the boot of the
  root.

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a lock
  of its own, and none has a preemption point.
- A commit maps and copies the whole image of a child in one transition,
  the longest work of the component without a preemption point, bounded by
  the pages of the image window and the private pages that the loading part
  of the capacity record allows.
- No requirement bounds the time that a creation takes.

## Scope

- One CPU. The tokens, their locks and their order on several CPUs are not
  covered.
- The creation of further threads of a process, shared memory objects and
  other ways of putting a capability into another process belong to later
  releases; a process has one thread.
- The validation of the segments of an image, the loading part of the
  capacity record and the image window belong to the
  [dispatch](../../runtime-sdk/dispatch/requirements.md) component; the
  parsing of ELF files and the start of a program at EL0 to
  the runtime of EL0.
- The destruction of a child, its reaping with the return of its limits,
  its exit, its kill and the notifications of its death belong to the
  [lifecycle](../lifecycle/requirements.md) component.
- The capability to the device directory of the root, the device grants and
  the notifications of interrupts belong to the devices and DMA domain.
- The operation numbers, the registers of arguments and results, the values
  of the classes and the numeric codes of errors of the ABI inventory are
  not covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Extractability](contract.md#extractability) states the module, its layer
  and the modules that it does not refer to, which no requirement observes.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Open obligations](contract.md#open-obligations) lists the effects across
  components that no target covers.
- [Current deviations](contract.md#current-deviations) states where the
  rules differ from the prototype, which the requirements state directly.
