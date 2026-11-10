---
features: none
---

# Capabilities requirements

The observable behaviour of the `capabilities` component of the
[kernel objects and capabilities](../README.md) domain. The rules that its
code and tests follow are in the [contract](contract.md). No feature
document covers the component, so the metadata lists none.

## Sources

- The per-process tables, the rights bits, attenuation, the lookup that
  fails without a change, close with its outward descendants, revocation of
  the descendants of a capability, the teardown of a table and the copy and
  move of a transfer with their commit and abort take the rules of the
  prototype's capability registry and of its capability transfer, which the
  [references](contract.md#references) of the contract list, with their
  host tests as the frozen [vectors](contract.md#legacy-test-vectors).
- Handles of a slot and its generation, the creation right, badges set once,
  the derivation links with their bound of depth, revocation in two phases
  with its steps of bounded work, and the release of an endpoint or a
  notification at its last capability are new, from the kernel's
  [objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities)
  and its execution model; the
  [behaviour changes](contract.md#legacy-test-vectors) of the contract list
  where they differ from the prototype.
- The order of errors, the choice of slots and identifiers, cascading
  revocation and the observable outputs follow the
  [security model](../../../security.md#internal-choices), and the
  completion of a revocation its
  [effective revocation](../../../security.md#effective-revocation); the
  classes of state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The object references, owners, quotas and write sets that the entries use
  are those of the [objects](../objects/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2, one
  Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host, booted with the default capacity record of the board.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release 0.1,
  with one of its four Cortex-A76 cores running and the default capacity
  record of the board.
- **Host.** The host tests of the module `capabilities` of the core
  (planned) run on the development host and in CI, with the frozen vectors
  and the tests that the [contract](contract.md#testing-obligations) adds.
- One CPU: no requirement here covers secondary CPUs, the order in which
  several CPUs take the tokens of tables, the acknowledgement of a TLB
  invalidation by another CPU, or the locks that provide the tokens.

## Requirements

### CAPS-R01

**Handles.** A handle is a 64-bit value of a slot number of the caller's
own table in its low 16 bits and the generation of that slot in its high 48
bits. For each process that occupies a process slot, every slot of its
table starts at generation 1 and gains one each time its capability is
deleted, and a slot deleted at $2^{48} - 1$ retires while that process
occupies the slot, so the value 0 never names a capability, a handle that
has gone stale never names one again, and no handle depends on an earlier
process of the same slot. A handle names a slot of its holder's table only,
and the kernel returns a handle only for a capability that it puts into the
slot that the caller named. The criterion: the frozen vectors hold, among
them a slot reused at a new generation, a slot retired at the largest
generation and a process slot that a new process occupies.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::new`, `Tables::lookup`, `Tables::install` and
  `Tables::close` (planned).
- **Contract.** [Handles](contract.md#handles).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-admission-2`, `caps-admission-7`,
  `caps-lifetime-5` and `caps-endpoint-lifetime-5` as host tests, and the
  host tests of handles of the
  [contract](contract.md#testing-obligations). They show the rule on the
  host with generations set by the tests; reaching $2^{48} - 1$ by deletions
  is not run.

### CAPS-R02

**Rights.** Each of the seven kinds of object that EL0 holds has its set of
rights, and the rights of a process include OBSERVE, CONTROL and the
creation right. CONTROL on a process authorizes its forced kill and its
reaping by its owner; OBSERVE authorizes its queries and the subscription
to its death notification. GRANT and REVOKE imply no other right, a reply
capability holds only the right to reply, and the capability to the device
directory can be neither derived nor transferred. An operation that lacks
a right it needs fails with `PermissionDenied`, and a malformed rights mask
with `InvalidRights`. The criterion: for each kind and each rights mask, a
derivation from a capability with every right of its kind gives exactly
the requested rights or the stated error, and the frozen vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::lookup`, `Tables::derive` and
  `Tables::install` (planned).
- **Contract.** [Rights](contract.md#rights).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-admission-1`, `caps-admission-3`
  and `caps-admission-4`, and `objects-7` of the
  [objects contract](../objects/contract.md#legacy-test-vectors), as host
  tests, and the host tests of rights of the
  [contract](contract.md#testing-obligations). The operations that the
  rights of a process authorize are shown by the tests of the lifecycle and
  creation components.

### CAPS-R03

**Lookup.** A lookup of a handle checks, in this order, that its slot
number is within the table, that the slot holds a usable capability, that
its generation is that of the handle, that the capability is of the kind
that the operation needs, that its object is live, that it holds the rights
that the operation needs, and that neither it nor an ancestor is under
revocation and it is not the source of a pending move; it returns the first
error and changes no state. A forged handle, a handle out of range and a
stale handle each fail with a fixed error. The criterion: for each pair of
consecutive checks with different errors, a handle that breaks both gives
the error of the earlier, every field is unchanged after each refusal, and
the frozen vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::lookup` (planned).
- **Contract.** [Lookup](contract.md#lookup) and [Errors](contract.md#errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-admission-2`,
  `caps-endpoint-admission-1`, `caps-lifetime-5` and `caps-transfer-1` as
  host tests, and the host tests of the order of lookup of the
  [contract](contract.md#testing-obligations); QEMU runs of lookups from
  EL0 once the operations exist.

### CAPS-R04

**Attenuation and badges.** Derivation and copy are two operations that
both need GRANT on their source and put the new capability, as a child of
the source, into an empty slot of the caller's own table that the caller
names. Derivation takes a subset of the rights of the source, copy keeps
them and the badge, and a transfer reduces rights in the same way, so no
capability ever has a right that one of its ancestors lacks. A badge is set
once, by the derivation that mints an endpoint send capability from one
without a badge, and every derivation, copy and transfer keeps it. The
criterion: the frozen vectors hold, and a property test finds no filled
entry with a right that an ancestor lacks after any sequence of
operations.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::derive`, `Tables::copy` and `Tables::reserve`
  (planned).
- **Contract.** [Derivation and badges](contract.md#derivation-and-badges).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-admission-4`, `caps-admission-5`,
  `caps-endpoint-admission-2` and `caps-transfer-5` as host tests, and the
  property test of the derivation links of the
  [contract](contract.md#testing-obligations). The test samples sequences on
  the host; it does not prove the statement for every sequence.

### CAPS-R05

**Derivation depth.** A capability has at most 16 live ancestors when it is
made, so a chain of twelve capabilities across two tables and a chain of
eight are allowed, and a derivation, copy or transfer that would exceed the
bound fails with `DepthExceeded`; an ancestor that has been closed no
longer counts. The criterion: a chain of 16 derivations succeeds and one
more fails, the chain extends again after the close of an ancestor in the
middle, and the frozen chain of twelve holds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::derive`, `Tables::copy` and `Tables::reserve`
  (planned).
- **Contract.** [Derivation links](contract.md#derivation-links) and
  [Derivation and badges](contract.md#derivation-and-badges).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `caps-lifetime-6` as a host test, and the
  host tests of depth of the [contract](contract.md#testing-obligations).

### CAPS-R06

**Close.** `close` deletes one capability of the caller and frees its slot,
whatever its rights; the capabilities derived from it keep their rights and
their place among their siblings, and a revocation of an ancestor still
withdraws them. A capability whose object has been released stays in its
slot and fails every operation that uses its object until it is closed. The
criterion: the frozen vectors hold, with the slot of a closed capability
free at once and its descendants still usable.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::close` (planned).
- **Contract.** [Close](contract.md#close).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-admission-6`, `caps-lifetime-1`
  and `caps-endpoint-lifetime-1` as host tests, and the property test of the
  derivation links of the [contract](contract.md#testing-obligations).

### CAPS-R07

**Revocation in two phases.** `revoke` withdraws every descendant of a
capability that holds REVOKE and keeps the capability itself. From its first
transition, every operation that resolves to a capability of the subtree,
or to the capability itself other than a continuing `revoke`, fails with
`RevocationPending`, and every call that waits through the subtree settles
as revoked. The subtree is then removed in post-order, siblings in the order
of their derivation, in steps of at most four capabilities; an interrupt at
the point between two steps leaves the progress in the tables and the call
continues from it. The revocation reports completion, and no count, only
once the subtree is empty and every mapping derived from it has been
removed with its TLB invalidation completed. The criterion: a chain of eight
capabilities is removed in at least two steps, in post-order, every
operation on the subtree is refused between the first transition and
completion, an interrupted revocation ends in the same state as an
uninterrupted one, and the frozen vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::revoke` (planned).
- **Contract.** [Revocation](contract.md#revocation).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-lifetime-1`, `caps-lifetime-7`,
  `caps-endpoint-lifetime-1` and `caps-transfer-4` as host tests, and the
  host tests of revocation of the
  [contract](contract.md#testing-obligations); QEMU runs that revoke long
  chains from EL0 once the operations exist. The settlement of waits and the
  drains of device grants are shown by the tests of the waits, IPC and
  device-authority rules.

### CAPS-R08

**Transfer.** A capability that a message carries is reserved in the
receive slot that the receiver named, charged to the receiver and invisible
to it, before the message is sent; a commit makes it usable and, for a
move, deletes the source, and an abort deletes the reservation and, for a
move, makes the source usable again with its rights. A revocation of the
source or an ancestor refuses the commit and removes the reservation, and
the teardown of either table ends the transfer, without ever restoring a
deleted source. The criterion: the frozen vectors hold, for copy and move,
commit and abort, revocation and the teardown of each side.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::reserve`, `Tables::commit` and `Tables::abort`
  (planned).
- **Contract.** [Transfer](contract.md#transfer).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-quota-1` to `caps-quota-4` and
  `caps-transfer-1` to `caps-transfer-7` as host tests. The visibility of
  the capability together with its message is shown by the tests of the IPC
  component.

### CAPS-R09

**Teardown of a table.** When a process is destroyed, its capability table
is closed in steps of at most four slots, with the progress kept in the
dying process; the capabilities that it gave to other processes keep their
rights, and a revocation pending in the table is completed before its
target is closed. After the last step the table holds no capability and the
process counts no capability slot. The criterion: the frozen vectors hold,
among them a chain of twelve capabilities across two tables whose last
survives the teardown of the other table.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::teardown_step` (planned).
- **Contract.** [Teardown of a table](contract.md#teardown-of-a-table).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-lifetime-4`, `caps-lifetime-6`,
  `caps-endpoint-lifetime-5` and `caps-transfer-6` as host tests, and the
  host tests of teardown of the [contract](contract.md#testing-obligations).
  The order of the teardown among the steps of a destruction is shown by the
  tests of the lifecycle component.

### CAPS-R10

**Counts and the last capability.** Each object counts the capabilities of
its current generation, and only the entries of this component change the
count. An endpoint or a notification is released, and its owner credited,
when its last capability is deleted, and not before; no count holds back
the reclamation of an object. Each filled slot of a table is charged to the
process of the table, and the charge never fails. The criterion: a property
test finds every count equal to the filled entries other than replies that
name its object, and the frozen vectors hold with the release at the last
capability.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Tables::count`, with the write entries of the
  [entry table](contract.md#entry-points) (planned).
- **Contract.** [Capability counts](contract.md#capability-counts).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-endpoint-admission-1`,
  `caps-endpoint-admission-4`, `caps-endpoint-lifetime-3` and
  `caps-endpoint-lifetime-4` as host tests, and the property test of the
  [contract](contract.md#testing-obligations). The conservation of the
  capability-slot item is the property test of the
  [objects requirements](../objects/requirements.md#obj-r08).

### CAPS-R11

**No change on failure.** Every error of the component leaves every entry,
count and quota record as it was and counts nothing, and a failure of the
write phase of an operation leaves the state from before it. The criterion:
for each error of the contract, a call that gives it leaves every field
compared before and after unchanged; for each fault-injection point, an
operation that fails there leaves the tables as before; and the frozen
vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `caps-admission-4`, `caps-admission-5`,
  `caps-endpoint-admission-2` and `caps-transfer-5`, and the host tests of
  each error and each fault-injection point of the
  [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component other than `revoke` and the teardown of a
  table runs to its end within the bounds of the
  [contract](contract.md#work-bounds).
- A revocation and a teardown proceed in steps of at most four capabilities
  each; the number of steps grows with the size of what they withdraw, and
  no requirement bounds the time until they complete.
- No requirement bounds the time that a step takes.

## Scope

- One CPU. The tokens, their locks, the order in which several CPUs take
  them and the acknowledgement of TLB invalidations by other CPUs are not
  covered.
- The operations that the rights authorize, the creation of objects, the
  lifetimes of processes, IPC with the visibility of a message and its
  capabilities, the settlement of waits, budget loans and the drains of
  device grants are not covered; they compose the entries of this component
  and have their own requirements.
- The operation numbers and numeric error codes of the ABI inventory are
  not covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Derivation links](contract.md#derivation-links) states the fields that
  [CAPS-R04](#caps-r04) to [CAPS-R07](#caps-r07) rely on.
- [Determinism](contract.md#determinism) and
  [State fields](contract.md#state-fields) bind the code without an
  observable behaviour of their own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Open obligations](contract.md#open-obligations) has no row.
