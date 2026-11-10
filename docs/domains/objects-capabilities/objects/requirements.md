---
features: none
---

# Objects requirements

The observable behaviour of the `objects` component of the
[kernel objects and capabilities](../README.md) domain. The rules that its
code and tests follow are in the [contract](contract.md). No feature
document covers the component, so the metadata lists none.

## Sources

- The pools with their control reserves, the identities of slots, the
  rejection of foreign and stale references, the quota checks before the
  first write and the totality of the owner checks take the rules of the
  prototype's object pool and of its activation contract, which the
  [references](contract.md#references) of the contract list, with their
  host tests as the frozen [vectors](contract.md#legacy-test-vectors).
- The generations of single slots with their retirement, the capacity
  record with its checks and its storage carved at boot, the quota records
  with their split and returned limits, the conservation of usages and the
  write-set transactions are new, from the kernel's
  [objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities);
  the [behaviour changes](contract.md#legacy-test-vectors) of the contract
  list where they differ from the prototype.
- The order of errors, the choice of slots and the observable outputs
  follow the [security model](../../../security.md#internal-choices); the
  classes of state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2, one
  Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host, booted with the default capacity record of the board or with a
  record of its boot bundle.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release 0.1,
  with one of its four Cortex-A76 cores running and the default capacity
  record of the board; the extents that the storage of the object table
  uses are shown on the host for the bank shape that the prototype
  measured on that model.
- **Host.** The host tests of the module `objects` of the core (planned) run
  on the development host and in CI, with the frozen vectors and the tests
  that the [contract](contract.md#testing-obligations) adds.
- One CPU: no requirement here covers secondary CPUs, the order in which
  several CPUs take a token, or the locks that provide the tokens.

## Requirements

### OBJ-R01

**Kinds and pools.** The kernel has eight kinds of object: processes,
threads, endpoints, replies, notifications, VM regions, the device
directory and device grants. Processes, threads, endpoints, notifications
and device grants each have a pool whose capacity the capacity record sets,
and the device directory a pool of one slot; a reply lives in its thread
and a VM region in its process. A pool that has no free slot for an
allocation refuses it and never takes a slot of another pool. The
criterion: a table built from a record has exactly the pools and
capacities of the record, and the frozen vectors that fill a pool hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ObjectTable::new`, `choose` and `counts` (planned).
- **Contract.** [Object kinds and pools](contract.md#object-kinds-and-pools).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `objects-4`, `objects-5` and `objects-6`
  as host tests, and the host test that fills the process pool and empties
  it again three times. They show the bookkeeping on the host; the QEMU boot
  with the default record shows that the table is built on the board's
  memory.

### OBJ-R02

**Generations and retirement.** Every slot starts at generation 1, keeps
its generation while it is allocated and gains one when it is released; a
slot released at $2^{64} - 1$ retires and is not allocated again before the
next boot. No generation wraps, so the reference of an object that has
been released never names another object. The free, allocated and retired
slots of a pool add up to its capacity. The criterion: the frozen vectors
hold, among them 128 rounds in which a slot takes 128 increasing
generations and the release of slots at $2^{64} - 1$ retires them.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ObjectTable::choose`, `occupy`, `release`, `resolve` and
  `counts` (planned).
- **Contract.** [Identities and generations](contract.md#identities-and-generations).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `objects-3`, `objects-10` and
  `objects-11` as host tests, and the host tests of generations of the
  [contract](contract.md#testing-obligations). They show the rule on the
  host with generations set by the tests; reaching $2^{64} - 1$ by releases
  is not run.

### OBJ-R03

**Total resolution.** Resolving a reference gives the slot of a live object
of the requested kind, and every other representable reference, whether of
another pool, of a slot number beyond the capacity or the largest slot
number, of a free or retired slot or of another generation, gives
`WrongPool` or `StaleReference` without a panic and without a change of any
field. A record that would give a pool of no process slot is refused. The
criterion: the frozen owner and capacity vectors hold, each with every field
of the table compared before and after.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ObjectTable::resolve` and `objects::validate_capacities`
  (planned).
- **Contract.** [Identities and generations](contract.md#identities-and-generations)
  and [Errors](contract.md#errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `activation-legacy-1` to
  `activation-legacy-6`, `activation-legacy-8` to `activation-legacy-10`,
  their `activation-parallel` counterparts, and `objects-8`, as host tests.
  They show the rejections for the inputs of the vectors; that every
  representable input is total is a property of the code that the host
  tests sample and do not prove.

### OBJ-R04

**Choice of slots.** An ordinary allocation takes the lowest free slot of
the ordinary range of its pool, which excludes the reserved tail of the
control reserve; a control allocation takes the lowest free slot of the
reserved tail, or of the ordinary range when the tail has none. A retired
slot is never taken. The criterion: the frozen vectors hold, among them a
pool whose every slot is reserved, which refuses an ordinary allocation and
gives the root's pair its slots.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ObjectTable::choose` and `occupy` (planned).
- **Contract.** [Identities and generations](contract.md#identities-and-generations)
  and [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `objects-1`, `objects-5`, `objects-6` and
  `objects-10` as host tests.

### OBJ-R05

**Capacity record.** The boot checks the object part of the capacity
record once, before it carves any storage, in a fixed order: the framing
of the record, then that it holds its 48 bytes and every capacity is at
least 1 and within its width, that there are at least as many threads as
processes, that each control reserve fits its pool, that the storage fits
the free memory, and that there are no more processes than ASIDs. A record
that fails a check stops the boot with the fixed error of the first failed
check, and the kernel does not fall back to the defaults. Without a record,
the boot uses the default record of the board, which provides at least 64
processes and 256 threads and passes the same checks. The criterion: each
check accepts its limit and refuses one beyond it, a record that breaks two
consecutive checks with different errors gives the error of the earlier,
and the frozen vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `objects::validate_capacities` and
  `Capacities::allocations` (planned).
- **Contract.** [Capacity record](contract.md#capacity-record).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `objects-2`, `activation-legacy-2` and
  `activation-parallel-2` as host tests; the host tests of the limits, the
  order and the default records of the
  [contract](contract.md#testing-obligations); the QEMU boot with a record
  that does not fit, which stops with `InsufficientMemory`. The checks 1
  and 6, of the address-space component, are shown by its tests.

### OBJ-R06

**Storage carved at boot.** The boot carves the storage of the object table
from the
[page ownership table](../../memory/page-tables/contract.md#page-ownership)
in eight allocations, each with its own owner identity: the five pools, the
capability tables, the VM region tables and the write-set buffers. No
entry takes or returns memory after boot. Each
allocation adds at most one extent to the page ownership table. The
criterion: for the default records and for a record at the limits, the
boot takes exactly eight allocations with distinct owner identities and the
pages that the contract computes, and on the bank shape of the 8 GB Pi 5
the extents in use grow by at most eight.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Capacities::allocations` and `ObjectTable::new`
  (planned).
- **Contract.** [Storage carved at boot](contract.md#storage-carved-at-boot).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of the allocations of the
  [contract](contract.md#testing-obligations), and the QEMU boot with the
  default record and three cold boots with the same counts. That no entry
  allocates after boot is a property of the code that review and the
  absence of any allocating entry in the entry table establish.

### OBJ-R07

**Metadata quotas.** Every object that a calling domain creates is charged
to that domain, its owner, in one of seven quota items: child processes,
endpoints, notifications, capability slots, committed VM pages, private
pages of loaded images and page-table pages. A creation checks the
caller's own quota before the shared capacity and before its first write;
an ordinary charge beyond the limit fails with `QuotaExceeded` and changes
nothing. The limits of a child are split from what its creator has left
and return to the creator when the child is reaped; the capability slots
and page-table pages of a process are given by its own fixed structures.
The root starts with a limit of child processes equal to the smaller of the
ordinary capacities of the process and the thread pool, and with limits of
endpoints and notifications equal to the ordinary capacities of their
pools. The criterion: the quota steps of the frozen vectors hold, and the
host tests of splits, returns and the root's limits hold against an
independent model.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `QuotaRecord::check`, `charge`, `credit`, `split`,
  `merge`, `start_root` and `usage`, and `Capacities::root_limits`
  (planned).
- **Contract.** [Metadata quotas](contract.md#metadata-quotas).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `objects-1` as a host test, and the host
  tests of the root's limits and of an ordinary creation within the quota
  of the [contract](contract.md#testing-obligations). The creation of
  objects through the ABI, which composes these entries, is shown by the
  tests of the creation component.

### OBJ-R08

**Conservation.** For every quota item, the usages of different calling
domains never overlap, and the usages of all calling domains add up to
what is allocated for the item, after every operation and also while
processes are destroyed; for each split item, the limits of the live
domains add up to the root's starting limit. The criterion: a property test
over sequences of creations, charges, splits, releases, returns and the
destruction of a parent with children holds the two statements and the sum
after every write-back, against an independent model of owners, limits and
usages.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `QuotaRecord::charge`, `credit`, `split`, `merge` and
  `usage`, and `ObjectTable::occupy` and `release` (planned).
- **Contract.** [Metadata quotas](contract.md#metadata-quotas).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The property test of the
  [contract](contract.md#testing-obligations). It samples sequences on the
  host; it does not prove the statements for every sequence.

### OBJ-R09

**Write-set transactions.** An operation makes all its checks before its
first write and changes its write set through copies in the write-set
buffer of its CPU, which it writes back at once; after the checks only the
capacity and quota failures of its contract and, in a test build, its
fault-injection points can stop it, and then every slot, count and quota
record equals what it was before. No operation leaves half of a pair of a
process and its thread. The criterion: for each fault-injection point, an
operation that fails there leaves the table and the records as before, a
write set of 64 items commits, and the frozen vectors hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `WriteSet::stage`, `commit` and `discard`, with the write
  entries of the table and the quota records (planned).
- **Contract.** [Write-set transactions](contract.md#write-set-transactions)
  and [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `objects-3`, `objects-4` and `objects-11`
  as host tests, and the host tests of the write sets of the
  [contract](contract.md#testing-obligations).

### OBJ-R10

**No change on failure.** Every error of the component leaves every field
of the kernel state as it was, and no failure is counted: a rejected
request writes neither a slot, a count or a quota record nor a counter of
failures. Only committed operations are counted, as slots occupied and
released. The criterion: for each error of the contract, a call that gives
it leaves every field compared before and after unchanged, and the frozen
vectors hold without the prototype's counts of failures.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Write-set transactions](contract.md#write-set-transactions).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `objects-3`, `objects-4`, the owner and
  capacity vectors, and the host test of each error of the
  [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits or retries, and the
  component has no long operation.
- The choice of a slot scans at most the slots of one pool; the building of
  the table at boot writes each slot once.
- No requirement bounds the time that a step takes.

## Scope

- One CPU. The tokens, their locks and the order in which several CPUs take
  them are not covered.
- The operations that create objects, the lifetimes of processes and
  threads with their reaping, the capability tables and the waits are not
  covered; they compose the entries of this component and have their own
  requirements.
- The VM and loading part of the capacity record, the counting of committed
  and loaded pages, the boot-bundle directory and the number of ASIDs are
  not covered.
- A process has one thread; further threads of a process are not covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Determinism](contract.md#determinism) and
  [State fields](contract.md#state-fields) bind the code without an
  observable behaviour of their own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Open obligations](contract.md#open-obligations) lists the adapter that
  lends the write-set buffer and the board's forming of the slices of the
  carved storage, which no requirement observes.
