---
features: none
---

# VM requirements

The observable behaviour of the `vm` component of the
[memory and address spaces](../README.md) domain: the VM window and the
regions of each process, the commit, decommit and protection of their
pages, the two-phase release of a region and the revocation of the pages
of a destroyed process, the VM part of the capacity record and the page
pool, and the limits of commits. The rules that its code and tests follow
are in the [contract](contract.md). No feature document covers the
component, so the metadata lists none.

## Sources

- The checks of a request before any backing is taken, zero pages before
  EL0 can run, the order of unmap, completed invalidation, scrub and free,
  a release that blocks new work while it is not complete, and the
  isolation of the pages of two processes take the rules of the prototype's
  private user memory, which the [references](contract.md#references) of
  the contract list, with its host tests as the frozen
  [vectors](contract.md#legacy-test-vectors).
- The VM window, regions named by their address without a capability, the
  five operations on the caller's own address space, the page pool carved
  at boot with its frame metadata, the plans and their acknowledgement, the
  release that the destruction of a process shares, the cap of committed
  pages in the capacity record and the limit of 512 pages per call are new,
  from the kernel's
  [address spaces and VM objects](../../../architecture.md#address-spaces-and-vm-objects),
  its [capacities](../../../architecture.md#kernel-objects-and-capabilities)
  and its [execution model](../../../architecture.md#system-calls-and-the-abi);
  the [current deviations](contract.md#current-deviations) of the contract
  list where they differ from the prototype.
- The order of errors, the placement of regions and the observable outputs
  follow the [security model](../../../security.md#internal-choices), and
  the two phases its
  [effective revocation](../../../security.md#effective-revocation); the
  acknowledgement before reuse and the classes of state follow the
  [SMP design rules](../../../conventions/smp.md#s3-reclamation-after-acknowledgement).
- The descriptors, the write plans and the tables are those of the
  [page-tables](../page-tables/requirements.md) component; the EL0 window,
  the table pool and the release of an ASID are those of the
  [address-space](../address-space/requirements.md) component; the quota
  records, the capacity record and the write sets are those of the
  [objects](../../objects-capabilities/objects/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release
  0.1, with one of its four Cortex-A76 cores running.
- **Host.** The host tests of the module `vm` of the core (planned) run on
  the development host and in CI, with the frozen vectors and the tests
  that the [contract](contract.md#testing-obligations) adds, each with the
  page pool, the capacity record and the plans that it passes.
- One CPU. The region tables and the frames that a process holds are
  per-process, and the page pool is shared state under its token, also
  while one CPU runs; no requirement here covers the acknowledgement of a
  TLB invalidation by other CPUs, several threads of one process or the
  locks that provide the tokens.

## Requirements

### VM-R01

**The window and its regions.** Every region of a process lies in its VM
window, `[0x4040000000, 0x4080000000)`, a 1 GiB slot of the EL0 window
apart from the boot ranges and the image window; the regions of one
process never overlap. `reserve` with an address establishes the region
there, and with the address 0 at the lowest address of the window at which
the pages fit, and gives the start; a region is named by its start alone. A
process has at most the `vm_regions` rows of the capacity record, at most
256. The criterion: reserves at the edges of the window and one page
beyond, overlapping reserves, a reserve at 0 in a window with gaps, and a
region table filled to its last row and one beyond give the results of the
contract, and the frozen vectors of bounds and region capacity hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::reserve` and `Regions::new`, with the constants
  `vm::VM_START`, `VM_END` and `MAX_REGIONS` (planned).
- **Contract.** [VM window and regions](contract.md#vm-window-and-regions).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `vm-2`, `vm-3` and `vm-authority-5` as
  host tests, and the host tests of the operations and of the errors of the
  [contract](contract.md#testing-obligations), with the host test of the
  relations of the window to the EL0 window and the boot ranges.

### VM-R02

**Commit gives zero pages.** `commit` maps every page of its range, at most
512 pages in one region, writable and never executable, each with a frame
of the page pool that reads zero, or refuses and changes nothing; the
pages of one process never share a frame with another process. The
criterion: a committed page reads zero and takes a write, two processes
commit at the same addresses and get distinct frames, a commit of 512 pages
succeeds and one of 513 is refused, and the frozen vector of isolated
zeroed regions holds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::commit` and `vm::acknowledge` (planned).
- **Contract.** [Commit](contract.md#commit) and
  [Configuration and the page pool](contract.md#configuration-and-the-page-pool).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `vm-1`, `vm-2` and `vm-4` as host
  tests, the property test of the operations of the
  [contract](contract.md#testing-obligations), and its QEMU test of a
  commit whose pages read zero and take a write. The host tests show the
  frames and the plans; the QEMU test shows the mapping on QEMU virt.

### VM-R03

**Limits of commits.** A commit is refused, before any write, when it would
take the committed VM pages of the caller beyond the limit of its quota
item (`QuotaExceeded`) or beyond the cap of the capacity record
(`CommitLimit`), when the table pool of the caller has too few tables
(`OutOfTables`), or when the page pool has too few free frames
(`OutOfPages`), in this order. The root's limit and the cap of each
process come from the capacity record, at least 1 MiB in the default record
of every board, and a child's limit is its share. The criterion: commits
at each limit succeed and one page beyond each is refused with its error;
a commit that breaks two limits gets the error of the earlier; and the
frozen vectors of quota and exhaustion hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::commit`, `vm::check_config` and `Pool::free`
  (planned).
- **Contract.** [Quotas](contract.md#quotas),
  [Tables and extents](contract.md#tables-and-extents) and
  [Errors](contract.md#errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `vm-2`, `vm-3` and `vm-4` as host
  tests, and the host tests of the limits of a commit and of the default
  records of the [contract](contract.md#testing-obligations).

### VM-R04

**Decommit.** `decommit` returns the frames of committed pages of one
region and keeps the region: each page is unmapped, its translation
invalidated, its frame zeroed and only then returned to the pool, with one
page credited to the quota of the caller; an access to the page afterwards
takes a translation fault until it is committed again. The criterion: after
a decommit, the frames are in the pool and read zero, the usage is lower by
the pages, the range can be committed again, and the plans come in the
order unmap, zero, return for each page.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::decommit` and `vm::acknowledge` (planned).
- **Contract.** [Decommit](contract.md#decommit) and
  [Acknowledgement and reclamation](contract.md#acknowledgement-and-reclamation).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The property test of the operations of the
  [contract](contract.md#testing-obligations), and its QEMU test of an
  access after a decommit. The order of the plans is shown by the host
  tests; the translation fault on QEMU virt.

### VM-R05

**Protection and W^X.** `mprotect` changes committed pages of one region
between read-only and read-write, and refuses the execute bit with
`ExecuteDenied`; no frame of the page pool is ever mapped executable, and
no frame has more than one mapping at EL0. The criterion: a write to a page
made read-only takes a permission fault and a write after it is made
read-write again succeeds; an execution from a committed page takes a
permission fault; the execute bit is refused; and no sequence of operations
of the property test maps a frame executable or twice.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::mprotect` and `vm::acknowledge` (planned).
- **Contract.** [Protection and W^X](contract.md#protection-and-wx).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The property test and the test of W^X of the
  [contract](contract.md#testing-obligations), with its QEMU tests of a
  write to a read-only page and of an execution from a committed page.

### VM-R06

**Two-phase release.** `release` removes a region in two phases: from the
transaction that makes it pending, every new operation in the region is
refused with `Pending`; the release reports its completion only after
every committed page of it has been unmapped, its invalidation
acknowledged and its frame zeroed, and only then do its frames return to
the pool and its pages to the quota of the caller. A release works in steps
of at most 64 pages with a preemption point between two steps, and a call
executed again continues from the stored progress. The criterion: a release
of a region larger than one step that is preempted at each step and
executed again completes with the same result as one without preemption;
an operation in the region between the steps is `Pending`; and while a
host test holds a plan without its acknowledgement, the frame of the page
is off the pool and its page in the usage of the caller.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::release` and `vm::acknowledge` (planned).
- **Contract.** [Two-phase release](contract.md#two-phase-release) and
  [Acknowledgement and reclamation](contract.md#acknowledgement-and-reclamation).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `vm-1`, `vm-failures-2` and
  `vm-failures-3` as host tests, and the host tests of release of the
  [contract](contract.md#testing-obligations), with its QEMU tests of an
  access after a release and of a release that a timer interrupt preempts.
  On QEMU virt with one CPU, `Pending` reaches no thread at EL0; the host
  tests show it.

### VM-R07

**Revocation at process destruction.** The destruction of a process
returns every frame that it holds, committed and loaded, to the pool, each
zeroed first, after the invalidation of its ASID and the reset of its
tables and without unmapping a page, in steps of at most 64 frames, and
credits each page to the item of its kind; once the revocation is
complete, the process holds no frame, its usages of committed VM pages and
of private pages of loaded images are 0 and its region table is empty. The
frames of other processes are not touched. The criterion: a process with
committed and loaded frames and a pending release is revoked to no frame
and usages of 0 in the number of steps of the contract, while another
process keeps its bytes; and the frozen vector of a faulted owner holds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::revoke_step`, `vm::acknowledge` and `Pool::take`
  (planned).
- **Contract.** [Revocation at process destruction](contract.md#revocation-at-process-destruction).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `vm-failures-3` and `vm-failures-4` as
  host tests, and the host test of revocation of the
  [contract](contract.md#testing-obligations). The order of the steps in
  the destruction and the gate of reaping are shown by the tests of the
  lifecycle component.

### VM-R08

**Configuration and the page pool.** The VM part of the capacity record,
bytes 48 to 63, gives the root's limit of committed VM pages, the cap of
each process and the frames of the page pool, and its reserved field is 0;
the boot checks it once, as untrusted input, and stops at the first check
that fails, without a fallback, and a record without the VM part is
refused. The boot carves the pool and its metadata as two holders of the
page ownership table, zeroed, after the root's private pages, and stops
when no range is found; every frame of the pool is zero whenever it is
free. The criterion: each check at its limit passes and one beyond fails;
the default record of each board passes, with a root limit and a cap of at
least 256 pages; and the carving adds at most one extent for each of the
two allocations.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `vm::check_config` and `Pool::new` (planned).
- **Contract.** [Configuration and the page pool](contract.md#configuration-and-the-page-pool)
  and [Tables and extents](contract.md#tables-and-extents).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of configuration and of the pool of the
  [contract](contract.md#testing-obligations). The boot with the default
  record on QEMU virt is shown by the QEMU tests of the operations, which
  run on it.

### VM-R09

**One holder for every frame.** Every frame of the page pool has exactly
one holder at any time, the pool or one process; a frame that a process
holds is mapped at most once at EL0, by that process, and reaches another
holder only after it has been unmapped or its tables reset and it has been
zeroed. No operation of one process reads or changes the pages or the
frames of another. The criterion: the property test finds, after every
step, every frame with one holder and at most one mapping, every free frame
zero, and the bytes of a process unchanged by the operations of another;
and the frozen vectors of isolation hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every write entry of the
  [entry table](contract.md#entry-points).
- **Contract.** [Configuration and the page pool](contract.md#configuration-and-the-page-pool),
  [Acknowledgement and reclamation](contract.md#acknowledgement-and-reclamation)
  and [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `vm-1`, `vm-4` and `vm-failures-4` as
  host tests, and the property test of the operations of the
  [contract](contract.md#testing-obligations). It samples sequences and
  does not prove the rule for every one.

### VM-R10

**No change on failure.** Every error of the component leaves the kernel
state as it was: a refused operation writes nothing, gives no plan, takes
no frame and changes no table, and no refusal is counted. The errors follow
the order of the security model: the form of the arguments, the region
that the address names, the execute bit, object state, the caller's quota,
shared capacity. The criterion: for each error of the contract, a call that
gives it leaves every field compared before and after unchanged; for each
pair of consecutive checks whose errors differ, a call that breaks both
gets the error of the earlier; and the frozen vectors of refusals hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `vm-2`, `vm-3`, `vm-4` and
  `vm-authority-5` as host tests, and the host tests of the errors of the
  [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a lock
  of its own.
- A commit, a decommit and an `mprotect` run in one transition with at most
  512 pages; a decommit zeroes at most 2 MiB in it, the longest work of the
  component without a preemption point.
- A release of a region of $n$ pages and the revocation of a process with
  $m$ frames take at most $\lceil n / 64 \rceil$ and
  $\lceil m / 64 \rceil + 1$ steps, with a preemption point between two
  steps; a step zeroes at most 256 KiB. No requirement bounds the time until
  a revocation is reached, which the lifecycle component decides.
- No requirement bounds the time that a step takes.

## Scope

- One CPU. The acknowledgement of a TLB invalidation by other CPUs, the
  tokens and their locks are not covered.
- VM objects that several address spaces map, capabilities to regions or
  VM objects, copy-on-write and file-backed objects with their pagers, the
  execute right of memory objects and region generations belong to later
  releases.
- The user copies of the kernel and Privileged Access Never are not
  covered; they belong to a later release.
- The validation of loading requests and the loading part of the capacity
  record belong to the dispatch component; the mapping of loaded images, the
  copy of their file bytes and the charge of their private pages to the
  creation component; the order of the steps of a destruction and the gates
  of reaping to the lifecycle component.
- A process has one thread; further threads of a process are not covered.
- The operation numbers, the registers of arguments and results and the
  numeric codes of errors of the ABI inventory are not covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Extractability](contract.md#extractability) states the module, its layer
  and the modules that it does not refer to, which no requirement observes.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Open obligations](contract.md#open-obligations) lists the adapter of the
  architecture crate and the board code that no target covers.
- [Current deviations](contract.md#current-deviations) states where the
  rules differ from the prototype, which the requirements state directly.
