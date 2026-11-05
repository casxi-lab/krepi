# SMP design rules

These rules govern how code classifies its state and shares it between CPUs.
They turn the design goals of
[multicore by design](../architecture.md#multicore-by-design) into rules for
code. Each rule has a statement, a violation and the reason why the
violation fails. A component records how its state follows the rules in the
`State fields` section of its `contract.md`
([component documents](documentation.md#component-documents)).

## Scope

- The rules bind all kernel code, including the adapters around proof
  targets, and all EL0 system code: the root, the services and the drivers.
- They hold while the system runs on one CPU as well as on several (S4).
- They do not depend on how the kernel represents an operation that waits.
- The modules that proofs are to cover also follow the
  [provable Rust subset](provable-subset.md), which keeps the primitives of S2
  in adapters outside the proved code
  ([rule 8](provable-subset.md#8-no-interior-mutability)).

## Rules

### S1 State classes

Every piece of state belongs to exactly one of four classes and has one
stated owner; for state that several CPUs reach, the owner is the lock or
protocol that serializes access to it. The kernel design fixes the class of
each piece of kernel state, and each contract records it per field (S5).

| Class | Holds | Owner |
| --- | --- | --- |
| Per-CPU | State that one CPU alone reaches and that does not move with a thread, such as the run queue and the emergency stack of a CPU | That CPU, with local interrupts masked for every access that an interrupt handler on that CPU can interleave with; another CPU changes it only by a request in shared state that the owning CPU applies |
| Per-thread | State of one thread that moves with it, such as its registers, its TLS and its FP/SIMD state | The CPU that runs the thread; while the thread does not run, the owner that the contract names |
| Per-process | State of one process that its threads and the operations on the process reach | The lock or protocol that the contract names, because every CPU that runs one of its threads or acts on the process can reach it |
| Shared | State with no single owner, including data that does not change after its publication | The lock or atomic protocol that the contract names, or none after its single publication when it no longer changes |

State that moves between owners, such as the saved context of a thread that
stops on one CPU and resumes on another, has one owner at a time, and the
handover is a publication (S2). EL0 system code has per-CPU state only in a
thread bound to that CPU, and state that several threads of a process reach
is per-process. Only state that one owner alone reaches can be reasoned
about as if no other CPU existed: in the CPU-local model of the verified
SeKVM hypervisor, for example, the events of other CPUs do not affect
private state, and a CPU consults them only before it accesses a shared
object (Li et al. 2021).

**Violation.**

```rust
pub struct Cpu {
    /// Per-CPU: only this CPU reads or writes it.
    pub run_queue: RunQueue,
}

/// Runs on the CPU that completes the wait.
pub fn wake(cpus: &mut [Cpu], thread: ThreadRef) {
    cpus[thread.last_cpu].run_queue.push(thread);
}
```

The run queue is declared per-CPU but written by whichever CPU completes the
wait, so it has two owners.

### S2 Synchronization and memory order

State that can change and that more than one CPU reaches is accessed only
through one of these primitives:

- a lock that the contract names, held for every access to the fields it
  protects; acquiring it is an Acquire operation and releasing it a Release
  operation;
- an atomic location of `core::sync::atomic`, accessed with the orderings
  that the contract states;
- data that does not change after its single publication.

Locks, atomics and published data lie in Normal, Inner Shareable,
Write-Back memory, which every CPU that takes part maps with the same
attributes and accesses with its MMU and data cache on: the architecture
orders a write only for the observers that access the location coherently
in the stated shareability domain (Arm 2022, chapter 4). No lock or atomic
lies in Device memory. A CPU whose data cache is off, such as a secondary CPU
at its entry, uses no lock or atomic, and data that it reads before it turns
its cache on becomes visible to it only through the cache maintenance that
the publication rule of that data names.

The orderings follow these conventions:

- Publication is a Release store, or the release of a lock, after the data
  is written, paired with an Acquire load, or the acquisition of the lock,
  before the data is read.
- A read-modify-write that both takes over and hands over data, such as the
  decrement of a reference count whose last holder frees the object, uses
  `AcqRel`. The verification of the Arm Confidential Compute Architecture
  firmware found a defect of this kind: a counter decrement without Release
  semantics (Li et al. 2022).
- `Relaxed` is used only for a value that orders no other access, such as a
  statistics counter.
- `SeqCst` is used only where the correctness argument needs a single order
  over accesses to different locations, such as two CPUs that each store
  their own flag and then load the other's flag; the contract states that
  argument.

Masking interrupts on the local CPU, `volatile` accesses and `UnsafeCell`
order nothing between CPUs. Rust orderings order the memory accesses of
CPUs; they do not order translation table walks, TLB maintenance or cache
maintenance, for which the architecture has barriers of its own (S6a to
S6d). The rules do not fix the number of locks: one lock for all shared
kernel state, as the SMP configuration of seL4 uses (seL4 Foundation),
follows them as well as several locks do. In the modules that the provable
Rust subset lists, every entry receives the one `&mut` reference to the
kernel root
([rule 3](provable-subset.md#3-flat-relations-and-one-kernel-root)), so the
adapters run these entries one at a time.

**Violation.**

```rust
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

pub static REQUEST: AtomicU64 = AtomicU64::new(0);
pub static READY: AtomicBool = AtomicBool::new(false);

pub fn post(request: u64) {
    REQUEST.store(request, Ordering::Relaxed);
    READY.store(true, Ordering::Relaxed);
}

pub fn take() -> Option<u64> {
    if READY.load(Ordering::Relaxed) {
        return Some(REQUEST.load(Ordering::Relaxed));
    }
    None
}
```

`READY` publishes `REQUEST`, but both accesses to it are `Relaxed`, so
another CPU can see the flag set and still read the old request; the flag
needs a Release store and an Acquire load (Arm 2022, chapter 10).

### S3 Reclamation after acknowledgement

A resource that another CPU may still reach is reused only after every CPU
that may reach it has acknowledged that it no longer does:

- for a translation that an unmap removes, the completion of the
  invalidation of S6c on the reclaiming CPU is the acknowledgement of every
  CPU that may hold the translation;
- the translation tables and the ASID of an address space are reused only
  after every CPU that may run the address space has acknowledged that its
  root and ASID are no longer in `TTBR0_EL1`, and the ASID only after its
  TLB entries are invalidated as S6c states;
- memory, stacks and kernel objects are reused only after every CPU that
  may hold a reference to them has acknowledged that it dropped it.

The set of these CPUs is fixed when reclamation starts and does not shrink;
a CPU that goes offline or does not answer stays in the set until it is
shown to be quiescent. A timeout, a request that was only sent and a CPU
that has only gone offline are not acknowledgements, and a resource whose
acknowledgement never arrives stays quarantined.

**Violation.**

```rust
pub fn destroy_space(
    space: AddressSpace,
    asids: &mut Asids,
    frames: &mut Frames,
) {
    // Asks every CPU that runs the space to switch to another root.
    let pending = space.request_switch();
    // Gives up waiting after the deadline.
    let _ = pending.wait_until(DEADLINE);
    asids.free(space.asid());
    frames.free_tables(space.into_tables());
}
```

When the deadline passes first, a CPU that still runs the address space
keeps its root and ASID in `TTBR0_EL1`: its table walks read tables that now
have another owner, and its TLB entries tagged with the ASID serve the next
address space that receives it.

### S4 Classification on one CPU

While the system runs on one CPU, code follows S1 to S3 as on several: it
reaches per-CPU state through the identity of the executing CPU, takes the
lock or follows the protocol of shared state, and publishes and acknowledges
as S2 and S3 require. That no other CPU runs is never the reason why an
access is correct. The CPUs that S3 and S6c count are those that the state
records, such as the CPUs that have had the root and ASID of an address
space in `TTBR0_EL1` (S6c): on one CPU the record holds the executing CPU
alone, and the local invalidation that S6c allows for that case is correct
because of the record.

**Violation.**

```rust
pub fn current_thread(kernel: &Kernel) -> ThreadRef {
    // Only CPU 0 runs.
    kernel.cpus[0].current
}
```

As soon as a second CPU runs, it gets the thread of CPU 0; the function has
to take the state of the executing CPU.

### S5 State field tables

The `State fields` section of a component's `contract.md` is a table with
one row for every field of the component's state and these columns:

| Column | Content |
| --- | --- |
| Field | The field, by its path in the component's state |
| Class | Per-CPU, per-thread, per-process or shared (S1) |
| Lock or owner | The lock that every access holds, the atomic protocol of the field, or its single owner; for a field whose owner changes, the handover that passes it on |
| Linearization point | The step at which an operation's change of the field takes effect for every other CPU, such as the release of the lock after the commit of a write set, or the Release store of a publication |
| Publication | For a field that more than one CPU reaches, which includes shared and per-process fields and a per-thread field at its handover: how a new value becomes visible to other CPUs, under the lock, by a Release store that readers load with Acquire, or once before the field stops changing; `none` for a field whose single owner never changes |

Fields that a structure holds together may share a row when every column
holds the same for each of them.

**Violation.**

```markdown
| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| `Endpoint::queue` | shared | kernel root lock | | |
```

The row gives neither a linearization point nor a publication rule, so
nothing states when a message that one CPU sends takes effect for a receiver
on another CPU.

## Page tables and published data

The four rules below follow four of the six weak data-race-free conditions of
VRM: write-once kernel mapping, transactional page tables, sequential TLB
invalidation and memory isolation; S2 corresponds to the other two, the
synchronization of shared accesses and the placement of barriers around
critical sections. For a kernel that satisfies all six, VRM proves that
every behaviour the kernel can show on Armv8 relaxed-memory hardware is also
a behaviour on a sequentially consistent model; the conditions are
sufficient, not necessary (Tao et al. 2021). These rules alone do not give
krepi that result.

A CPU that writes a valid entry where the entry was invalid, including the
parent entry that publishes a new table, completes the write with `DSB ISH`
and then executes `ISB`, or returns to EL0 by an exception return, which
synchronizes context as an `ISB` does (Arm 2022, chapter 11), before it or
EL0 relies on the entry. Another CPU that relies on the entry after it
observes the publication first executes `DSB` and `ISB`, unless the
processor implements Enhanced Translation Synchronization or the writer
follows the write with `DSB ISH`, `TLBI` and `DSB ISH` (Simner et al. 2022).

### S6a Kernel mappings

The translation tables of the kernel's own address space are written once:
the kernel writes only entries that are invalid and never changes or removes
a valid entry of its own mappings. Because W^X holds for every alias
([address spaces](../architecture.md#address-spaces-and-vm-objects)), these
mappings hold no writable alias of a frame that may later become
executable. The processor caches no translation that results in a
translation fault, an address size fault or an access flag fault, so filling
an invalid entry needs no TLB invalidation (Arm 2024, chapter 8), only the
barriers stated at the start of this section.

**Violation.**

```rust
/// Moves a page of the kernel's own mappings to another frame.
pub fn remap_kernel_page(
    tables: &mut KernelTables,
    va: VirtAddr,
    frame: Frame,
) {
    let entry = tables.leaf_mut(va);
    *entry = Descriptor::page(frame, KERNEL_RW);
}
```

The entry was valid: other CPUs keep translating through the old frame from
their TLBs, and a valid entry overwritten with another output address
without break-before-make (S6c) can give them a mix of the old and the new
translation.

### S6b New translation tables

A new translation table is complete before it becomes reachable: every
entry is written, a store barrier (`DMB ISHST` or stronger) orders these
writes before the publishing store for every observer in the inner-shareable
domain (Arm 2022, chapters 5 and 8), and one store of the table descriptor
into the parent entry publishes the table. A table walk then sees the
mapping from before the change, the mapping from after it, or a fault. The
table walk unit is an observer of its own, whose reads the program order of
the writing CPU does not order (Arm 2022, chapter 9), and a lock around
table changes does not hide intermediate states from the table walkers of
other CPUs (Li et al. 2021). `TCR_EL1` sets the shareability and
cacheability of table walks (Arm 2024, section 7.2), and they are those of
the mapping through which the kernel writes the tables, so that the walks
read what the barrier orders.

**Violation.**

```rust
pub fn install_table(
    parent: &mut Table,
    index: usize,
    frames: &mut Frames,
) -> Result<Frame, Error> {
    let frame = frames.allocate()?; // holds stale descriptors
    parent.set(index, Descriptor::table(frame)); // reachable from here on
    frames.zero(frame);
    Ok(frame)
}
```

Between the two writes, a walk on another CPU can follow the new descriptor
into stale entries and translate to frames that this address space never
owned.

### S6c TLB invalidation

An unmap writes an invalid entry. The CPU completes the write with
`DSB ISH`, invalidates the TLB entries of the affected addresses and ASIDs
on every CPU that may hold them, waits for the invalidation to complete, and
executes `ISB` before it relies on the change itself. Entries that another
CPU may hold are invalidated with the inner-shareable form of `TLBI`, which
is broadcast to the other CPUs of the inner-shareable domain, and `DSB ISH`
waits for that invalidation and completes it (Arm 2022, chapter 6); Arm
gives the sequence `STR`, `DSB ISH`, `TLBI VAAE1IS`, `DSB ISH`, `ISB` (Arm
2024, section 8.1). Entries that, by the state that the kernel records, only
the executing CPU may hold, such as those of an address space whose root and
ASID no other CPU has had in `TTBR0_EL1`, need only the local form of
`TLBI`, which is not broadcast, and a `DSB`. A CPU may walk the tables of
the root and ASID in its `TTBR0_EL1` at any time (Simner et al. 2022), so it
joins this record before it loads them, with a `DSB ISH` between the two,
and leaves it only after its `TTBR0_EL1` no longer holds them and it has
invalidated their entries with the local form of `TLBI` and a `DSB`; the
unmapping CPU reads the record after the `DSB ISH` that completes its write.
If either barrier is missing, the two CPUs form the store-buffering case of
S2, and the unmapping CPU can miss a CPU whose walk reads the old entry. A
TLB may also hold entries of any level of the walk (Simner et al. 2022), so
when the invalid entry is a table descriptor, the invalidation covers the
cached entries of every level for the addresses below it. A change of the
attributes of a valid entry, such as its permissions, is followed by the
same invalidation (Arm 2024, chapter 8). Where the architecture requires
break-before-make for a change from one valid entry to another, as for a
change of the output address, the entry is first unmapped by this sequence,
and only then is the new entry written, with the barriers stated at the
start of this section; a change of permissions alone needs no
break-before-make (Simner et al. 2022). What the old entry mapped, including
a table that a table descriptor pointed to, is reused only as S3 states.

**Violation.**

```asm
    str     xzr, [x5]       // unmap: clear the leaf entry
    tlbi    vaae1is, x0     // invalidate the VA on every CPU
    dsb     ish
    isb
```

Without a `DSB` between the store and the `TLBI`, the invalidation can
complete before the table walkers see the cleared entry, and a walk on
another CPU can load the old entry into its TLB again.

### S6d User memory

The kernel's correctness does not depend on what EL0 writes into memory that
it can write, which includes shared buffers and the indices and descriptors
in them. The kernel reads such memory only by copying it once into memory
that EL0 cannot write, validates the copy, and from then on uses only the
copy.

**Violation.**

```rust
pub fn submit(ring: &SharedRing, queue: &mut Queue) -> Result<(), Error> {
    if ring.head() >= RING_SLOTS {
        return Err(Error::InvalidArgument);
    }
    queue.push(ring.slot(ring.head())) // reads the head again
}
```

A thread on another CPU can change the head between the check and the
second read, so the kernel uses a slot that it never validated.

## References

- Arm Limited. "Learn the architecture - AArch64 memory management Guide."
  Version 1.4, document ID 101811_0104_01_en, 2024. Chapter 7, "Translation
  granule", and chapter 8, "Translation Lookaside Buffer maintenance".
  <https://documentation-service.arm.com/static/670e4dc89fbc7343d3e4cee1>
- Arm Limited. "Learn the architecture - Memory Systems, Ordering, and
  Barriers." Version 1.0, document ID 102336_0100_01_en, 2022. Chapters 4 to
  6 and 8 to 11.
  <https://documentation-service.arm.com/static/62a304f231ea212bb662321d>
- S.-W. Li, X. Li, R. Gu, J. Nieh, J. Z. Hui. "A Secure and Formally Verified
  Linux KVM Hypervisor." IEEE Symposium on Security and Privacy, 2021.
  <https://www.cs.columbia.edu/~nieh/pubs/ieeesp2021_kvm.pdf>
- X. Li, X. Li, C. Dall, R. Gu, J. Nieh, Y. Sait, G. Stockwell. "Design and
  Verification of the Arm Confidential Compute Architecture." OSDI 2022.
  <https://www.cs.columbia.edu/~nieh/pubs/osdi2022_cca.pdf>
- seL4 Foundation. "Frequently Asked Questions." Accessed 2026.
  <https://sel4.systems/About/FAQ.html>
- B. Simner, A. Armstrong, J. Pichon-Pharabod, C. Pulte, R. Grisenthwaite,
  P. Sewell. "Relaxed virtual memory in Armv8-A." European Symposium on
  Programming (ESOP), 2022. Extended version, arXiv:2203.00642.
  <https://arxiv.org/abs/2203.00642>
- R. Tao, J. Yao, X. Li, S.-W. Li, J. Nieh, R. Gu. "Formal Verification of a
  Multiprocessor Hypervisor on Arm Relaxed Memory Hardware." SOSP 2021.
  <https://www.cs.columbia.edu/~nieh/pubs/sosp2021_vrm.pdf>
