# Provable Rust subset

This convention states how the code of the modules that proofs are to cover
is written: which constructs to avoid because the pinned extraction tools
reject them, leave them unproved or fail on them in Lean, what to write
instead, and the design rules that keep the code provable.
[Formal verification](../formal-verification.md) describes the tools, the
qualification of code shapes and the proof gate. The
[SMP design rules](smp.md) bind these modules as they bind all code.

## Scope

The convention binds the code of the following modules. Their source paths
are not fixed yet, so each is named by its role; the `contract.md` of its
component names its source paths.

| Module | Role |
| --- | --- |
| fdt | Bounded parsing of the device tree that the firmware hands to the kernel |
| Page-table logic | Building and changing translation tables: descriptors, attributes, address arithmetic and how each write changes the mapping; the stores into live tables and the barrier, cache and TLB instructions are in adapters |
| Objects | The object table: slots, generations, boot-time capacities, metadata quotas and write-set transactions |
| Context `validate` | The validation of a thread's saved user context before the kernel restores it |
| Scheduling ledger | The budget ledger of scheduling: budgets, charges and replenishment, apart from run-queue selection and preemption |
| Capabilities | Per-process capability tables: lookup, copy, delegation and revocation |
| IPC | Call, receive and reply, one-shot reply rights, capability transfer and budget lending |
| Waits and notifications | Notifications, timeouts and wait sets |
| ABI dispatch | The dispatch of system calls from operation numbers to their handlers |
| Loader `validate` | The validation of a segment description before the kernel maps it |
| Creation | The creation of endpoints, notifications and child processes, with the charge to the caller's metadata quota |
| VM | VM objects of a single thread: `reserve`, `commit`, `decommit`, `mprotect` and `release` |
| Lifecycle state machine | The life of a process: alive, dying, dead and reaped |

- The rules apply from the first change of such a module, whether or not a
  proof target is registered for it, and to new, ported and redesigned code
  alike ([porting](porting.md#rules-for-a-port)).
- The list holds the components for which the project's verification plan,
  kept in its coordination records, plans a specification, and it changes
  when that plan changes.
- The `Extractability` section of each component's `contract.md` states
  which of its code follows this convention
  ([component documents](documentation.md#component-documents)).

## Constructs and alternatives

The constructs below stop extraction, leave unproved declarations or fail in
Lean with the pinned tools. Each item states what the tools do with it, a
minimal example, the alternative to write instead and its qualification
reference. Paths in the prototype tree are at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, and paths in the CAS
project at `cas-project@bc5e9dea08b4b8ae5e7a4f72c56ca20b311544e6`.

**Tool versions.** The outcomes were observed in the prototype tree, or are
recorded by the qualification cases and the Code shapes section of the CAS
project, with Lean 4.31.0, Charon `798016509139eb51f0d764645f76d068d34ba5f6`
and Aeneas `d119a474f852781f8ae88a85424f2f8ba8407b82` with reviewed patches.
The prototype pins them in `verification/object-waits/toolchain.json` and
`verification/object-waits/lean-toolchain`, the CAS project in
`verification/toolchain.json`. R3 alone has no observed outcome of its own.
Other pins can change an outcome, and qualification
([tools](../formal-verification.md#tools)) checks again only the shapes that
its cases record.

**Qualification references.** Each item names the nearest cases, where there
are any, of `verification/qualification/cases.json` and the rules of the
section "Code shapes" of `docs/formal-verification.md` in the CAS project.
None of the seven items has a corresponding case there, and each item says
so.

**Loop shapes.** The alternatives replace adapters and callbacks with loops,
and the tools accept only some loop shapes. Following the Code shapes
section, every alternative below keeps to these:

- A function has at most one loop; a nested loop goes into a helper
  function.
- Returning from inside the loop is accepted (`series-summer`).
- A function whose loop uses `?` leaves before the loop only through `?`,
  and the loop sits at the top level of its body, not inside an `if`,
  `if let` or `match` arm. Checks and shortcuts that return early stay in a
  function without a loop that calls the helper holding the loop
  (`return-before-loop`, `flag-before-loop` and `loop-in-branch` are
  rejected; `returns-then-helper` translates).
- Slices are walked by index loops (`index-loop`), and a loop condition
  calls a function rather than a macro such as `matches!`.
- `match` takes the place of combinators with closures.

R1 to R3 use the types below. Their integer keys, like the slot indices of
R5, keep the examples small; in the listed modules such relations are the
references of [rule 3](#3-flat-relations-and-one-kernel-root).

```rust
#[derive(Clone, Copy)]
pub struct Activation {
    pub key: u64,
    pub legacy: bool,
}

pub struct Thread {
    pub process: u64,
    pub alive: bool,
}
```

### R1 Function items as values

A function item passed as a value when its signature has a late-bound
lifetime, which makes it higher-ranked: for example `Option::is_some`, with
the signature `for<'a> fn(&'a Option<T>) -> bool`, given to `Iterator::any`.

**Outcome.** Rejected by Aeneas. It stops with an error at an unsupported
constraint between the higher-ranked lifetime and a free lifetime, and the
extraction that contains the call generates no Lean. This stopped the
extraction of the activation entries in the prototype's
`src/objects/activation.rs`. A closure in the place of the function item
translates, but `any` remains (R2) and the closure is R4.

**Example.**

```rust
pub fn any_active(active: &[Option<Activation>]) -> bool {
    active.iter().any(Option::is_some)
}
```

**Alternative.** Methods are called directly, dispatch is a `match`, and no
function is bound to a local or passed as a value.

```rust
pub fn any_active(active: &[Option<Activation>]) -> bool {
    let mut index = 0;
    while index < active.len() {
        match active[index] {
            Some(_) => return true,
            None => index += 1,
        }
    }
    false
}
```

**Qualification.** No corresponding case. Nearest: `function-pointers`
(rejected). The Code shapes rule that a method is called directly, not
through a local bound to it, notes that no case records this shape.

### R2 `Iterator::any`

**Outcome.** Translated with an unproved external declaration. The library
of the tools has no model of `any`, so the call becomes a call of an
external function, which the generated Lean declares as an axiom. A theorem
must hold for every interpretation of such a function
([trusted boundary](../formal-verification.md#trusted-boundary)), so no
property that depends on the result of `any` can be proved unless a reviewed
model of it is registered, which adds a trusted item; the alternative needs
none. The prototype searched its activation and thread tables with it, in
`src/objects/activation.rs` and `src/objects/lifecycle.rs`.

**Example.** The closure is R4.

```rust
pub fn has_survivor(threads: &[Thread], process: u64) -> bool {
    threads.iter().any(|thread| thread.process == process && thread.alive)
}
```

**Alternative.**

```rust
pub fn has_survivor(threads: &[Thread], process: u64) -> bool {
    let mut index = 0;
    while index < threads.len() {
        if threads[index].process == process && threads[index].alive {
            return true;
        }
        index += 1;
    }
    false
}
```

**Qualification.** No corresponding case. Nearest: `iterator-adapters`
(ill-typed: the library has no model of `map` and `collect`) and its index
form `index-loop` (translated). Code shapes: index loops instead of iterator
adapters.

### R3 `Iterator::flatten`

**Outcome.** Not observed on its own: the prototype extractions whose roots
call it stopped earlier, at R1 and R5. `flatten` is, like `map` and
`collect`, a provided method of `Iterator` that the library of the tools
does not model, and for those two the case `iterator-adapters` records
generated Lean that does not type-check. A call of `flatten` therefore
leaves the generated Lean ill-typed or becomes a call of an external
function without a model, as for `any`; either way no property that depends
on it can be proved. The prototype skipped the empty slots of its activation
table with it, in `src/objects/activation.rs` and
`src/objects/lifecycle.rs`.

**Example.**

```rust
pub fn holds_legacy(active: &[Option<Activation>]) -> bool {
    for activation in active.iter().flatten() {
        if activation.legacy {
            return true;
        }
    }
    false
}
```

**Alternative.** Each element is matched in an index loop.

```rust
pub fn holds_legacy(active: &[Option<Activation>]) -> bool {
    let mut index = 0;
    while index < active.len() {
        match active[index] {
            Some(activation) => {
                if activation.legacy {
                    return true;
                }
            }
            None => {}
        }
        index += 1;
    }
    false
}
```

**Qualification.** No corresponding case. Nearest: `iterator-adapters` and
`index-loop`; `iterator-arena` (translated) writes nested iteration as
stages over an explicit stack, without closures. Code shapes: index loops
instead of iterator adapters, and nested iterators as stages in one vector.

### R4 Closures as callbacks

A closure given to a combinator such as `Option::filter`,
`Option::is_some_and` or `Result::map_err`, to an iterator adapter, or to a
parameter of an `Fn`, `FnMut` or `FnOnce` type.

**Outcome.** Translated with unproved external declarations: combinators
such as `Option::filter` and `Option::and_then` are external declarations,
and each closure becomes a function of its own without an inventory key, so
a target can neither prove it nor list it as unclosed. A parameter of type
`impl FnOnce(&mut Self) -> T` is a Lean-side failure: the generated Lean
does not type-check. The prototype used such closures in the table searches
of R2 and R3 and in combinators such as `map_err`, in
`src/objects/activation.rs`.

**Example.**

```rust
pub fn owner(pool: &Pool, process: u64) -> Result<usize, Error> {
    pool.process_index(process).map_err(|_| Error::InvalidState)
}
```

**Alternative.**

```rust
pub fn owner(pool: &Pool, process: u64) -> Result<usize, Error> {
    match pool.process_index(process) {
        Ok(index) => Ok(index),
        Err(_) => Err(Error::InvalidState),
    }
}
```

A callback becomes a generic parameter bounded by a crate-private trait
whose `&mut self` methods the function calls, or the caller drives the loop
and the callee returns what it needs next.

**Qualification.** No corresponding case. Nearest: `option-combinators`
(translated; `Option::filter` is an external declaration),
`closure-parameter` (ill-typed), and for callbacks `series-summer` and
`iterator-arena` (translated). Code shapes: `match` rather than combinators
with closures, no `FnOnce(&mut Self)` parameters, shared interfaces as
crate-private traits, and iterator stages that hand a call back to their
driver.

### R5 Borrow joins on the stop path

The borrow join at the conditional update of the prototype's stop path, and
shapes like it: a function that holds a mutable borrow of a table entry
across an early return and a write to another field of `self`, and then
updates an entry of another table through a mutable borrow inside a branch
whose arms meet again before further code.

**Outcome.** Rejected by Aeneas. In `stop_thread` in the prototype's
`src/objects/lifecycle.rs`, Aeneas cannot match the borrow contexts at the
conditional update of the process state, as the prototype's
`verification/group-stop/README.md` records; this stopped the extraction of
the entries that reach it, such as those that terminate a process. The
record locates the failure only in that function, which reached the entries
through `as_mut().unwrap()`; the reduced shape below is not known to fail on
its own.

**Example.** The shape of that function, reduced:

```rust
impl Pool {
    fn stop_thread(&mut self, index: usize, reason: ExitReason) {
        let entry = &mut self.threads[index];
        if entry.state == ThreadState::Dead {
            return;
        }
        entry.exit = Some(reason);
        self.stopped += 1;
        let process = entry.process;
        if !self.has_survivor(process) {
            let owner = &mut self.processes[process];
            if owner.state == ProcessState::Alive {
                owner.state = ProcessState::Dying;
            }
        }
        self.finish_thread(index);
    }
}
```

**Alternative.** `Copy` values are read into locals, every write indexes the
table again, and the conditional update moves into a helper whose `match`
arms all end the helper.

```rust
impl Pool {
    fn stop_thread(&mut self, index: usize, reason: ExitReason) {
        let process = match self.threads[index].state {
            ThreadState::Dead => return,
            _ => self.threads[index].process,
        };
        self.threads[index].exit = Some(reason);
        self.stopped += 1;
        if !self.has_survivor(process) {
            self.close_admission(process);
        }
        self.finish_thread(index);
    }

    fn close_admission(&mut self, process: usize) {
        match self.processes[process].state {
            ProcessState::Alive => {
                self.processes[process].state = ProcessState::Dying;
            }
            _ => {}
        }
    }
}
```

The reviewed Aeneas patch that the pins carry translates
`Option<&mut T>::unwrap` for a borrow-free `T`; the alternative needs
neither that nor the join. Because the failing shape is not isolated, the
alternative is the conservative form: it keeps to the accepted shapes, but
no case confirms it.

**Qualification.** No corresponding case. Nearest: `moving-if-join`
(rejected: after an earlier branch of the same kind, a branch whose arms
meet again, one arm moving an owned value and the other borrowing it for a
call with `?`) and `moving-if-helper` (translated: that later branch in a
helper whose arms both return). Code shapes: the later of two such branches
goes into a helper whose arms both return.

### R6 Enumeration names across targets

**Outcome.** Lean-side failure. Every enumeration is translated with a
`Discriminant` instance that is named after the last component of its path
and lies outside the generated namespace. Two targets that each define an
enumeration of the same name produce two instances of the same name, such as
`instDiscriminantErrorIsize` for two enumerations `Error`, and a Lean module
that imports both, such as a composition proof, fails at the import.

**Example.**

```rust
pub mod objects {
    pub enum Error {
        Stale,
        Exhausted,
    }
}

pub mod capabilities {
    pub enum Error {
        Stale,
        RightsExceeded,
    }
}
```

**Alternative.** The name of an enumeration is unique among the targets
whose generated code one Lean module may import together.

```rust
pub mod objects {
    pub enum ObjectError {
        Stale,
        Exhausted,
    }
}

pub mod capabilities {
    pub enum CapabilityError {
        Stale,
        RightsExceeded,
    }
}
```

Unique names are not enough on their own: external declarations that two
targets both make also lie outside the generated namespace, so the generated
code of such targets cannot be imported into one Lean module at all. A proof
about functions of two components therefore extracts them in one target, or
the target that reaches functions which another target proves lists them as
`unclosed` and states its theorems in terms of them
([proof targets](../formal-verification.md#proof-targets)).

**Qualification.** No corresponding case. Nearest: `series-summer` and
`series-summer-owned` (translated, with proofs), whose enumerations `Halt`
and `SeriesStop` have distinct names. The rule is the paragraph of the Code
shapes section on `Discriminant` instances and external declarations.

### R7 Private enumerations in Lean

**Outcome.** Lean-side failure. The `discriminant` attribute of the Aeneas
library, which generated code puts on every enumeration, does not support an
enumeration that is private in Lean: its declaration fails with
`invalid scope`, and Lean's error recovery leaves `sorryAx` in the
declarations that depend on it. The prototype's
`verification/group-stop/README.md` records private enumerations as
unsupported. Generated code declares no enumeration private, since it puts
its declarations in a `public section`; the construct arises in hand-written
Lean that generated code uses, such as models and reviewed external
declarations. In a Lean `module` file, a declaration outside a
`public section` that is not marked `public` is private as well (Lean
4.31.0, `src/Lean/Elab/DeclModifiers.lean`).

**Example.**

```lean
module
public import Aeneas

namespace Model

@[discriminant isize]
private inductive Phase where
  | idle
  | running

end Model
```

**Alternative.** The enumeration is public: in a `module` file it is
declared inside a `public section`, as the hand-written models of the CAS
project are (`verification/Casxi/Models/Arc.lean`), and its name follows R6.

```lean
module
public import Aeneas

@[expose] public section

namespace Model

@[discriminant isize]
inductive Phase where
  | idle
  | running

end Model
```

**Qualification.** No corresponding case and no near one: no case and no
Lean file of the CAS project declares an enumeration `private`, and the Code
shapes section has no rule for it.

## Provable design rules

Each rule has a statement, a violation with the reason why it fails, and the
alternative form.

### 1. Check, then execute

Every check of an operation completes before its first write. The write
phase fails only with the failures that the contract lists, capacity and
quota, and such a failure restores the state from before the operation. The
rule follows the checking and executing phases of seL4, whose execution
phase never fails (Klein et al. 2014).

**Violation.**

```rust
pub fn copy_cap(
    table: &mut CapTable,
    from: usize,
    to: usize,
    rights: u32,
) -> Result<(), Error> {
    let source = table.get(from)?;
    table.set(to, source.with_rights(rights));
    if source.rights & rights != rights {
        return Err(Error::RightsExceeded);
    }
    Ok(())
}
```

The rights check runs after the write, so a refused copy leaves a capability
with more rights than its source.

**Alternative.**

```rust
pub fn copy_cap(
    table: &mut CapTable,
    from: usize,
    to: usize,
    rights: u32,
) -> Result<(), Error> {
    let source = table.get(from)?;
    if source.rights & rights != rights {
        return Err(Error::RightsExceeded);
    }
    if table.is_occupied(to) {
        return Err(Error::SlotOccupied);
    }
    table.set(to, source.with_rights(rights)); // the only write
    Ok(())
}
```

### 2. No allocation at run time

Capacities are fixed at boot. An operation takes its storage from a pool of
that capacity and charges the metadata it uses to the quota of the calling
domain. The seL4 kernel likewise allocates nothing dynamically and hands
memory to user level as untyped memory (Klein et al. 2014).

**Violation.**

```rust
pub fn create_endpoint(kernel: &mut Kernel) -> Result<usize, Error> {
    kernel.endpoints.push(Box::new(Endpoint::new()));
    Ok(kernel.endpoints.len() - 1)
}
```

The endpoint comes from a heap that grows at run time and is charged to no
one, so neither a capacity bound nor the conservation of quotas can be
stated.

**Alternative.** `ObjectRef` is the reference of rule 3. Object creation
first reserves the caller's metadata quota
([kernel objects](../architecture.md#kernel-objects-and-capabilities)): the
check of the caller's own quota comes before the check of the shared
capacity, and the quota is charged before the slot is taken.

```rust
pub fn create_endpoint(
    kernel: &mut Kernel,
    caller: ObjectRef,
) -> Result<usize, Error> {
    kernel.quotas.check(caller, ENDPOINT_METADATA)?; // checks the generation
    let slot = match kernel.endpoints.free_slot() {
        Some(slot) => slot,
        None => return Err(Error::Capacity),
    };
    kernel.quotas.charge(caller, ENDPOINT_METADATA); // the first write
    kernel.endpoints.occupy(slot, Endpoint::new(), caller);
    Ok(slot)
}
```

### 3. Flat relations and one kernel root

Objects refer to each other only by `(pool, slot, generation)` indices.
Structural invariants are statements quantified over whole tables, and every
operation has a lemma that it preserves well-formedness, separate from its
functional theorem. Every handler entry receives the one `&mut` reference to
the kernel root, and the listed modules use no `static mut`. Atmosphere
keeps the permissions of a subsystem in one flat table in the same way and
proves a preservation lemma for each operation apart from the functional
proof (Chen et al. 2025).

**Violation.**

```rust
pub struct Process {
    pub live_threads: u32,
}

pub struct Thread {
    pub process: *mut Process,
}

pub fn exit_thread(thread: &Thread) {
    unsafe { (*thread.process).live_threads -= 1 };
}
```

The relation is a pointer: the write reaches the process past the kernel
root and the tables that the invariants quantify over, and nothing rejects
the pointer after the process slot is reused.

**Alternative.** `PoolId` and `Generation` stand for the pool and generation
types of the object table, whose widths the kernel design fixes.

```rust
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ObjectRef {
    pub pool: PoolId,
    pub slot: u32,
    pub generation: Generation,
}

pub struct Thread {
    pub process: ObjectRef,
}

pub fn exit_thread(
    root: &mut KernelRoot,
    thread: ObjectRef,
) -> Result<(), Error> {
    let process = root.threads.get(thread)?.process; // checks the generation
    let entry = root.processes.get_mut(process)?;
    entry.live_threads -= 1;
    Ok(())
}
```

### 4. Bounded work per entry

The contract states a bound for every loop of every entry. A long
operation, such as cascading revocation or the destruction of a process,
runs in steps of bounded work; its progress is stored in the object it works
on, and the next step continues from there. seL4 keeps long operations
consistent in the same way, with their progress in the objects (Klein et al.
2014).

**Violation.**

```rust
pub fn revoke(table: &mut CapTable, slot: usize) {
    while let Some(child) = table.first_child(slot) {
        revoke(table, child);
        table.clear(child);
    }
}
```

One call removes the whole derivation tree below `slot`, so the work of the
entry has no bound that the contract could state.

**Alternative.**

```rust
/// Removes at most `REVOKE_BATCH` capabilities derived from `slot`.
/// `next_leaf` returns the leaf below `slot` that the traversal order of the
/// contract removes next and scans at most `CAP_CAPACITY` slots, so a step
/// visits at most `REVOKE_BATCH * CAP_CAPACITY` slots; the capabilities that
/// remain below `slot` are the progress, stored in the table.
pub fn revoke_step(table: &mut CapTable, slot: usize) -> Progress {
    let mut removed = 0;
    while removed < REVOKE_BATCH {
        match table.next_leaf(slot) {
            Some(leaf) => table.clear(leaf),
            None => return Progress::Complete,
        }
        removed += 1;
    }
    Progress::Pending
}
```

### 5. Abstract information in concrete fields

Information that a proof needs about the state, such as the derivation
relation, generations and the owner of a quota charge, exists in concrete
fields; otherwise the theorem takes it as an explicit parameter together
with its relation to the state.

**Violation.**

```rust
pub struct Capability {
    pub object: ObjectRef,
    pub rights: u32,
}
```

Revocation withdraws everything derived from a grant, but no field records
from which capability this one was derived, and the translation holds only
the fields that exist.

**Alternative.**

```rust
pub struct Capability {
    pub object: ObjectRef,
    pub rights: u32,
    pub parent: Option<CapRef>,
    pub charged_to: ObjectRef,
}
```

### 6. Compile-time guards

Premises that a proof needs and that the translation does not show, such as
a handle type that is neither `Clone` nor `Copy`, or a constructor that other
modules cannot call, are fixed at compile time: by an assertion that fails
the build once the premise breaks, and by private fields that leave the
constructor to the defining module. Theseus guards the premises of its
proofs with such assertions (Ijaz et al. 2024).

**Violation.**

```rust
#[derive(Clone, Copy)]
pub struct ReplyRight {
    pub slot: u32,
    pub generation: Generation,
}
```

The proof that a reply completes at most once assumes that a reply right
cannot be duplicated, but `Copy` duplicates it silently and public fields
let any module forge one; the translation shows neither.

**Alternative.**

```rust
pub struct ReplyRight {
    slot: u32,
    generation: Generation,
}

// Does not compile once `ReplyRight` implements `Clone`, and so `Copy`.
const _: () = {
    trait AmbiguousIfClone<A> {
        const CHECK: () = ();
    }
    impl<T: ?Sized> AmbiguousIfClone<()> for T {}
    impl<T: ?Sized + Clone> AmbiguousIfClone<u8> for T {}
    <ReplyRight as AmbiguousIfClone<_>>::CHECK
};
```

### 7. No shape-changing `cfg`

Platforms are not told apart by a `cfg` that changes the shape of the code.
A platform difference is a value of the boot-time configuration that the
code branches on, and numeric configuration consists of named constants that
proofs do not unfold. seL4 replaced `#ifdef` by `if` so that one proof
covers both cases, and gives numeric configuration symbolic names that its
proofs do not unfold (Klein 2025).

**Violation.**

```rust
pub fn map_ram(tables: &mut Tables, ram: Range) -> Result<(), Error> {
    #[cfg(board = "pi5")]
    return map_blocks(tables, ram);
    #[cfg(not(board = "pi5"))]
    return map_pages(tables, ram);
}
```

Each board's image compiles a different body, so a proof of one extraction
says nothing about the other.

**Alternative.**

```rust
pub fn map_ram(
    tables: &mut Tables,
    ram: Range,
    layout: &Layout,
) -> Result<(), Error> {
    if layout.block_mappings {
        map_blocks(tables, ram)
    } else {
        map_pages(tables, ram)
    }
}
```

### 8. No interior mutability

The listed modules use no interior mutability. Per-CPU state comes in by an
explicit `&mut` argument. Finding the state of the executing CPU and masking
interrupts happen in an adapter outside the proof target, which the
component lists among its open obligations. Aeneas spares memory reasoning
only for code without interior mutability and `unsafe` (Ho and Protzenko
2022).

**Violation.**

```rust
use core::cell::Cell;

pub struct Ledger {
    pub charged: Cell<u64>,
}

pub fn charge(ledger: &Ledger, amount: u64) {
    ledger.charged.set(ledger.charged.get() + amount);
}
```

The update goes through a shared reference, which the translation does not
follow, and the signature hides that `charge` changes the ledger.

**Alternative.**

```rust
pub struct Ledger {
    pub charged: u64,
}

/// A handler entry in the proof target: it receives the kernel root, as
/// rule 3 states, and the ledger of the executing CPU.
pub fn tick(root: &mut KernelRoot, ledger: &mut Ledger, amount: u64) {
    root.ticks += 1;
    ledger.charged += amount;
}

/// The adapter, outside the proof target.
pub fn tick_entry(root: &mut KernelRoot, amount: u64) {
    let mut cpu = percpu::enter_masked();
    tick(root, cpu.ledger_mut(), amount);
}
```

`enter_masked` masks local interrupts and returns the only token of the
executing CPU, and `ledger_mut(&mut self)` lends the ledger for no longer
than the token lives, so no second reference to it can exist.

### 9. Unsafe sites

Every `unsafe` site that a listed module contains or calls is an open
obligation of its component, and its row in the `Open obligations` section
of the contract states whether the site reads or writes state that a proof
covers.

**Violation.**

```rust
/// Stores a descriptor that the page-table logic computed into a live
/// translation table.
///
/// # Safety
///
/// `table` points to a live table of `ENTRIES` descriptors, and
/// `index < ENTRIES`.
pub unsafe fn store_descriptor(
    table: *mut u64,
    index: usize,
    descriptor: u64,
) {
    // SAFETY: the caller guarantees the table and the index.
    unsafe { table.add(index).write_volatile(descriptor) };
}
```

The site writes the translation tables, whose contents the proofs of the
page-table logic describe, but nothing records it, so a proof that relies on
the tables changing only as the proved code computes rests on a premise that
nobody checks.

**Alternative.** The same site, with its row in `Open obligations`; Aeneas
does not translate it, so the row names what covers it outside the
sequential refinement:

```markdown
| Obligation | Kind | Verified state | Carrier |
| --- | --- | --- | --- |
| `store_descriptor` | `unsafe` volatile write | Writes the translation tables that the page-table logic describes | Lifted when the architecture layer proves translation-table stores |
```

## Constructs the tools do not support

- This convention covers the constructs of the list and the shape rules
  stated above, such as the loop shapes. They are coding rules: new code
  avoids the listed constructs and follows the shape rules, code taken from
  the prototype tree is brought to them in the change that ports it, and
  merged code is brought to them as the next two points state.
- The alternatives of R1 to R3 and R5, and the R4 alternative for a closure
  given to a combinator or an iterator adapter, are local: they change only
  function bodies, may add private helper functions to the same module, and
  keep the signatures, data representations, return values, error codes,
  state changes and loop bounds that the contract states. The R4
  alternative for a callback parameter, a generic parameter bounded by a
  crate-private trait or a loop that the caller drives, changes the
  interface between caller and callee: new code is written that way from
  the start, and in merged code it is a design change. R6 renames an
  enumeration without changing its values or representation, but every
  signature and proof statement that names the type changes with it: new
  code takes a unique name from the start, and a rename of merged code is a
  design change. R7 concerns hand-written Lean only, and a change under it
  is a change of the statements or proofs that contain the enumeration. A
  change that needs another data representation, object relation or
  interface is a design change, not a rewrite under this convention.
- A rewrite of merged code preserves behaviour. It brings code to a local
  form that this convention covers, such as a local alternative of the list
  or a loop shape above, or makes a local change that a named proof
  obligation needs, such as moving a loop into a helper function to state
  its invariant. It is a change of its own and changes no specification,
  proof statement, external declaration, axiom or proof. It changes only
  the bodies of the functions that it names and may add private helper
  functions of the same module that only those functions call. The function
  bodies from before the rewrite are copied verbatim into a `#[cfg(test)]`
  child module of the module that defines them, with only their names
  changed and the calls among the copies renamed to the copies.
  Differential tests run the rewritten code and the copy on the same
  inputs, which reach every branch of both bodies, run every loop zero
  times, once and as often as the contract bound allows, and include the
  frozen legacy test vectors of the contract; they compare return values,
  error codes and the changes of the state fields that the contract lists.
  They show that the old and the new code agree, not that either is correct
  ([testing](testing.md#independent-evidence)). Regression tests check
  inputs against expected values from an independent source, such as the
  frozen legacy test vectors of the contract, and never take an output of
  the copy as an expected value. When the rewritten code and the copy
  disagree, the result that the specification gives for the input decides:
  if it agrees with the copy, the rewrite is wrong; otherwise the old
  behaviour breaks the contract, and its fix changes behaviour and is not a
  rewrite. After the affected target is first proved, a change that changes
  no proof removes the copy and the differential tests; the regression
  tests stay.
- A rejection that this convention does not cover, and an external
  declaration without a model that this convention does not cover and that a
  proof needs, are first checked against the tool configuration: versions,
  sysroot, MIR and builtins. If one remains, it keeps its diagnostic and is
  reported, and the change stops there without working around it. For each
  such construct, one of three choices is made and recorded in the project's
  coordination records: the tools are repaired and pass qualification again;
  the construct joins this list with its alternative and a qualification
  case; or, where a proof of merged code meets it and no local alternative
  exists, a design change removes it.

## Planned mechanical checks

Four checks of the listed modules are planned as part of
`cargo xtask check`:

1. no `static mut` item;
2. no interior-mutability type: `Cell`, `RefCell`, `UnsafeCell`, `OnceCell`
   or another type of `core::cell` that provides interior mutability, and no
   atomic type of `core::sync::atomic`;
3. no `cfg` attribute outside an allowlist, which admits `#[cfg(test)]` on
   the unit-test modules that [testing](testing.md#layout) places next to
   the code;
4. compile-fail negative tests of the compile-time guards of rule 6: each
   test changes a guarded type, for example by deriving `Clone` for a handle
   type, and fails the check when the build still succeeds.

Until the checks exist, and for what they do not see, such as a type that
wraps an `UnsafeCell`, a `cfg_attr` attribute or the `cfg!` macro, review
applies rules 3 and 6 to 8.

## References

- X. Chen, Z. Li, J. Zhang, V. Narayanan, A. Burtsev. "Atmosphere: Practical
  Verified Kernels with Rust and Verus." SOSP 2025.
  <https://mars-research.github.io/doc/2025-sosp-atmo.pdf>
- S. Ho, J. Protzenko. "Aeneas: Rust Verification by Functional
  Translation." Proceedings of the ACM on Programming Languages 6 (ICFP),
  Article 116, 2022. <https://arxiv.org/abs/2206.07185>
- R. Ijaz, K. Boos, L. Zhong. "Combining Type Checking and Formal
  Verification for Lightweight OS Correctness." arXiv:2501.00248, 2024.
  <https://arxiv.org/pdf/2501.00248>
- G. Klein. "The Next 700 Verified seL4 Platforms." seL4 Summit 2025.
  <https://sel4.systems/Summit/2025/slides/next-700.pdf>
- G. Klein, J. Andronick, K. Elphinstone, T. Murray, T. Sewell, R. Kolanski,
  G. Heiser. "Comprehensive Formal Verification of an OS Microkernel." ACM
  Transactions on Computer Systems 32(1), 2014.
  <https://trustworthy.systems/publications/nicta_full_text/7371.pdf>
- Lean 4, version 4.31.0. Source file `src/Lean/Elab/DeclModifiers.lean`,
  the visibility of declarations.
  <https://github.com/leanprover/lean4/blob/v4.31.0/src/Lean/Elab/DeclModifiers.lean>
