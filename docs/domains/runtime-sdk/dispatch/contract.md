# Dispatch contract

This page governs the code of the dispatch component of the
[runtime ABI and SDK](../README.md) domain. The component has two modules
of the core. The module `dispatch` decodes every native system call and
refuses those that the dispatch table does not serve, makes the checks that
come before those of an operation, writes the results of a call, and
composes every entry from EL0 into one transition, with the round trip of
its plans through the architecture crate and the return to EL0. The module
`loader` validates the requests that load an image into a child, segment by
segment and at the commit, and checks the loading part of the capacity
record at boot; it fixes the image window of every child. The operations
that the dispatch table reaches belong to their components: the
[capabilities](../../objects-capabilities/capabilities/contract.md),
[IPC](../../ipc-waits/ipc/contract.md),
[waits](../../ipc-waits/waits/contract.md),
[scheduler](../../scheduling/scheduler/contract.md),
[creation](../../objects-capabilities/creation/contract.md),
[VM](../../memory/vm/contract.md) and
[lifecycle](../../objects-capabilities/lifecycle/contract.md) components.
The entry from EL0 and the return to it, the classes of its exceptions and
the boot-bundle directory belong to the
[address-space](../../memory/address-space/contract.md) component; the
saved context of a thread and the writing of its results to the
[context](../../boot-platform/context/contract.md) component; the mapping
of a loaded image to the creation component; the parsing of ELF files to
the loader of the runtime of EL0
([Application entry and CRT](../README.md#application-entry-and-crt));
and the operation numbers, the registers of arguments and results and the
numeric codes of errors to the ABI inventory (planned). The observable
behaviour that these rules serve, with its evidence, is in the
[requirements](requirements.md), the other document of the component.

## Terms

- **The component.** One component with two modules, `dispatch` and
  `loader`. Other contracts call it the dispatch component or the dispatch
  of the ABI, and its module `dispatch` the dispatch of the core, or, in
  the address-space and scheduler contracts, the
  [composer of the return](../../memory/address-space/contract.md#terms);
  for the validation of loading requests and the loading part of the
  capacity record, they call the component the loading component.
- **ABI inventory.** The committed inventory of the native operations
  (planned): for each operation its number, the major version that added
  it, the registers of its arguments and results and the codes of its
  errors and outcomes
  ([system calls](../../../architecture.md#system-calls-and-the-abi)),
  which the dispatch table of the core and the ABI crate `krepi-abi` each
  hold: the
  [operation inventory](../README.md#the-operation-inventory) of the
  domain page. This page names the operations and fixes the rules of their
  dispatch.
- **System call.** An entry from EL0 of the class `Svc` of the
  [exception classes](../../memory/address-space/contract.md#exception-classes):
  an `SVC` in AArch64 state. Its **immediate** is bits 0 to 15 of the
  instruction-specific syndrome of `ESR_EL1`.
- **Registers of a call.** The values that the entry saved in the saved
  context of the current thread: `x8`, whose bits 0 to 15 hold the
  **operation number**; `x7`, the major **version** of the ABI for which
  the caller was built; `x0` to `x5`, the **argument registers**; and `x6`,
  the **reserved register**. The **result registers** are `x0`, which
  holds the **status**, and `x1` to `x5`, which hold the **results**.
- **Operation.** A row of the dispatch table: a version and a number with
  the entry of a component that serves them and the argument registers that
  it uses, in the order that the ABI inventory gives. The **dispatch
  table** is that of the running image: its production rows, and, in a
  test build only, its diagnostic rows.
- **Status.** `OK`, the status of success, or the code of an error: of
  this page, or of the contract of an operation, which the ABI inventory
  gives (planned).
- **Current thread.** The thread that a CPU runs, which the record of the
  CPU names, as the
  [address-space](../../memory/address-space/contract.md#terms) component
  states; an idle CPU has none.
- **Scheduler dispatch.** The interval in which a CPU runs one thread, from
  the `choose` that selects it to its stop, with its start and its
  deadline: a [dispatch](../../scheduling/scheduler/contract.md#terms) of
  the scheduler, not this component.
- **Transition.** What a CPU does from an exception taken from EL0, an
  interrupt pending at a return or the wake of an idle CPU, to its return
  to EL0, its wait or the halt of the system, with every exception masked.
  The architecture crate reads the time `now` once at its start
  ([ND-01](../../../security.md#nd-01)).
- **Plan.** What an entry of another component gives for the architecture
  crate to execute: a write plan of the
  [page-tables](../../memory/page-tables/contract.md#write-plans-and-publication)
  component, the release plan of an ASID of the
  [address-space](../../memory/address-space/contract.md#address-spaces-and-asids)
  component, or a frame plan of the
  [VM](../../memory/vm/contract.md#acknowledgement-and-reclamation)
  component. A plan is **in flight** from the entry that gives it to its
  acknowledgement.
- **Pending value.** `dispatch::Pending` (planned): what the dispatch gives
  the architecture crate with a plan and takes back with `resume`: the
  component whose entry gave the plan, the process whose cursor or progress
  holds it, and the time of the transition. Only the core forms one.
- **Again.** The end of a step of a long operation that has stored its
  progress in its object and has no result yet, which `kill` of the
  lifecycle component, `release` of the VM component and `revoke` of the
  capabilities component give.
- **Image.** An entry of the kind Image of the
  [boot-bundle directory](../../memory/address-space/contract.md#boot-bundle-directory).
- **Image window.** The virtual addresses of a child from `IMAGE_BASE` in
  which it maps its segments and its initial stack
  ([The image window](#the-image-window)).
- **Segment.** A range of bytes of an image with the virtual address, the
  bytes in memory and the access, R, RX or RW, at which a child maps it:
  the five arguments of `spawn_segment` of the creation component.
- **Plan of an image.** `loader::Plan` (planned): an image with the
  segments that `validate` has accepted for it.
- **Private pages.** The pages of the memory of the RW segments of an image
  and of its initial stack.
- **Loading part.** Bytes 64 to 91 of the capacity record, which hold the
  limits of loading ([Loading configuration](#loading-configuration)).
  **Limits** are `loader::Limits` (planned), the seven values of the
  loading part.
- **Composer.** This component composes every entry from EL0: it calls the
  entries of the other components of the core in the order of
  [Composition of a transition](#composition-of-a-transition).
- **Boot wiring.** The code of a board crate that runs on the boot CPU
  before the first entry from EL0, as in the
  [objects](../../objects-capabilities/objects/contract.md#terms) and
  [address-space](../../memory/address-space/contract.md#terms) contracts.
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.

## Entry points

The entries of the core are in the modules `dispatch` and `loader` of
`krepi-kernel` (planned). No entry of this page is an operation of the ABI
inventory: `syscall` decodes every operation of the table, and each
operation is the entry of its own component. The rights that each needs
are listed in [Rights](#rights). The first row holds constants.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `dispatch::VERSION`, `loader::IMAGE_BASE`, `IMAGE_END`, `MAX_WINDOW_PAGES`, `MAX_SEGMENTS` and `MAX_BUNDLE_PAGES` (planned) | Constants, host-testable | The entries of this page; the module `creation` (planned), for the image window and the segments of a plan; the ABI inventory, which gives the version and `IMAGE_BASE` to EL0 (planned) | None | [Operation numbers and versions](#operation-numbers-and-versions), [The image window](#the-image-window), [Loading configuration](#loading-configuration) |
| `dispatch::entry` (planned), with the value types `dispatch::Event`, `dispatch::Transition` and `dispatch::Pending` | Write entry, host-testable; composes the entries of other components and gives plans | `el0_dispatch` of each kernel image (planned): at each exception taken from EL0, at an interrupt that is pending before a return, and at the wake of an idle CPU | None | [Composition of a transition](#composition-of-a-transition), [Results](#results) |
| `dispatch::syscall` (planned), with the value type `dispatch::Call` | Function that writes nothing, host-testable | `dispatch::entry`, at each system call | None of its own: it decodes every operation of the table | [Operation numbers and versions](#operation-numbers-and-versions), [Rejection](#rejection), [Order of errors](#order-of-errors), [Rights](#rights) |
| `dispatch::resume` (planned) | Write entry, host-testable; gives the next plan or the end of the transition | `el0_dispatch` (planned), after it has executed a plan that `entry` or `resume` gave, with the pending value of that plan | None | [The round trip of plans](#the-round-trip-of-plans) |
| `dispatch::compose_return` (planned) | Write entry, host-testable; gives the return plan, the wait or, for a refused context of the root, the halt | `dispatch::entry` and `dispatch::resume`, at the end of every transition whose event or operation has not halted the system | None | [The return](#the-return) |
| `loader::validate` (planned), with `Plan::new` and the value types `loader::Plan`, `Segment`, `Step`, `Boot`, `Limits`, `Accepted` and `loader::Error` | Function that writes nothing, host-testable | `creation::spawn_segment` and `creation::spawn_commit` (planned), for a segment and a commit, and `creation::spawn_begin` (planned), with `Plan::new`, for the plan of an image; the boot wiring, once, for the step `Limits`, after `vm::check_config` and before it carves any storage | None | [Load validation](#load-validation), [Loading configuration](#loading-configuration) |

## Extractability

The module `dispatch` of the core (planned), in `kernel/src/dispatch.rs`
(planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the
decoding of a system call with its dispatch table, the checks of the
reserved and unused registers, the writing of results and the composition
of a transition. It is in layer 9 of the
[module order](../../../architecture.md#module-order-in-the-core), above
every other module of the core, and refers to the modules below it whose
entries it composes: `objects`, `context` and `address_space` of layer 1,
for references, the saved context with its results and bounds, the
classification of an exception and the return; `page_tables` of layer 2,
for the write plans that it hands on; the kernel root; `capabilities` and
`ledger` of layer 4, for the operations on capabilities and the lookup of a
served endpoint, and for the budget ledger of the CPU that the scheduler
takes; `vm`, `waits` and `scheduler` of layer 5; `ipc` of layer 6;
`lifecycle` of layer 7; and `creation` of layer 8, for the operations of
the table and their acknowledgements. It does not refer to `loader`, which
the creation component and the boot wiring call.

The module `loader` of the core (planned), in `kernel/src/loader.rs`
(planned), follows the subset as well: the values of a plan and of the
limits and the checks of `validate`. It is in layer 1 and refers to no
other module of the core. The bounds of the image window are its own
constants; the range of an image in the bundle comes in its plan, from the
creation component, and the facts of the boot in the step `Limits`, from
the boot wiring. So it takes neither the constants of `address_space`,
another module of its own layer, nor any other module, and the relations
of its constants with those of the address-space and VM components are
checked by a host test
([The image window](#the-image-window)).

- **Reads across layers.** Whether an endpoint is served is a state of the
  lifecycle component, in layer 7: the dispatch reads it with
  `lifecycle::is_alive` and passes it to `ipc`, in layer 6, as a value, as
  the [IPC](../../ipc-waits/ipc/contract.md#terms) and
  [lifecycle](../../objects-capabilities/lifecycle/contract.md#extractability)
  contracts state.
- **The table.** The dispatch table is a `match` on the version and the
  number in `syscall`, and the composition of each operation a `match` on
  the operation in `entry`; no function is bound to a value or kept in a
  table, the alternative of
  [function items as values](../../../conventions/provable-subset.md#r1-function-items-as-values).
  The `match` of the core and the ABI crate `krepi-abi` each hold the
  operation numbers and the codes of the errors, apart from each other, and
  `cargo xtask check` is to keep both equal to the inventory (planned), as
  the [kernel workspace crates](../../../architecture.md#kernel-workspace-crates)
  state.
- **Visibility.** The items are `pub(crate)` except the rows that the
  architecture crate and the boot wiring call, `entry`, `resume` and
  `validate`, with the value types that those rows take and return
  ([provable core](../../../architecture.md#the-provable-core)); the
  constructor of a pending value stays in the module, so the architecture
  crate passes back only values that the core gave it
  ([rule 6](../../../conventions/provable-subset.md#6-compile-time-guards)).
  The write entries receive the one kernel root by `&mut`
  ([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root))
  and the per-CPU record of the executing CPU, with its write-set buffer,
  scheduler record and budget ledger, by an explicit `&mut` argument
  ([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
- **No hardware action.** Neither module touches a register, writes a
  frame or defines a callback for a hardware action. The dispatch gives
  each plan to `el0_dispatch` as the result of `entry` or `resume`, and
  `el0_dispatch`, code of the board crate of each image, executes it with
  the adapter that its component names and enters the core again
  ([The round trip of plans](#the-round-trip-of-plans)).
- **Forms to rewrite.** In the prototype tree at
  `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, `Segment::validate`
  and `validate` in `src/loader/segments.rs`, lines 41 to 111, and `Plan`
  in `src/loader/plan.rs`, lines 1 to 38, are the sources of the checks of
  [Load validation](#load-validation), and `image_window` in
  `src/loader/segments.rs`, lines 23 to 31, that of its two profiles,
  which [The image window](#the-image-window) replaces; their code is
  rewritten, not carried. Their forms are written here as follows: the
  walk with `iter().enumerate()` (segments.rs, line 91) as an index loop,
  in the loop shapes of the
  [subset](../../../conventions/provable-subset.md#constructs-and-alternatives);
  each `.any` with a closure (segments.rs, lines 104 to 107; plan.rs, lines
  25 to 28) as an index loop in a helper function, the alternatives of
  [`Iterator::any`](../../../conventions/provable-subset.md#r2-iteratorany)
  and of
  [closures as callbacks](../../../conventions/provable-subset.md#r4-closures-as-callbacks);
  `Range::contains` and the `contains` of a slice (segments.rs, lines 24,
  26 and 72) as comparisons; and `is_multiple_of` (segments.rs, lines 45 to
  47 and 87) as a remainder compared with 0. The porting record of the
  change that adds the module names these sources
  ([porting records](../../../conventions/porting.md#porting-records)).

The prototype's ABI module and its loader are sources of this page
([References](#references)). The contract is written before its code, so
this section lists no source paths; the change that adds the modules
writes their `paths` block here.

## Operation numbers and versions

The rules of the
[system calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
of the architecture hold; this section states how the dispatch applies
them.

- **The number.** Bits 0 to 15 of `x8` hold the operation number, and bits
  16 to 63 are 0. The number 0 is not used. Production operations take the
  numbers `0x0001` to `0x7FFF`, diagnostic operations `0x8000` to `0xFFFF`,
  and the ABI inventory assigns the numbers within each range
  ([operation numbers](../../../architecture.md#system-calls-and-the-abi)).
- **The diagnostic range.** The dispatch table of the default image has no
  row in the diagnostic range; a test build adds the rows of its diagnostic
  operations. A stable ABI freezes only the production range
  ([operation numbers](../../../architecture.md#system-calls-and-the-abi)).
- **The version.** `x7` holds the major version for which the caller was
  built. `VERSION` is 1, the only version that release 0.1 accepts; the
  version 0 of the prototype and every other value are refused. A new
  operation takes a new number and leaves the version as it is, arguments
  are extended by flags that must be 0 and by structures that carry their
  size, and there is no minor version
  ([versions](../../../architecture.md#system-calls-and-the-abi)).
- **The table.** The dispatch table is keyed by the version and the
  number. The kernel serves the current major version and the one before
  it: once a version 2 exists, the table holds the rows of both, and a row
  of version 1 keeps its meaning
  ([versions](../../../architecture.md#system-calls-and-the-abi)).
- **Deprecation.** A number is never reused. A deprecated operation keeps
  its meaning within its major version and loses its row only with a new
  major version, after which its number is refused with
  `UNSUPPORTED_OPERATION`; a retired major version, at a release boundary
  of the stable ABI, is refused with `UNSUPPORTED_VERSION`
  ([deprecation](../../../architecture.md#system-calls-and-the-abi)).
- **The immediate.** A native call is `svc #0`
  ([SVC immediate](../../../architecture.md#system-calls-and-the-abi)).
  Every process of release 0.1 is native, so every `SVC` takes native
  dispatch; the path of a Linux process, which dispatches by the exception
  class whatever the immediate, belongs to Linux compatibility (planned).
- **The inventory.** The numbers, the registers of the arguments and
  results and the codes of the statuses belong to the ABI inventory; the
  `match` of the core and the definitions of `krepi-abi` are each written
  from it ([Extractability](#extractability)).

## Rejection

`syscall(immediate, registers)` takes the immediate of the `SVC` and the
registers of the call, `x0` to `x8`, and gives either the operation of the
dispatch table with the values of its argument registers, or the refusal of
the call with its status. It writes nothing. Its checks, in this order,
each before any check of the operation:

1. the immediate is 0 (`UNSUPPORTED_OPERATION`); a native call with another
   immediate is refused and is not a fault
   ([exception classes](../../memory/address-space/contract.md#exception-classes));
2. `x7` is `VERSION` (`UNSUPPORTED_VERSION`);
3. bits 16 to 63 of `x8` are 0, the number is not 0, and the dispatch table
   of the running image has a row for the version and the number
   (`UNSUPPORTED_OPERATION`);
4. `x6` is 0 (`INVALID_ARGUMENT`);
5. each argument register of `x0` to `x5` that the operation does not use,
   in ascending order of its number, is 0 (`INVALID_ARGUMENT`).

Every value of the immediate, of `x7` and of `x8` has one result:

| Immediate | `x7` | `x8` | Result |
| --- | --- | --- | --- |
| Not 0 | Any | Any | `UNSUPPORTED_OPERATION` |
| 0 | Not 1 | Any | `UNSUPPORTED_VERSION` |
| 0 | 1 | A bit of bits 16 to 63 set | `UNSUPPORTED_OPERATION` |
| 0 | 1 | 0 | `UNSUPPORTED_OPERATION` |
| 0 | 1 | `0x0001` to `0x7FFF` without a row of version 1 | `UNSUPPORTED_OPERATION` |
| 0 | 1 | `0x8000` to `0xFFFF`, in the default image | `UNSUPPORTED_OPERATION` |
| 0 | 1 | `0x8000` to `0xFFFF` without a row of version 1, in a test build | `UNSUPPORTED_OPERATION` |
| 0 | 1 | A number with a row of version 1 | The checks of `x6` and of the unused argument registers, then the operation |

So the three checks of the operation number and the version come in this
order, and before the reserved register, the arguments and the rights of
any operation.

- **The rules of the dispatch function.** The six rules that `syscall`
  states, over every row of the table:
  1. an immediate other than 0 gives `UNSUPPORTED_OPERATION`;
  2. with the immediate 0, a version other than `VERSION` gives
     `UNSUPPORTED_VERSION`;
  3. with both, an `x8` without a row gives `UNSUPPORTED_OPERATION`;
  4. with a row, an `x6` other than 0, and then an unused argument register
     other than 0, gives `INVALID_ARGUMENT`;
  5. otherwise the result is the operation of the row with the values of
     the argument registers that it uses, and nothing that EL0 passes
     selects the rights that its lookups check ([Rights](#rights));
  6. `syscall` writes nothing, so a refused call changes no state.
- **The footprint of a refusal.** A call that `syscall` refuses, and a
  call that the entry of its operation refuses, changes no field of the
  kernel state: its operation writes nothing, its write set is empty and it
  gives no plan. The dispatch writes only the result registers of the
  saved context of the caller ([Results](#results)). The settlements of
  the waits whose deadlines passed before the operation, in the same
  transition, and the scheduling of the return after it are transactions
  of their own and stay
  ([Composition of a transition](#composition-of-a-transition)). There is
  no exception.
- **Determinism of the result.** The result of a call depends only on its
  registers, the state, and the table of the running image, so a test can
  give every value of the three registers an expected result, as the table
  above does.

## Order of errors

The order of errors of the
[security model](../../../security.md#internal-choices) holds for every
operation. Its places, in order:

1. the operation number and version, which this page checks;
2. the form of the register arguments;
3. handle resolution;
4. rights;
5. the range and permissions of user buffers, and then the form of the
   argument structures copied in;
6. object state;
7. the caller's quota;
8. shared capacity.

- **The first place.** The dispatch checks the immediate, the version and
  the number, in this order ([Rejection](#rejection)).
- **The dispatch in the second place.** The checks of `x6` and then of the
  unused argument registers come first in the form of the register
  arguments, before any check of the operation; the other checks of that
  place, and those of places 3 to 8, are the rules of the contract of the
  operation, which each contract states in its Errors section.
- **The place of an argument.** An argument that the ABI inventory passes
  in a register is checked for its form in place 2, before handle
  resolution, whatever it holds: a slot, a mask of rights, a packed field,
  a class or an amount. An argument that an argument structure copied in
  from user memory carries is checked for its form in place 5, after the
  handles, the rights and the range of its buffer, and before object
  state. Every argument of every operation of release 0.1 is in a
  register, and no operation of release 0.1 reads a user buffer, so place
  5 is empty there; the
  [scheduler](../../scheduling/scheduler/contract.md#errors) and
  [budget-ledger](../../scheduling/budget-ledger/contract.md#errors)
  contracts already place the form of the arguments of admission by this
  rule. The place of each argument of every operation follows this rule.
- **Composed checks.** An operation that composes the checks of several
  entries, as a commit composes those of `loader::validate`, returns the
  error of the earlier place, and at one place the error that the order of
  its rule section puts first.
- **Shared capacity.** The errors of shared capacity depend on other
  processes and are outside the output sources of the
  [observable outputs](../../../security.md#observable-outputs).

## Rights

- **A constant of the operation.** The rights that an operation needs are
  constants of the operation, which its contract states and the lookups of
  its entry check
  ([rights of an operation](../../objects-capabilities/capabilities/contract.md#rights)).
  The dispatch reads no right that authorizes anything from EL0: an
  argument that holds a mask of rights, such as that of `derive`, is the
  mask of a new capability, which only attenuates.
- **No check of its own.** The dispatch makes no check of rights: the
  lookup of each handle by the entry of the operation does, in place 4 of
  the [order of errors](#order-of-errors), after the form of the
  arguments and the resolution of the handles.
- **The operations of the inventory.** The operations that the dispatch
  table serves in release 0.1, with the contract that defines each and the
  rights that the lookups of its handles need; their numbers belong to the
  ABI inventory.

| Operation | Contract | Handles and the rights that their lookups need |
| --- | --- | --- |
| `copy` | [Capabilities](../../objects-capabilities/capabilities/contract.md#derivation-and-badges) | `source`: GRANT |
| `derive` | [Capabilities](../../objects-capabilities/capabilities/contract.md#derivation-and-badges) | `source`: GRANT and every requested right |
| `close` | [Capabilities](../../objects-capabilities/capabilities/contract.md#close) | `handle`: None |
| `revoke` | [Capabilities](../../objects-capabilities/capabilities/contract.md#revocation) | `handle`: REVOKE |
| `call` | [IPC](../../ipc-waits/ipc/contract.md#calls-and-receives) | `endpoint`: SEND; the source of a transfer: GRANT and the requested rights |
| `receive` | [IPC](../../ipc-waits/ipc/contract.md#calls-and-receives) | `endpoint`: RECEIVE, for its bound thread |
| `reply` | [IPC](../../ipc-waits/ipc/contract.md#replies) | `reply`: REPLY |
| `signal` | [Waits](../../ipc-waits/waits/contract.md#notifications) | `target`: SIGNAL on a notification |
| `wait` | [Waits](../../ipc-waits/waits/contract.md#notifications) | `handle`: WAIT on a notification |
| `sleep` | [Waits](../../ipc-waits/waits/contract.md#deadlines-and-sleep) | None |
| `wait_set_add` | [Waits](../../ipc-waits/waits/contract.md#wait-sets) | `handle`: WAIT on a notification, or RECEIVE on an endpoint |
| `wait_set_remove` | [Waits](../../ipc-waits/waits/contract.md#wait-sets) | None |
| `wait_set_wait` | [Waits](../../ipc-waits/waits/contract.md#wait-sets) | None |
| `yield` | [Scheduler](../../scheduling/scheduler/contract.md#entry-points) | None |
| `create_endpoint` | [Creation](../../objects-capabilities/creation/contract.md#rights) | `create`: CREATE on the caller's process; `thread`: CONTROL |
| `create_notification` | [Creation](../../objects-capabilities/creation/contract.md#rights) | `create`: CREATE on the caller's process |
| `spawn_begin` | [Creation](../../objects-capabilities/creation/contract.md#rights) | `create`: CREATE on the caller's process |
| `spawn_segment` | [Creation](../../objects-capabilities/creation/contract.md#rights) | None |
| `spawn_grant` | [Creation](../../objects-capabilities/creation/contract.md#rights) | `source`: GRANT and every requested right |
| `spawn_commit` | [Creation](../../objects-capabilities/creation/contract.md#rights) | `create`: CREATE on the caller's process; the source of each grant: GRANT and its rights |
| `spawn_abort` | [Creation](../../objects-capabilities/creation/contract.md#rights) | None |
| `reserve` | [VM](../../memory/vm/contract.md#vm-window-and-regions) | None: it takes no handle |
| `commit` | [VM](../../memory/vm/contract.md#commit) | None: it takes no handle |
| `decommit` | [VM](../../memory/vm/contract.md#decommit) | None: it takes no handle |
| `mprotect` | [VM](../../memory/vm/contract.md#protection-and-wx) | None: it takes no handle |
| `release` | [VM](../../memory/vm/contract.md#two-phase-release) | None: it takes no handle |
| `exit` | [Lifecycle](../../objects-capabilities/lifecycle/contract.md#entry-points) | None |
| `kill` | [Lifecycle](../../objects-capabilities/lifecycle/contract.md#entry-points) | `process`: CONTROL |
| `query` | [Lifecycle](../../objects-capabilities/lifecycle/contract.md#entry-points) | `process`: OBSERVE |
| `reap` | [Lifecycle](../../objects-capabilities/lifecycle/contract.md#entry-points) | `process`: CONTROL, with the caller's process its owner |
| `watch` | [Lifecycle](../../objects-capabilities/lifecycle/contract.md#entry-points) | `process`: OBSERVE; `notification`: SIGNAL |

These are 31 operations: four of the capabilities component, three of the
IPC component, six of the waits component, one of the scheduler, seven of
the creation component, five of the VM component and five of the lifecycle
component. An operation that a later contract adds takes a row here with
its rights, and a number from the inventory.

## Results

The results of a call are values of the saved context of the caller, which
the dispatch writes, while the executing CPU owns that context, with
`Context::set_return_registers` of the
[context](../../boot-platform/context/contract.md#results-of-a-call)
component and the bounds of the
[EL0 window](../../memory/address-space/contract.md#el0-address-layout):

- **Success.** A call that completes in its transition gets `OK` in `x0`
  and its results in `x1` to `x5`, in the order of the ABI inventory, and 0
  in each of `x1` to `x5` that its operation does not use.
- **Failure.** A call that is refused, by this page or by the entry of its
  operation, gets the status of its error in `x0` and 0 in `x1` to `x5`.
- **Kept.** After a success or a failure, every other field of the saved
  context keeps its value: `x6` to `x30`, `sp`, `elr`, `spsr`, the TLS
  registers, the vector registers, FPCR and FPSR; only execution again
  moves `elr`.
- **A blocked call.** A call that blocks gets no result in its transition;
  the completer of its wait writes it later, in its own transaction, in
  `x0` and `x1` or in `x0` to `x5`, as the contract of the call states
  ([blocking](../../memory/address-space/contract.md#kernel-stacks-and-blocking)).
- **Execution again.** A call whose step ends with `Again` gets no result:
  the dispatch moves the saved `elr` back by 4, to its `SVC`
  ([Execution again](#execution-again)).
- **No return.** An `exit`, and a `kill` that ends the caller's own
  process, end the caller's thread, which gets no result and never runs
  again; a call that halts the system gets none either.
- **A refused context.** When `set_return_registers` finds that the saved
  context fails `validate`, it writes nothing, and the return composes the
  end of the process of the thread as for every refused context
  ([The return](#the-return)); the operation of the call has taken effect.
- **Outcomes.** The outcomes that the contracts of the operations write as
  results, such as `Timeout`, `Revoked` and `PeerClosed`, are results of an
  accepted call, not refusals; the statuses that they take belong to the
  ABI inventory.

## Composition of a transition

A transition runs with every exception masked, from its entry, through the
plans that the architecture crate executes for it, to the return to EL0,
the wait of the CPU or the halt. This section orders the entries of the
other components into it; their rules are in their contracts.

### The entry

`entry(root, cpu, event, now)` starts a transition. `event` is one of
three: an exception taken from EL0, with its vector, `ESR_EL1` and
`FAR_EL1`, and, for an IRQ, the interrupt that the architecture crate has
acknowledged; an interrupt that the architecture crate found pending at a
return, with the interrupt that it acknowledged, for the thread of the
return plan, whose saved context is complete
([The round trip of plans](#the-round-trip-of-plans)); or the wake of an
idle CPU, with the interrupt that woke it. `now` is the time that the
architecture crate read once at the start of the transition, and every
entry that the transition composes takes it
([Platform parameters and time](../../scheduling/scheduler/contract.md#platform-parameters-and-time)).

1. **Expiry first.** The dispatch settles every wait whose deadline is not
   later than `now`, each in a transaction of its own, before the event of
   the transition
   ([deadlines and sleep](../../ipc-waits/waits/contract.md#deadlines-and-sleep)).
2. **The event.** For an exception, `address_space::classify` gives its
   class
   ([exception classes](../../memory/address-space/contract.md#exception-classes)):
   - `Svc`: `syscall`, and then the operation ([Operations](#operations));
   - a user fault, every class but `Svc` and `Irq`: `lifecycle::fault` of
     the process of the current thread with the fault record that the
     [address-space](../../memory/address-space/contract.md#user-faults)
     component gives
     ([faults](../../objects-capabilities/lifecycle/contract.md#faults));
   - `Irq`: the interrupt. The timer interrupt needs no rule of its own:
     the return compares `now` with the deadline of the scheduler
     dispatch. An interrupt that the device-authority rules of the devices
     and DMA domain bind to a notification is signalled by their rules
     (planned).
   - An interrupt pending at a return is handled as `Irq`, without
     `classify`, with the thread of that return as the current thread; the
     wake of an idle CPU is handled as `Irq`, with no current thread.
3. **The return.** `compose_return`, unless the event has halted the system
   ([The return](#the-return), [The halt](#the-halt)).

- **The end of an interrupt.** The architecture crate passes no special ID,
  1020 to 1023, to `entry`, and ends each interrupt that it acknowledged
  once, after it has armed the timer for the next return or wait and
  before that return or wait, as `irq::handle` of the
  [boot](../../boot-platform/boot/contract.md#interrupts) component does;
  it disables every interrupt that is neither the timer interrupt nor bound
  to a notification by the device-authority rules (planned).

### Operations

When `syscall` refuses a call, the dispatch writes its status
([Results](#results)) and composes the return. Otherwise it calls the
entry of the operation with the values of its argument registers, `now`
and the parts of the state that the entry takes, and composes it with the
entries that its contract names:

| Operation | What the dispatch composes | Rule |
| --- | --- | --- |
| `call`, `receive` | `served`: whether the endpoint is served, which it reads, after a lookup of the endpoint that writes nothing, with `lifecycle::is_alive` of the owner of the endpoint and of the process of its bound thread, false for a bound thread that is not live, and passes as a value; when that lookup fails, the operation fails at its own lookup with the same error | [Served endpoint](../../ipc-waits/ipc/contract.md#terms), [bound thread](../../ipc-waits/ipc/contract.md#bound-thread) |
| `signal` | `scheduler::enqueue` of the thread that the signal completes | [Notifications](../../ipc-waits/waits/contract.md#notifications) |
| `wait`, `sleep` | `scheduler::block` when the wait blocks | [Deadlines and sleep](../../ipc-waits/waits/contract.md#deadlines-and-sleep) |
| `wait_set_add` | `waits::check_source`; for an endpoint, `ipc::check_receiver`; then `waits::wait_set_add` | [Wait sets](../../ipc-waits/waits/contract.md#wait-sets) |
| `wait_set_wait` | `waits::sources`; `ipc::has_call` of each endpoint that it gives; `waits::wait_set_wait` with the answers; `scheduler::block` when the wait blocks | [Wait sets](../../ipc-waits/waits/contract.md#wait-sets) |
| `close` | For a reply capability, `ipc::reply_deleted` with `Tables::close` | [Replies](../../ipc-waits/ipc/contract.md#replies) |
| `revoke` | In the transition that makes a revocation pending, the scan with `waits::revoked` and the settlement of each wait that it names; in each step, the drains of the revocation and `waits::unpause` with `scheduler::enqueue` for each capability that the step removes; `Again` | [Revocation](../../objects-capabilities/capabilities/contract.md#revocation), [revocation and release](../../ipc-waits/waits/contract.md#revocation-and-release) |
| `spawn_commit` | Its plans, with `creation::acknowledge` of the caller | [The round trip of plans](#the-round-trip-of-plans) |
| `commit`, `decommit`, `mprotect`, `release` | Their plans, with `vm::acknowledge` of the caller; for `release`, `Again` | [The round trip of plans](#the-round-trip-of-plans) |
| `exit` | No result: the thread is removed | [Exit](../../objects-capabilities/lifecycle/contract.md#exit) |
| `kill` | Its steps, with their plans and `lifecycle::acknowledge` of the target; `Again`; the halt; no result for a kill of the caller's own process | [Kill](../../objects-capabilities/lifecycle/contract.md#kill) |

The other operations are their entries alone. Then, by what the operation
gives:

- a result, or an error: the dispatch writes it ([Results](#results)) and
  composes the return;
- a blocked wait, or no return: it writes nothing and composes the return,
  which runs another thread;
- a plan: the round trip ([The round trip of plans](#the-round-trip-of-plans));
- `Again`: execution again ([Execution again](#execution-again));
- the halt ([The halt](#the-halt)).

**Write sets.** The transactions of a transition stay apart: each
settlement of an expired wait, the transaction of the operation, each
death notification, each drain and release of a destruction, each
settlement of a revocation and each acknowledgement of a plan is a
transaction of its own, with the write set that its contract bounds. The
dispatch merges none of them and adds no item to any: the largest is the
54 items of a step of the teardown of a table
([destruction](../../objects-capabilities/lifecycle/contract.md#destruction)),
a commit of a child writes at most 31
([check and execute](../../objects-capabilities/creation/contract.md#check-and-execute))
and an entry of the VM component at most 5
([check and execute](../../memory/vm/contract.md#check-and-execute)), all
within $W$ = 64 of the
[objects](../../objects-capabilities/objects/contract.md#write-set-transactions)
contract.

### The round trip of plans

An entry of another component fixes in its checks every plan that it and
its continuation give, and gives its first plan only after the write-back
of its write set
([write plans](../../memory/page-tables/contract.md#write-plans-and-publication)).
The core sets no callback for a hardware action and writes no frame, so
`entry` and `resume` give one of five results of a transition, a value of
`dispatch::Transition` (planned):

| Result | What `el0_dispatch` does |
| --- | --- |
| The return: the return plan of a thread, or, when the CPU has no thread to run, the wait of the CPU | For a return plan, it arms the timer for the timer deadline of the scheduler record and, while no interrupt is pending, calls `__el0_return` with the plan; with an interrupt pending, it acknowledges it and calls `entry` with that IRQ for the thread of the plan, whose saved context is complete. For the wait, it calls `krepi_arch::el0::load_kernel_tables`, arms the timer for the wake time, waits for an interrupt and calls `entry` with the wake |
| A write plan, with a pending value | `krepi_arch::mmu::apply`, then `resume` with the pending value |
| The release plan of an ASID, with a pending value | `krepi_arch::el0::invalidate_asid`, then `resume` with the pending value |
| A frame plan, with a pending value: the zeroing of a frame or the copy of bytes of the boot bundle into a frame | `krepi_arch::frames::apply`, then `resume` with the pending value |
| The halt of the system | The fatal path of the [boot](../../boot-platform/boot/contract.md#records) component ([The halt](#the-halt)) |

- **Resume.** `resume(root, cpu, pending)` calls the acknowledgement of the
  component that the pending value names, for its process: `vm::acknowledge`
  of the caller, whose VM head holds the cursor of an operation of the VM
  component; `creation::acknowledge` of the caller, whose staging record
  holds the cursor of a commit; or `lifecycle::acknowledge` of the target
  of a kill, below which the working process holds the progress of a
  destruction, and which calls `vm::acknowledge` for the zero plans of the
  revocation of the frames of a process. The acknowledgement gives the next
  plan, which `resume` gives with a pending value; `Again`; or the result
  of the operation. Then `resume` ends the transition as `entry` does after
  the operation ([Operations](#operations)), with the time that the pending
  value holds.
- **One at a time.** One plan is executed before the next is given, and no
  other entry runs on the tables, the VM head, the staging record or the
  progress of that process in between
  ([write plans](../../memory/page-tables/contract.md#write-plans-and-publication)).
  A plan does not fail
  ([page-tables](../../memory/page-tables/contract.md#write-plans-and-publication),
  [ASIDs](../../memory/address-space/contract.md#address-spaces-and-asids)),
  so an operation has no error after its first plan.
- **Frames.** A frame returns to the page pool in the acknowledgement of
  the zero plan that cleared it, after that plan has been executed, so a
  free frame is zero
  ([reclamation](../../memory/vm/contract.md#acknowledgement-and-reclamation)).
  The frames that a commit takes leave the pool before its first plan, so
  no plan in flight needs a free frame.
- **No cursor across transitions.** A commit, a decommit, an `mprotect` and
  a commit of a child give all their plans in one transition, and a step of
  a release or of a destruction ends with its cursor empty and its progress
  in its object. So no cursor of a multi-page operation outlives its
  transition, and the steps of a destruction are separated by preemption
  points, with their progress in the process slot
  ([destruction](../../objects-capabilities/lifecycle/contract.md#destruction)).
- **A pending value that names no plan.** The architecture crate passes
  only pending values that the core gave it, after their plans; one that
  names no plan in flight, which only a host test passes, makes the
  acknowledgement refuse with `InvalidState` without a change, and `resume`
  then gives the halt, the fatal path for a broken premise of the core.

### Execution again

When the operation, or the acknowledgement of its plan, gives `Again`, the
call has stored its progress in its object and has no result. The dispatch
writes no result and moves the saved `elr` of the thread back by 4, from
the address after the `SVC` to the `SVC`, as the
[address-space](../../memory/address-space/contract.md#kernel-stacks-and-blocking)
component states, and composes the return. The composer continues the
scheduler dispatch of the thread unless its deadline has passed or the
reschedule flag is set, and the architecture crate returns to EL0 only
while no interrupt is pending; so the thread executes the call again at
once unless one of these holds, and once it runs again otherwise. The call
repeats its checks and continues from the stored progress.

Every step of a long operation ends the call with `Again`, whether an
interrupt is pending or not, since the core reads no interrupt controller:
this is how the dispatch reads the preemption points of the
[long operations](../../../architecture.md#system-calls-and-the-abi) of
the execution model, as the
[lifecycle](../../objects-capabilities/lifecycle/contract.md#kill) and
[VM](../../memory/vm/contract.md#two-phase-release) contracts do. So every
step runs in a transition of its own, between two preemption points.

### The return

`compose_return(root, cpu, now)` ends every transition whose event or
operation has not halted the system. It takes the four steps of the
[return](../../memory/address-space/contract.md#entry-and-return) of the
address-space component with the entries below, and gives the return plan,
the wait of the CPU or, for a refused context of the root, the halt:

- **The choice, step 1.** When the current thread has a scheduler dispatch
  whose deadline is not later than `now`, or the reschedule flag of the
  scheduler record is set, the composer calls `scheduler::preempt`
  ([preemption](../../scheduling/scheduler/contract.md#preemption));
  otherwise a scheduler dispatch that no stop has ended continues, and its
  thread returns without a `choose`. With no scheduler dispatch, it calls
  `scheduler::choose` with `now` and the external deadline that
  `waits::first_deadline` gives
  ([selection](../../scheduling/scheduler/contract.md#selection-and-time-slices));
  when `choose` takes no thread, the result of the transition is the wait
  of the CPU.
- **Validation, step 2.** `Context::validate` with the bounds of the EL0
  window, and, for a refused context, `lifecycle::fault` of the process of
  the thread with the cause `Other`
  ([a refused context](../../memory/address-space/contract.md#user-faults)),
  after which the composer starts again at step 1. Each refusal removes one
  thread for good, so the composer starts again at most the thread capacity
  times; a refused context of the root gives the halt
  ([The halt](#the-halt)).
- **The address space and the plan, steps 3 and 4.** `Space::join` when
  the CPU record of the address space lacks the executing CPU, the thread
  as the current thread of the CPU, and the return plan with `Space::ttbr0`
  of the address space.
- **Interrupts before the return.** No thread returns to EL0 while an
  interrupt is pending: the architecture crate, which alone reads the
  interrupt controller, enters the core with that interrupt instead of
  returning ([The round trip of plans](#the-round-trip-of-plans)), so the
  interrupt is handled, as the class `Irq`, in a transition of its own
  before the thread returns, and is never left to be taken at EL0 after
  the `ERET`, where an `SVC` of the first instruction could come before it.
  This differs from step 1 of the address-space component, whose composer
  handles the pending interrupts in the same transition before it chooses:
  the core cannot learn of them, so it handles them after the choice, in
  the next transition, with the time of that transition, whose return
  chooses again.
- **The timer.** The scheduler record holds the timer deadline that the
  choice gives, and the architecture crate arms the timer for it before it
  returns or waits
  ([preemption](../../scheduling/scheduler/contract.md#preemption)).

### The halt

An entry of the lifecycle component gives `Halt` when the root leaves
Alive: by its `exit`, a user fault of its thread, a refused context or a
`kill` of the root
([the root](../../objects-capabilities/lifecycle/contract.md#the-root)).
The entry makes no write, and the dispatch gives the halt as the result of
the transition, without another step: no death notification, no return
and no further transaction. `el0_dispatch` takes the fatal path of the
[boot](../../boot-platform/boot/contract.md#records) component, as for an
exception at EL1: it writes the record of the end of the root to the
serial console with `CASXI_HALTED` and halts with `krepi_arch::cpu::halt`.

## Load validation

`loader::validate(plan, step, limits)` is a function that writes nothing.
It takes the plan of an image, or none; a step; and the limits of the
loading part. It gives what it accepts, a value of `loader::Accepted`
(planned), or the error of the first check that fails. It has three steps,
`loader::Step` (planned):

- `Segment(segment)`, for `spawn_segment`, which adds one segment to the
  plan ([Segments](#segments));
- `Commit(entry)`, for `spawn_commit`, which checks the plan as a whole
  ([Commit](#commit));
- `Limits(boot)`, for the boot wiring, which checks the loading part of the
  capacity record once at boot
  ([Loading configuration](#loading-configuration)).

The validation is incremental: each segment is checked when it is staged,
against the segments accepted before it, and the commit checks only what
needs the whole plan. The checks of each step follow the
[order of errors](#order-of-errors), not the order of the prototype, and
within a place the order of the lists below.

- **The plan.** `loader::Plan` holds the index of its image, the offset and
  the bytes of the entry of that image in the boot bundle, and at most
  `MAX_SEGMENTS` = 8 segments in the order of their steps. `Plan::new(image,
  offset, file_bytes)` gives the plan of an image with no segment, which
  `spawn_begin` writes into the staging record of its caller after
  `Directory::entry` has given an entry of the kind Image
  ([child processes](../../objects-capabilities/creation/contract.md#child-processes)).
  Only a segment step adds a segment: it gives the plan with the segment
  after those that it holds, which `spawn_segment` writes. A plan holds no
  page, frame, table or object.
- **The segment.** `loader::Segment` holds the five arguments of
  `spawn_segment`: `offset`, the start of the bytes of the segment in its
  image; `file_bytes`, the number of those bytes; `address`, the virtual
  address of the segment; `memory_bytes`, its size in memory; and `flags`,
  its access: 4 for R, 5 for RX and 6 for RW, the values of the flags of an
  ELF program header, so that the runtime of EL0 passes them as it reads
  them.
- **None.** A plan of none, which the creation component passes when the
  staging record of its caller is empty, is refused with `NotStaged` at the
  first check of object state of a segment step and of a commit step,
  after the checks of form.
- **The limits.** `loader::Limits` holds the seven fields of the loading
  part, and `loader::Boot` the facts of the boot that the step `Limits`
  checks them with. That step makes six checks, in this order, each with
  its fixed error: the length of the record, the range of each field, the
  stack within the window and the private pages, the tables of a child, the
  root's limit and the limits of the boot bundle
  ([Loading configuration](#loading-configuration)). The segment and commit
  steps take the limits that it has accepted, which do not change after
  boot.
- **Accepted.** For a segment step, the plan with the segment; for a commit
  step, the private pages of the image; for a step `Limits`, the limits
  that it has checked.

### The image window

- **The constants.** `IMAGE_BASE` is `0x4020000000`, the start of the
  second half of the first 1 GiB slot of the
  [EL0 window](../../memory/address-space/contract.md#el0-address-layout),
  just after the bundle window, and `IMAGE_END` is `0x4040000000`, the
  start of the [VM window](../../memory/vm/contract.md#vm-window-and-regions).
  `MAX_WINDOW_PAGES` is 131,072, the pages from `IMAGE_BASE` to
  `IMAGE_END`, 512 MiB.
- **The window.** The image window of every child is
  `[IMAGE_BASE, top)`, `top` being `IMAGE_BASE` plus 4096 times
  `image_window_pages` of the limits. The check of the loading part keeps
  `top` at most `IMAGE_END`, and the tables of the window within the
  tables of a process ([Loading configuration](#loading-configuration)).
- **The stack.** The initial stack of a child is the highest
  `image_stack_pages` pages of its window, `[top - 4096 s, top)` for $s$ =
  `image_stack_pages`, and the page below it is its guard, which no
  mapping names. `top` is the initial stack pointer of the child, which
  the creation component gives `Context::new`
  ([child processes](../../objects-capabilities/creation/contract.md#child-processes)).
- **The segment range.** Every segment of a child lies in
  `[IMAGE_BASE, top - 4096 (s + 1))`, below the guard and the stack.
- **The neighbours.** The window lies in the EL0 window, outside the boot
  ranges of the root, which end at `IMAGE_BASE`, and below the VM window;
  the windows of device grants, which the device-authority rules of the
  devices and DMA domain place, lie above the VM window (planned). A child
  maps no boot range, and the root maps no page of the image window. So
  the window shares its 1 GiB slot with no window of the same process, and
  needs one level 2 table and one level 3 table for each 2 MiB of it. These
  are relations of constants with those of the address-space and VM
  components: a host test checks them, and the boot checks only the values
  of the record.
- **The link address.** `IMAGE_BASE` is the address at which the runtime
  of EL0 links its images, a constant of the ABI that the inventory gives
  EL0 (planned).

### Segments

`spawn_segment(offset, file_bytes, address, memory_bytes, flags)` calls
`validate(plan, Segment(segment), limits)`. Its checks, in this order:

The form of the register arguments:

1. `memory_bytes` is not 0 and `file_bytes` is at most `memory_bytes`
   (`Bounds`);
2. `address`, `offset` and `memory_bytes` are multiples of 4096
   (`Alignment`);
3. `address` + `memory_bytes` and `offset` + `file_bytes` fit 64 bits
   (`Overflow`);
4. `flags` is 4, 5 or 6 (`Permissions`);
5. for an R or RX segment, `file_bytes` equals `memory_bytes` (`Bounds`);
6. the range `[address, address + memory_bytes)` lies in the segment range
   of [The image window](#the-image-window) (`Bounds`).

Object state:

7. the plan is not none (`NotStaged`);
8. `offset` + `file_bytes` is at most the bytes of the entry of the image,
   rounded up to a multiple of 4096 (`Truncated`);
9. the segment shares no page with a segment of the plan (`Overlap`).

The caller's quota:

10. the plan holds fewer than `image_segments` segments (`Capacity`);
11. the pages of the memory of the RW segments of the plan, with this
    segment, are at most `image_private_pages` (`PrivatePages`).

- **The file range.** The offset of a segment counts from the start of its
  image. The bytes of an entry need not be a multiple of a page, and the
  entries of the directory share no page, so the page that holds the last
  byte of an image belongs to it, and the range of a segment may reach the
  end of that page. A segment does not reach into another entry of the
  bundle.
- **Sizes.** An RW segment may hold fewer bytes of the file than of
  memory: its private pages hold the bytes of the file and zero beyond
  them. An R or RX segment maps pages of the boot bundle, so it holds as
  many bytes of the file as of memory.
- **Pages.** Every address and size is a multiple of 4096, so two segments
  share a page exactly when their ranges meet.
- **Result.** The plan with the segment, after the segments that it held.

### Commit

`spawn_commit` calls `validate(plan, Commit(entry), limits)`, with the
virtual address `entry` of the first instruction of the child. Its checks,
in this order:

1. the form: `entry` is a multiple of 4 (`Entry`);
2. object state: the plan is not none (`NotStaged`), and it holds at least
   one segment (`Capacity`);
3. object state: `entry` lies in an RX segment of the plan (`Entry`);
4. the caller's quota: the private pages of the image, the pages of the
   memory of its RW segments and `image_stack_pages`, are at most
   `image_private_pages` (`PrivatePages`).

- **Result.** The private pages of the image, which the creation component
  checks against the share of its child and the free frames of the page
  pool, and takes from the pool
  ([child processes](../../objects-capabilities/creation/contract.md#child-processes)).
- **With the checks of a commit.** The creation component composes these
  checks with its own by their places; the limit of private pages of this
  page comes before its `ImageShare`
  ([quotas and admission](../../objects-capabilities/creation/contract.md#quotas-and-admission)).
- **The entry.** An entry in an RX segment lies in the image window, so the
  initial context passes `validate` with the bounds of the EL0 window.

**W^X by construction.** `validate` accepts only R, RX and RW segments.
The pages of R and RX segments are pages of the boot bundle, which the
creation component maps read-only, and which no mapping makes writable; the
pages of RW segments and of the stack are private pages, frames of the page
pool, which no mapping makes executable. So no page of a child is writable
and executable, by the same argument as for the root
([first process](../../memory/address-space/contract.md#first-process-and-boot-information)),
and no check of W^X needs the tables of the child.

## Loading configuration

The loading part of the capacity record is bytes 64 to 91, after the
[VM part](../../memory/vm/contract.md#configuration-and-the-page-pool) of
bytes 48 to 63, which the VM component holds: seven unsigned 32-bit fields,
little-endian, without padding, in this order.

| Offset | Field | Width | Unit | Content | Default |
| ---: | --- | ---: | --- | --- | --- |
| 64 | `image_window_pages` | 4 bytes | Pages | The pages of the image window of every child, from `IMAGE_BASE` | `DEFAULT_CAPACITIES.image_window_pages` |
| 68 | `image_segments` | 4 bytes | Segments | The segments of the plan of an image at most | `DEFAULT_CAPACITIES.image_segments` |
| 72 | `image_private_pages` | 4 bytes | Pages | The private pages of an image at most, those of its RW segments and of its stack | `DEFAULT_CAPACITIES.image_private_pages` |
| 76 | `image_stack_pages` | 4 bytes | Pages | The pages of the initial stack of every child | `DEFAULT_CAPACITIES.image_stack_pages` |
| 80 | `root_private_pages` | 4 bytes | Pages | The root's starting limit of private pages of loaded images, the value of `root_limits` of the objects component for that item | `DEFAULT_CAPACITIES.root_private_pages` |
| 84 | `bundle_pages` | 4 bytes | Pages | The pages of the boot bundle at most | `DEFAULT_CAPACITIES.bundle_pages` |
| 88 | `bundle_entries` | 4 bytes | Entries | The entries of the directory of the boot bundle at most | `DEFAULT_CAPACITIES.bundle_entries` |

**The step `Limits`.** The boot wiring calls `validate(none, Limits(boot),
limits)` once. `limits` holds the seven fields as the boot wiring reads
them from the record, a field beyond the end of the record being 0;
`loader::Boot` (planned) holds the length of the record in bytes, the
tables that the copy of the lower kernel set leaves to EL0, $N - K$
([table pools](../../memory/address-space/contract.md#table-pools)), and
the root's private pages, the pages of the boot bundle and the entries of
its directory, which the boot wiring counts from the directory that
`Directory::parse` has checked. Its checks, in this order, each with its
fixed error:

1. the record holds the 92 bytes up to the end of its loading part
   (`InvalidConfiguration`);
2. each field is at least 1; `image_window_pages`, `image_private_pages`
   and `image_stack_pages` are at most `MAX_WINDOW_PAGES`, 131,072;
   `image_segments` is at most `MAX_SEGMENTS`, 8, the bound that
   `MAX_ROOT_SEGMENTS` of the address-space component sets for the root;
   and `bundle_pages` and
   `bundle_entries` are at most `MAX_BUNDLE_PAGES`, 130,560, the pages of
   the bundle window of the address-space component, since every entry
   holds a page of its own (`InvalidConfiguration`);
3. the initial stack and its guard leave a page of the window to the
   segments, `image_stack_pages` + 1 < `image_window_pages`, and the stack
   is within the private pages of an image, `image_stack_pages` at most
   `image_private_pages` (`InvalidConfiguration`);
4. the tables of a child fit its table pool:

   ```math
   2 + \lceil p / 512 \rceil + 1 \le N - K
   ```

   for $p$ = `image_window_pages`: the level 2 tables of the 1 GiB slots of
   the image window and of the VM window, the level 3 tables of the image
   window, and one level 3 table of the VM window (`WindowTables`);
5. `root_private_pages` is at least the root's private pages, the pages of
   the memory of its RW segments and its `ROOT_STACK_PAGES` pages of stack
   (`RootPrivatePages`);
6. the pages of the boot bundle are at most `bundle_pages`, and the entries
   of its directory at most `bundle_entries` (`BundleLimits`).

- **When.** The boot wiring makes the step after the checks of the object
  part of the
  [capacity record](../../objects-capabilities/objects/contract.md#capacity-record),
  its check 6 included, and after `vm::check_config`, and before it carves
  any storage; it stops the boot at the first error, without a fallback to
  the defaults. The record is then read-only, and the creation component
  and the boot of the root take the limits that the step accepted.
- **The bound of a boot.** Check 4 bounds the image window of each boot by
  the tables that the lower kernel set leaves, with $N$ = 32, as the table
  after this list shows for the images of the
  [table pools](../../memory/address-space/contract.md#table-pools). The
  tables of the VM window beyond the one of check 4 are refused by `commit`
  of the VM component with `OutOfTables`
  ([tables](../../memory/vm/contract.md#tables-and-extents)). The
  device-authority rules add to the left side the tables of the windows of
  device grants (planned). So no `map_page` of the commit of a child meets
  `OutOfTables`.
- **The root.** The root's private pages are those of
  [the first process](../../memory/address-space/contract.md#first-process-and-boot-information)
  without the page of the boot information: the pages of the memory of
  each RW root's segment of the directory, rounded up to a page, and
  `ROOT_STACK_PAGES`. The boot wiring counts them from the entries that
  `Directory::parse` has checked, so the step needs neither the carving
  nor `Directory::root_plan`, which runs later and gives the same pages
  and the page of the boot information. Check 5 keeps the charge of those
  pages to the root's item of private pages of loaded images within its
  starting limit, so the
  [boot of the root](../../objects-capabilities/creation/contract.md#the-boot-of-the-root)
  cannot fail at it.
- **The bundle.** The capacity record is an entry of the boot bundle that
  it limits. The build checks the bundle against the limits of its record
  (planned), and the boot can check them only after `Directory::parse`,
  which reads the record from the bundle: so check 6 refuses a bundle that
  its own record does not admit, and says nothing of another bundle.
- **Units.** Every field counts pages, segments or entries, so a limit that
  a test exceeds by one page or one entry is refused at boot, or by the
  check of a segment or a commit.
- **Fixed bounds.** The loops of `validate` and of a commit of a child are
  bounded by the hard limits `MAX_SEGMENTS` and `MAX_WINDOW_PAGES`, not by
  the values of a record, so a change of the values changes neither the
  checks nor the bounds.
- **Defaults.** When the directory holds no capacity record, the default
  record of the board, `DEFAULT_CAPACITIES` (planned) of the
  [objects](../../objects-capabilities/objects/contract.md#capacity-record)
  contract, gives the loading part, which is checked in the same way. Each
  default value is a constant of the board crate, named by its field as the
  last column states, and passes these checks with the image of the board;
  the tests of the limits of loading measure them (planned).

The largest image window that check 4 admits, for the images of the
[table pools](../../memory/address-space/contract.md#table-pools) of the
address-space component:

| Image | $N - K$ | Largest `image_window_pages` | Window |
| --- | ---: | ---: | ---: |
| QEMU virt, 8 MiB | 22 | 9,728 | 38 MiB |
| Raspberry Pi 5, 8 MiB | 21 | 9,216 | 36 MiB |
| Either board, the largest | 14 | 5,632 | 22 MiB |

## Errors

The dispatch refuses a call with three statuses of the ABI, which the
[architecture](../../../architecture.md#system-calls-and-the-abi) names;
`loader::Error` (planned) holds the errors of `validate`.

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `UNSUPPORTED_OPERATION` | An immediate of the `SVC` other than 0; an `x8` with a bit of bits 16 to 63 set, the number 0, or a number without a row of the version in the dispatch table of the running image, every diagnostic number of the default image among them | `syscall` | The operation number and version: first, for the immediate, and third, for the number |
| `UNSUPPORTED_VERSION` | An `x7` other than `VERSION` | `syscall` | The operation number and version, after the immediate |
| `INVALID_ARGUMENT` | An `x6` other than 0; an argument register that the operation does not use other than 0 | `syscall` | The form of the register arguments, first: `x6`, then the unused registers in ascending order |
| `Bounds` | A `memory_bytes` of 0 or below `file_bytes`; an R or RX segment whose `file_bytes` differs from its `memory_bytes`; a range outside the segment range of the image window | `validate`, segment step | The form of the register arguments: first, fifth and sixth |
| `Alignment` | An `address`, `offset` or `memory_bytes` that is not a multiple of 4096 | `validate`, segment step | The form of the register arguments, after the first `Bounds` |
| `Overflow` | An `address` + `memory_bytes` or `offset` + `file_bytes` beyond 64 bits | `validate`, segment step | The form of the register arguments, after `Alignment` |
| `Permissions` | `flags` other than 4, 5 and 6 | `validate`, segment step | The form of the register arguments, after `Overflow` |
| `Entry` | An `entry` that is not a multiple of 4, or that lies in no RX segment of the plan | `validate`, commit step | The form of the register arguments, for the multiple of 4; object state, after `Capacity`, for the RX segment |
| `NotStaged` | A plan of none: the caller has no creation staged | `validate`, segment and commit steps | Object state, first |
| `Truncated` | A range of the file beyond the bytes of the entry of the image, rounded up to a page | `validate`, segment step | Object state, after `NotStaged` |
| `Overlap` | A segment that shares a page with a segment of the plan | `validate`, segment step | Object state, after `Truncated` |
| `Capacity` | A plan that holds `image_segments` segments, at a segment; a plan without a segment, at a commit | `validate`, segment and commit steps | The caller's quota, first, at a segment; object state, after `NotStaged`, at a commit |
| `PrivatePages` | Private pages of the image beyond `image_private_pages`: those of its RW segments at a segment, with the stack at a commit | `validate`, segment and commit steps | The caller's quota, last |
| `InvalidConfiguration` | A record shorter than 92 bytes; a field of 0 or above its hard limit; an initial stack that leaves no page of the window to the segments or exceeds the private pages of an image | `validate`, step `Limits` | At boot, after the checks of the VM part |
| `WindowTables` | An image window whose tables, with those of the VM window, exceed the tables that the lower kernel set leaves | `validate`, step `Limits` | At boot, after `InvalidConfiguration` |
| `RootPrivatePages` | A `root_private_pages` below the root's private pages | `validate`, step `Limits` | At boot, after `WindowTables` |
| `BundleLimits` | A boot bundle with more pages than `bundle_pages` or more entries than `bundle_entries` | `validate`, step `Limits` | At boot, last |

- **Order.** Each entry checks in the order of its rule section and returns
  the first error. The places of the last column are those of
  [Order of errors](#order-of-errors). The dispatch refuses before any
  entry of an operation runs; the errors of `validate` reach EL0 through
  `spawn_segment` and `spawn_commit`, which return them as they are, by
  their places among the errors of the creation component
  ([errors](../../objects-capabilities/creation/contract.md#errors)); the
  errors of the step `Limits` stop the boot.
- **No change on failure.** No error changes state. `syscall` and
  `validate` write nothing; a call that the dispatch refuses leaves every
  field of the kernel state as it was, gives no plan and writes no counter,
  and the dispatch writes only its result registers; a composing entry
  that meets an error of `validate` discards its buffer, so the kernel
  state after any failed operation equals the state before it. There is no
  exception. The settlements before the operation in its transition are
  transactions of their own and stay.
- **Outcomes are not errors.** `Again`, a blocked wait, the end of the
  caller's thread and the halt are results of a step, not errors; the
  outcomes that the contracts of the operations write are results of
  accepted calls ([Results](#results)).
- **Totality.** `syscall` gives a result for every value of the registers,
  and `validate` for every plan, step and limits. The `InvalidState` of an
  acknowledgement that a pending value without a plan in flight would
  meet answers a call that the architecture crate never makes
  ([The round trip of plans](#the-round-trip-of-plans)).
- **Names.** The names are those of this contract; the numeric values of
  the statuses and of the errors that reach EL0 belong to the ABI
  inventory, which maps every error of every contract to its status.

The prototype's ABI had ten statuses besides those of IPC and waits, which
the IPC and waits contracts map, and its loader nine errors. Here:

| Prototype status or error | Here |
| --- | --- |
| `OK` | Kept: the status of success, in `x0` |
| `PERMISSION_DENIED` | Not a status of this page: a status of the ABI inventory (planned), for errors that refuse authority, such as `PermissionDenied` of the capabilities component, `NotReceiver` of the IPC component, `NotOwner` of the lifecycle component and `NotOwnProcess` of the creation component; the mapping and the value belong to the inventory |
| `INVALID_HANDLE` | Not a status of this page: a status of the inventory for the errors of the resolution of a handle, `InvalidHandle`, `NoCapability` and `StaleHandle` of the capabilities component |
| `INVALID_ARGUMENT` | Kept, for an `x6` or an unused argument register other than 0; the inventory may give the same status to the errors of the form of the register arguments of other contracts |
| `UNSUPPORTED_VERSION` | Kept, for an `x7` other than 1, where the prototype refused every value other than 0 |
| `UNSUPPORTED_OPERATION` | Kept, for an immediate other than 0, the bits of `x8` above bit 15, the number 0 and a number without a row, the diagnostic numbers of the default image among them |
| `NO_CAPACITY` | Not a status of this page: a status of the inventory for errors of shared capacity; the full capability space of the prototype is `SlotOccupied` or `InvalidSlot` of the capabilities component, since the caller names the slot |
| `INVALID_STATE` | Not a status of this page: a status of the inventory for errors of object state |
| `OBJECT_GONE` | Not a status of this page: a status of the inventory for `StaleReference` of the objects component |
| `OVERFLOW` | Not a status of this page: a status of the inventory for errors of the caller's quota and of exhausted generations (planned); the prototype's overflow of its global token and transaction counters does not apply, since no identifier of the kernel is global |
| `Truncated` | Rewritten: a range of the file beyond the entry of its image, rounded up to a page, not beyond the whole bundle; the truncations of an ELF file belong to the parser of the runtime of EL0 |
| `Format` | Moved to the creation component: `NoImage` of `spawn_begin`, an index that names no entry of the kind Image; the format of an ELF file belongs to the parser of the runtime of EL0 |
| `Capacity` | Kept, for a plan with no segment at a commit and for a segment beyond `image_segments` |
| `Overflow` | Kept, for an addition beyond 64 bits |
| `Alignment` | Kept, for an address, offset or size that is not a multiple of 4096 |
| `Bounds` | Kept, for the sizes and the range of a segment; the private pages beyond their limit, which the prototype's `Bounds` held as the size of its data segment, are `PrivatePages` |
| `Permissions` | Kept, for flags other than R, RX and RW |
| `Overlap` | Kept, for a segment that shares a page with a segment of the plan |
| `Entry` | Kept, for an entry that is not a multiple of 4 or that lies in no RX segment; the profile that the prototype's entry selected does not exist |

The [creation](../../objects-capabilities/creation/contract.md#errors)
contract moves four rows of the prototype's execution manager and spawn
controller here: `InvalidLayout`, whose counterparts are the errors of
`validate` for a segment and a commit and the checks of the step `Limits`;
and the refusals of a version that differs, of an unused argument register
that is not 0 and of an unknown operation of spawning, which are
`UNSUPPORTED_VERSION`, `INVALID_ARGUMENT` and `UNSUPPORTED_OPERATION` of
`syscall`.

## Check and execute

`syscall` and `validate` write nothing. The write entries of the dispatch
make no write of their own on a write set: every write of kernel state in
a transition is a transaction of a composed entry, which makes all its
checks before its first write
([rule 1](../../../conventions/provable-subset.md#1-check-then-execute)),
changes only the copies in its write set and allows in its write phase
only the failures that its contract lists. The dispatch writes outside
write sets only fields that the executing CPU owns: the result registers
and the saved `elr` of the saved context of the current thread, and the
current thread in the record of the CPU, each after the write-back of the
transaction that decides it, and none of them changes anything else: a
refused saved context makes `set_return_registers` write nothing, and the
return then ends the process ([Results](#results)).

| Entry | Checks before the first write | Write set | Writes after the write-back |
| --- | --- | --- | --- |
| `syscall` | The immediate, the version, the number, `x6` and the unused argument registers | Nothing: a function | Nothing |
| `validate` | Those of its step | Nothing: a function | Nothing |
| `entry` | The class of the event; for a system call, those of `syscall` and then those of the entry of the operation | None of its own: the settlements of expired waits, each a transaction of its own, and then the transactions of the operation, each with the write set of its contract | The result registers, or the `elr` moved back by 4; the first plan of the operation, if there is one; then those of `compose_return` |
| `resume` | The pending value | None of its own: that of the acknowledgement that it calls | The next plan, if there is one; the result registers or the `elr`; then those of `compose_return` |
| `compose_return` | The deadline of the scheduler dispatch and the reschedule flag; the saved context of the chosen thread | None of its own: those of `scheduler::preempt`, `scheduler::choose`, `lifecycle::fault` of a refused context and `Space::join` | The current thread of the CPU; the return plan, the wait or the halt |

- **Failures of a composed transaction.** A failure in the write phase of a
  composed entry, `WriteSetFull` or a fault-injection point of a test build
  ([write-set transactions](../../objects-capabilities/objects/contract.md#write-set-transactions)),
  discards that transaction and leaves the state from before it; the
  transactions before it in the transition, the settlements of expired
  waits among them, stay. The dispatch then writes the error of the call
  as for every refused call.
- **Within W.** The dispatch adds no item to a composed write set, so each
  stays within the bound of its contract and of $W$ = 64, as the write sets
  of [Operations](#operations) state.
- **Plans.** No plan is given before the write-back of the entry that
  fixes it, and no plan fails, so no failure follows a plan.

## Work bounds

- `syscall` takes a fixed number of steps: the immediate, the version, the
  number, the `match` of the table, `x6` and at most six argument
  registers.
- `validate` compares a segment with at most the `MAX_SEGMENTS` = 8
  segments of the plan, since the check of overlap comes before that of
  their number, and sums at most 8 segments; a commit step reads at most 8
  segments; the step `Limits` makes a fixed number of checks.
- `entry` settles at most the thread capacity of expired waits, the loop
  that the [waits](../../ipc-waits/waits/contract.md#work-bounds) contract
  bounds; for a system call it adds `syscall` and the operation, within the
  bounds of its contract, with, for `call` and `receive`, one lookup and two
  calls of `is_alive`.
- `resume` makes one acknowledgement, within the bounds of its contract,
  and then ends the transition as `entry` does.
- `compose_return` makes at most one `preempt`, and for each start one
  `choose`, which walk at most the run queues of the CPU
  ([work bounds](../../scheduling/scheduler/contract.md#work-bounds)), and,
  after a refused context, one `lifecycle::fault`, within the
  [work bounds](../../objects-capabilities/lifecycle/contract.md#work-bounds)
  of the lifecycle component; it starts again at most the thread capacity
  times, each after a refused context that ends a process.
- **Plans of a transition.** A transition gives at most the plans that the
  operation of its call allows, one round trip each: for a commit and a
  decommit at most `MAX_CALL_PAGES` = 512 pages, with a zero plan for each
  page of a decommit, for an `mprotect` two plans for each of at most 512
  pages, and for a step of a release at most `RELEASE_BATCH` = 64 pages
  ([work bounds](../../memory/vm/contract.md#work-bounds)); for a commit of
  a child the plans of its image, at most the pages of the image window
  and the private pages that the loading part allows
  ([work bounds](../../objects-capabilities/creation/contract.md#work-bounds));
  and for a step of a destruction at most one release plan, one reset plan
  or `RELEASE_BATCH` zero plans
  ([work bounds](../../objects-capabilities/lifecycle/contract.md#work-bounds)).
- **No long operation.** The component has no long operation of its own:
  every transition runs to its result, and no progress of the dispatch is
  stored between two transitions. The long operations that it composes, a
  revocation, a destruction and a release, store their progress in their
  objects and are executed again from the saved user registers, one step
  in each transition ([Execution again](#execution-again)).
- The constants are `VERSION` = 1; `MAX_SEGMENTS` = 8; `MAX_WINDOW_PAGES` =
  131,072; `MAX_BUNDLE_PAGES` = 130,560; `IMAGE_BASE` = `0x4020000000` and
  `IMAGE_END` = `0x4040000000`; and $W$ = 64 of the objects contract.

## Determinism

- **Decoding.** The result of `syscall` follows from the immediate and the
  registers of the call and the dispatch table of the running image, and
  that of `validate` from its arguments; neither makes a choice.
- **Order in a transition.** The settlements of expired waits come first,
  in the order of their deadlines and registrations
  ([internal choices](../../../security.md#internal-choices)); then the
  event, with the transactions of the operation in the order of its
  contract; then the return. Each plan is executed before the next is
  given, in the order of the entry that gives them.
- **Time.** A transition reads the time once on entry and passes it to
  every entry that it composes, also after its plans, through the pending
  value: the time source of
  [ND-01](../../../security.md#nd-01) of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism).
- **Interrupts.** Which interrupt is pending at an entry or at a return,
  and so where a long operation meets a preemption point and which thread
  runs next, is the arrival of interrupts of
  [ND-01](../../../security.md#nd-01), for the timer, and of
  [ND-02](../../../security.md#nd-02), for devices; for each, the rules of
  this page fix the result, and the result of a call does not depend on
  it.
- **Several CPUs.** With more than one CPU, the order in which CPUs enter
  the kernel and take their tokens is the multicore interleaving of
  [ND-03](../../../security.md#nd-03); for each such order, the rules of
  this page fix the result.
- **The limits.** The limits follow from the capacity record, or the
  default record of the board, and the boot bundle, so cold boots of one
  image check the same values.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The limits of the loading part, `loader::Limits` in the kernel root | Shared, read-only after boot | The boot CPU, which checks them with the step `Limits` before the first entry from EL0 | The acceptance of the step `Limits` at boot, before the first entry from EL0 | Once, at boot, before the first entry from EL0 and before any other CPU starts; the field does not change afterwards |

The dispatch keeps no field of its own across a transition: the dispatch
table is code, and a pending value lives in the frame of `el0_dispatch` on
the kernel stack of the CPU, within one transition. The saved context of a
thread, whose result registers and `elr` the dispatch writes, is classified
by the [context](../../boot-platform/context/contract.md#state-fields)
component, and the current thread of a CPU by the
[address-space](../../memory/address-space/contract.md#state-fields)
component; the plans of images in the staging records belong to the
[creation](../../objects-capabilities/creation/contract.md#state-fields)
component, and the state that the composed entries change to their own
contracts.

## Testing obligations

- The host tests of the modules `dispatch` and `loader` (planned) replay
  every vector of [Legacy test vectors](#legacy-test-vectors) whose entry
  is on this page, with its expected output, and the cases of the vectors
  of other pages that this page names, and write their results for the
  comparison with the specification
  ([host results](../../../formal-verification.md#host-results)).
- Rejection: one call for each row of the table of [Rejection](#rejection),
  with the immediates 1 and `0xFFFF`, the versions 0, 2, $2^{32}$ and
  $2^{64} - 1$, the values of `x8` 0, $2^{16}$, $2^{32}$ plus the number of
  an operation and $2^{64} - 1$, a production number without a row, and a
  diagnostic number in the default image and in a test build; `x6` with 1
  and $2^{64} - 1$; and, for each operation of the table, each unused
  argument register with 1, $2^{63}$ and $2^{64} - 1$. Each compares every
  field of the state before and after, the result registers aside, and
  checks those registers.
- Order: for each pair of consecutive checks of `syscall` and of each step
  of `validate`, a call that breaks both gets the error of the earlier;
  a call that breaks a check of `syscall` and one of its operation gets the
  error of `syscall`.
- A property test with fixed seeds draws the immediate and `x0` to `x8` and
  compares the result of `syscall` with an independent model of the table
  built from the ABI inventory; it is the seed of the fuzzing of the
  dispatch (planned).
- Results: after a success, a failure, a blocked call and execution again,
  `x0` to `x5` hold what [Results](#results) states and every other field of
  the saved context is unchanged; after execution again `elr` is the
  address of the `SVC`.
- Composition, with a host double of `el0_dispatch` that executes plans: a
  commit of the VM component gives its plans one at a time through `entry`
  and `resume`; a commit of a child gives its plans and copies in their
  order; a kill gives the release plan, the reset plan and the zero plans
  of its steps, and ends each step with `Again` and the `elr` moved back;
  an interrupt pending before a return is handled before the return; the
  expiry of a wait in the transition of an operation settles first; a
  refused context starts the return again, and one of the root halts; a CPU
  with no thread to run waits and chooses again at its wake; the exit of
  the root gives the halt.
- Load validation: each error of a segment step and of a commit step
  through a case that gives it, the plan given back unchanged; segments at
  the edges of the segment range, at `IMAGE_BASE`, at the last page below
  the guard, on the guard, in the stack and below `IMAGE_BASE`; two
  segments that share one page; `image_segments` segments and one more;
  the private pages at their limit and one page beyond, at a segment and at
  a commit; and a property test with fixed seeds over random plans that
  checks that no accepted plan holds a page that would be mapped writable
  and executable.
- Loading configuration: a record that breaks each check of the step
  `Limits`, which stops the boot with its error and without a fallback; a
  record of 91 bytes; the largest window that check 4 admits for
  $N - K$ = 14 and 22, and one page more; a `root_private_pages` one page
  below the root's private pages; a bundle one page and one entry beyond
  its limits; and the default record of each board, which passes.
- The image window: a host test checks the relations of `IMAGE_BASE` and
  `IMAGE_END` with the bundle window of the address-space component and
  the VM window of the VM component.
- QEMU tests on QEMU virt, from EL0, once the operations exist: for each
  operation of the inventory, one call with an argument that its checks
  refuse; one call with an unknown operation number and one with an
  unknown version; and a child whose segments the root stages with an
  overlap, with W and X, outside the window and unaligned, each refused
  with the state unchanged. The 8 GB Pi 5 runs the same.
- The tests take their expected values from this page, from the vectors
  and from independent models, never from an earlier run of the code under
  test ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The modules `dispatch` and `loader` have no `unsafe` code, no assembly and
no MMIO. Their targets are to be two: the dispatch function `syscall`,
whose obligations are the six rules of the dispatch function of
[Rejection](#rejection), over every row of the table, and `validate`,
with its three steps. The value types of the rows of `syscall` and
`validate`, `Plan::new`, which forms the input of `validate`, and the
constants of the first row belong to these two targets. The entries that
compose the entries of other components, `entry`, `resume` and
`compose_return`, have effects on the state of those components that the
specification of this component does not describe: the expiry of waits,
the operations of the table with their compositions, the faults of
processes, the round trip of plans with the acknowledgements of the VM,
creation and lifecycle components, and the return with the scheduler, the
context and the address space. Each
composed entry is covered by the targets of its own component, and the
composition by none; the rows below record it, carried by the proof of
object lifetimes, waits and sequential composition, by release 0.2. The
plans are executed by `krepi_arch::mmu::apply`,
`krepi_arch::el0::invalidate_asid` and `krepi_arch::frames::apply`, rows of
the [page-tables](../../memory/page-tables/contract.md#open-obligations),
[address-space](../../memory/address-space/contract.md#open-obligations)
and [VM](../../memory/vm/contract.md#open-obligations) obligations; the
Rust entry `el0_dispatch` of an image, which calls `entry` and `resume` and
executes their results, is code of its board crate, which the open
obligations of that crate cover by its path, as the address-space contract
states; and the halt is the fatal path of the boot contract.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/src/dispatch.rs#entry` (planned) | `code` | Reads and writes (composes the expiry of waits with `waits::first_deadline`, `waits::complete`, `ipc::settle` and `scheduler::enqueue`, `address_space::classify`, the entry of each operation of the table with the compositions of [Operations](#operations), `lifecycle::fault`, and the result registers with `Context::set_return_registers`) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/dispatch.rs#resume` (planned) | `code` | Reads and writes (composes `vm::acknowledge`, `creation::acknowledge` and `lifecycle::acknowledge` after an executed plan, and ends the transition as `entry` does) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/dispatch.rs#compose_return` (planned) | `code` | Reads and writes (composes `scheduler::preempt`, `scheduler::choose` with `waits::first_deadline`, `Context::validate`, `lifecycle::fault` of a refused context, `Space::join` and `Space::ttbr0`) | The proof of object lifetimes, waits and sequential composition | `0.2` |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 20 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository,
so the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/loader/tests.rs` | 9 |
| `src/abi/tests/validation.rs` | 3 |
| `src/abi/tests/authority.rs` | 5 |
| `src/abi/tests/lifecycle.rs` | 3 |

- These are all the tests of these four files. The prototype's
  `src/loader` holds 22 tests: these 9, and 13 of the parser, the
  thread-local storage and the start-up of the runtime of EL0,
  `src/loader/tls_tests.rs` 4, `src/loader/startup/tests.rs` 7 and
  `src/loader/catalog.rs` 2, which are code of EL0 and not vectors of the
  kernel. Its `src/abi` holds 78: these 11, the 57 of its IPC,
  notification, wait and clock tests, which the IPC, waits and scheduler
  contracts freeze, and the 10 of `src/abi/channel/tests.rs` and
  `src/abi/thread/tests.rs`, 4 and 6, whose shared buffers and threads of
  a process come in release 0.2.
- The id of a vector is the path of its file below `src/`, without the
  directories and files named `tests` and without `.rs`, with a hyphen
  between the parts and in place of each underscore, and the position of
  the test among the tests of its file, from 1.

A vector of this page is one test function. The vector file is to hold one
line for each case of a vector through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1 in the order of the test; a
case that its row marks not applicable has no line, and a vector whose
Entry column names no entry of this page has none.

**The fixtures.** The tests of `src/loader/tests.rs` build an ELF file of
8192 bytes whose one program header names an RX segment of 4096 bytes
from offset 4096 at the start of the prototype's compact window, with that
address as the entry. Here that file is the entry I of the kind Image of
the directory, 8192 bytes, and its segment is
`S = seg(4096, 4096, B, 4096, 5)`. The limits L are
`image_window_pages=512`, `image_segments=8`, `image_private_pages=64` and
`image_stack_pages=4`, so the image window is `[B, B + 0x200000)`, its
stack the four pages below its top, and the segment range `[B, G)` for
G = `B + 0x1FB000`, the guard. The tests of `src/abi/tests/` keep a caller
process with a capability space of 8 entries, or 1, another process, and a
target process with its thread, to whose thread the caller holds a token
with every right. Here R is the root; C, O and P are children of R, with
P's thread T; C's table holds in slot 2 a capability to P with every right
of a process and in slot 3 one to T with every right of a thread, grants
of R at C's creation, and the other slots of C's table and every slot of
O's table are empty; the tables have `capability_slots=8`.

**Notation.** B is `IMAGE_BASE`, and M is $2^{64} - 4096$.
`seg(o, f, a, m, x)` is the segment of offset o, file bytes f, address a,
memory bytes m and flags x;
`plan(I, n)` is the plan of the image I whose entry holds n bytes, with
the segments listed after it. "validate of s into p" is
`validate(p, Segment(s), L)`, and "the commit of p at e" is
`validate(p, Commit(e), L)`. A handle is written `<slot>@<generation>`.
"C's `op` of h" is a system call of C's thread through the dispatch, with
the version 1, the number of `op` and the handle h, and the other argument
registers that the row gives; "C kills P through h" is `kill` through h,
called again until its result. The output of a call is `ok`, followed by
its results, or `err=<error>`, with the error by its name on this page or
on the contract of the operation. "Changes nothing" means that every field
of the kernel state is as before, the result registers aside.

**Behaviour changes.** These rules differ from the prototype:

- The version is 1 here, and 0, the prototype's only version, is refused:
  a case of the prototype with its invalid version 1 is a case with the
  version 0 here, and its valid version 0 the version 1.
- The dispatch checks the immediate, the version and the operation number
  before the reserved register, where the prototype checked the version,
  then the reserved register, then the number.
- Only the operation numbers whose result does not depend on the numbers
  that the inventory assigns are cases: 0 and the values with a bit above
  bit 15, such as $2^{32}$ plus a number and $2^{64} - 1$.
- A query names a process, and its results are the state, the exit reason
  and code and the CPU time of the process: the prototype's states of a
  thread are those of its process here, and a capability to a thread is
  not queried in release 0.1.
- A handle names a slot of the caller's own table, chosen by the caller;
  the prototype's tokens of a capability space, chosen by its registry,
  and its full space (`NO_CAPACITY`) are the slots and errors of the
  capabilities component, and the codes of the statuses belong to the ABI
  inventory.
- A revocation reports completion and no count, and a close leaves no
  closed entry in place, where the prototype counted closed ancestry.
- One image window, from the limits, replaces the prototype's two
  profiles: the private data of an image may lie anywhere in the segment
  range, its stack is configured, and the file range of a segment is
  checked against its image, not against the whole bundle.
- The parsing of ELF files is the runtime's of EL0: the cases of the
  prototype that break a field of an ELF header have no line.

### `src/loader/tests.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `loader-1` | 35 | `every_truncation_before_last_load_byte_is_rejected` | validate of S into `plan(I, n)`: for n from 1 to 4096, `err=Truncated`; for n from 4097 to 8192, `ok`, the plan with S, since the page that holds the last byte of an entry belongs to it. The prototype's truncations of the headers of the ELF file, which its parser refused, have no case: the parser of the runtime of EL0 reads them | `validate` |
| `loader-2` | 43 | `parser_rejects_overflow_format_entry_and_alignment` | The broken fields that have a counterpart in the arguments of a segment or a commit, each changing nothing: validate of `seg(4096, 4096, B, 4096, 7)`, `err=Permissions`; of `seg(M, 4096, B, 4096, 5)`, `err=Overflow`; of `seg(4096, 4096, B + 1, 4096, 5)`, `err=Alignment`; of `seg(4096, 4096, B, M, 5)`, `err=Overflow`; the commit of `plan(I, 8192), S` at `B + 1`, `err=Entry`, and at `B + 4096`, outside S, `err=Entry`. The offset of the program headers, their type, their alignment, the machine and the number of program headers have no case: they are fields of the ELF file, which the parser of the runtime of EL0 checks | `validate` |
| `loader-3` | 63 | `overlapping_loads_and_entry_in_nx_data_are_rejected` | validate of S into `plan(I, 8192), S`: `err=Overlap`. The commit of `plan(I, 8192), seg(4096, 4096, B, 4096, 4)` at B, an entry in an R segment: `err=Entry` | `validate` |
| `loader-4` | 74 | `failed_mapping_does_not_change_plan` | validate of S into `plan(I, 8192), S`: `err=Overlap`; validate of `seg(4096, 4096, B, 4096, 7)` into it: `err=Permissions`; `validate` writes nothing, so the plan of the staging record stays `plan(I, 8192), S` after each; the commit of that plan at B: `ok`, with 4 private pages, those of the stack | `validate` |
| `loader-5` | 90 | `private_data_may_have_zero_tail_but_immutable_pages_may_not` | validate of `seg(8192, 0, B + 0x1000, 4096, 6)`, an RW segment of no byte of the file, into `plan(I, 8192)`: `ok`; validate of `seg(8192, 0, B, 4096, 5)`, an RX segment with fewer bytes of the file than of memory: `err=Bounds` | `validate` |
| `loader-6` | 110 | `virtual_and_source_overflow_fail_closed` | validate of `seg(4096, 4096, M, 4096, 5)` into `plan(I, 8192)`: `err=Overflow`, before the check of the window; of `seg(M, 4096, B, 4096, 5)`: `err=Overflow` | `validate` |
| `loader-7` | 134 | `native_profiles_reject_mixed_code_data_and_reserved_gaps` | With U = `seg(4096, 4096, G - 4096, 4096, 5)`, the last page of the segment range, and V = `seg(8192, 0, B, 65536, 6)`, 16 private pages: validate of U and then of V into `plan(I, 8192)`, `ok`, and the commit of the plan at `G - 4096`, `ok`, with 20 private pages. Into `plan(I, 8192), U`: V at `B - 0x10000`, below the window, and at `G`, on the guard, each `err=Bounds`, while V at `B + 0x100000` is `ok`, since the private data of an image has no fixed base; and V with the flags 7, `err=Permissions`. Into `plan(I, 8192)`: `seg(4096, 8192, G - 4096, 8192, 5)`, into the guard, `err=Bounds`. The commit of U and V at B, an entry in the RW segment, `err=Entry`. The prototype's window of each profile and its plans that mix the two have no case: there is one window | `validate` |
| `loader-8` | 219 | `native_elf_entry_and_loaded_extents_must_select_the_same_profile` | No case: there is one image window, and that the entry of an ELF file and its program headers agree is checked by the parser of the runtime of EL0 | None |
| `loader-9` | 236 | `initial_stack_charge_is_profile_bound` | The initial stack is `image_stack_pages` of the limits for every image: the commit of `plan(I, 8192), S` at B gives 4 private pages, those of the stack, and at `B + 4092`, the last instruction of S, the same. The commit of that plan at `B + 0x200000`, the top of the window, at `G`, at 0 and at $2^{64} - 1$, entries in no RX segment or not a multiple of 4, is each `err=Entry`. The prototype's stack of 4096 bytes and of 16 KiB by profile does not apply | `validate` |

### `src/abi/tests/validation.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-validation-1` | 4 | `version_and_operation_are_full_width_and_fail_without_mutation` | C kills P through `2@1` with `x7` 0, $2^{32}$ and $2^{64} - 1$: each `err=UNSUPPORTED_VERSION`; with the version 1 and `x8` 0, $2^{32}$ plus the number of `kill`, and $2^{64} - 1$: each `err=UNSUPPORTED_OPERATION`. Each changes nothing: C's table and P are as before, P alive. The prototype's operation number 6 has no case, since whether a number has a row depends on the inventory | `syscall` |
| `abi-validation-2` | 24 | `every_reserved_or_unused_argument_is_rejected_before_a_mutating_operation` | For C's `query` of `2@1` with the selector 0, `derive` from `3@1` with OBSERVE into slot 5, `close` of `3@1`, `revoke` of `3@1` and `kill` of `2@1`: `x6` 1 and $2^{64} - 1$, and each argument register that the operation does not use set to $2^{64} - 1$, are each `err=INVALID_ARGUMENT` and change nothing. Then C's `derive` from `3@1` with OBSERVE into slot 5: `ok 5@1` | `syscall`; `derive` of the capabilities component |
| `abi-validation-3` | 60 | `malformed_rights_and_invalid_tokens_never_allocate_or_release` | C's `derive` from `3@1` into slot 5 with the masks 0, $2^{63}$ and $2^{64} - 1$: each `err=InvalidRights`; with 16, bit 4, which a thread does not define: `err=PermissionDenied`, where the prototype gave `INVALID_ARGUMENT`. C's `query`, `close`, `revoke` and `kill`, and `derive` with OBSERVE, through the handles 0, `4@1` and $2^{63}$, which name an empty slot of C's table: each `err=NoCapability`; through $2^{64} - 1$, slot 65,535: `err=InvalidHandle`. None changes anything | `syscall`; the lookups and `derive` of the capabilities component |

### `src/abi/tests/authority.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-authority-1` | 4 | `scalar_tokens_never_select_another_callers_namespace` | O's `query`, `close`, `revoke` and `kill` of `2@1`, and `derive` from `2@1` with OBSERVE, name slot 2 of O's own table, which is empty: each `err=NoCapability`, changing nothing. Then C's `query` of `2@1` with the selector 0: `ok state=Alive`. The prototype's caller without a capability space has no case: every process has its table, and the caller is the process of the running thread | `syscall`; the lookups of the capabilities component |
| `abi-authority-2` | 46 | `derived_observation_cannot_control_revoke_or_amplify_authority` | C's `derive` from `2@1` with OBSERVE into slot 4: `ok 4@1`; C's `query` of `4@1`: `ok state=Alive`. C's `kill` and `revoke` of `4@1`: each `err=PermissionDenied`; C's `derive` from `4@1` with OBSERVE, and with every right of a process, into slot 5: each `err=PermissionDenied`, since `4@1` lacks GRANT. None changes anything, and P stays alive | `syscall`; `derive` of the capabilities component; `query` and `kill` of the lifecycle component |
| `abi-authority-3` | 77 | `grant_and_revoke_bits_do_not_imply_native_object_authority` | C's `derive` from `2@1` with OBSERVE and GRANT into slot 4: `ok 4@1`; from `4@1` with CONTROL into slot 5: `err=PermissionDenied`, changing nothing; from `4@1` with OBSERVE into slot 5: `ok 5@1`. C's `derive` from `2@1` with GRANT and REVOKE into slot 6: `ok 6@1`; C's `query` and `kill` of `6@1`: each `err=PermissionDenied`; C's `revoke` of `6@1`, which has no descendant: `ok`, complete at once | `syscall`; `derive` and `revoke` of the capabilities component; `query` and `kill` of the lifecycle component |
| `abi-authority-4` | 108 | `capacity_failure_is_explicit_and_preserves_the_original_authority` | With C's slots 0, 1 and 4 to 7 filled by derivations from `2@1`, every slot of its table full: C's `derive` from `2@1` with OBSERVE into slot 4: `err=SlotOccupied`, and into slot 8: `err=InvalidSlot`; each changes nothing, the count of capabilities of P among it. C's `query` of `2@1`: `ok state=Alive`; C's `close` of `2@1`: `ok`. The prototype's capability space of one entry has no case: a table has `capability_slots` entries, at least 2 by the boot of the root | `syscall`; `derive` and `close` of the capabilities component |
| `abi-authority-5` | 126 | `caller_generation_and_liveness_are_checked_independently_of_tokens` | After R kills and reaps P, C's `query` of `2@1`: `err=StaleReference`; R's next child P2 takes P's process slot at its next generation, and C's `query` of `2@1` is still `err=StaleReference`, since the capability names P and not P2. Each changes nothing. The prototype's calls of a caller that was dying or reaped have no case: a thread whose process has left Alive was removed and makes no call | `syscall`; the lookup of the capabilities component; `query` of the lifecycle component |

### `src/abi/tests/lifecycle.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-lifecycle-1` | 5 | `query_reports_actual_object_states_and_preserves_a_retained_exit` | C's `query` of `2@1` with the selector 0 reaches `query` of the lifecycle component through the dispatch: `ok state=Alive` while T is ready, blocked or running; after P exits with 31, `ok state=Dying reason=Exited code=31`; after R kills P, `ok state=Dead reason=Exited code=31`; after R reaps P, `err=StaleReference`. The states of a thread and the take of the result of a wait have no counterpart, as the lifecycle contract states for this vector | `syscall`; `query`, `exit`, `kill` and `reap` of the lifecycle component |
| `abi-lifecycle-2` | 57 | `close_preserves_descendants_and_revoke_counts_closed_ancestry` | C's `derive` from `2@1` with every right into slot 4: `ok 4@1`; from `4@1` with OBSERVE into slot 5: `ok 5@1`. C's `close` of `4@1`: `ok`; C's `query` of `4@1`: `err=NoCapability`; of `5@1`: `ok state=Alive`, since the descendant stays. C's `revoke` of `2@1`: `ok`, once complete; C's `query` of `5@1`: `err=NoCapability`; of `2@1`: `ok state=Alive`. C's `derive` from `2@1` with OBSERVE into slot 4: `ok 4@2`, the next generation of the slot; C's `close` of `5@1`: `err=NoCapability`; C's `query` of `4@2`: `ok state=Alive`. The prototype's count of closed entries and of removed nodes has no counterpart | `syscall`; `derive`, `close` and `revoke` of the capabilities component; `query` of the lifecycle component |
| `abi-lifecycle-3` | 99 | `control_without_observation_can_stop_but_not_inspect_a_peer` | C's `derive` from `2@1` with CONTROL into slot 4: `ok 4@1`; C's `query` of `4@1`: `err=PermissionDenied`; C kills P through `4@1`: `ok`; C's `query` of `2@1`: `ok state=Dead reason=Killed code=0`; C's `close` of `4@1` and of `2@1`: each `ok`. These are the cases of the lifecycle contract for this vector, through the dispatch, with C as its Q and C's query of `2@1` in place of R's query of P, which gives the same result | `syscall`; `derive` and `close` of the capabilities component; `query` and `kill` of the lifecycle component |

### Vectors of other pages

These vectors are frozen on other pages, whose rows leave their cases of
the dispatch to this page, and the count of 20 leaves them out. Their
rows on those pages name the prototype's versions; by the conversion of
**Behaviour changes**, their invalid versions are 0, $2^{32}$ and
$2^{64} - 1$ here, and the version 1 is the valid one.

| Vector | Page and file | Line | Test | Here | Entry |
| --- | --- | ---: | --- | --- | --- |
| `abi-ipc-validation-1` | The [IPC contract](../../ipc-waits/ipc/contract.md#legacy-test-vectors), `src/abi/ipc/tests/validation.rs` | 4 | `full_width_version_and_operation_reject_without_side_effects` | A call with `x7` 0, $2^{32}$ and $2^{64} - 1$: each `err=UNSUPPORTED_VERSION`; with the version 1 and `x8` 0, $2^{32}$ plus the number of `call` and $2^{64} - 1$: each `err=UNSUPPORTED_OPERATION`; each before any entry of the IPC component, changing nothing. The prototype's numbers of its query and 20 have no case, since whether a number has a row depends on the inventory | `syscall` |
| `abi-ipc-validation-2` | The IPC contract, `src/abi/ipc/tests/validation.rs` | 31 | `every_reserved_argument_is_rejected_before_registration_or_endpoint_closure` | For `call`, `receive` and `reply`, `x6` or an argument register that the operation does not use holding 1, $2^{63}$ or $2^{64} - 1$: each `err=INVALID_ARGUMENT`, before any entry of the IPC component, changing nothing | `syscall` |
| `waits-transfers-5` | The [waits contract](../../ipc-waits/waits/contract.md#legacy-test-vectors), `src/waits/tests/transfers.rs` | 275 | `transfer_abi_rejects_malformed_and_forged_authority_without_reservation` | A call that transfers a capability, with `x7` 0: `err=UNSUPPORTED_VERSION`; with `x6` 1: `err=INVALID_ARGUMENT`; each before the form of the arguments of the call, its lookups and any reservation, changing nothing | `syscall` |
| `abi-notification-3` | The waits contract, `src/abi/notification/tests.rs` | 180 | `reserved_registers_version_and_unknown_operations_cannot_publish_events` | A `signal` with `x7` 0: `err=UNSUPPORTED_VERSION`; with `x6` 1: `err=INVALID_ARGUMENT`; with `x8` $2^{64} - 1$: `err=UNSUPPORTED_OPERATION`; with an argument register that `signal` does not use set to 1: `err=INVALID_ARGUMENT`; each with `x1` to `x5` 0, before the lookup, the word of the notification unchanged | `syscall` |
| `abi-waits-3` | The waits contract, `src/abi/waits/tests.rs` | 228 | `malformed_operations_leave_all_waits_untouched` | For `signal`, `wait`, `call`, `receive` and `reply`: an argument register that the operation does not use set to 1, `x7` 0 and `x6` 1, each refused before any lookup with the error of its check, changing nothing | `syscall` |

## Current deviations

The rules of this page differ from those of the prototype's ABI module and
loader, which [References](#references) lists:

- **The version.** The prototype served the experimental version 0 alone;
  here the first version is 1, and 0 is refused.
- **The order of the checks.** The prototype checked the version, then the
  reserved register, then the operation number; here the immediate, the
  version and the number come first, then the reserved register and the
  unused argument registers, as the order of errors of the security model
  puts the operation number and version first.
- **One table.** The prototype had a dispatcher for each group of its
  operations, with numbers of its own; here one table, keyed by the version
  and the number, with a production and a diagnostic range, serves every
  native operation.
- **Results.** The prototype's scalar calls replaced `x0` and `x1`, with
  the status and one value, and its IPC calls `x0` to `x5`; here every call
  that completes or is refused in its transition writes `x0` to `x5`, with 0
  in each unused result register and in `x1` to `x5` of a failure, and the
  completer of a blocked call writes the form, `x0` and `x1` or `x0` to
  `x5`, that the
  [waits](../../ipc-waits/waits/contract.md#wait-records) contract records
  for its operation.
- **Statuses.** The prototype's dispatcher mapped the errors of its
  components to fifteen statuses; here the errors keep the names of their
  contracts, and the ABI inventory maps them to statuses.
- **One image window.** The prototype's kernel admitted two profiles of
  windows, selected by the entry, with a fixed base of the private data, a
  stack of a fixed size by profile, at most four segments and private data
  of at most 64 KiB; here one window from `IMAGE_BASE`, whose size, stack,
  number of segments and private pages are limits of the capacity record,
  holds the segments anywhere below the guard of the stack.
- **The range of the file.** The prototype checked the file range of a
  segment against the whole bundle; here it is checked against the entry of
  its image, so a segment never reads another entry of the bundle.
- **Incremental checks.** The prototype checked each segment when it was
  staged and every segment again with the entry at the commit; here each
  segment is checked once, against those before it, and the commit checks
  only the entry, the number of segments and the private pages.
- **The order of the checks of loading.** The prototype checked the range
  of the file against the bundle before the access and the range of a
  segment, the number of segments before the overlap, and, at the commit,
  the number of segments and the entry before every segment; here the
  checks of a segment and of a commit follow the
  [order of errors](#order-of-errors): the form of the arguments, the
  access and the range of the segment among them, first, then the range of
  the file and the overlap, as object state, and then the number of
  segments and the private pages, as the caller's quota.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  the exception class `0x15` of `ESR_EL1` for an `SVC` in AArch64 state,
  with the immediate of the instruction in bits 0 to 15 of its
  instruction-specific syndrome.
- The kernel's own rules, which this page instantiates:
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for the operation numbers, the versions, the rejection, the deprecation,
  the SVC immediate and the execution model;
  [Kernel objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities)
  for the capacity record with the limits of loading;
  [Address spaces and VM objects](../../../architecture.md#address-spaces-and-vm-objects)
  for the mappings that loading creates from a request that the kernel has
  validated again;
  [Processes, POSIX and Linux compatibility](../../../architecture.md#processes-posix-and-linux-compatibility)
  for the loader of EL0 whose images the kernel validates again; the
  [provable core](../../../architecture.md#the-provable-core) and the
  [module order](../../../architecture.md#module-order-in-the-core); and
  the [internal choices](../../../security.md#internal-choices),
  [observable outputs](../../../security.md#observable-outputs),
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  and [integrity policy](../../../security.md#integrity-policy) of the
  security model.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/capabilities.md`, lines 36 to 75: the register
    contract of the prototype's scalar ABI, with the operation in `x8`, six
    arguments, the reserved `x6`, the version in `x7` and the status in
    `x0`, and its table of statuses, which this page keeps for the
    registers and the three statuses of the dispatch, and whose version 0,
    single result register and fifteen statuses it does not carry
    ([Current deviations](#current-deviations));
  - `docs/features/kernel/ipc.md`, lines 39 to 43: unused arguments that
    must be zero, inputs checked at full 64-bit width, and results that
    replace exactly `x0` to `x5` and keep every other register;
  - `docs/features/services/static-bootstrap.md`, lines 43 to 105: the
    interface of the prototype's staged loading, its segments of page-aligned
    ranges with R, RX and RW access, the equal file and memory sizes of R
    and RX segments, the zero tail of an RW segment, the refusal of overlap,
    overflow, other permissions and entries outside RX, and the check of
    the plan by the kernel even when the root parses no ELF file, which
    this page keeps, and its two profiles with their fixed bases and stacks,
    which it does not; its transaction and authority belong to the creation
    component;
  - `docs/features/kernel/user-execution.md`, lines 41 to 50: the
    prototype's layout of the EL0 address space, whose fixed addresses are
    not carried; the image window of this page takes their place.
