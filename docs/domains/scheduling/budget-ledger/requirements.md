---
features: none
---

# Budget-ledger requirements

The observable behaviour of the `budget-ledger` component of the
[scheduling and budgets](../README.md) domain. The rules that its code and
tests follow are in the [contract](contract.md). No feature document covers
the component, so the metadata lists none.

## Sources

- The class caps with one shared period, the charge of the whole interval
  of a dispatch, the debt of an overrun, credit that never accumulates
  beyond one allocation, the closed-form accounting of long intervals, and
  the loans of a caller's context to the services of its calls, with their
  effective priority, their bound of depth and their withdrawal, take the
  rules of the prototype's budget scheduler and of its synchronous budgets,
  which the [references](contract.md#references) of the contract list, with
  their host tests as the frozen [vectors](contract.md#legacy-test-vectors).
- The holdings that an admission carves from its creator, class by class,
  and that the reap returns, with charges to the record of a thread and to
  its class alone, the time of a transition as an argument with its
  premises, the platform parameters with the kernel margin converted at
  boot, and the records in the thread slots are new, from the kernel's
  [scheduling and budgets](../../../architecture.md#scheduling-and-budgets)
  and the budget lending of its
  [IPC](../../../architecture.md#ipc-notifications-and-waits); the
  [behaviour changes](contract.md#legacy-test-vectors) of the contract list
  where they differ from the prototype.
- The order of errors and the rules for internal choices follow the
  [security model](../../../security.md#internal-choices), and the time of a
  transition its entry [ND-01](../../../security.md#nd-01); the classes of
  state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The thread references, the write sets and the errors of references that
  the entries use are those of the
  [objects](../../objects-capabilities/objects/requirements.md) component;
  the classes, the run queues, the selection and the admission checks of
  the class and the ceiling are those of the
  [scheduler](../scheduler/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2, one
  Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host, booted with the platform parameters of the board.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release 0.1,
  with one of its four Cortex-A76 cores running and the platform parameters
  of the board.
- **Host.** The host tests of the module `ledger` of the core (planned) run
  on the development host and in CI, with the frozen vectors and the tests
  that the [contract](contract.md#testing-obligations) adds, each with the
  time and the platform parameters that it passes.
- One CPU. The ledger is a per-CPU data structure and the records of the
  threads belong to the ledger of one CPU, also while one CPU runs; no
  requirement here covers secondary CPUs, the settlement of a charge across
  CPUs or the locks that provide the tokens.

## Requirements

### LEDG-R01

**Ledger of a CPU.** At boot the ledger of a CPU takes the replenishment
period, the cap of each of the three classes and the kernel margin of its
board in microseconds, with the counter frequency, and converts them into
ticks of the virtual counter. It refuses a frequency of 0, a period of 0
ticks or of $2^{62}$ ticks or more, and caps and a margin whose sum
exceeds the period with `InvalidConfiguration`, and a value whose ticks do
not fit 64 bits with `Overflow`. Every class and every record of the CPU
counts its periods from one epoch with one period. The criterion: the
checks hold at their limits, and replenishment of a ledger whose epoch is
37 happens at 137 for a control and a background thread.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Ledger::new` (planned).
- **Contract.** [Classes](contract.md#classes) and
  [Replenishment](contract.md#replenishment).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `scheduler-budget-8` as a host test, and
  the host tests of the boot checks of the
  [contract](contract.md#testing-obligations). They show the conversion and
  the checks for parameters that the tests pass; the parameters of each
  board are shown by the tests of the scheduler, which hold their values.

### LEDG-R02

**Classes.** Each class has a ledger with its cap per period. The dispatch
credit of a thread never exceeds what remains of the cap of the class of
its context in the current period, and a class never uses the cap of
another, also when that cap is unused. An overrun of a class is its debt,
which later periods repay. The criterion: a control thread that has used
the control cap is not selectable while the interactive and background caps
stay unused, and a loan between threads of any two classes charges only the
class of the context.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ledger::charge` and `ledger::available` (planned).
- **Contract.** [Classes](contract.md#classes) and
  [Charging and debt](contract.md#charging-and-debt).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-4`,
  `scheduler-budget-accounting-8` and `scheduler-budget-loans-10` as host
  tests, with the selection of the scheduler.

### LEDG-R03

**Charging and debt.** When a dispatch stops, for any reason, its whole
interval is charged to the record of the owner of the context that it had
at its start and to the class ledger of that owner's class, and the part
beyond the remaining credit becomes debt in full. An interval that crosses
period boundaries is charged as if each tick were charged in turn and each
boundary replenished the credit, in a fixed number of steps for any
length. The criterion: the charges equal those of an independent tick
model, among them an overrun of 7 ticks in one period, a stop across two
boundaries and a stop after $10^{12}$ periods.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ledger::charge` (planned).
- **Contract.** [Charging and debt](contract.md#charging-and-debt).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-credit-1`,
  `scheduler-budget-scopes-accounting-1`,
  `scheduler-budget-scopes-accounting-3`, `scheduler-budget-accounting-1`
  to `scheduler-budget-accounting-4`, `scheduler-budget-accounting-7` and
  `scheduler-budget-accounting-9` as host tests, and the property test of
  the closed form of the [contract](contract.md#testing-obligations). They
  show the charges for the intervals of the tests; that the closed form
  equals the tick model for every interval is a property that the host
  tests sample and do not prove.

### LEDG-R04

**Replenishment.** At each period boundary the credit of a record becomes
the smaller of its credit plus its budget and its budget, and that of a
class the smaller of its credit plus its cap and its cap: a debt is repaid
first, and unused credit never accumulates. A record that a gap of any
number of periods separates from its last update is brought up to date in
a fixed number of steps. A record with debt $d$ and budget $b > 0$ that is
not charged, and whose budget no admission or release changes, regains
credit within $\lceil d/b \rceil$ boundaries, its debt falling at each of
them; a record with budget 0 is never replenished. Waits and sleeps neither
add nor remove credit. The criterion: the vectors of
replenishment hold, among them a gap of $10^{10}$ periods and a debt of 25
that a wait across one boundary leaves at 5.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ledger::replenish` and `ledger::available` (planned).
- **Contract.** [Replenishment](contract.md#replenishment).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-credit-2`,
  `scheduler-budget-6`, `scheduler-budget-accounting-5`,
  `scheduler-budget-accounting-6`, `scheduler-budget-accounting-8`,
  `scheduler-budget-scopes-accounting-7` and `scheduler-budget-waits-1` to
  `scheduler-budget-waits-3` as host tests, and the host tests of the two
  terminations of the [contract](contract.md#testing-obligations).

### LEDG-R05

**Admission and release.** The root starts with a holding of each class
equal to its cap and is admitted once. An admission gives a new thread one
amount for its class and one for each class below it, each carved from its
creator's holding of the same class: the amount of its class is its
budget, and the others let its process admit threads of those classes in
turn. A creator's own budget falls only when it admits a thread of its own
class. A budget of 0 and an amount for a class above the thread's are
refused with `InvalidConfiguration`, and an amount beyond the creator's
holding with `AdmissionRejected`. The reap of a thread returns all its
holdings to its owner at once, and the spending of its class stays in the
class ledger. For each class, the holdings of all records and the part
that the root has not taken add up to its cap. The criterion: the vectors
hold, among them a chain of six processes each of which gives its whole
holding to the next, and a thread admitted after the reap of one that
overran its budget, which the class ledger throttles, and the host test of
the carving by class holds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ledger::admit` and `ledger::release` (planned).
- **Contract.** [Admission and release](contract.md#admission-and-release)
  and [Budget records](contract.md#budget-records).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-scopes-accounting-2`,
  `scheduler-budget-scopes-accounting-4`,
  `scheduler-budget-scopes-accounting-5`,
  `scheduler-budget-scopes-lifecycle-1`,
  `scheduler-budget-scopes-lifecycle-3`,
  `scheduler-budget-scopes-lifecycle-7`, `scheduler-budget-lifecycle-3` and
  `scheduler-budget-lifecycle-4` as host tests, and the property test of
  the conservation of holdings and the host tests of the root, of the
  carving by class and of the current dispatch of the
  [contract](contract.md#testing-obligations).

### LEDG-R06

**Budget lending.** A loan lets one borrower run on the context of its
lender, the lender's own record or the context that the lender borrows, at
a depth of at most `MAX_LOAN_DEPTH` = 8 loans from the owner of the
context; it moves no credit, and every interval that the borrower runs is
charged to the owner of the context and to the owner's class, never to the
borrower. The borrower runs at the higher of its own class and the
effective class of its lender bounded by the borrower's ceiling. A borrower
whose borrowed context has no credit gets no credit from its own record. A
withdrawal returns one borrower to its own record and class. A second loan
to a borrower is refused with `OutstandingLoan`, and a ninth level of
depth with `LoanDepth`. The criterion: the vectors of loans hold, among them
a chain of eight loans whose withdrawal leaves no record with a source and
nine pairs of classes in which only the class of the caller is charged.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ledger::lend`, `ledger::withdraw` and `ledger::charge`
  (planned).
- **Contract.** [Lending](contract.md#lending).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-loans-1` to
  `scheduler-budget-loans-5`, `scheduler-budget-loans-7` to
  `scheduler-budget-loans-11` and `scheduler-budget-loan-scopes-1` as host
  tests, and the host tests of loans of the
  [contract](contract.md#testing-obligations). When a loan is made and
  withdrawn is shown by the tests of the IPC component, which compose these
  entries.

### LEDG-R07

**CPU time.** The CPU time of a thread is the sum of the intervals in which
it ran, on its own context or on a borrowed one, as far as their dispatches
have stopped; it never exceeds the time since the epoch. The criterion: the
vectors hold, among them a service that runs 7 ticks on its caller's
context, whose CPU time grows by 7 while its caller's grows by nothing.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ledger::cpu_time` and `ledger::charge` (planned).
- **Contract.** [CPU time](contract.md#cpu-time).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-scopes-accounting-1`,
  `scheduler-budget-accounting-2`, `scheduler-budget-accounting-3`,
  `scheduler-budget-accounting-7`, `scheduler-budget-lifecycle-3` and
  `scheduler-budget-loans-1` as host tests. The query of the CPU time of a
  process from EL0 is shown by the tests of the lifecycle component.

### LEDG-R08

**Time as an argument.** Every entry that depends on time takes the time
of its transition, and `charge` also the start of the dispatch, as explicit
arguments; no entry reads a counter or a clock. The time is the virtual
counter of the board in ticks, which does not decrease within a boot and
stays below $2^{63}$. The criterion: every host test passes its times, the
results do not depend on the speed of the host or on a fixed instruction
count, and the same calls with the same times give the same results.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Ledger::new`, `ledger::admit`, `ledger::release`,
  `ledger::charge`, `ledger::replenish` and `ledger::available` (planned).
- **Contract.** [Replenishment](contract.md#replenishment) and
  [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** Every frozen vector as a host test, with the times of the
  test, and the host tests of the
  [contract](contract.md#testing-obligations), each run twice with the same
  inputs. The reading of the counter on entry is the architecture crate's
  and is shown by its QEMU tests.

### LEDG-R09

**No change on failure.** Every error of the component leaves every record
and every ledger as it was: a refused admission, release or loan writes
nothing, and no refusal is counted. The criterion: for each error of the
contract, a call that gives it leaves every field compared before and after
unchanged, and the frozen vectors of refused loans hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-loans-7` to
  `scheduler-budget-loans-9` and `scheduler-budget-loans-11` as host tests,
  and the host test of each error of the
  [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or loops over
  periods, threads or loans, and the component has no long operation.
- The withdrawal of a chain of loans is at most `MAX_LOAN_DEPTH`
  withdrawals, which the IPC component makes in one transition.
- A record with debt $d$ and budget $b > 0$ regains credit within
  $\lceil d/b \rceil$ period boundaries once no dispatch on its context
  runs, while no admission or release changes its budget, and a class with
  debt $d$ and cap $c > 0$ within $\lceil d/c \rceil$; no requirement
  bounds when a thread with credit is selected, which is the scheduler's.
- No requirement bounds the time that an entry takes.

## Scope

- One CPU. The pending ticks of a record, which carry a charge from another
  CPU, stay 0; their protocol across CPUs, the migration of a record
  between ledgers, the tokens and their locks are not covered.
- The priority classes and their order, the run queues, the selection of a
  thread with its time slice and deadline, preemption, the admission checks
  of the class and the ceiling, and the platform parameters of each board
  are not covered; they are the
  [scheduler requirements](../scheduler/requirements.md).
- When a loan is made and withdrawn, the creation and reap calls that
  admit and release a thread, and the query of the CPU time of a process
  are not covered; the IPC, creation and lifecycle components compose the
  entries of this component and have their own requirements.
- No scheduling-context object, replenishment list, sporadic server or
  timeout handler exists, and no charge reaches an ancestor of a process.
- A process has one thread; further threads of a process are not covered.
- The operation numbers and numeric error codes of the ABI inventory are
  not covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Open obligations](contract.md#open-obligations) lists the adapter that
  lends the ledger of the executing CPU, which no requirement observes.
