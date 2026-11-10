---
features: none
---

# Context requirements

The observable behaviour of the `context` component of the
[boot and platform](../README.md) domain: the saved user context of a
thread, its initial value, its validation before every return to EL0, the
results that a call writes into it, and the save and restore of the FP/SIMD
and TLS registers of EL0. The rules that its code and tests follow are in
the [contract](contract.md). No feature document covers the component, so
the metadata lists none.

## Sources

- The layout, the initial context, the validation and the write of results
  take the rules of the prototype's saved user context and of its execution
  manager, which the [references](contract.md#references) of the contract
  list, with their host tests as the frozen
  [vectors](contract.md#legacy-test-vectors).
- FP/SIMD access for every thread at EL0, the save and restore at every
  entry from EL0 and return to it with the switch of `CPACR_EL1.FPEN`, and
  the errors that name the broken rule of a refused context are new; the
  [behaviour changes](contract.md#legacy-test-vectors) of the contract list
  where they differ from the prototype.
- The registers, their fields and their encodings follow the Arm
  Architecture Reference Manual and the Cortex-A76 manual; the default
  FPCR and the division of the floating-point environment between the
  kernel and EL0 follow the
  [floating-point state](../../../architecture.md#floating-point-state) of
  the architecture, and the save at every entry its
  [execution model](../../../architecture.md#system-calls-and-the-abi).

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host.
- **Raspberry Pi 5.** The models with 1, 2, 4, 8 and 16 GB of RAM, each
  with its four Cortex-A76 cores of which one runs. The rules depend on the
  core alone, which every model shares. Only the 8 GB model is run on a
  board in release 0.1; the other four are not run on a board in that
  release.
- **Host.** The host tests of the module `context` of the core (planned)
  run on the development host and in CI, with the frozen vectors and the
  tests that the [contract](contract.md#testing-obligations) adds.
- One CPU: no requirement here covers a thread that moves from one CPU to
  another.

## Requirements

### CTX-R01

**Layout of the saved context.** The saved context of a thread holds
`x0` to `x30`, `SP_EL0`, `ELR_EL1`, `SPSR_EL1`, `TPIDR_EL0`, `TPIDRRO_EL0`,
all 128 bits of each of `q0` to `q31`, FPCR and FPSR at the offsets of the
[contract](contract.md#layout), 816 bytes aligned to 16 bytes, and the
assembly that saves and restores it uses the same offsets. A copy of a
context holds every bit of the original, whatever later happens to the
original. The criterion: the size, the alignment and each offset equal
those of the contract at compile time, and the frozen vectors of the
layout hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `context::Context` with the offset constants of its
  fields (planned).
- **Contract.** [Layout](contract.md#layout).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The constant assertions of the module `context` (planned),
  which every build checks, and the frozen vectors `cx-02` and `cx-04` as
  host tests. They show the layout of the type; that the assembly reads and
  writes the fields at these offsets is shown on QEMU virt by the evidence
  of CTX-R06.

### CTX-R02

**Initial context.** A new thread starts from the context that
`Context::new` gives: its general registers, its TLS registers and its
vector registers are 0; its return address is its entry and its stack
pointer the top of its initial stack; its SPSR is `0x340`, EL0 with
`SP_EL0` in AArch64, with IRQs unmasked and FIQs, SErrors and debug
exceptions masked; its FPCR is `0x0000_0000`, which rounds to nearest with
ties to even and selects no flush to zero, no default NaN, the IEEE
half-precision format and no trap; its FPSR is 0. No field comes from
another thread, also when the new thread takes the slot of a destroyed
one. The criterion: the frozen vectors hold, and on QEMU virt a new process
finds these values in its registers at its first instruction.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Context::new`, `context::USER_PSTATE`, `DEFAULT_FPCR`
  and `DEFAULT_FPSR` (planned).
- **Contract.** [Initial context](contract.md#initial-context).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `cx-01` and `cx-19` as host tests, and
  the QEMU test of a new process of the
  [contract](contract.md#testing-obligations). They show the value of the
  context and, on QEMU virt with one CPU, that the first return loads it;
  they do not show the floating-point environment that a thread inherits
  from its creator, which EL0 sets.

### CTX-R03

**Bounds and validation.** `Bounds::new` refuses a code range that is
empty, not aligned to 4 bytes or wraps, with `CodeRange`, and then a stack
range that is empty, not aligned to 16 bytes or wraps, with `StackRange`.
`validate` refuses a return address that is not aligned to 4 bytes or
whose instruction does not lie wholly in the code range, with
`ProgramCounter`, then a stack pointer that is not aligned to 16 bytes or
lies outside the stack range with its top included, with `StackPointer`,
then an SPSR that differs from `0x340` in any bit other than NZCV, with
`Pstate`. It reads no other field, so TLS values are never dereferenced.
Each refusal names the first broken rule in this order and changes
nothing. The criterion: the frozen vectors hold, among them both ends of
each range and each single bit of the SPSR outside NZCV.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Bounds::new` and `Context::validate` (planned).
- **Contract.** [Validation](contract.md#validation) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `cx-05` to `cx-11` and `cx-14` as host
  tests. They show the rules on contexts that the tests build.

### CTX-R04

**No return with a refused context.** The kernel restores no context that
`validate` refuses: a return to EL0 whose saved context has an illegal
return address, stack pointer or SPSR executes no `ERET` with it, and the
thread does not run at EL0 again. The criterion: on QEMU virt, three cases
each give the saved context of a thread an illegal PC, SP or PSTATE before
its return, and no instruction of the thread executes afterwards.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Context::validate` (planned), with the return to EL0
  that the address-space component of the
  [memory](../../memory/README.md) domain governs (planned).
- **Contract.** [Validation](contract.md#validation).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The three QEMU cases of the
  [contract](contract.md#testing-obligations) and the frozen vector `cx-15`
  as a host test. They show the refusal on QEMU virt with one CPU; how the
  process of the thread ends afterwards is shown by the components of user
  faults and of the termination of processes (planned).

### CTX-R05

**Results of a call.** `set_return_values` writes `x0` and `x1` of a saved
context, and `set_return_registers` writes `x0` to `x5`, and neither writes
any other field. Each first validates the whole context with its bounds
and, when that fails, returns the error and changes no field. The
criterion: the frozen vectors hold, with every other field unchanged bit
for bit after each write and every field unchanged after each refusal.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Context::set_return_values` and
  `set_return_registers` (planned).
- **Contract.** [Results of a call](contract.md#results-of-a-call) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `cx-21`, `cx-23`, `cx-25` and `cx-28` as
  host tests. They show the write on contexts that the tests build; which
  results each call writes is shown by the components of the calls.

### CTX-R06

**User state across entries and returns.** After every entry from EL0 and
the return to it, a thread finds the registers that it left: `x0` to
`x30`, `SP_EL0`, NZCV, `TPIDR_EL0`, `TPIDRRO_EL0`, all 128 bits of each of
`q0` to `q31`, FPCR and FPSR, bit for bit, whatever other threads ran in
between, apart from the results that a call writes. Every entry saves the
FP/SIMD and TLS registers and every return restores them, eagerly, and EL0
cannot write `TPIDRRO_EL0`. The criterion: on QEMU virt, two processes that
interleave by a system call that yields and by timer interrupts compare,
in each of a fixed number of rounds, every one of these registers with
values that they compute from the round alone, and every comparison holds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `__fpsimd_save` and `__fpsimd_restore` in
  `kernel/arch/src/fpsimd.S` (planned), with the entry from EL0 and the
  return to it that the address-space component governs (planned).
- **Contract.** [FP/SIMD and TLS state](contract.md#fpsimd-and-tls-state)
  and [Layout](contract.md#layout).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path; the save and the
  restore are [open obligations](contract.md#open-obligations).
- **Evidence.** The QEMU test of two interleaving processes of the
  [contract](contract.md#testing-obligations), whose timer period is a
  platform parameter, the frozen vectors `cx-03` and `cx-13`, and the tests
  that the open obligations name for the rules of the save and the restore.
  They show the save and the restore on QEMU virt with one CPU; they do not
  show the Raspberry Pi 5, which needs a board run of its own, or a thread
  that moves between CPUs.

### CTX-R07

**Software floating point at EL1.** No Rust code of the kernel runs with
FP/SIMD access: `CPACR_EL1.FPEN` is `0b00` whenever such code runs, so an
FP/SIMD instruction in it traps with the exception class `0x07`, and it is
`0b11` while a thread runs at EL0. The criterion: on QEMU virt, an FP/SIMD
instruction in EL1 code after an entry from EL0 takes the trap, and the
threads of CTX-R06 execute FP/SIMD instructions at EL0 without one.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `__fpsimd_save` and `__fpsimd_restore` (planned).
- **Contract.** [FP/SIMD and TLS state](contract.md#fpsimd-and-tls-state).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path; the switch of
  `FPEN` is an [open obligation](contract.md#open-obligations).
- **Evidence.** The QEMU case of the trap at EL1 after an entry from EL0 of
  the [contract](contract.md#testing-obligations), which is also the test
  of the rule `el1-fp-trap`, and the QEMU test of CTX-R06. The trap after
  the cold entry, before any entry from EL0, is
  [BOOT-R05](../boot/requirements.md#boot-r05). They show the trap on QEMU
  virt; they do not show that no other code of the kernel writes
  `CPACR_EL1`, which the review of its writes holds.

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a
  lock.
- Every entry from EL0 stores 536 bytes of FP/SIMD and TLS state, and every
  return to EL0 loads 544 bytes. No requirement bounds the time that a step
  takes.

## Scope

- One CPU: the handover of the saved context of a thread that moves from
  one CPU to another is not covered.
- The entry from EL0 and the return to it, the save and restore of the
  general registers, the load of the address space and the classes of
  exceptions and user faults belong to the address-space component of the
  [memory](../../memory/README.md) domain (planned); this component gives
  them the layout, `validate` and the save and restore of the FP/SIMD and
  TLS registers.
- The life of threads and processes, their handles and generations, the
  waits whose completion writes results, and the end of a process after a
  refused context belong to other components (planned). The frozen vectors
  that assert those states are inputs of those components, and the
  [contract](contract.md#legacy-test-vectors) gives them no case.
- Every thread at EL0 has FP/SIMD access; there is no thread without it.
  The Cortex-A76 has neither SVE nor SME, so no other register state of EL0
  is saved.
- The floating-point environment of a thread beyond the default of a new
  one, its inheritance and the libraries that use it belong to the
  [runtime ABI and SDK](../../README.md) domain; the delivery of upcalls,
  and which fields their return restores, to the component that delivers
  them.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Determinism](contract.md#determinism) and
  [State fields](contract.md#state-fields) bind the code without an
  observable behaviour of their own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
