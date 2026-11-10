# Context contract

This page governs the code of the `context` component of the
[boot and platform](../README.md) domain: the saved user context of a
thread, with its layout, its initial value and the default FPCR and FPSR
of a new thread; the validation of a context before the kernel restores
it; the results that a call writes into it; and the save and restore of
the FP/SIMD and TLS registers of EL0 at an entry from EL0 and at the
return to it, with the switch of `CPACR_EL1.FPEN` that they need. The
entry from EL0 and the return to it, which save and restore the general
registers and call the save and the restore of this page, follow the rules
of the address-space component of the [memory](../../memory/README.md)
domain (planned). The observable behaviour that these rules serve, with its
evidence, is in the [requirements](requirements.md), the other document of
the component.

## Terms

- **Saved context.** `context::Context` (planned): the user context of one
  thread as the kernel holds it while the thread does not execute at EL0:
  `x0` to `x30`, `SP_EL0`, the return address and status in `ELR_EL1` and
  `SPSR_EL1`, `TPIDR_EL0`, `TPIDRRO_EL0`, `q0` to `q31`, FPCR and FPSR, in
  the [layout](#layout).
- **Entry from EL0.** An exception taken from EL0 to EL1, by a system call,
  another synchronous exception or an interrupt, through vector 8 or 9 of
  the [exception vectors](../boot/contract.md#exception-vectors). It saves
  the user context of the current thread.
- **Return to EL0.** The one-way exit of the
  [execution model](../../../architecture.md#system-calls-and-the-abi): it
  restores the saved context of the thread that is to run and executes
  `ERET`.
- **Current thread.** The thread that a CPU runs, whose context an entry
  from EL0 on that CPU saves.
- **Bounds.** `context::Bounds` (planned): the code range
  `[code_start, code_start + code_len)` and the stack range
  `[stack_start, stack_start + stack_len]` of a thread, against which
  `validate` checks a context. The address-space component gives them,
  inside the EL0 window of the process (planned).
- **FP window.** The instructions of an entry from EL0 up to the point at
  which the save sets `CPACR_EL1.FPEN` to `0b00`, and those of a return to
  EL0 from the point at which the restore sets it to `0b11`: the only
  instructions at EL1 that run with FP/SIMD access.
- **Result registers.** `x0` to `x5`: the registers in which a call
  returns its results, among them the registers that the completion of a
  wait writes back
  ([execution model](../../../architecture.md#system-calls-and-the-abi)).
- **Completer.** The code that writes the results of a call into the saved
  context of its thread: the dispatch, for a call that returns at once, or
  the operation that completes the wait record of a blocked thread, in its
  own transaction.

## Entry points

The entries of the core are in the module `context` of `krepi-kernel`
(planned); the adapter is the module `fpsimd` of `krepi-arch` (planned).
The core has seven entries: the value type `Context` with the constants of
its layout, the constants of its values, `Context::new`, `Bounds::new`,
`Context::validate`, `Context::set_return_values` and
`Context::set_return_registers`. The adapter has two, both assembly.

| Entry point | Kind | Called by | Rules |
| --- | --- | --- | --- |
| `context::Context` with the offset constants of its fields (planned) | Value type and constants, host-testable | The modules of the core above it that hold or pass the saved context of a thread (planned); `krepi_arch::fpsimd` and the entry from EL0 and the return to EL0 of `krepi_arch` (planned), for the offsets | [Layout](#layout) |
| `context::USER_PSTATE`, `NZCV_MASK`, `DEFAULT_FPCR` and `DEFAULT_FPSR` (planned) | Constants, host-testable | The entries of this page; the module `creation` of the core (planned) | [Initial context](#initial-context), [Validation](#validation) |
| `Context::new` (planned) | Function that writes nothing, host-testable | The module `creation` of the core (planned), for each new thread, the first thread of the first process at boot among them | [Initial context](#initial-context) |
| `Bounds::new` (planned), with the value types `context::Bounds` and `context::Error` | Function that writes nothing, host-testable | The callers of `validate`, `set_return_values` and `set_return_registers`, with the code and stack ranges of the thread that the address-space component gives (planned) | [Validation](#validation) |
| `Context::validate` (planned) | Read entry, host-testable | The return to EL0, for the saved context of the thread that is to run, before the restore, by the module that the address-space component names as the composer of the return (planned); the module `creation` of the core (planned), for an initial context | [Validation](#validation) |
| `Context::set_return_values` and `Context::set_return_registers` (planned) | Write entries, host-testable | A completer: the module `dispatch` of the core (planned), for a call that returns at once; the modules of the core that complete wait records (planned), in their own transactions | [Results of a call](#results-of-a-call) |
| `__fpsimd_save` and `__fpsimd_restore` in `kernel/arch/src/fpsimd.S` (planned) | Assembly routines | `__fpsimd_save`: the entry from EL0 of `krepi_arch` (planned), after it saved the general registers and before any Rust code; `__fpsimd_restore`: the return to EL0 of `krepi_arch` (planned), after `validate` passed for the context and the address space of its process is loaded, before the general registers are loaded | [FP/SIMD and TLS state](#fpsimd-and-tls-state) |

## Extractability

The module `context` of the core (planned), below `kernel/src/`
(planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the
layout with its constants, the initial context, the bounds, `validate`
and the write of results. It is in layer 1 of the
[module order](../../../architecture.md#module-order-in-the-core) and
refers to no other module of the core. Its items are `pub(crate)` except
the rows of the entry table that the architecture crate calls, with the
value types that those rows take and return
([provable core](../../../architecture.md#the-provable-core)). It touches
no register and defines no callback for a hardware action.

The adapter `fpsimd` of `krepi-arch` (planned), in
`kernel/arch/src/fpsimd.rs` with its assembly in
`kernel/arch/src/fpsimd.S` (planned), does not follow the subset: it
stores and loads the FP/SIMD and TLS registers of EL0 and writes
`CPACR_EL1`, and the assembly takes the offsets of the layout from the
constants of the core. No board crate holds code of this component. The
contract is written before its code, so this section lists no source
paths; the change that adds the module writes its `paths` block here.

## Layout

The saved context is the `repr(C)` structure `Context`, aligned to 16
bytes, of 816 bytes. Each offset is a constant of the module, `OFFSET_`
followed by the name of the field in upper case, such as `OFFSET_ELR`
(planned). Constant assertions fix the size, the alignment and every
offset, and the assembly of the save, of the restore and of the entry and
return takes the offsets from these constants.

| Offset | Field | Bytes | Content |
| ---: | --- | ---: | --- |
| 0 | `x` | 248 | `x0` to `x30`, 8 bytes each |
| 248 | `sp` | 8 | `SP_EL0`, the stack pointer of EL0 |
| 256 | `elr` | 8 | `ELR_EL1`: the address at which the thread resumes at EL0 |
| 264 | `spsr` | 8 | `SPSR_EL1`: the PSTATE with which the thread resumes, NZCV among it |
| 272 | `tpidr` | 8 | `TPIDR_EL0`, which EL0 reads and writes |
| 280 | `tpidrro` | 8 | `TPIDRRO_EL0`, which EL0 reads and only the kernel writes |
| 288 | `q` | 512 | `q0` to `q31`, all 128 bits of each, 16 bytes each as a 128-bit store at EL1 writes them |
| 800 | `fpcr` | 8 | FPCR |
| 808 | `fpsr` | 8 | FPSR |

- A context is a value: a copy holds every field of the original, all
  128 bits of each vector register among them, and a later change of one
  of the two leaves the other unchanged.
- The save slots of an upcall area hold a context in this layout
  ([upcalls](../../../architecture.md#futexes-and-upcalls)). Which fields
  the return from an upcall restores from a slot, which EL0 can write, is
  a rule of the component that delivers upcalls, not of this page.

## Initial context

`Context::new(entry, sp)` gives the initial context of a new thread, the
value with which the kernel creates it:

- `x0` to `x30`, `TPIDR_EL0`, `TPIDRRO_EL0` and `q0` to `q31` are 0;
- `elr` is `entry`, and `sp` is `sp`, the top of the initial stack;
- `spsr` is `USER_PSTATE`, `0x340`: M[3:0] is `0b0000`, EL0 with `SP_EL0`,
  and M[4] is 0, AArch64; F and A, bits 6 and 8, are 1, so that FIQs and
  SErrors taken to EL1 are masked at EL0; I, bit 7, is 0, so that IRQs
  reach EL1 while the thread runs at EL0, since the masks of PSTATE at EL0
  also hold off an interrupt taken to EL1; D, bit 9, is 1 and masks no
  debug exception at EL0, since `PSTATE.D` masks none whose target
  Exception level is higher than the current one: the debug exceptions of
  EL0, other than those of `BRK`, which are always enabled, follow the
  enables of `MDSCR_EL1`, which the EL0 controls of the address-space
  component fix (planned); NZCV and every other bit are 0;
- `fpcr` is `DEFAULT_FPCR`, `0x0000_0000`, and `fpsr` is `DEFAULT_FPSR`, 0.

`DEFAULT_FPCR` gives every field of FPCR the value 0: RMode `0b00`, round
to nearest with ties to even; FZ 0, no flush to zero, and FZ16 0, none for
half precision either; DN 0, NaN operands propagate; AHP 0, the IEEE
half-precision format; the trap enables IOE, DZE, OFE, UFE, IXE and IDE 0;
EBF 0; and the FEAT_AFP bits AH, FIZ and NEP 0. On the Cortex-A76 of both
boards bits 0 to 18 of FPCR, which hold the trap enables, EBF and the
FEAT_AFP bits, are RES0 and reset to 0, so only RMode, FZ, DN, AHP and FZ16
exist there. An FPSR of 0 holds no cumulative exception flag and no
saturation flag.

The initial context is the value of the kernel's creation of a thread
([floating-point state](../../../architecture.md#floating-point-state)):
where a new thread inherits the floating-point environment of its creator,
EL0 sets it, and the kernel copies no environment into a new context. No
field of a new context comes from an earlier thread, also when the new
thread takes the slot of a destroyed one.

## Validation

`Bounds::new(code_start, code_len, stack_start, stack_len)` and
`Context::validate` check a context against the ranges of its thread. The
address-space component gives the ranges, inside the EL0 window of the
process (planned); these entries do not check the window themselves. The
rules, in the order in which the entries check them, each with its error
of `context::Error`:

| Rule | Statement | Error | Entry |
| ---: | --- | --- | --- |
| 1 | The code range is not empty, `code_start` and `code_len` are multiples of 4, and `code_start + code_len` fits in 64 bits | `CodeRange` | `Bounds::new` |
| 2 | The stack range is not empty, `stack_start` and `stack_len` are multiples of 16, and `stack_start + stack_len` fits in 64 bits | `StackRange` | `Bounds::new` |
| 3 | `elr` is a multiple of 4, and `[elr, elr + 4)` lies in the code range, so that the whole instruction at the return address is in it | `ProgramCounter` | `validate` |
| 4 | `sp` is a multiple of 16, and `stack_start <= sp <= stack_start + stack_len`: the top of the stack, where an empty descending stack starts, is in the range | `StackPointer` | `validate` |
| 5 | `spsr` equals `USER_PSTATE` in every bit outside `NZCV_MASK`, `0xf000_0000`, the bits 28 to 31 that hold NZCV | `Pstate` | `validate` |

- Each entry returns the error of the first rule that fails, and `ok` when
  every rule holds.
- `validate` reads no other field. The general registers, `TPIDR_EL0` and
  `TPIDRRO_EL0` are opaque values that it never dereferences; their use as
  addresses is subject to the translation tables of the process. The
  vector registers, FPCR and FPSR may hold any value.
- A context that fails `validate` is never restored: the return to EL0
  executes no `ERET` with it, and the process of the thread ends by a user
  fault, by the rules of the address-space component and of the component
  that terminates processes (planned).
- Rule 5 refuses the context of a thread that left `PSTATE.SSBS`, bit 12,
  set at EL0. The Cortex-A76 of both boards implements FEAT_SSBS, under
  which `MSR SSBS, #<imm>` sets or clears the bit at EL0. It does not
  implement FEAT_SSBS2, so on the Raspberry Pi 5 the `MRS` and `MSR` forms
  that read and write the special-purpose register `SSBS` are undefined at
  EL0 and trap with the exception class `0x00`; QEMU defines that register
  for EL0 whenever `ID_AA64PFR1_EL1.SSBS` is not 0, so on QEMU virt they
  change the bit as well.
- Apart from SSBS, the only bits of PSTATE that EL0 can change directly on
  the Cortex-A76 are NZCV and DAIF: the core implements none of FEAT_DIT,
  FEAT_BTI and FEAT_MTE, whose fields of PSTATE EL0 could otherwise
  change. With `SCTLR_EL1.UMA` 0, which the EL0 controls of the
  address-space component fix (planned), an access of EL0 to `DAIF` traps
  with the exception class `0x18` and changes nothing. So the SPSR that an
  entry from EL0 saves differs from `USER_PSTATE` only in NZCV and SSBS,
  unless the kernel changed it, and rule 5 refuses it exactly when its
  bit 12 is 1.

## Results of a call

- `set_return_values(bounds, x0, x1)` writes the two values to `x0` and
  `x1`; `set_return_registers(bounds, values)` writes the six values to
  the result registers, `x0` to `x5`.
- Each first runs `validate` on the whole saved context with `bounds`.
  When it fails, the entry returns its error and changes no field.
  Otherwise the entry writes the given registers and no other field: the
  other general registers, `sp`, `elr`, `spsr`, the TLS fields, the vector
  registers, FPCR and FPSR keep their values.
- A completer calls them only while it owns the saved context
  ([State fields](#state-fields)), never while the thread executes at EL0.
  Which results a call writes, and whether a blocking call completes by a
  write of its results or by being executed again from the saved
  registers, is a rule of the contract of that call.

## FP/SIMD and TLS state

- EL0 uses the FP/SIMD registers of the hardware; the kernel is built for
  `aarch64-unknown-none-softfloat`, and its code uses none of them
  ([floating-point state](../../../architecture.md#floating-point-state)).
  Every thread at EL0 has FP/SIMD access; there is no thread without it.
- `CPACR_EL1.FPEN`, bits 20 and 21, has four encodings: `0b00` and `0b10`
  trap the FP/SIMD instructions of EL0 and EL1 to EL1 with the exception
  class `0x07`, `0b01` traps those of EL0 alone, and `0b11` traps none. No
  encoding traps those of EL1 alone, so the kernel switches the field: it
  is `0b11` while a thread runs at EL0 and `0b00` while Rust code of the
  kernel runs. The rule needs `HCR_EL2.{E2H, TGE}` other than `{1, 1}`
  where EL2 exists, under which FPEN governs EL0; QEMU virt in its
  configuration has no EL2, and a board that enters at EL2 drops to EL1
  with `HCR_EL2.TGE` 0.
- The save, `__fpsimd_save`, runs at every entry from EL0, with every
  exception masked, after the general registers are saved and before any
  Rust code: with FPEN still `0b11` from EL0, it stores `q0` to `q31`,
  FPCR, FPSR and `TPIDR_EL0` into the saved context of the current thread,
  then sets FPEN to `0b00` by a read-modify-write of `CPACR_EL1` that
  changes no other field, and executes `ISB`.
- The restore, `__fpsimd_restore`, runs at every return to EL0, with every
  exception masked, after `validate` passed for the saved context of the
  thread that is to run and the address space of its process is loaded: it
  sets FPEN to `0b11` in the same way, executes `ISB`, and loads `q0` to
  `q31`, FPCR, FPSR, `TPIDR_EL0` and `TPIDRRO_EL0` from that context. The
  return then loads the general registers and executes `ERET`, with no
  FP/SIMD instruction and no write of `CPACR_EL1` in between.
- The save and the restore are eager: every entry saves and every return
  restores, so the saved context of a thread that does not execute at EL0
  is complete, and the code that reads or writes the user state of such a
  thread, a completer among it, reads and writes the saved context alone.
- `TPIDRRO_EL0` is read-only at EL0. The save does not store it, since its
  value at an entry is the one that the restore loaded, and only the
  kernel changes the field `tpidrro` of a saved context.
- With FPEN `0b00`, an FP/SIMD instruction at EL1 outside the FP window
  traps with the exception class `0x07`, which the
  [exception record](../boot/contract.md#records) of the boot component
  names with the class `fp`.

The rules of the saved and restored state, each an
[open obligation](#open-obligations) with its test:

| Label | Statement |
| --- | --- |
| `save-fp` | At every entry from EL0, `q0` to `q31`, all 128 bits of each, FPCR and FPSR are stored into the saved context of the current thread before any of them changes and before FPEN is set to `0b00`. |
| `save-tls` | At every entry from EL0, `TPIDR_EL0` is stored into the saved context of the current thread before it changes. |
| `fpen-window` | At EL1, FPEN is `0b11` only in the FP window: the save sets it to `0b00` and executes `ISB` before it returns to the entry, and the restore sets it to `0b11` and executes `ISB` before its first FP/SIMD instruction; each write changes no other field of `CPACR_EL1`. |
| `el1-fp-trap` | No Rust code of the kernel runs with FPEN other than `0b00`, so that an FP/SIMD instruction in it traps with the exception class `0x07`. |
| `restore-fp` | At every return to EL0, `q0` to `q31`, FPCR and FPSR are loaded from the saved context of the thread that is to run, after `validate` has passed for that context, and none of them changes before the `ERET`. |
| `restore-tls` | At every return to EL0, `TPIDR_EL0` and `TPIDRRO_EL0` are loaded from the saved context of the thread that is to run. |
| `new-context-clear` | The first return of a new thread loads the values of its initial context, so that its vector registers, FPCR, FPSR and TLS registers hold 0 and no value that another thread or the kernel left in them. |

## Check and execute

- `Context::new`, `Bounds::new` and `validate` write nothing. `Bounds::new`
  checks rule 1 and then rule 2 of [Validation](#validation); `validate`
  checks rules 3, 4 and 5 in this order.
- `set_return_values` and `set_return_registers` complete `validate` of
  the whole saved context, with the bounds that their caller gives, before
  their first write. Their write phase stores the given registers and
  cannot fail, so a refused call changes no field.
- `__fpsimd_save` and `__fpsimd_restore` check nothing and do not fail.
  Their callers vouch that the address that they pass is that of the saved
  context of the current thread, or of the thread that is to run, aligned
  to 16 bytes and mapped for reads and writes at EL1, and that every
  exception is masked; the restore relies on its caller for the `validate`
  that passed before it.

## Work bounds

- `Context::new` builds one value of 816 bytes. `Bounds::new` checks two
  rules and `validate` three, each with a fixed number of comparisons and
  no loop. `set_return_values` writes two words and `set_return_registers`
  six, after one `validate`.
- `__fpsimd_save` stores 32 vector registers of 16 bytes, FPCR, FPSR and
  `TPIDR_EL0`, 536 bytes, and makes one read-modify-write of `CPACR_EL1`
  and one `ISB`; `__fpsimd_restore` makes one read-modify-write and one
  `ISB` and loads those registers and `TPIDRRO_EL0`, 544 bytes. Each runs a
  fixed sequence of instructions with no loop.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls.

## Determinism

The component makes no internal choice: the output of each entry follows
from its arguments alone, and the save and the restore copy registers to
and from one context in a fixed order. The specification of the component
(planned) leaves no choice open either, so no entry of the register of
[permitted nondeterminism](../../../security.md#permitted-nondeterminism)
applies to it. Which instruction an interrupt interrupts, and so the values
that a save finds, follows from when the interrupt arrives, which the entry
from EL0 of the address-space component accounts for (planned).

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The saved context of a thread, every field | Per-thread | While the thread runs, the CPU that runs it, from the save of an entry from EL0 to the restore of the return; while the thread is ready, the CPU of the run queue that holds it; while it is blocked, the object that it waits on, whose completer writes its results; while the thread executes at EL0, its user state is in the registers and no code reads the saved context | The end of `__fpsimd_save` for the state of an entry; the end of the write phase of `set_return_values` or `set_return_registers`, within the transaction of the completer | At a handover between two owners, by the publication of the record that hands the thread over, which the contracts of scheduling and of waits state (planned); with one CPU every owner is the executing CPU |
| `q0` to `q31`, FPCR, FPSR, `TPIDR_EL0` and `TPIDRRO_EL0` | Per-CPU | The executing CPU: from a restore to the next save they hold the values of the thread that it runs, and after a save no code of the kernel reads them | The `ERET` after the restore, for the thread at EL0 | `none`: each CPU has its own |
| `CPACR_EL1.FPEN` | Per-CPU | The executing CPU; after the cold entry, only `__fpsimd_save` and `__fpsimd_restore` write it | The `ISB` after each write | `none`: each CPU has its own |

## Testing obligations

- The host tests of the module `context` (planned) hold the frozen vectors
  of [Legacy test vectors](#legacy-test-vectors), each case with its
  expected output, and write their results for the comparison with the
  specification
  ([host results](../../../formal-verification.md#host-results)).
- The constant assertions of the module fix the size, the alignment and
  every offset of [Layout](#layout); the assembly takes the offsets from
  the constants, so a change of the layout that the assembly does not
  follow fails to build.
- A QEMU test on QEMU virt runs two processes that interleave by a system
  call of the test image that yields and by timer interrupts, for a fixed
  number of rounds. In each round each process compares `x0` to `x30`,
  `SP_EL0`, NZCV, `TPIDR_EL0`, `TPIDRRO_EL0`, all 128 bits of each of `q0`
  to `q31`, FPCR and FPSR with values that it computes from the round
  alone. The timer period is a platform parameter, and the test decides by
  the number of rounds and the comparisons only, never by the speed of the
  CPU or a count of instructions.
- A QEMU test reads the registers of a new process at its first
  instruction: `x0` to `x30`, `q0` to `q31` and the TLS registers are 0,
  FPCR is `DEFAULT_FPCR` and FPSR is 0.
- A QEMU test executes an FP/SIMD instruction in EL1 code after an entry
  from EL0 and takes the trap with the exception class `0x07`. The case of
  the boot component that takes the trap after the cold entry stays as a
  regression test.
- Three QEMU cases each give the saved context of a thread an illegal PC,
  SP or PSTATE before its return to EL0, and the return restores none of
  them: the thread executes no instruction at EL0 afterwards.
- Each rule of [FP/SIMD and TLS state](#fpsimd-and-tls-state) has one
  test, a case of a QEMU suite or a self-check of a test image, which the
  change that adds the code names in the Test column of its row of
  [Open obligations](#open-obligations); one test may serve several rules.
- No test bounds the time that a step takes.

## Open obligations

The seven entries of the module `context` are those that the
specification of the component (planned) covers, so they have no row here;
an entry that a later change adds to the module gets a row. The table lists
the obligations of the adapter `fpsimd`: its two routines, each rule of the
saved and restored state, its assembly and its code.

| Obligation | Kind | Verified state | Carrier | Stage | Test |
| --- | --- | --- | --- | --- | --- |
| `kernel/arch/src/fpsimd.S#__fpsimd_save` (planned) | `assembly` | Writes the saved user context that the context logic describes, its `q0` to `q31`, FPCR, FPSR and `TPIDR_EL0`, and writes `CPACR_EL1` | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/fpsimd.S#__fpsimd_restore` (planned) | `assembly` | Reads the saved user context that the context logic describes, and writes `CPACR_EL1` and the FP/SIMD and TLS registers of EL0 | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/fpsimd.S#save-fp` (planned) | `register-state` | Writes the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/fpsimd.S#save-tls` (planned) | `register-state` | Writes the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/fpsimd.S#fpen-window` (planned) | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/fpsimd.S#el1-fp-trap` (planned) | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/fpsimd.S#restore-fp` (planned) | `register-state` | Reads the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/fpsimd.S#restore-tls` (planned) | `register-state` | Reads the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/fpsimd.S#new-context-clear` (planned) | `register-state` | Reads the saved user context that the context logic describes | The proof of the register state that exception entry and return save, restore and clear | `0.2` | - |
| `kernel/arch/src/fpsimd.S` (planned) | `assembly` | Reads and writes the saved user context that the context logic describes | The proof of contexts, user copies and the private VM | `0.2` | - |
| `kernel/arch/src/fpsimd.rs` (planned) | `code` | Neither | The proof of contexts, user copies and the private VM | `0.2` | - |

## Legacy test vectors

The component freezes 29 vectors from the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`. A vector of this
page is one `#[test]` function of the prototype; in the vector file it is
the lines whose id starts with the id of the vector and a dot, one line for
each case, `<vector>.<n>` from 1 in the order of the test, where a case is
one call of an entry of this page that the test makes, with the output that
it asserts. The expected outputs below are the assertions of the test
bodies.

| File | Vectors |
| --- | ---: |
| `src/arch/aarch64/context/tests.rs` | 11 |
| `src/execution/tests/context.rs` | 9 |
| `src/execution/tests/returns.rs` | 9 |

The prototype's `src/arch/aarch64/context.rs` holds its tests in the first
file; `src/arch/aarch64/context/hardware.rs` and
`src/arch/aarch64/context/entry.S` have no host test, so they give no
vector. The other tests of the prototype's execution manager are not
vectors of this page.

**Notation.** Addresses, lengths and register values are written as `0x`
and lowercase hexadecimal digits without separators, zero also as 0, and a
value that a test computes by a formula as that formula; counts are written
in decimal, and a range as `<start>+<length>`. The output of a call is
`ok`, followed by its fields, or `err=<error>`, with the errors of this
page. The prototype's `UserContext::new` is `Context::new`, and its
`UserContext::validate(code_start, code_len, stack_start, stack_len)` is
`Bounds::new` with the same four values followed by `validate` with the
bounds, so a case whose output is `err=CodeRange` or `err=StackRange` is a
case of `Bounds::new`. The tests of the execution manager name the errors
of the prototype, `InvalidState`, `Busy`, `Stale` and `InvalidContext`,
which the expected outputs below keep; the Entry column gives the output
on this page.

**Vectors without a case.** A vector whose Entry column names no entry of
this page has no line in the vector file; its row gives the reason.

**Behaviour changes.** These rules differ from the prototype:

- Every thread at EL0 has FP/SIMD access. The prototype's choice of FP/SIMD
  for each domain, with the rule that a context without it holds zero
  vector registers, FPCR and FPSR, is not carried: `cx-17` does not apply,
  and neither do the parts of `cx-13`, `cx-19` and `cx-28` with a domain
  without FP/SIMD.
- An entry from EL0 stores the FP/SIMD and TLS registers and takes the
  stack pointer from `SP_EL0`. The prototype's capture from an exception
  frame took the stack pointer of the frame and left the TLS and FP/SIMD
  fields 0: `cx-03` keeps its output for the general registers, `sp`,
  `elr` and `spsr`, and its TLS and FP/SIMD fields equal the registers at
  the entry, 0 in its case.
- The prototype refused an invalid context when a domain was suspended and
  kept the earlier one. Here every entry saves the context that EL0 left,
  and `validate` refuses it before the return, so that the thread does not
  run at EL0 again (`cx-15`); the prototype's check at the configuration
  of a domain is the `validate` of the initial context when a thread is
  created (`cx-14`).
- The errors of `validate` name the broken rule; the prototype's execution
  manager reported each as `InvalidContext`.
- The prototype's execution manager kept the context with the state of its
  domain and refused an access with `InvalidState`, `Busy` or `Stale`.
  Here the saved context is a value of its thread, read and written only
  by its owner and never while the thread executes at EL0
  ([State fields](#state-fields)); the state of a thread, its handle and
  generation, the reuse of its slot, its waits and the reclamation of its
  process belong to the components of objects, of the lifecycle of
  processes, of waits and of address spaces (planned), whose rules take
  these assertions as inputs. A thread gets its initial context when it is
  created, so a configuration that may happen once does not exist, and the
  release of an address space identifier cannot fail. `cx-12`, `cx-16`,
  `cx-18`, `cx-20`, `cx-22`, `cx-24`, `cx-26`, `cx-27` and `cx-29` have no
  case on this page, and the other vectors keep only their cases of this
  page.

### `src/arch/aarch64/context/tests.rs`

`CODE` is `0x10000000`, `STACK` `0x10003000` and `PAGE` `0x1000`. Unless a
row says otherwise, a context is checked with the code range
`0x10000000+0x1000` and the stack range `0x10003000+0x1000`, and starts as
`Context::new(0x10000000, 0x10004000)`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `cx-01` | 12 | `initial_context_has_no_inherited_register_or_extension_state` | `Context::new(0x10000000, 0x10004000)` is `ok` in the ranges; its `x0` to `x30` are 0, `sp` `0x10004000`, `elr` `0x10000000`, `spsr` `0x340`, `tpidr` and `tpidrro` 0, `q0` to `q31` 0, `fpcr` 0 and `fpsr` 0 | `Context::new`, `Bounds::new`, `validate` |
| `cx-02` | 27 | `assembly_layout_covers_every_field_and_all_vector_lanes` | Size 816 and alignment 16; offsets `x` 0, `sp` 248, `elr` 256, `spsr` 264, `tpidr` 272, `tpidrro` 280, `q` 288 with 512 bytes, `fpcr` 800 and `fpsr` 808 | `Context` and its offset constants |
| `cx-03` | 44 | `exception_capture_keeps_all_gprs_sp_pc_and_condition_flags` | From an exception with register $i$ of `x0` to `x30` holding `0xa53a760000000000` plus $i$, stack pointer `0x10003fc0`, return address `0x10000080`, SPSR `0xa0000340`, ESR `0xffffffffffffffff`, FAR `0xfffffffffffffffe` and vector 8: the context holds those `x0` to `x30`, `sp`, `elr` and `spsr`, its TLS fields, `q0` to `q31`, `fpcr` and `fpsr` are 0, and it is `ok` in the ranges | The saved context that an entry from EL0 and `__fpsimd_save` write; `validate`. The TLS and FP/SIMD fields are the registers at the entry, 0 in this case |
| `cx-04` | 69 | `copied_context_owns_all_128_bits_of_every_vector` | A context with register $i$ of `q0` to `q31` holding `0x8000000000000000` plus $i$ in its high 64 bits and `0x1000000000000000` plus $i$ in its low 64 bits, `fpcr` `0x400000` and `fpsr` `0x8000010`: after a copy, the vector registers, `fpcr` and `fpsr` of the original are set to 0 and read 0, and the copy keeps all 128 bits of each vector register, `fpcr` `0x400000` and `fpsr` `0x8000010` | `Context`, a value |
| `cx-05` | 92 | `every_condition_flag_combination_preserves_el0_entry_policy` | `spsr` `0x340` with each of the 16 values in bits 28 to 31: `ok` | `validate`, rule 5 |
| `cx-06` | 101 | `any_non_condition_pstate_change_is_rejected` | `spsr` `0x340` with one bit outside bits 28 to 31 inverted, for each of the 60 bits: `err=Pstate`; `spsr` `0x3c5`, `0x345`, `0x3c0`, `0x0` and `0xffffffffffffffff`: `err=Pstate` | `validate`, rule 5 |
| `cx-07` | 117 | `program_counter_must_name_a_whole_aligned_instruction` | `elr` `0x10000000`, `0x10000004` and `0x10000ffc`: `ok`; `elr` `0xffffffc`, `0x10000001`, `0x10000002`, `0x10001000` and `0xfffffffffffffffc`: `err=ProgramCounter` | `validate`, rule 3 |
| `cx-08` | 130 | `stack_pointer_accepts_aligned_bounds_but_not_guard_or_other_pages` | Starting as `Context::new(0x10000000, 0x10003000)`: `sp` `0x10003000`, `0x10003010`, `0x10003ff0` and `0x10004000`: `ok`; `sp` `0x10002ff0`, `0x10003001`, `0x10003008`, `0x10004010` and `0xffffffffffffffff`: `err=StackPointer` | `validate`, rule 4 |
| `cx-09` | 149 | `malformed_or_wrapping_code_ranges_are_rejected` | With the stack range `0x10003000+0x1000`, the code ranges `0x10000000+0x0`, `0x10000001+0x1000`, `0x10000000+0x2` and `0xfffffffffffffffc+0x4`: `err=CodeRange` | `Bounds::new`, rule 1 |
| `cx-10` | 160 | `malformed_or_wrapping_stack_ranges_are_rejected` | With the code range `0x10000000+0x1000`, the stack ranges `0x10003000+0x0`, `0x10003008+0x1000`, `0x10003000+0x8` and `0xfffffffffffffff0+0x10`: `err=StackRange` | `Bounds::new`, rule 2 |
| `cx-11` | 176 | `tls_registers_are_opaque_values_and_do_not_trigger_dereferences` | `tpidr` `0xffffffffffffffff` and `tpidrro` `0xdeadbeef12345678`: `ok` | `validate`, which reads no TLS field |

### `src/execution/tests/context.rs`

The ranges and the initial context are those of the file above. A domain
of the prototype is a process with one thread; it runs between `begin`
and `suspend` or `finish`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `cx-12` | 26 | `configuration_is_once_only_and_cannot_observe_or_mutate_active_contexts` | Of two new domains, the saved context of the first, unconfigured, is `InvalidState`; once configured with the initial context and FP/SIMD it reads back that context, with no other change; a second configuration is `InvalidState`; while the first runs, reading or configuring either domain is `Busy` and changes nothing; after the first is suspended, the second, unconfigured, is `InvalidState` and is then configured without FP/SIMD | No case: the owner of a saved context ([State fields](#state-fields)) and the state of a thread belong to the address-space and lifecycle components (planned); a thread gets its initial context when it is created |
| `cx-13` | 64 | `alternating_suspensions_preserve_distinct_registers_backing_and_charges` | Two domains, the first with FP/SIMD and the second without, run in turn, four turns each. Before each run the saved context equals the last one saved, at first the initial context; in turn $t$ the suspension of domain $d$, 0 or 1, saves a context with register $r$ of `x0` to `x30` holding $2^{32} d + 2^{16} t + r$, `elr` 4 more, `sp` 16 less, `tpidr` $4096 (d + 1) + t$, `tpidrro` that plus 256, and, with FP/SIMD, register $r$ of `q0` to `q31` holding $2^{96} t + r$, `fpcr` `0x400000` and `fpsr` `0x1`; it reads back bit for bit; the backing, the address space identifier, the process, alive, the thread, ready, and the charges are unchanged, and no hardware event is recorded; after both are destroyed, no page allocation remains | `Context`, a value: each saved context reads back bit for bit; on a CPU the save and the restore are shown by the QEMU test of two processes of [Testing obligations](#testing-obligations). The domain without FP/SIMD does not apply |
| `cx-14` | 133 | `malformed_configuration_does_not_publish_saved_state` | The initial context with `elr` `0x10001000`, with `sp` `0x10004001` and with `spsr` `0x341` is each `InvalidContext`, the domain stays unconfigured, `InvalidState`, and nothing changes; with the code length 0, `InvalidContext`; the initial context is then accepted | `validate`: `err=ProgramCounter`, `err=StackPointer` and `err=Pstate`; `Bounds::new` with the code range `0x10000000+0x0`: `err=CodeRange`; the initial context: `ok`. That a refused creation publishes nothing is the creation's |
| `cx-15` | 164 | `invalid_suspension_retains_active_ownership_for_terminal_fault_handling` | A suspension of a running domain with `elr` `0xffffffc` is `InvalidContext`; nothing changes and the saved context stays the initial context; the domain then finishes as faulted, after which reading its context and running it are `InvalidState` | `validate`: `err=ProgramCounter`, so the context is not restored. The saved context is the one that the entry saved, and the end of the process is the lifecycle component's (planned) |
| `cx-16` | 200 | `wrong_handle_nonactive_and_unconfigured_suspensions_do_not_mutate_ownership` | Suspending a configured domain that does not run, or the second domain while the first runs, is `InvalidState` and changes nothing; once the first is suspended and the second, unconfigured, runs, its suspension is `InvalidState` and changes nothing | No case: an entry from EL0 saves into the current thread of its CPU and names no other |
| `cx-17` | 232 | `disabled_fp_rejects_each_extended_state_component_before_publication` | Without FP/SIMD, a context with `q31` `0x80000000000000000000000000000000`, with `fpcr` `0x400000` or with `fpsr` `0x1` is `InvalidContext` at the configuration and at a suspension, and the thread keeps running; the initial context is accepted and reads back | Not applicable: every thread at EL0 has FP/SIMD access |
| `cx-18` | 267 | `terminal_thread_cannot_resume_reconfigure_or_accept_saved_state` | After an exit with 0 and after a fault, reading the context, running, suspending and configuring the domain are each `InvalidState` and change nothing | No case: the state of a thread belongs to the lifecycle component (planned) |
| `cx-19` | 298 | `destroyed_paused_domain_reuses_backing_without_inheriting_old_context` | A domain suspended with every `x` `0x11223344` and every `q` all ones is destroyed, and the usage returns to the baseline; a new domain has another handle, the same backing and the same address space identifier, and an unconfigured context, `InvalidState`; the old handle is `Stale` for reading, suspending and configuring, with no change; the new domain, configured without FP/SIMD, reads the initial context | `Context::new`: the context of the new thread equals that of `cx-01`, with no value of the destroyed one. The handles and the reuse belong to the objects, lifecycle and address-space components (planned); the domain without FP/SIMD does not apply |
| `cx-20` | 337 | `failed_retirement_keeps_context_inaccessible_until_resources_are_reclaimed` | When the invalidation fails, the destruction is `Asid(InvalidationFailed)`, and reading and configuring the context are `InvalidState` with no change; after a destruction that succeeds, reading is `Stale` | No case: the reclamation belongs to the lifecycle and address-space components (planned), and the invalidation cannot fail |

### `src/execution/tests/returns.rs`

The ranges are those of the first file. The initial context of these tests
is `Context::new(0x10000000, 0x10004000)` with register $i$ of `x0` to
`x30` holding $i + 11$, every `q` all ones, `tpidr` `0x1234` and `tpidrro`
`0x5678`, with FP/SIMD unless a row says otherwise.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `cx-21` | 29 | `completed_wait_return_values_change_only_x0_and_x1` | After a wait that completes as signalled, writing `0x7` and `0xffffffffffffffe9` is `ok`: the context is the initial one with `x0` `0x7` and `x1` `0xffffffffffffffe9`, and the counts and the thread are unchanged | `set_return_values` |
| `cx-22` | 54 | `return_values_require_configured_ready_state_and_no_active_domain` | Writing `0x1` and `0x2` to an unconfigured domain is `InvalidState`; while one of two domains runs, writing to either is `Busy`; to a blocked domain, `InvalidState`, with its context unchanged; to a terminated one, `InvalidState`; after its destruction and the creation of another, through the old handle, `Stale`, and the new domain reads the initial context | No case: the owner of a saved context and the state of a thread belong to the address-space and lifecycle components (planned) |
| `cx-23` | 100 | `malformed_saved_context_prevents_partial_return_value_publication` | With the saved `elr` moved by a page, to `0x10001000`, writing `0x1` and `0x2` is `InvalidContext`, and the context is unchanged | `set_return_values`: `err=ProgramCounter`, no field changes |
| `cx-24` | 121 | `retired_context_rejects_return_values_until_reclamation` | After a failed invalidation at the destruction, writing `0x1` and `0x2` is `InvalidState`, and the context is the initial one | No case: the reclamation belongs to the lifecycle and address-space components (planned), and the invalidation cannot fail |
| `cx-25` | 141 | `six_register_completion_preserves_every_other_context_field` | After a wait that completes as signalled, writing `0x0`, `0xffffffffffffffff`, `0x8000000000000000`, `0x0`, `0x2a` and `0x0` is `ok`: `x0` to `x5` hold them, every other field is that of the initial context, and the counts of the manager and of the objects are unchanged; then writing `0x47` and `0x48` changes only `x0` and `x1` | `set_return_registers`, `set_return_values` |
| `cx-26` | 173 | `six_register_publication_rejects_inactive_unconfigured_active_and_blocked_states` | Writing six registers of `0x9` to an unconfigured domain is `InvalidState`; while one of two domains runs, to either, `Busy`; to a blocked domain, `InvalidState`, with its context unchanged; the other domain reads the initial context | No case: as `cx-22` |
| `cx-27` | 204 | `ready_metadata_does_not_bypass_an_unconsumed_owned_wait` | A wait that its object completed as signalled and that the domain has not consumed: the thread is ready, writing six registers of `0x9` is `InvalidState`, the context is unchanged and the wait stays recorded | No case: the consumption of a completed wait belongs to the waits component (planned) |
| `cx-28` | 229 | `six_register_publication_validates_the_complete_context_before_mutation` | With FP/SIMD and the saved `elr` moved by a page, and without FP/SIMD with every `q` all ones, writing six registers of `0x9` is `InvalidContext`, and the context is unchanged | `set_return_registers` with `elr` `0x10001000`: `err=ProgramCounter`, no field changes. The case without FP/SIMD does not apply |
| `cx-29` | 250 | `six_register_publication_cannot_modify_terminal_retired_or_reused_domains` | Writing six registers of `0x9` to a terminated domain is `InvalidState`; after a failed invalidation at its destruction, `InvalidState`, with the context unchanged; after a destruction that succeeds and the creation of another domain, through the old handle, `Stale`, and the new domain reads the initial context | No case: the state of a thread and the reclamation belong to the lifecycle and address-space components (planned) |

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  the SIMD and floating-point registers `V0` to `V31`, FPCR with its fields
  and FPSR; `CPACR_EL1` with the encodings of FPEN and the effect of
  `HCR_EL2.{E2H, TGE}`; `SPSR_EL1` and the fields of PSTATE, with
  `PSTATE.SSBS`, FEAT_DIT, FEAT_BTI and FEAT_MTE; FEAT_SSBS with
  `MSR SSBS, #<imm>`, which EL0 may execute, and FEAT_SSBS2 with the
  special-purpose register `SSBS`; `ELR_EL1`, `SP_EL0`, `TPIDR_EL0` and
  `TPIDRRO_EL0`; the masking of asynchronous exceptions by PSTATE; the
  masking of debug exceptions by `PSTATE.D` and their enables in
  `MDSCR_EL1`; `SCTLR_EL1.UMA`; and `ESR_EL1` with the exception classes
  `0x00`, `0x07` and `0x18`.
- Arm Limited, *Arm Cortex-A76 Core Technical Reference Manual*, revision
  r4p1, document 100798_0401_00_en, 2020,
  <https://documentation-service.arm.com/static/5f562083235b3560a01e03bc>:
  FPCR, whose bits 0 to 18 are RES0 and reset to 0, and the field SSBS of
  `ID_AA64PFR1_EL1`, whose value 1 implements `PSTATE.SSBS` without the
  `MSR` and `MRS` forms that read and write the register `SSBS`.
- The QEMU Project, QEMU 8.2.2, `target/arm/tcg/cpu64.c`,
  <https://gitlab.com/qemu-project/qemu/-/blob/v8.2.2/target/arm/tcg/cpu64.c>:
  the `ID_AA64PFR0_EL1` and `ID_AA64PFR1_EL1` of the CPU `cortex-a76`, with
  FEAT_SSBS and with neither FEAT_DIT nor FEAT_BTI nor FEAT_MTE.
- The QEMU Project, QEMU 8.2.2, `target/arm/helper.c`,
  <https://gitlab.com/qemu-project/qemu/-/blob/v8.2.2/target/arm/helper.c>:
  the register `SSBS`, which QEMU defines with access from EL0 whenever
  `ID_AA64PFR1_EL1.SSBS` is not 0.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/user-execution.md`, lines 185 to 199: the layout
    of the saved user context, the initial context, the validation of the
    code and stack ranges, of the return address, of the stack pointer and
    of PSTATE, TLS values as opaque integers, and the zero FP/SIMD state of
    a context without FP/SIMD, which is not carried.
