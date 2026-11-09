# Boot contract

This page governs the code of the `boot` component of the
[boot and platform](../README.md) domain: the cold entry of a kernel image,
the exception vectors of EL1 with the frame that they save, the processor
primitives that EL1 code reads, the GICv2 and the generic timer, and the
QEMU virt board support with its serial console, its exception record, its
interrupt wiring, its default image and its test images. The observable
behaviour that these rules serve, with its evidence, is in the
[requirements](requirements.md), the other document of the component.

## Terms

- **Cold entry.** `_start`, the ELF entry point of an image, which the
  machine enters on its first CPU with the MMU and the caches off.
- **Boot CPU.** The CPU whose `MPIDR_EL1` affinity levels 0, 1 and 2 are all
  0. Only the boot CPU runs kernel code here.
- **Default image.** The release build of the binary `krepi-qemu-virt` for
  the target `aarch64-unknown-none-softfloat`: the one image of QEMU virt,
  which holds no diagnostic operation, fault probe or command that a
  received byte triggers.
- **Record.** A line of the serial console that starts with `CASXI_` and
  ends in CR LF, in a form that [Records](#records) fixes.
- **Console bounds.** The `Bounds` of a board: the attempts that one byte
  of a record may take, the attempts of the failure marker and the window of
  one record on the counter.
- **Platform parameter.** A spin limit, timeout or window that a board
  gives with a documented value, never a constant tuned on one machine.
- **Exception vectors.** `__exception_vectors`, the table of the 16 entries
  that the CPU branches to through `VBAR_EL1` when it takes an exception to
  EL1.
- **Frame.** The 304 bytes that an entry saves on `SP_EL1`: the general
  registers, the stack pointer above the frame and the exception registers,
  the `Frame` of `krepi_arch::exception`.
- **Dispatch.** `exception_dispatch`, the function of each image that the
  vectors call with the frame.
- **Test image.** An example of the QEMU virt board crate: an image that
  links the production code of the default image and adds its own
  `kernel_main`, dispatch and trigger sequence, for the QEMU boot suite. It
  is test code, not a production image.

## Entry points

| Entry point | Kind | Called by | Rules |
| --- | --- | --- | --- |
| `_start` in `kernel/arch/src/boot.S` | Hardware entry | The machine, at the ELF entry point | [Cold entry](#cold-entry) |
| `__exception_vectors` in `kernel/arch/src/exception.S` | Hardware entry, 16 entries | The CPU, through `VBAR_EL1`, at an exception taken to EL1 | [Exception vectors](#exception-vectors), [Frames](#frames) |
| `kernel_main` in `kernel/boards/qemu-virt/src/main.rs` | Rust entry, `extern "C" fn() -> !` | `_start`, once, on the boot CPU | [Initialization checks](#initialization-checks), [Echo](#echo) |
| `exception_dispatch` in `kernel/boards/qemu-virt/src/main.rs` | Rust entry, `extern "C" fn(&mut Frame)` | The vectors, with every exception masked | [Dispatch](#dispatch) |
| The panic handler of the default image | Rust panic | A failed check or any other panic | [Records](#records), [Console output](#console-output) |
| `krepi_qemu_virt::uart::print` | Function | Kernel code of the boot CPU | [Console output](#console-output) |
| `krepi_qemu_virt::uart::write_echo` | Function | The echo loop | [Echo](#echo) |
| `krepi_qemu_virt::uart::report_panic` | Function | The panic handler | [Records](#records), [Console output](#console-output) |
| `krepi_qemu_virt::uart::report_exception` and `report_fatal` | Functions | The dispatches | [Records](#records), [Dispatch](#dispatch) |
| `krepi_qemu_virt::fault::report` and `report_fatal` | Functions, host-testable | The PL011 driver of a board | [Records](#records), [Console output](#console-output) |
| `krepi_qemu_virt::uart::init`, `try_put` and `get` | Functions | `kernel_main` and the console functions | [Console output](#console-output) |
| `krepi_qemu_virt::console::print`, `write`, `echo`, `report_panic`, `failure_marker`, `report_failure` and `window_ticks` | Functions, host-testable | The PL011 driver of a board | [Console output](#console-output), [Echo](#echo) |
| `verify_cpu` in `kernel/boards/qemu-virt/src/main.rs` | Function | `kernel_main` | [Initialization checks](#initialization-checks) |
| `krepi_arch::exception::Class::of`, `Class::name` and `exception_class` | Functions, host-testable | The exception record | [Records](#records) |
| `krepi_qemu_virt::irq::init` and `handle` | Functions | The test images that take the timer interrupt: their `kernel_main` and their dispatch | [Interrupts](#interrupts) |
| `krepi_arch::gic::Gic::init`, `enable_ppi`, `acknowledge`, `end` and `disable`, `krepi_arch::gic::barrier` and `interrupt_id` | Functions | The interrupt wiring of a board | [Interrupts](#interrupts) |
| `krepi_arch::timer::stop_virtual` and `arm_virtual` | Functions | The interrupt wiring of a board and the test images | [Interrupts](#interrupts) |
| `krepi_arch::cpu::exception_level`, `main_id`, `system_control`, `counter_frequency`, `virtual_counter` and `cpacr` | Functions | Kernel code at EL1 | [Processor registers](#processor-registers) |
| `krepi_arch::cpu::halt` | Function | Fatal paths | [Processor registers](#processor-registers) |

## Extractability

No code of this component follows the
[provable Rust subset](../../../conventions/provable-subset.md): the cold
entry, the exception vectors, the processor primitives, the GICv2 and
timer drivers, the board support and the PL011 driver are none of the
modules that the subset lists, and
its page-table logic leaves the barrier, cache and TLB instructions to
adapters. The section therefore
lists no source paths, and the `subset` step of `cargo xtask check` checks
no file of this component.

## Cold entry

- `_start` masks debug, SError, IRQ and FIQ exceptions with `DAIF` before
  anything else.
- A CPU that is not the boot CPU, or that does not run at EL1, waits in a
  `WFE` loop and never enters Rust.
- The boot CPU sets `CPACR_EL1.FPEN` to 0, so that FP/SIMD instructions trap
  at EL0 and EL1, clears `TPIDR_EL1`, selects `SP_EL1` and sets the stack
  pointer to `__stack_top`.
- It clears `[__bss_start, __bss_end)` with 8-byte stores, writes the
  address of `__exception_vectors` to `VBAR_EL1` followed by an `ISB`, then
  clears the whole stack, `[__stack_bottom, __stack_top)`, with 8-byte
  stores, clears the frame pointer and the link register and calls
  `kernel_main`. If `kernel_main` returned, the CPU would wait in the same
  `WFE` loop.
- Every exception stays masked: neither the cold entry nor the default
  image clears a bit of `DAIF`. An exception before `VBAR_EL1` is written is
  outside these rules: no code of the component handles it.
- The link script places `_start` first, at the start of the image's RAM,
  `0x4020_0000` on QEMU virt, and the exception vectors after it, aligned
  to the 2 KiB that `VBAR_EL1` requires; aligns the stack, 64 KiB with a
  4 KiB guard below it, and the ends of BSS to 4 KiB; requires a GNU
  build-id note of 36 bytes, a SHA-1 build-id; and requires the image to end
  within the 128 MiB of RAM that QEMU virt has at least. A link that breaks
  one of these rules fails. The default image is entered at `_start`; a test
  image names its own entry, `krepi_test_entry`, which branches to `_start`
  or, on the machine with EL2, drops to EL1 and returns to `_start`.

## Exception vectors

- `__exception_vectors`, in the section `.text.vectors`, holds the 16
  entries of the architecture, 128 bytes apart: vectors 0 to 3 for the
  current exception level with `SP_EL0`, 4 to 7 for the current level with
  `SP_ELx`, 8 to 11 for a lower level in AArch64 and 12 to 15 for a lower
  level in AArch32, each four in the order synchronous, IRQ, FIQ and SError.
- Every entry needs a valid `SP_EL1` with 304 bytes below it. It moves
  `SP_EL1` down by 304 bytes, stores `x0` and `x1` at the new stack pointer,
  puts its own number into `x0` and branches to the common save path.
- The save path stores `x2` to `x30` and the vector number in the frame,
  keeps the vector number in `x19`, stores the stack pointer above the
  frame, `ELR_EL1`, `SPSR_EL1`, `ESR_EL1` and `FAR_EL1`, and 0 in the
  reserved word, sets D, A, I and F in `DAIF` and calls
  `exception_dispatch` with the address of the frame.
- When the dispatch returns, the path returns only for vectors 4 to 7,
  which it tells by the number in `x19`, not by the frame: it writes the
  frame's `ELR` and `SPSR` to `ELR_EL1` and `SPSR_EL1`, clears `x0` to `x30`,
  loads each of them from the frame, releases the frame and executes
  `ERET`. For any other vector it masks every exception and waits in a
  `WFE` loop forever.
- The entries save no FP/SIMD state, `SP_EL0` or other system register. For
  the entries of `SP_EL0` and of a lower level, the stack pointer in the
  frame is the address above the frame on `SP_EL1`, not the interrupted
  stack pointer.

The rules of the saved and restored state, each an
[open obligation](#open-obligations) with its test:

| Label | Statement |
| --- | --- |
| `frame` | The entry allocates the 304-byte frame on `SP_EL1`, 16-byte aligned, just below the interrupted stack pointer, and records that stack pointer, the top of the frame. |
| `save-general` | `x0` to `x30` are stored in the frame before any of them is changed: the entry stores `x0` and `x1` before it writes the vector number, and the save path the others before it uses them. |
| `save-system` | `ELR_EL1`, `SPSR_EL1`, `ESR_EL1`, `FAR_EL1` and the vector number are stored in the frame, and the reserved word is 0. |
| `mask` | The dispatch runs with D, A, I and F set, so exceptions do not nest. |
| `restore-elr-spsr` | Before the return, `ELR_EL1` and `SPSR_EL1` are loaded from the frame: a change of the frame's `ELR` by the dispatch takes effect, and the interrupted `PSTATE`, NZCV, DAIF and the mode, comes back. |
| `clear-and-load` | Before the return, `x0` to `x30` are cleared and then each loaded from the frame, so no value that the dispatch left reaches the interrupted code. |
| `release` | The return releases the frame: after it, the stack pointer is that of the interrupted code. |
| `no-fp-state` | Entry and return save and restore no FP/SIMD state: FP/SIMD instructions at EL1 trap through `CPACR_EL1.FPEN`, which no code of the kernel changes after the cold entry. |

## Frames

The frame is the `repr(C)` structure `Frame` of `krepi_arch::exception`,
304 bytes, a multiple of 16; constant assertions fix each offset, and
`exception.S` writes and reads the frame at the same offsets.

| Offset | Field | Content |
| ---: | --- | --- |
| 0 | `x` | `x0` to `x30`, 8 bytes each |
| 248 | `sp` | The stack pointer above the frame |
| 256 | `elr` | `ELR_EL1`, which the return loads back |
| 264 | `spsr` | `SPSR_EL1`, which the return loads back |
| 272 | `esr` | `ESR_EL1` |
| 280 | `far` | `FAR_EL1` |
| 288 | `vector` | The number of the entry, 0 to 15 |
| 296 | `reserved` | 0 |

## Dispatch

- Each image defines `exception_dispatch` as an unmangled
  `extern "C" fn(&mut Frame)`. The vectors call it on `SP_EL1` below the
  frame with every exception masked; it may change the frame, and after a
  return from vectors 4 to 7 the changes of `elr`, `spsr` and `x` become the
  state of the interrupted code.
- The dispatch of the default image writes the exception record of the
  frame and `CASXI_HALTED` with `uart::report_fatal` and halts. The default
  image never unmasks an exception, so only a synchronous exception of its
  own code reaches it.
- A dispatch writes the console only through the exception record, and the
  code that it interrupts is then between two console accesses: the
  default image takes no asynchronous exception, and a test image unmasks
  one only in code that does not write.

## Interrupts

- `irq::init` runs with IRQs masked and leaves them masked. It stops the
  virtual timer, sets the GICv2 at `GIC_DISTRIBUTOR` and `GIC_CPU` up with
  `Gic::init`, enables the timer interrupt `TIMER_INTID`, 27, with
  `Gic::enable_ppi` at `TIMER_PRIORITY`, arms the virtual timer for one
  period after the virtual count of now and completes the writes with
  `barrier`.
- `Gic::init` disables the distributor and the CPU interface, disables the
  SGIs and PPIs of the executing CPU and puts them in group 0, sets the
  priority mask to `0xff` and the binary point to 0, and enables the
  distributor and the CPU interface again, with an end of interrupt that
  drops the priority and deactivates together. `Gic::enable_ppi` clears the
  pending state of a PPI, sets its priority, makes it level-sensitive and
  enables it.
- `irq::handle` runs in the dispatch of an IRQ with every exception masked.
  It acknowledges the interrupt with `GICC_IAR`. A special ID, 1020 to 1023,
  returns without an end of interrupt. The timer interrupt re-arms the
  timer one period after now, so that its level drops; any other interrupt
  is disabled. Then `barrier`, the end of interrupt with the whole
  acknowledged value in `GICC_EOIR`, and `barrier` again. Each acknowledged
  interrupt is ended once.
- The period is the counter frequency divided by `TIMER_RATE`, rounded up
  and at least 1.
- The default image calls neither function: it never unmasks IRQs, so no
  IRQ reaches its dispatch.

## Initialization checks

`kernel_main` first sets the PL011 up, then checks, in this order, and
panics with the message in brackets when a check fails:

1. a word in BSS reads 0 (`BSS not initialized`);
2. a word in the data section reads its initial value (`data not
   initialized`);
3. `CurrentEL` is EL1 (`kernel requires EL1`);
4. `SCTLR_EL1` has the MMU, the data cache and the instruction cache off
   (`MMU/cache must be off`);
5. `MIDR_EL1` names an Arm Cortex-A76 of any variant and revision: its
   implementer and part number, `MIDR_EL1 & 0xff00_fff0`, are
   `0x4100_d0b0` (`QEMU Cortex-A76 required`); the `CASXI_CPU` record
   follows the check;
6. `SCTLR_EL1.EE` is 0, so that EL1 data accesses are little-endian (`EL1
   data must be little-endian`);
7. `CPACR_EL1.FPEN` is 0 (`FP/SIMD must trap`).

The checks read the CPU and two words of the image and write nothing but
the records. Once all have passed, the image writes `CASXI_BOOT` and
`CASXI_READY`.

## Records

Every record is one line that ends in CR LF. The text of a boot record
holds no count, time or address; the `midr` field is the value that the CPU
reports, and the fields of the exception record are the registers of the
exception.

| Record | Form | Written | Then |
| --- | --- | --- | --- |
| `CASXI_CPU` | `CASXI_CPU model=cortex-a76 midr=0x` and the 16 lowercase hexadecimal digits of `MIDR_EL1` | Once, when the CPU check passes | The last two checks |
| `CASXI_BOOT` | `CASXI_BOOT kernel=krepi board=qemu-virt el=` and the exception level from `CurrentEL` in decimal, `1` | Once, after every check has passed | `CASXI_READY` |
| `CASXI_READY` | `CASXI_READY` | Once, after `CASXI_BOOT` | The echo; no other record follows unless a console write fails or the kernel panics |
| `CASXI_PANIC` | A line break, then `CASXI_PANIC` and, after a space, the message of the panic when it is a static text, or `dynamic_panic_message_omitted` | At a panic | `CASXI_PANIC_LOCATION` when the panic has a location, then `CASXI_HALTED` |
| `CASXI_PANIC_LOCATION` | `CASXI_PANIC_LOCATION file=<path> line=<line> column=<column>`, the numbers in decimal | After `CASXI_PANIC` | `CASXI_HALTED` |
| `CASXI_EXCEPTION` | A line break, then `CASXI_EXCEPTION vector=<n> ESR=0x<16> ELR=0x<16> FAR=0x<16> SPSR=0x<16> class=<class>`: the vector number in decimal, the four registers of the frame in 16 lowercase hexadecimal digits, and the class of the table below | When a dispatch reports an exception | `CASXI_HALTED` on a fatal path; otherwise the dispatch returns |
| `CASXI_UART_FAIL` | A line break, then `CASXI_UART_FAIL reason=` and `clock`, `length`, `deadline`, `stalled` or `format` | When a console write fails | `CASXI_HALTED` |
| `CASXI_HALTED` | `CASXI_HALTED` | Last, on a fatal path | The CPU masks every exception and waits forever |

The class of an exception follows from its vector and, at vector 4, from
the exception class `EC`, bits 26 to 31 of `ESR_EL1`, as the Arm
Architecture Reference Manual encodes it:

| Class | Vectors | Syndrome |
| --- | --- | --- |
| `brk` | 4 | EC `0x3c`: a `BRK` instruction in AArch64 state |
| `fp` | 4 | EC `0x07`: an FP/SIMD access that `CPACR_EL1.FPEN` traps |
| `sync` | 4 with any other EC; 0, 8 and 12 with any syndrome | - |
| `irq` | 1, 5, 9 and 13 | - |
| `fiq` | 2, 6, 10 and 14 | - |
| `serror` | 3, 7, 11 and 15 | EC `0x2f` |

The architecture defines no value of `FAR_EL1` for a breakpoint, an FP/SIMD
trap, an IRQ or an SError, and none of `ESR_EL1` for an IRQ or an FIQ; the
record writes the registers as the frame holds them.

The reasons of `CASXI_UART_FAIL` stand for the failures of a console write:
`clock` for bounds or a counter that give no valid window, `length` for a
record longer than 1,024 bytes, `deadline` for a record that took longer
than its window, `stalled` for a byte that the device refused as often as
the bounds allow, and `format` for a formatter that failed.

## Console output

- `uart::init` disables the PL011, masks and clears its interrupts, turns
  DMA off, sets the divisor of 115200 baud for a 24 MHz clock, 8 data bits,
  no parity, 1 stop bit with the FIFOs on, and enables the UART with its
  transmitter and receiver, without flow control.
- `try_put` writes a byte only when the transmit FIFO is not full, and
  `get` reads one only when the receive FIFO is not empty; neither waits.
- A record is formatted without allocation, with each LF written as CR LF,
  and is at most 1,024 bytes long after that expansion.
- Each attempt to write a byte first reads the counter: once the window has
  passed since the start of the record, the write fails. A byte that the
  device refuses as often as `attempts_per_byte` fails the write, also when
  the counter stops. A written byte renews that allowance, never the window.
- A failed write can leave a prefix of the record on the device. It never
  restarts, and the caller does not report the record as written: the PL011
  driver writes the failure marker of the failure, `CASXI_UART_FAIL` and
  `CASXI_HALTED`, with at most `failure_attempts` attempts in all, without
  formatting or the counter, and halts the CPU.
- A panic writes its record line by line, each line a record within the
  bounds: `CASXI_PANIC`, `CASXI_PANIC_LOCATION` when the panic has a
  location, and `CASXI_HALTED`. A line that fails ends the panic record, and
  the PL011 driver writes the failure marker and halts; a message too long
  for one record fails with `length`.
- The exception record and, on a fatal path, `CASXI_HALTED` are written as
  records of their own within the bounds; a line that fails is followed by
  the failure marker and the halt, not by the next line.
- Only the boot CPU writes. An exception dispatch writes only the
  exception record, with every exception masked, between two console
  accesses of the code that it interrupted ([Dispatch](#dispatch)), and no
  dispatch reads the console.

## Echo

- After `CASXI_READY`, `kernel_main` loops forever: it takes the next
  received byte, when there is one, and writes it back with
  `uart::write_echo`, which writes the byte unchanged and, after a carriage
  return (`0x0d`), a line feed (`0x0a`). No other byte is translated, added
  or dropped, and no received byte starts any other action.
- An echo is written within the same bounds as a record and fails in the
  same ways, except that it has no formatting to fail.

## Processor registers

- The functions of `krepi_arch::cpu` read `CurrentEL`, `MIDR_EL1`,
  `SCTLR_EL1`, `CNTFRQ_EL0`, `CNTVCT_EL0` and `CPACR_EL1` of the CPU that
  executes them, at EL1. They touch no memory.
- `virtual_counter` executes `ISB` before it reads `CNTVCT_EL0`, so that the
  read follows the instructions before it, and is never merged with another
  read.
- `halt` masks every exception of the executing CPU and waits in a `WFE`
  loop forever; other CPUs are not stopped.

## Platform parameters

| Parameter | Use | QEMU virt |
| --- | --- | ---: |
| `attempts_per_byte` | Refusals of one byte before a record fails | 1,000,000 |
| `failure_attempts` | Attempts of the failure marker in all | 1,000,000 |
| `window_ms` | Longest time of one record on the counter | 250 ms |
| `TIMER_RATE` | Timer interrupts per second, whose inverse is the period of the timer | 100 |

At 115200 baud a record of 1,024 bytes takes about 89 ms on the wire, so the
window leaves room for a whole record; QEMU does not model the baud rate.
The Raspberry Pi 5 values are given by its board support.

## Check and execute

- A console write checks its bounds before it reads the counter or touches
  the device: attempts per byte of 0, or a window of 0 ticks or of at least
  `2^63` ticks, fail with `clock` before the first write. Its write phase
  can fail with `length`, `deadline`, `stalled` or `format` and leaves the
  bytes written so far.
- `kernel_main` sets the console up, which writes the PL011, before its
  checks, so that a failed check can be reported. The checks themselves
  write nothing but records.

## Work bounds

- `_start` clears BSS and the 64 KiB stack once: its loops run at most once
  per 8 bytes of each.
- A console write makes at most `attempts_per_byte` attempts for each of at
  most 1,024 bytes and ends at the latest when its window has passed on a
  running counter. The failure marker makes at most `failure_attempts`
  attempts.
- The echo loop does not end: each pass reads the receive FIFO once and
  writes at most two bytes within the bounds of a record.
- An exception entry and its return run a fixed sequence of instructions
  without a loop. The dispatch of the default image writes two records
  within the console bounds and halts.
- `irq::init` and `irq::handle` make a fixed number of register accesses
  without a loop.

## Determinism

The component makes no internal choice. Every record follows from the
state of the CPU and the bytes received, in a fixed order. Whether a console
write fails by its window depends on the counter, which is time:
[ND-01](../../../security.md#nd-01) of the register of
[permitted nondeterminism](../../../security.md#permitted-nondeterminism).
Which bytes arrive, and when, is the input of the echo. When a timer
interrupt arrives, and so which instruction it interrupts, depends on the
counter as well.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The PL011 registers | Shared | The boot CPU alone; no interrupt handler accesses them | The volatile access to the register | `none`: its single owner never changes |
| The BSS and data probe words of the default image | Shared, read-only after load | The boot CPU, which only reads them | Their initialization by the cold entry and the load of the image | `none`: no CPU writes them after the cold entry |
| The boot stack, `[__stack_bottom, __stack_top)` | Per-CPU, of the boot CPU | The boot CPU | - | `none` |
| `DAIF`, `CPACR_EL1`, `SCTLR_EL1`, `TPIDR_EL1`, `VBAR_EL1` and the stack pointer of EL1 | Per-CPU | The executing CPU | The `ISB` after the cold entry's writes | `none` |
| The frame of an exception, 304 bytes on `SP_EL1` | Per-CPU, of the CPU that took the exception | Its exception entry, then its dispatch, then its return | - | `none`: the return releases it |
| `ELR_EL1`, `SPSR_EL1`, `ESR_EL1` and `FAR_EL1` | Per-CPU | The exception entry and the return path of the executing CPU | The `ERET` | `none` |
| The distributor and CPU interface registers of the GICv2 | Shared | The boot CPU alone: `irq::init` with IRQs masked, then `irq::handle` in the dispatch of an IRQ | The volatile access to the register | `none`: its single owner never changes |
| `CNTV_CTL_EL0` and `CNTV_CVAL_EL0` | Per-CPU | The executing CPU | The `ISB` after the writes | `none` |

## Testing obligations

- The host tests of `kernel/boards/qemu-virt/src/console/` cover the console
  logic: the expansion of LF, the echo of every kind of byte, the panic
  record with a static message, with a message that is not static, without
  a location and with a message too long for a record, each failure of a
  write with its marker, the bounds of the failure marker and the
  conversion of the window into ticks, with values written from this page.
  The tests taken from the prototype tree keep their expected values.
- The host tests of `kernel/boards/qemu-virt/src/fault/` hold the bytes of
  the exception record and of the fatal path against the record table, and
  those of `kernel/arch/src/exception/` the class of each vector and
  syndrome, with syndromes written from the Arm Architecture Reference
  Manual.
- The QEMU boot suite boots the default image on QEMU virt and holds its
  transcript against the records of this page, written into the suite, not
  taken from an earlier run. Three cold boots give identical transcripts.
- The suite also boots the test images, each once, and holds each
  transcript against an exact sequence of records: the start record
  `CASXI_TEST image=<image>`, the exception records of the case, and then
  `CASXI_HALTED` or the self-check records `CASXI_CHECK name=<check>
  failures=0x<16>` of the image, each with no failure, and
  `CASXI_RESUMED`. The return address of each exception record must be that
  of a symbol of the image, or lie between two. Each rule of the saved and
  restored state has one test, a self-check of a test image or a case of
  the suite, named in the [open obligations](#open-obligations).
- The test images that take the timer interrupt wait for it for at most
  1,000 ms on the counter, a platform parameter of QEMU virt for these
  images, where the interrupt comes after one period of 10 ms.
- No test bounds the time that a step takes, and the guest takes its
  windows and spin limits from the platform parameters.

## Open obligations

| Obligation | Kind | Verified state | Carrier | Stage | Test | Lines |
| --- | --- | --- | --- | --- | --- | --- |
| `kernel/arch/src/boot.S` | `assembly` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | 64 |
| `kernel/arch/src/exception.S` | `assembly` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | 133 |
| `kernel/arch/src/exception.S#frame` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `frame-records-interrupted-sp` | - |
| `kernel/arch/src/exception.S#save-general` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `entry-saves-general-registers` | - |
| `kernel/arch/src/exception.S#save-system` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `frame-records-system-registers` | - |
| `kernel/arch/src/exception.S#mask` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `dispatch-masks-daif` | - |
| `kernel/arch/src/exception.S#restore-elr-spsr` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `return-restores-elr-and-pstate` | - |
| `kernel/arch/src/exception.S#clear-and-load` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `irq-preserves-registers` | - |
| `kernel/arch/src/exception.S#release` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `return-restores-sp` | - |
| `kernel/arch/src/exception.S#no-fp-state` | `register-state` | Neither | The proof of the register state that exception entry and return save, restore and clear | `0.2` | `el1-fp-trap` | - |
| `kernel/arch/src/exception.rs` | `code` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/gic.rs` | `code` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/gic.rs#read` | `mmio` | Neither (reads a GICv2 register) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/gic.rs#write` | `mmio` | Neither (writes a GICv2 register) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/gic.rs#barrier` | `unsafe` | Neither (executes `DSB SY` and `ISB`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/timer.rs` | `code` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/timer.rs#stop_virtual` | `unsafe` | Neither (writes `CNTV_CTL_EL0`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/timer.rs#arm_virtual` | `unsafe` | Neither (writes `CNTV_CVAL_EL0` and `CNTV_CTL_EL0`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs` | `code` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs#exception_level` | `unsafe` | Neither (reads `CurrentEL`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs#main_id` | `unsafe` | Neither (reads `MIDR_EL1`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs#system_control` | `unsafe` | Neither (reads `SCTLR_EL1`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs#counter_frequency` | `unsafe` | Neither (reads `CNTFRQ_EL0`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs#virtual_counter` | `unsafe` | Neither (reads `CNTVCT_EL0`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs#cpacr` | `unsafe` | Neither (reads `CPACR_EL1`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/arch/src/cpu.rs#halt` | `unsafe` | Neither (writes `DAIF`, waits with `WFE`) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/boards/qemu-virt/src` | `code` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/boards/qemu-virt/src/uart.rs#read` | `mmio` | Neither (reads a PL011 register) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/boards/qemu-virt/src/uart.rs#write` | `mmio` | Neither (writes a PL011 register) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/boards/qemu-virt/src/main.rs#image::initialize` | `unsafe` | Neither (reads two words of the image) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/boards/qemu-virt/src/main.rs#image::kernel_main` | `unsafe` | Neither (exports the unmangled symbol that the cold entry calls) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |
| `kernel/boards/qemu-virt/src/main.rs#image::exception_dispatch` | `unsafe` | Neither (exports the unmangled symbol that the vectors call) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | - |

## Legacy test vectors

The component has no specification, so it freezes no test vectors. The
prototype tests that the console took over are host tests of its code, with
their expected values, and the
[porting record of the console](../../../porting/console.md) lists them.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487,
  <https://developer.arm.com/documentation/ddi0487/latest/>: `CurrentEL`,
  `MIDR_EL1`, `SCTLR_EL1`, `CPACR_EL1`, `CNTFRQ_EL0`, `CNTVCT_EL0`, `DAIF`
  and `WFE`; the exception entry and return, the vector table and
  `VBAR_EL1`; `ESR_EL1` with the exception classes `0x07`, `0x2f` and
  `0x3c`, `ELR_EL1`, `SPSR_EL1` and `FAR_EL1`; and, for the test image that
  enters at EL2, `HCR_EL2` with RW, AMO and VSE, `VSESR_EL2`,
  `CNTHCTL_EL2`, `CNTVOFF_EL2` and `VMPIDR_EL2`; the generic timer,
  `CNTV_CTL_EL0` and `CNTV_CVAL_EL0`, and `ISR_EL1`.
- Arm Limited, *ARM Generic Interrupt Controller Architecture
  Specification, GIC architecture version 2.0*, IHI 0048B: the distributor
  and CPU interface registers, the acknowledgement, the special interrupt
  IDs and the end of interrupt.
- Arm Limited, *Arm Cortex-A76 Core Technical Reference Manual*, revision
  r4p1, document 100798_0401_00_en, 2020,
  <https://documentation-service.arm.com/static/5f562083235b3560a01e03bc>:
  the implementer and part number in `MIDR_EL1`.
- Arm Limited, *PrimeCell UART (PL011) Technical Reference Manual*, revision
  r1p5, DDI 0183G, 2007,
  <https://documentation-service.arm.com/static/5e8e36c2fd977155116a90b5>:
  the registers, flags and divisors.
- The QEMU Project, *'virt' generic virtual platform*,
  <https://www.qemu.org/docs/master/system/arm/virt.html>: the machine, its
  RAM, its PL011, its GICv2 and the virtual timer interrupt.
