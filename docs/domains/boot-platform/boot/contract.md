# Boot contract

This page governs the code of the `boot` component of the
[boot and platform](../README.md) domain: the cold entry of a kernel image,
the processor primitives that EL1 code reads, and the QEMU virt board
support with its serial console and its default image. The observable
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

## Entry points

| Entry point | Kind | Called by | Rules |
| --- | --- | --- | --- |
| `_start` in `kernel/arch/src/boot.S` | Hardware entry | The machine, at the ELF entry point | [Cold entry](#cold-entry) |
| `kernel_main` in `kernel/boards/qemu-virt/src/main.rs` | Rust entry, `extern "C" fn() -> !` | `_start`, once, on the boot CPU | [Initialization checks](#initialization-checks), [Echo](#echo) |
| The panic handler of the default image | Rust panic | A failed check or any other panic | [Records](#records), [Console output](#console-output) |
| `krepi_qemu_virt::uart::print` | Function | Kernel code of the boot CPU | [Console output](#console-output) |
| `krepi_qemu_virt::uart::write_echo` | Function | The echo loop | [Echo](#echo) |
| `krepi_qemu_virt::uart::report_panic` | Function | The panic handler | [Records](#records), [Console output](#console-output) |
| `krepi_qemu_virt::uart::init`, `try_put` and `get` | Functions | `kernel_main` and the console functions | [Console output](#console-output) |
| `krepi_qemu_virt::console::print`, `write`, `echo`, `report_panic`, `failure_marker`, `report_failure` and `window_ticks` | Functions, host-testable | The PL011 driver of a board | [Console output](#console-output), [Echo](#echo) |
| `krepi_qemu_virt::verify_cpu` | Function | `kernel_main` | [Initialization checks](#initialization-checks) |
| `krepi_arch::cpu::exception_level`, `main_id`, `system_control`, `counter_frequency`, `virtual_counter` and `cpacr` | Functions | Kernel code at EL1 | [Processor registers](#processor-registers) |
| `krepi_arch::cpu::halt` | Function | Fatal paths | [Processor registers](#processor-registers) |

## Extractability

No code of this component follows the
[provable Rust subset](../../../conventions/provable-subset.md): the cold
entry, the processor primitives, the board support and the PL011 driver are
none of the modules that the subset lists, and its page-table logic leaves
the barrier, cache and TLB instructions to adapters. The section therefore
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
- It clears `[__bss_start, __bss_end)` and then the whole stack,
  `[__stack_bottom, __stack_top)`, with 8-byte stores, clears the frame
  pointer and the link register and calls `kernel_main`. If `kernel_main`
  returned, the CPU would wait in the same `WFE` loop.
- The link script places `_start` first, at the start of the image's RAM,
  `0x4020_0000` on QEMU virt; aligns the stack, 64 KiB with a 4 KiB guard
  below it, and the ends of BSS to 4 KiB; requires a GNU build-id note of 36
  bytes, a SHA-1 build-id; and requires the image to end within the 128 MiB
  of RAM that QEMU virt has at least. A link that breaks one of these rules
  fails.
- The image installs no exception vector table. An exception before one is
  installed is outside these rules: no code of the component handles it.

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

Every record is one line that ends in CR LF. The text of a record holds no
count, time or address; the `midr` field is the value that the CPU reports.

| Record | Form | Written | Then |
| --- | --- | --- | --- |
| `CASXI_CPU` | `CASXI_CPU model=cortex-a76 midr=0x` and the 16 lowercase hexadecimal digits of `MIDR_EL1` | Once, when the CPU check passes | The last two checks |
| `CASXI_BOOT` | `CASXI_BOOT kernel=krepi board=qemu-virt el=` and the exception level from `CurrentEL` in decimal, `1` | Once, after every check has passed | `CASXI_READY` |
| `CASXI_READY` | `CASXI_READY` | Once, after `CASXI_BOOT` | The echo; no other record follows unless a console write fails or the kernel panics |
| `CASXI_PANIC` | A line break, then `CASXI_PANIC` and, after a space, the message of the panic when it is a static text, or `dynamic_panic_message_omitted` | At a panic | `CASXI_PANIC_LOCATION` when the panic has a location, then `CASXI_HALTED` |
| `CASXI_PANIC_LOCATION` | `CASXI_PANIC_LOCATION file=<path> line=<line> column=<column>`, the numbers in decimal | After `CASXI_PANIC` | `CASXI_HALTED` |
| `CASXI_UART_FAIL` | A line break, then `CASXI_UART_FAIL reason=` and `clock`, `length`, `deadline`, `stalled` or `format` | When a console write fails | `CASXI_HALTED` |
| `CASXI_HALTED` | `CASXI_HALTED` | Last, on a fatal path | The CPU masks every exception and waits forever |

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
- Only the boot CPU writes, and no interrupt handler writes or reads the
  console.

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

## Determinism

The component makes no internal choice. Every record follows from the
state of the CPU and the bytes received, in a fixed order. Whether a console
write fails by its window depends on the counter, which is time:
[ND-01](../../../security.md#nd-01) of the register of
[permitted nondeterminism](../../../security.md#permitted-nondeterminism).
Which bytes arrive, and when, is the input of the echo.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The PL011 registers | Shared | The boot CPU alone; no interrupt handler accesses them | The volatile access to the register | `none`: its single owner never changes |
| The BSS and data probe words of the default image | Shared, read-only after load | The boot CPU, which only reads them | Their initialization by the cold entry and the load of the image | `none`: no CPU writes them after the cold entry |
| The boot stack, `[__stack_bottom, __stack_top)` | Per-CPU, of the boot CPU | The boot CPU | - | `none` |
| `DAIF`, `CPACR_EL1`, `SCTLR_EL1`, `TPIDR_EL1` and the stack pointer of EL1 | Per-CPU | The executing CPU | The `ISB` after the cold entry's writes | `none` |

## Testing obligations

- The host tests of `kernel/boards/qemu-virt/src/console/` cover the console
  logic: the expansion of LF, the echo of every kind of byte, the panic
  record with a static message, with a message that is not static, without
  a location and with a message too long for a record, each failure of a
  write with its marker, the bounds of the failure marker and the
  conversion of the window into ticks, with values written from this page.
  The tests taken from the prototype tree keep their expected values.
- The QEMU boot suite boots the default image on QEMU virt and holds its
  transcript against the records of this page, written into the suite, not
  taken from an earlier run. Three cold boots give identical transcripts.
- No test bounds the time that a step takes, and the guest takes its
  windows and spin limits from the platform parameters.

## Open obligations

| Obligation | Kind | Verified state | Carrier | Stage | Test | Lines |
| --- | --- | --- | --- | --- | --- | --- |
| `kernel/arch/src/boot.S` | `assembly` | Neither | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` | - | 59 |
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
  and `WFE`.
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
  RAM and its PL011.
