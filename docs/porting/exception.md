---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/arch/aarch64/exception.rs
  - src/arch/aarch64/kernel_vectors.S
destination:
  - kernel/arch/src/exception.rs
  - kernel/arch/src/exception.S
  - kernel/arch/src/exception/tests.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/exception.rs

## Summary

The exception vectors of EL1 and the frame that they save: the 16 entries
of `src/arch/aarch64/kernel_vectors.S` with their common save path and
return, and the frame `ExceptionFrame` of `src/arch/aarch64/exception.rs`.
The module `exception` of `krepi-arch` holds the frame, which the vectors
fill and each image's dispatch receives, and the class of an exception,
which the exception record names; both are plain code that the host tests
run. Its submodule `vectors` includes the assembly `exception.S` and is
compiled only for the bare-metal target. The cold entry installs the table
in `VBAR_EL1`; the
[boot contract](../domains/boot-platform/boot/contract.md#exception-vectors)
states the rules of the vectors, the frame and the dispatch.

## Changes

- `ExceptionFrame` is `Frame`, and its field `regs` is `x`; the layout, 304
  bytes with the stack pointer at 248, `ELR_EL1` at 256 and the vector number
  at 288, is the legacy one. Constant assertions fix the offset of every
  field, not only of three. The frame is `Clone`, `Copy`, `Debug`,
  `PartialEq` and `Eq` and has a frame of zeros, `Frame::ZERO`.
- New: the exception class `exception_class`, the two vector numbers and
  exception classes that the record needs, and `Class` with `Class::of` and
  `Class::name`, which name the class of the exception record: `brk` and
  `fp` for a breakpoint and an FP/SIMD trap at vector 4, `sync` for any
  other synchronous exception, `irq`, `fiq` and `serror`. The legacy fault
  record had no class.
- The entries of a lower exception level no longer read `SP_EL0` into the
  frame (legacy lines 48-51), and the return no longer writes `SP_EL0` back
  (lines 69-73): every entry records the stack pointer above the frame on
  `SP_EL1`, which for the entries of the current level with `SP_EL1` is the
  interrupted stack pointer (lines 53 and 55, kept).
- The legacy path returned from every entry. This one returns only from the
  four entries of the current level with `SP_EL1`, vectors 4 to 7, and halts
  with every exception masked when the dispatch of another entry returns. It
  tells the entries apart by the vector number that it keeps in `x19`, which
  the dispatch preserves, so a dispatch that changes the frame's vector
  field cannot make a halting entry return.
- The clear of `x0` to `x30` before their loads is kept, with a comment that
  states what it changes: a register that a load missed reads 0, not a value
  of the dispatch. The mask of every exception before the dispatch is kept,
  with a comment that taking the exception has set the four bits already.
- The table symbol has the type `%function`, as `_start` has. The comments
  are written again; the line `//! Feature: krepi.platform.qemu-virt-boot`,
  an assembly comment, names the feature.

## Tests carried over

None: the legacy tree had no host test of the frame or the vectors. The new
tests of `kernel/arch/src/exception/tests.rs` hold the class of each entry
and syndrome, with syndromes written from the Arm Architecture Reference
Manual.

## Behaviour changes

| Change | Evidence |
| --- | --- |
| An exception of a lower level or of the current level with `SP_EL0` halts once its dispatch returns, where the legacy path returned to it | Host: `exception::tests::the_other_entries_give_sync_for_a_breakpoint` for the class; the return path itself has no test, as no image takes such an exception |
| The saved stack pointer of those entries is the address above the frame, not `SP_EL0` | None: no image takes such an exception |
| The entries of the current level with `SP_EL1` return as before | The case `el1-brk` of `cargo xtask qemu-boot` |

## Hardware evidence to re-obtain

- The breakpoint, the FP/SIMD trap and the virtual SError on the machine
  with EL2 on QEMU virt with one Cortex-A76: the cases `el1-brk`,
  `el1-fp-trap` and `injected-serror` of `cargo xtask qemu-boot`, in CI.
- The same vectors on the Pi 5, after its EL2 to EL1 entry, on the HIL bench
  (planned).

## Not carried over

- `irq_register_probe` (legacy lines 126-212), the IRQ return probe of the
  register-preservation diagnostic: the test images check the registers
  around an exception with sequences of their own.
- `diagnostic_bad_fp` (lines 214-222), a fault probe: the default image
  holds none.
- The save and restore of `SP_EL0` and the return to a lower level: they
  come with the handling of exceptions from EL0, which has rules of its own.
- The legacy feature annotation `system.kernel.interrupts` of
  `src/arch/aarch64/exception.rs`.
