---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/qemu/irq.rs
destination:
  - kernel/arch/src/timer.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/timer.rs

## Summary

The virtual timer of the ARM generic timer, taken from the QEMU virt
interrupt code of `src/board/qemu/irq.rs`: `arm`, which set the compare
value of the virtual timer and enabled it, and the stop of the timer in its
`init`, as `arm_virtual` and `stop_virtual`. The module `timer` of
`krepi-arch` holds them, so that the boards share the generic timer; QEMU
virt uses the virtual timer, and the physical timer of the Pi 5 comes with
its board support. The period and the interrupt of QEMU virt are in
[irq](irq.md). The module is compiled only for the bare-metal target.

## Changes

- `arm_virtual` keeps the writes of `arm`, `CNTV_CVAL_EL0` and then
  `CNTV_CTL_EL0` with ENABLE set and IMASK clear, and the `ISB` after them;
  the enable value is an input operand in place of a write of `x9`, which
  the legacy asm clobbered.
- `stop_virtual` is the write of 0 to `CNTV_CTL_EL0` with its `ISB` from the
  legacy `init`, as a function of its own.
- The asm keeps its options and is not `nomem`, so that the compiler keeps
  the accesses to the interrupt controller around it on their side.
- The `SAFETY` comments are written again; the module and each function
  have documentation, and the line
  `//! Feature: krepi.platform.qemu-virt-boot` names the feature.

## Tests carried over

None: the legacy module had no host tests.

## Behaviour changes

None: the instructions are those of the legacy code.

## Hardware evidence to re-obtain

- The timer interrupts of QEMU virt, armed, re-armed and stopped: the cases
  `timer-irq` and `irq-preserves-registers` of `cargo xtask qemu-boot`, in
  CI.
- The timer of the Pi 5 with its board support on the bench (planned).

## Not carried over

- The masked deadline of `set_syscall_probe_deadline`, which served a
  diagnostic probe.
- The physical timer of the physical-entry profile, which comes with the
  Pi 5 board support.
- The legacy feature annotation `system.kernel.interrupts`.
