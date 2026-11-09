---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/qemu/irq.rs
destination:
  - kernel/boards/qemu-virt/src/irq.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/boards/qemu-virt/src/irq.rs

## Summary

The interrupt wiring of QEMU virt, taken from `src/board/qemu/irq.rs`: its
`init`, which set the GICv2 and the virtual timer up, and its `handle`,
which acknowledged an interrupt, re-armed the timer or disabled another
interrupt and ended it. The module `irq` of `krepi-qemu-virt` keeps that
order of steps and gives the drivers of `krepi-arch`, [gic](gic.md) and
[timer](timer.md), the addresses, the timer interrupt 27, its priority and
the period of the board. The module is compiled only for the bare-metal
target; the default image does not call it, and the test images that take
the timer interrupt do.

## Changes

- `init` stops the timer, sets the GIC up, enables the timer interrupt at
  priority `0x80`, arms the timer one period from now and completes the
  writes with the barrier, in the legacy order but for the place of the
  enable, which [gic](gic.md) describes. It neither masks nor unmasks IRQs:
  the legacy `init` masked them first and unmasked them last; here they are
  masked from the cold entry on, and the code that takes the interrupt
  unmasks them.
- The period is the counter frequency divided by the platform parameter
  `TIMER_RATE`, 100, rounded up and at least 1, as in the legacy code, and
  is computed when it is needed, in place of a CPU-local cell that `init`
  set once.
- `handle` keeps the steps of the legacy `handle_local`: a special ID from
  1020 on returns without an end of interrupt; the timer interrupt re-arms
  the timer one period after now; any other interrupt is disabled; then
  the barrier, the end of interrupt with the whole acknowledged value and
  the barrier again. It returns which of the three it was, `Interrupt`, in
  place of whether a timer or a captured device interrupt was serviced.
- The addresses `GIC_DISTRIBUTOR`, `0x0800_0000`, and `GIC_CPU`,
  `0x0801_0000`, the interrupt `TIMER_INTID`, 27, `TIMER_PRIORITY` and
  `TIMER_RATE` are constants of the crate root, which the
  [qemu-virt](qemu-virt.md) record describes. The module names the GICv2
  with the `unsafe` function `Gic::new` of [gic](gic.md), in a constant
  whose `SAFETY` comment states why the addresses are those of the GICv2 of
  QEMU virt and why one CPU uses it with IRQs masked.
- The line `//! Feature: krepi.platform.qemu-virt-boot` names the feature.

## Tests carried over

None: the legacy module had no host tests.

## Behaviour changes

| Change | Evidence |
| --- | --- |
| `init` leaves IRQs masked, and the code that takes the timer interrupt unmasks them | The cases `timer-irq` and `irq-preserves-registers` of `cargo xtask qemu-boot` |
| `handle` keeps no statistics and returns the kind of the interrupt | The case `timer-irq`, whose image counts the timer interrupts |
| Every interrupt but the timer interrupt is unexpected, the device interrupt 34 of the PL031 among them: it is disabled and ended | The case `unexpected-irq` of `cargo xtask qemu-boot`, whose image enables interrupt 30, the physical timer, and checks that it came once and is disabled |

## Hardware evidence to re-obtain

- Two timer interrupts, each ended and re-armed, one taken at a known
  instruction and one unexpected interrupt, disabled and ended, on QEMU
  virt: the cases `timer-irq`, `irq-preserves-registers` and
  `unexpected-irq`, in CI.

## Not carried over

- The CPU-local state `Local` with its period cell, its statistics and the
  routing slot, `with`, `initialized`, `route` and `snapshot`, which served
  the serial diagnostics and the routing of device interrupts.
- The device interrupt 34 of the PL031 in `handle`, and the device functions
  `device_configure`, `device_disable`, `device_enable`, `device_idle`,
  `Idle` and `disable_device`: device interrupts come with their routing to
  EL0 drivers.
- `set_deadline`, `set_syscall_probe_deadline` and `restore_periodic`,
  which served the scheduler and a diagnostic probe.
- The legacy feature annotation `system.kernel.interrupts`.
