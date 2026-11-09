---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/qemu/irq.rs
destination:
  - kernel/arch/src/gic.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/gic.rs

## Summary

The GICv2 driver of the kernel, taken from the QEMU virt interrupt code of
`src/board/qemu/irq.rs`: the register accesses `read` and `write`, the
barrier, and the steps of its `init` and `handle` that touch the
controller, as `Gic::init`, `Gic::enable_ppi`, `Gic::acknowledge`,
`Gic::end` and `Gic::disable` on a controller whose base addresses the
board gives. The module `gic` of `krepi-arch` holds them, so that the boards
that have a GICv2 share them; the wiring of QEMU virt, its addresses, the
timer interrupt and the period, is in [irq](irq.md), and the virtual timer
in [timer](timer.md). The module is compiled only for the bare-metal
target. The legacy area `src/board` is ported, as
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies it.

## Changes

- The base addresses are the private fields of `Gic`, in place of the
  constants `DIST` and `CPU` of the legacy board module, and each register
  has a named offset. A board names its GICv2 with the `unsafe` function
  `Gic::new`, whose `# Safety` section states what the `SAFETY` comments of
  the register accesses rely on: the addresses are the register frames of a
  GICv2 reached as Device memory, and one CPU uses the controller with IRQs
  masked. With safe fields, safe code could have named any address.
- `Gic::init` takes the steps of the legacy `init` that set the controller
  up without an interrupt: the distributor and the CPU interface off, the
  PPIs of the CPU, and its SGIs where the GIC lets them be disabled,
  disabled and in group 0, the priority mask `0xff`, the binary point 0, and
  the distributor and the CPU interface on again. The legacy `init` enabled
  the timer interrupt before it turned them on; here `Gic::enable_ppi`
  enables it after, with IRQs masked at the CPU all the while, so no
  interrupt is taken in between. The documentation states, as the legacy
  comments did, that writes to clear the enable of an SGI may be ignored,
  that group 0 is signalled as IRQs only on a GIC without the Security
  Extensions, as QEMU virt with `secure=off` has, and that the binary point
  0 leaves the nesting of interrupts to the masking of the dispatch; it adds
  that the SPIs and the active state stay as the reset left them.
- `Gic::enable_ppi` takes the steps for the timer interrupt, clearing its
  pending state, setting its priority, making it level-sensitive and
  enabling it, for any PPI: the byte of the priority and the bits of the
  configuration follow from the interrupt ID, where the legacy code shifted
  by fixed amounts that held for interrupt 27 only. It panics before any
  access for an ID that is not a PPI, and `Gic::disable` for a special ID,
  so that no ID reaches a register outside the distributor's frame.
- `Gic::acknowledge`, `Gic::end` and `Gic::disable` are the accesses of the
  legacy `handle_local` to `GICC_IAR`, `GICC_EOIR` and `GICD_ICENABLER`;
  `interrupt_id` and `SPECIAL` name the interrupt ID field and the first
  special ID, 1020. The choice of what to do with an interrupt is in
  [irq](irq.md).
- `barrier` keeps `DSB SY` and `ISB` and their options.
- The `SAFETY` comments are written again for a controller whose addresses
  the board gives, and name the Device memory of the MMU while it is off;
  the line `//! Feature: krepi.platform.qemu-virt-boot` names the feature.

## Tests carried over

None: the legacy module had no host tests, as its functions run only on the
bare-metal target.

## Behaviour changes

| Change | Evidence |
| --- | --- |
| The timer interrupt is enabled after the distributor and the CPU interface are on, with IRQs masked, where the legacy code enabled it before | The case `timer-irq` of `cargo xtask qemu-boot`, whose interrupts arrive and end |
| The priority byte and the configuration bits of a PPI follow from its ID | The same case, for interrupt 27 |

## Hardware evidence to re-obtain

- The configuration, acknowledgement and end of the timer interrupt on the
  GICv2 of QEMU virt, and the disabling of another interrupt: the cases
  `timer-irq`, `irq-preserves-registers` and `unexpected-irq` of
  `cargo xtask qemu-boot`, in CI.
- The GIC-400 of the Pi 5, which implements GICv2, comes with the Pi 5
  board support and its bench runs (planned).

## Not carried over

- The CPU-local state of the legacy module, its period cell and its
  statistics with `snapshot`, which served the serial diagnostics, and the
  routing slot of a device interrupt: the wiring of [irq](irq.md) computes
  the period when it needs it.
- The device interrupt of the PL031, `device_configure`, `device_disable`,
  `device_enable`, `device_idle` and `Idle`, and the wait for an interrupt
  that they used: device interrupts come with the routing of interrupts to
  EL0 drivers.
- `set_deadline`, `set_syscall_probe_deadline` and `restore_periodic`,
  which served the scheduler and a diagnostic probe.
- The legacy feature annotation `system.kernel.interrupts`.
