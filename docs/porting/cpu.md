---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/arch/aarch64/cpu.rs
destination:
  - kernel/arch/src/cpu.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/cpu.rs

## Summary

The processor operations of EL1 that the boot of the QEMU virt image uses:
`exception_level`, `main_id`, `system_control`, `counter_frequency`,
`virtual_counter` and `cpacr`, which read `CurrentEL`, `MIDR_EL1`,
`SCTLR_EL1`, `CNTFRQ_EL0`, `CNTVCT_EL0` and `CPACR_EL1`, and `halt`, which
masks every exception and waits in a `WFE` loop. The module is compiled only
for the bare-metal target, as in the legacy tree, and part of it is ported:
the diagnostic triggers stay behind, and the operations that no code of this
change calls come with their first caller.

## Changes

- Each function keeps its instructions and its `asm!` options. The `SAFETY`
  comments are written again to state the exception level, the absence of
  memory accesses and, for `virtual_counter`, why the `ISB` precedes the read
  and why the asm is not `nomem`; each function has documentation.
- The module documentation states that each function acts only on the
  system registers of the executing CPU and touches no memory.
- The re-export of `ExceptionFrame` is left out; see
  [Not carried over](#not-carried-over).
- The line `//! Feature: krepi.platform.qemu-virt-boot` names the feature.

## Tests carried over

None: the legacy module had no host tests, as its functions run only on the
bare-metal target.

## Behaviour changes

None: the instructions and their options are those of the legacy functions.

## Hardware evidence to re-obtain

- The reads at EL1 on QEMU virt with one Cortex-A76, which the initialization
  checks and the CPU identity record of the case `cold-boot-echo` of
  `cargo xtask qemu-boot` obtain.
- The same reads on the Pi 5, after its EL2 to EL1 entry, on the HIL bench
  (planned).

## Not carried over

- The diagnostic triggers `diagnostic_breakpoint`, `fp_probe`,
  `register_probe` with `irq_probe_check`, and `bad_frame_probe`: the
  default image holds no fault probe. The tests of the exception vectors
  trigger a breakpoint, an FP/SIMD trap and a register check in test images
  of their own.
- `physical_counter`, the counter of the physical-entry profile of the Pi 5
  path.
- `stack_registers`, which the backtraces of the fault records use; it comes
  with fault symbolization.
- `irq_mask`, `irq_restore` and `irq_enable`: no code of this change masks or
  unmasks IRQs. They come with the interrupt handling that calls them.
- The re-export of `ExceptionFrame`, which comes with the exception vectors.
