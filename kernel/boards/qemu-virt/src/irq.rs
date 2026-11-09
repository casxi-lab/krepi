//! The interrupts of QEMU virt: the wiring of its GICv2 and of the virtual
//! timer of the CPU, which interrupts as the private peripheral interrupt
//! 27.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The drivers are the GICv2 and the timer of `krepi-arch`; this module
//! gives them the addresses, the interrupt ID, the priority and the period
//! of QEMU virt. [`init`] runs with IRQs masked and leaves them masked; the
//! code that takes the interrupt unmasks them, and its exception dispatch
//! calls [`handle`]. One CPU uses the module. It is compiled only for the
//! bare-metal target.

use crate::{GIC_CPU, GIC_DISTRIBUTOR, TIMER_INTID, TIMER_PRIORITY, TIMER_RATE};
use krepi_arch::gic::{self, Gic};
use krepi_arch::{cpu, timer};

/// The GICv2 of QEMU virt.
const GIC: Gic = Gic {
    distributor: GIC_DISTRIBUTOR,
    cpu: GIC_CPU,
};

/// The interrupt that [`handle`] took.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Interrupt {
    /// The timer interrupt, which the handler ended and re-armed.
    Timer,
    /// A special interrupt ID, 1020 to 1023: no interrupt could be taken,
    /// and none was ended.
    Spurious,
    /// Another interrupt ID, which the handler disabled and ended.
    Unexpected(u32),
}

/// The period of the timer interrupt in ticks of the counter: its frequency
/// divided by [`TIMER_RATE`], rounded up, and at least 1.
fn period() -> u64 {
    cpu::counter_frequency().div_ceil(TIMER_RATE).max(1)
}

/// Sets the interrupts up with IRQs left masked: stops the virtual timer,
/// sets the GIC up with only the timer interrupt enabled, level-sensitive
/// at [`TIMER_PRIORITY`], and arms the timer for one period from now.
pub fn init() {
    timer::stop_virtual();
    GIC.init();
    GIC.enable_ppi(TIMER_INTID, TIMER_PRIORITY);
    timer::arm_virtual(cpu::virtual_counter().wrapping_add(period()));
    gic::barrier();
}

/// Acknowledges the pending interrupt and ends it, from the dispatch of an
/// IRQ with every exception masked. The timer is re-armed one period after
/// now before the end of interrupt, so that its level drops first; another
/// interrupt is disabled before its end, so that it does not come back; a
/// special ID is not ended.
pub fn handle() -> Interrupt {
    let acknowledged = GIC.acknowledge();
    let intid = gic::interrupt_id(acknowledged);
    if intid >= gic::SPECIAL {
        return Interrupt::Spurious;
    }
    let interrupt = if intid == TIMER_INTID {
        timer::arm_virtual(cpu::virtual_counter().wrapping_add(period()));
        Interrupt::Timer
    } else {
        GIC.disable(intid);
        Interrupt::Unexpected(intid)
    };
    gic::barrier();
    GIC.end(acknowledged);
    gic::barrier();
    interrupt
}
