//! The GICv2 interrupt controller: its distributor and the CPU interface of
//! the executing CPU, at the base addresses that the board gives.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The functions configure one controller for the CPU that executes them,
//! acknowledge its interrupts and end them. They are written for one CPU,
//! which sets the controller up with IRQs masked and acknowledges and ends
//! its interrupts in the dispatch of an exception, with every exception
//! masked, so no two accesses overlap. The registers are reached as Device
//! memory while the MMU is off, and a later MMU setup must keep them mapped
//! with Device attributes. The caller of [`Gic::new`] vouches for the
//! addresses, the memory that reaches them and that one CPU uses them. The
//! module is compiled only for the bare-metal target.
//!
//! [`Gic::init`] puts the private interrupts in group 0 and enables group 0,
//! which a GICv2 without the Security Extensions, as QEMU virt has with
//! `secure=off`, signals as IRQs. On a GICv2 with them, where EL1 runs
//! Non-secure, `GICD_IGROUPR0` ignores the write and bit 0 of the two
//! control registers enables group 1, so the board of such a GIC must check
//! that its firmware has put the interrupts in group 1.

use core::arch::asm;
use core::ptr;

/// The distributor control register `GICD_CTLR`.
const GICD_CTLR: usize = 0x000;
/// The first interrupt group register `GICD_IGROUPR0`.
const GICD_IGROUPR: usize = 0x080;
/// The first interrupt set-enable register `GICD_ISENABLER0`.
const GICD_ISENABLER: usize = 0x100;
/// The first interrupt clear-enable register `GICD_ICENABLER0`.
const GICD_ICENABLER: usize = 0x180;
/// The first interrupt clear-pending register `GICD_ICPENDR0`.
const GICD_ICPENDR: usize = 0x280;
/// The first interrupt priority register `GICD_IPRIORITYR0`.
const GICD_IPRIORITYR: usize = 0x400;
/// The first interrupt configuration register `GICD_ICFGR0`.
const GICD_ICFGR: usize = 0xc00;
/// The CPU interface control register `GICC_CTLR`.
const GICC_CTLR: usize = 0x00;
/// The interrupt priority mask register `GICC_PMR`.
const GICC_PMR: usize = 0x04;
/// The binary point register `GICC_BPR`.
const GICC_BPR: usize = 0x08;
/// The interrupt acknowledge register `GICC_IAR`.
const GICC_IAR: usize = 0x0c;
/// The end of interrupt register `GICC_EOIR`.
const GICC_EOIR: usize = 0x10;

/// The first of the special interrupt IDs, 1020 to 1023, which an
/// acknowledge returns when no interrupt can be taken and which take no end
/// of interrupt.
pub const SPECIAL: u32 = 1020;

/// The interrupt ID in a value of `GICC_IAR`, bits 0 to 9.
pub const fn interrupt_id(iar: u32) -> u32 {
    iar & 0x3ff
}

/// A GICv2: the base addresses of its distributor and of its CPU interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gic {
    /// The base address of the 4 KiB register frame of the distributor.
    distributor: usize,
    /// The base address of the register frame of the CPU interface.
    cpu: usize,
}

impl Gic {
    /// The GICv2 whose distributor and CPU interface have their register
    /// frames at `distributor` and `cpu`.
    ///
    /// # Safety
    ///
    /// `distributor` and `cpu` must be the base addresses of the register
    /// frames of the distributor and of the CPU interface of a GICv2, which
    /// the executing CPU reaches as Device memory: with the MMU off, or
    /// through a mapping with Device attributes. Only one CPU may use the
    /// controller through the value and its copies, and only with IRQs
    /// masked, so that no two of its accesses overlap.
    pub const unsafe fn new(distributor: usize, cpu: usize) -> Gic {
        Gic { distributor, cpu }
    }

    /// Sets the controller up for the executing CPU with none of its PPIs
    /// enabled: disables the distributor and the CPU interface, disables the
    /// PPIs of the executing CPU, and its SGIs where the GIC lets them be
    /// disabled, puts them in group 0, lets every priority through the CPU
    /// interface with the binary point 0, and enables the distributor and
    /// the CPU interface again, the CPU interface with an end of interrupt
    /// that drops the priority and deactivates together. It leaves the SPIs
    /// and the active state of every interrupt as it finds them, disabled
    /// and inactive after a reset. The binary point 0 lets interrupts of a
    /// higher priority preempt; they do not nest because the dispatch runs
    /// with IRQs masked.
    pub fn init(&self) {
        write(self.distributor + GICD_CTLR, 0);
        write(self.cpu + GICC_CTLR, 0);
        write(self.distributor + GICD_ICENABLER, u32::MAX);
        write(self.distributor + GICD_IGROUPR, 0);
        write(self.cpu + GICC_PMR, 0xff);
        write(self.cpu + GICC_BPR, 0);
        write(self.distributor + GICD_CTLR, 1);
        write(self.cpu + GICC_CTLR, 1);
    }

    /// Enables the private peripheral interrupt `intid`, 16 to 31, of the
    /// executing CPU, level-sensitive with `priority`, after clearing a
    /// pending state that it may have kept.
    ///
    /// # Panics
    ///
    /// Panics when `intid` is not a PPI, before any access.
    pub fn enable_ppi(&self, intid: u32, priority: u8) {
        assert!((16..32).contains(&intid), "a PPI is 16 to 31");
        let bit = 1 << (intid % 32);
        write(self.distributor + GICD_ICPENDR, bit);
        let index = intid as usize;
        let priority_word = self.distributor + GICD_IPRIORITYR + (index & !3);
        let shift = (index % 4) * 8;
        let priorities = read(priority_word) & !(0xff << shift);
        write(priority_word, priorities | (u32::from(priority) << shift));
        let config_word = self.distributor + GICD_ICFGR + (index / 16) * 4;
        let edge = 2 << ((index % 16) * 2);
        write(config_word, read(config_word) & !edge);
        write(self.distributor + GICD_ISENABLER, bit);
    }

    /// Acknowledges the highest-priority pending interrupt: the value of
    /// `GICC_IAR`, whose [`interrupt_id`] is that interrupt or a special ID
    /// from [`SPECIAL`] on.
    pub fn acknowledge(&self) -> u32 {
        read(self.cpu + GICC_IAR)
    }

    /// Ends the interrupt whose acknowledge returned `iar`, with the whole
    /// value, so that the CPU ID of an SGI is kept.
    pub fn end(&self, iar: u32) {
        write(self.cpu + GICC_EOIR, iar);
    }

    /// Disables the interrupt `intid`.
    ///
    /// # Panics
    ///
    /// Panics when `intid` is not below [`SPECIAL`], before any access.
    pub fn disable(&self, intid: u32) {
        assert!(intid < SPECIAL, "an interrupt ID is below 1020");
        let word = self.distributor + GICD_ICENABLER + (intid as usize / 32) * 4;
        write(word, 1 << (intid % 32));
    }
}

/// Completes the memory accesses before it, the writes to the controller
/// and to the timer among them, and synchronizes the context: `DSB SY` and
/// `ISB`.
pub fn barrier() {
    // SAFETY: the barriers touch no memory, the stack or the flags and are
    // available at EL1; the asm is not `nomem`, so that the compiler keeps
    // the accesses before it on their side.
    unsafe { asm!("dsb sy", "isb", options(nostack, preserves_flags)) };
}

fn read(address: usize) -> u32 {
    // SAFETY: `address` is a 4-byte aligned register in the register frames
    // of a GICv2, at an offset below 4 KiB from a base address that the
    // caller of `Gic::new` vouched for, together with the Device memory
    // that reaches it. As `Gic::new` requires, one CPU accesses the
    // controller, with IRQs masked, so the read races with no other access.
    unsafe { ptr::read_volatile(address as *const u32) }
}

fn write(address: usize, value: u32) {
    // SAFETY: the same aligned, mapped and exclusively used register range as
    // in `read`.
    unsafe { ptr::write_volatile(address as *mut u32, value) }
}
