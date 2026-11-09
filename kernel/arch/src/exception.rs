//! The exception vectors of EL1 and the frame that their entries save: the
//! vector table `__exception_vectors` of `exception.S`, which the cold
//! entry installs in `VBAR_EL1`, the layout of [`Frame`] and the class of an
//! exception.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! Each of the 16 entries of the table moves the stack pointer `SP_EL1` 304
//! bytes down, saves `x0` and `x1` there, puts its number into `x0` and
//! branches to one save path. That path saves `x2` to `x30`, the stack
//! pointer above the frame, `ELR_EL1`, `SPSR_EL1`, `ESR_EL1`, `FAR_EL1` and
//! the vector number into the [`Frame`], clears its reserved word, masks
//! every exception and calls `exception_dispatch(&mut Frame)`, which each
//! image defines as an unmangled `extern "C"` function. When the dispatch
//! returns, the path masks every exception again, whatever the dispatch
//! unmasked. For one of the four entries of the current exception level with
//! `SP_EL1`, vectors 4 to 7, it then loads `ELR_EL1` and `SPSR_EL1` from the
//! frame, clears `x0` to `x30`, loads them from the frame, releases the frame
//! and returns with `ERET`. A dispatch that returns from any other entry ends
//! in a halt with every exception masked. The path tells the entries apart
//! by the vector number that it keeps in `x19` across the call, not by the
//! frame, so a dispatch that changes [`Frame::vector`] cannot make a halting
//! entry return.
//!
//! The entries need a valid `SP_EL1` with 304 bytes below it. They save no
//! FP/SIMD state: the kernel is built without it, and the cold entry makes
//! FP/SIMD instructions trap. The entries of the current exception level
//! with `SP_EL0`, vectors 0 to 3, and of a lower one, vectors 8 to 15, use
//! the same frame; for them the saved stack pointer is the address above
//! the frame on `SP_EL1`, not the interrupted `SP_EL0`.
//!
//! The vector table means something only on the bare-metal target, so it is
//! compiled only there; the frame and the classes are plain code that the
//! host tests run.

use core::mem::{offset_of, size_of};

/// The registers of an exception, as the vector entries save them on
/// `SP_EL1`: 304 bytes, 16-byte aligned. `exception.S` writes and reads it
/// at the offsets that the constant assertions below fix.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Frame {
    /// The general registers `x0` to `x30` at the exception, by number.
    pub x: [u64; 31],
    /// The stack pointer above the frame: for the entries of the current
    /// exception level with `SP_EL1`, the interrupted stack pointer.
    pub sp: u64,
    /// `ELR_EL1`, the return address; the return path loads it back.
    pub elr: u64,
    /// `SPSR_EL1`, the interrupted `PSTATE`; the return path loads it back.
    pub spsr: u64,
    /// `ESR_EL1`, the syndrome of the exception.
    pub esr: u64,
    /// `FAR_EL1`, the fault address, which the architecture defines only
    /// for some exceptions.
    pub far: u64,
    /// The number of the vector entry, 0 to 15.
    pub vector: u64,
    /// Zero.
    pub reserved: u64,
}

/// The bytes of a [`Frame`].
pub const FRAME_BYTES: usize = 304;

const _: () = assert!(size_of::<Frame>() == FRAME_BYTES);
const _: () = assert!(FRAME_BYTES.is_multiple_of(16));
const _: () = assert!(offset_of!(Frame, x) == 0);
const _: () = assert!(offset_of!(Frame, sp) == 248);
const _: () = assert!(offset_of!(Frame, elr) == 256);
const _: () = assert!(offset_of!(Frame, spsr) == 264);
const _: () = assert!(offset_of!(Frame, esr) == 272);
const _: () = assert!(offset_of!(Frame, far) == 280);
const _: () = assert!(offset_of!(Frame, vector) == 288);
const _: () = assert!(offset_of!(Frame, reserved) == 296);

impl Frame {
    /// A frame of zeros.
    pub const ZERO: Frame = Frame {
        x: [0; 31],
        sp: 0,
        elr: 0,
        spsr: 0,
        esr: 0,
        far: 0,
        vector: 0,
        reserved: 0,
    };
}

/// The vector of a synchronous exception at the current exception level
/// with `SP_EL1`.
pub const SYNC: u64 = 4;
/// The vector of an IRQ at the current exception level with `SP_EL1`.
pub const IRQ: u64 = 5;

/// The exception class of a `BRK` instruction in AArch64 state.
pub const EC_BRK: u64 = 0x3c;
/// The exception class of an FP/SIMD access that `CPACR_EL1.FPEN` traps.
pub const EC_FP: u64 = 0x07;

/// The exception class, `ESR_EL1.EC`, bits 26 to 31 of `esr`.
pub const fn exception_class(esr: u64) -> u64 {
    (esr >> 26) & 0x3f
}

/// The class of an exception, which its record names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// A `BRK` instruction at EL1.
    Brk,
    /// An FP/SIMD instruction at EL1 that `CPACR_EL1.FPEN` traps.
    Fp,
    /// Any other synchronous exception.
    Sync,
    /// An IRQ.
    Irq,
    /// An FIQ.
    Fiq,
    /// An SError, physical or virtual.
    Serror,
}

impl Class {
    /// The class of the exception that entered `vector` with the syndrome
    /// `esr`. The kind of the entry, the vector number modulo 4, gives
    /// synchronous, IRQ, FIQ or SError; a synchronous exception of vector 4
    /// is [`Class::Brk`] or [`Class::Fp`] by its exception class. A
    /// synchronous exception of any other vector is [`Class::Sync`],
    /// whatever its syndrome.
    pub const fn of(vector: u64, esr: u64) -> Class {
        match vector % 4 {
            0 if vector == SYNC => match exception_class(esr) {
                EC_BRK => Class::Brk,
                EC_FP => Class::Fp,
                _ => Class::Sync,
            },
            0 => Class::Sync,
            1 => Class::Irq,
            2 => Class::Fiq,
            _ => Class::Serror,
        }
    }

    /// The name that the record writes: `brk`, `fp`, `sync`, `irq`, `fiq`
    /// or `serror`.
    pub const fn name(self) -> &'static str {
        match self {
            Class::Brk => "brk",
            Class::Fp => "fp",
            Class::Sync => "sync",
            Class::Irq => "irq",
            Class::Fiq => "fiq",
            Class::Serror => "serror",
        }
    }
}

/// The vector table, `__exception_vectors`, in the section `.text.vectors`,
/// which the link script of each image keeps.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod vectors {
    core::arch::global_asm!(include_str!("exception.S"));
}

#[cfg(test)]
mod tests;
