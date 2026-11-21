//! The formats of descriptors: the bits of each kind, the page, block and
//! table descriptors and the fields that the walk reads.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! A leaf holds AP[2:1] in bits 7 and 6, AttrIndx in bits 2 to 4, SH in
//! bits 8 and 9, AF in bit 10, nG in bit 11, PXN in bit 53 and UXN in bit
//! 54; every other bit of a leaf is 0 or a bit of its output address.

use super::Kind;

/// Bits 12 to 47: the output address of a page and the address of the
/// next table of a table descriptor.
pub(super) const ADDRESS_MASK: u64 = 0x0000_ffff_ffff_f000;

/// Bits 1 and 0 of a table or a page descriptor.
pub(super) const TABLE_OR_PAGE: u64 = 0b11;

/// AP[2]: no write at EL1 or EL0.
const READ_ONLY: u64 = 1 << 7;

/// AP[1]: data access at EL0.
const EL0: u64 = 1 << 6;

/// SH `0b11`: inner shareable.
const INNER_SHAREABLE: u64 = 0b11 << 8;

/// AttrIndx 1: Normal memory. AttrIndx 0, Device-nGnRnE, has no bit.
const NORMAL: u64 = 1 << 2;

/// AF: the access flag.
const ACCESS: u64 = 1 << 10;

/// nG: tagged with the ASID.
const NOT_GLOBAL: u64 = 1 << 11;

/// PXN: no execution at EL1.
const PXN: u64 = 1 << 53;

/// UXN: no execution at EL0.
const UXN: u64 = 1 << 54;

impl Kind {
    /// The attribute bits of a leaf of the kind, the row of the kind table.
    pub(super) fn bits(self) -> u64 {
        match self {
            Kind::ReadExecute => READ_ONLY | INNER_SHAREABLE | NORMAL | ACCESS | UXN,
            Kind::ReadOnly => READ_ONLY | INNER_SHAREABLE | NORMAL | ACCESS | PXN | UXN,
            Kind::ReadWrite => INNER_SHAREABLE | NORMAL | ACCESS | PXN | UXN,
            Kind::KernelPrivateReadWrite => {
                INNER_SHAREABLE | NORMAL | ACCESS | NOT_GLOBAL | PXN | UXN
            }
            Kind::Device => ACCESS | PXN | UXN,
            Kind::UserReadExecute => {
                READ_ONLY | EL0 | INNER_SHAREABLE | NORMAL | ACCESS | NOT_GLOBAL | PXN
            }
            Kind::UserReadOnly => {
                READ_ONLY | EL0 | INNER_SHAREABLE | NORMAL | ACCESS | NOT_GLOBAL | PXN | UXN
            }
            Kind::UserReadWrite => EL0 | INNER_SHAREABLE | NORMAL | ACCESS | NOT_GLOBAL | PXN | UXN,
            Kind::UserDevice => EL0 | ACCESS | NOT_GLOBAL | PXN | UXN,
        }
    }
}
