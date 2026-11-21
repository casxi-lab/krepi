//! The first checks of an entry on a set, the walk of an address through
//! the three levels, and the entries that write nothing.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The walk reads one entry at each level. A valid root entry is read as a
//! table descriptor, and a valid level 2 entry as a block when its bits 1
//! and 0 are `0b01` and as a table descriptor otherwise; a table descriptor
//! counts only by its address, which must be that of a table in use.

use super::encoding::{BLOCK, TABLE_OR_PAGE, is_valid, output_address, type_bits};
use super::{BLOCK_SIZE, DIRECT_BASE, ENTRIES, PAGE_SIZE, TableError, Tables, VA_LIMIT};

/// The index of `va` at level 1, the root: its bits 30 to 38.
pub(super) fn index1(va: u64) -> usize {
    ((va >> 30) & 511) as usize
}

/// The index of `va` at level 2: its bits 21 to 29.
pub(super) fn index2(va: u64) -> usize {
    ((va >> 21) & 511) as usize
}

/// The index of `va` at level 3: its bits 12 to 20.
pub(super) fn index3(va: u64) -> usize {
    ((va >> 12) & 511) as usize
}

/// The physical address of table `table` of the pool at `base`.
pub(super) fn table_address(base: u64, table: usize) -> u64 {
    base + PAGE_SIZE * table as u64
}

/// Whether `va` lies in the upper region when `upper`, and in the lower
/// region otherwise.
fn in_region(upper: bool, va: u64) -> bool {
    if upper {
        va >= DIRECT_BASE
    } else {
        va < VA_LIMIT
    }
}

/// Whether `bits` is a physical width, 32 to 48.
fn width_ok(bits: u8) -> bool {
    bits >= 32 && bits <= 48
}

/// Whether a pool of `count` tables at `base` holds a table and ends at or
/// below `2^bits`; `bits` is a physical width.
fn pool_fits(count: usize, base: u64, bits: u8) -> bool {
    let limit = 1u64 << bits;
    if count == 0 || count as u64 > limit / PAGE_SIZE {
        return false;
    }
    match base.checked_add(count as u64 * PAGE_SIZE) {
        Some(end) => end <= limit,
        None => false,
    }
}

/// The first checks of a pool of `count` tables at `base`, without a
/// virtual address: `Alignment`, `AddressWidth` and `TableBacking`.
pub(super) fn check_pool(count: usize, base: u64, bits: u8) -> Result<(), TableError> {
    if base % PAGE_SIZE != 0 {
        return Err(TableError::Alignment);
    }
    if !width_ok(bits) {
        return Err(TableError::AddressWidth);
    }
    if !pool_fits(count, base, bits) {
        return Err(TableError::TableBacking);
    }
    Ok(())
}

/// The first checks of an entry on a set of the region `upper` and `count`
/// tables that takes the virtual address `va`, a multiple of `align`, and
/// the pool at `base`: `Alignment`, `AddressWidth` and `TableBacking`, in
/// this order.
pub(super) fn check_entry(
    upper: bool,
    count: usize,
    va: u64,
    align: u64,
    base: u64,
    bits: u8,
) -> Result<(), TableError> {
    if va % align != 0 || base % PAGE_SIZE != 0 {
        return Err(TableError::Alignment);
    }
    if !in_region(upper, va) || !width_ok(bits) {
        return Err(TableError::AddressWidth);
    }
    if !pool_fits(count, base, bits) {
        return Err(TableError::TableBacking);
    }
    Ok(())
}

/// The checks of the physical address `pa` after those of the set: off a
/// multiple of `align`, `Alignment`; at or above `2^bits`, `AddressWidth`.
pub(super) fn check_physical(pa: u64, align: u64, bits: u8) -> Result<(), TableError> {
    if pa % align != 0 {
        return Err(TableError::Alignment);
    }
    if pa >= 1u64 << bits {
        return Err(TableError::AddressWidth);
    }
    Ok(())
}

/// The table below `limit` that the table descriptor `entry` of the pool
/// at `base` points at, or none when its address is that of no such table.
pub(super) fn child_index(entry: u64, base: u64, limit: usize) -> Option<usize> {
    let address = output_address(entry);
    if address < base {
        return None;
    }
    let index = (address - base) / PAGE_SIZE;
    if index < limit as u64 {
        Some(index as usize)
    } else {
        None
    }
}

impl<const N: usize, const UPPER: bool> Tables<N, UPPER> {
    /// The set of the storage `pool`, with the root alone in use. It
    /// checks nothing: the storage must be zero in all its tables.
    pub const fn new(pool: [[u64; ENTRIES]; N]) -> Self {
        Tables { pool, used: 1 }
    }

    /// The number of tables in use.
    // Called by the modules vm and creation of the core, which are planned.
    #[allow(dead_code)]
    pub(crate) fn used(&self) -> usize {
        self.used
    }

    /// The tables that a walk may reach: those below the record and the
    /// capacity.
    pub(super) fn in_use(&self) -> usize {
        if self.used < N { self.used } else { N }
    }

    /// The table in use that the table descriptor `entry` of the pool at
    /// `base` points at, or none when its address is that of no table in
    /// use.
    pub(super) fn child(&self, entry: u64, base: u64) -> Option<usize> {
        child_index(entry, base, self.in_use())
    }

    /// The level 2 table of `va` with its level 2 entry, or none when the
    /// root entry is invalid; `TableBacking` when the root entry points at
    /// no table in use.
    pub(super) fn walk_level2(
        &self,
        va: u64,
        base: u64,
    ) -> Result<Option<(usize, u64)>, TableError> {
        let root = self.pool[0][index1(va)];
        if !is_valid(root) {
            return Ok(None);
        }
        match self.child(root, base) {
            Some(table) => Ok(Some((table, self.pool[table][index2(va)]))),
            None => Err(TableError::TableBacking),
        }
    }

    /// The level 3 table and the page descriptor of `va`: `TableBacking`
    /// for a valid level 2 entry, other than a block, that points at no
    /// table in use; `NotMapped` without a page leaf, which includes a page
    /// of a block.
    pub(super) fn page_leaf(&self, va: u64, base: u64) -> Result<(usize, u64), TableError> {
        let entry = match self.walk_level2(va, base)? {
            Some((_, entry)) => entry,
            None => return Err(TableError::NotMapped),
        };
        if !is_valid(entry) || type_bits(entry) == BLOCK {
            return Err(TableError::NotMapped);
        }
        let leaf = match self.child(entry, base) {
            Some(leaf) => leaf,
            None => return Err(TableError::TableBacking),
        };
        let d = self.pool[leaf][index3(va)];
        if type_bits(d) == TABLE_OR_PAGE {
            Ok((leaf, d))
        } else {
            Err(TableError::NotMapped)
        }
    }

    /// The page descriptor of `va` in the set whose pool is at `base`, of
    /// physical width `bits`.
    // Called by the modules vm and creation of the core, which are planned.
    #[allow(dead_code)]
    pub(crate) fn lookup_page(&self, va: u64, base: u64, bits: u8) -> Result<u64, TableError> {
        check_entry(UPPER, N, va, PAGE_SIZE, base, bits)?;
        let (_, d) = self.page_leaf(va, base)?;
        Ok(d)
    }

    /// The block descriptor at the block slot `va`; `NotMapped` when its
    /// level 2 entry is not a block. It reads the root entry and the level 2
    /// entry only.
    // Called by the modules vm and creation of the core, which are planned.
    #[allow(dead_code)]
    pub(crate) fn lookup_block(&self, va: u64, base: u64, bits: u8) -> Result<u64, TableError> {
        check_entry(UPPER, N, va, BLOCK_SIZE, base, bits)?;
        let entry = match self.walk_level2(va, base)? {
            Some((_, entry)) => entry,
            None => return Err(TableError::NotMapped),
        };
        if type_bits(entry) == BLOCK {
            return Ok(entry);
        }
        if is_valid(entry) {
            if let None = self.child(entry, base) {
                return Err(TableError::TableBacking);
            }
        }
        Err(TableError::NotMapped)
    }
}
