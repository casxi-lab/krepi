//! The copy of the kernel tables into the tables of a process: the checks
//! of `clone_kernel_from`, with the walk of the source, and the steps of its
//! plan.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The walk of the source starts at its root, which it has reached, and
//! takes the entries in the order of their indices, each table under its
//! entry before the next entry. It records the level of each table that it
//! reaches, so that the plan stores the leaves of a level 3 table as they
//! are and points every table descriptor at the target's table of the same
//! index.

use super::encoding::{ADDRESS_MASK, TABLE_OR_PAGE, is_valid, output_address, table_descriptor};
use super::walk::{child_index, pool_fits, table_address, width_ok};
use super::{ClonePlan, ENTRIES, Kind, PAGE_SIZE, Step, TableError, Tables, descriptor};

/// The level of a table that the walk has not reached.
const UNREACHED: u8 = 0;

/// The level of the root.
const ROOT: u8 = 1;

/// The level of a table that a root entry reaches.
const LEVEL2: u8 = 2;

/// The level of a table of leaves.
const LEAVES: u8 = 3;

/// The first checks of a pool of `count` tables at `base`, without a
/// virtual address: `Alignment`, `AddressWidth` and `TableBacking`.
fn check_pool(count: usize, base: u64, bits: u8) -> Result<(), TableError> {
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

/// Whether `d` is the page descriptor at `address` of `ReadExecute`,
/// `ReadOnly`, `ReadWrite` or `Device`.
// The chain is the value of a function of its own: bound to a local, a
// chain of `||` that ends in a comparison does not type-check in Lean.
fn copy_kind(d: u64, address: u64) -> bool {
    d == descriptor(Kind::ReadExecute, address)
        || d == descriptor(Kind::ReadOnly, address)
        || d == descriptor(Kind::ReadWrite, address)
        || d == descriptor(Kind::Device, address)
}

/// Whether the copy takes the leaf `d`: the page descriptor of
/// `ReadExecute`, `ReadOnly`, `ReadWrite` or `Device` with an output
/// address below `2^bits`.
fn copyable(d: u64, bits: u8) -> bool {
    let address = output_address(d);
    if !copy_kind(d, address) {
        return false;
    }
    address < 1u64 << bits
}

/// The table that the valid entry `entry` of a table of level 1 or 2 of
/// the source reaches: `InvalidDescriptor` when it is not a table
/// descriptor without an attribute bit, `TableBacking` when it points at a
/// table that is not in use or that the walk has reached.
fn reach<const N: usize>(
    entry: u64,
    base: u64,
    used: usize,
    levels: &[u8; N],
) -> Result<usize, TableError> {
    if entry & !ADDRESS_MASK != TABLE_OR_PAGE {
        return Err(TableError::InvalidDescriptor);
    }
    let table = match child_index(entry, base, used) {
        Some(table) => table,
        None => return Err(TableError::TableBacking),
    };
    if levels[table] != UNREACHED {
        return Err(TableError::TableBacking);
    }
    Ok(table)
}

/// The leaves of a table of level 3 of the source, in the order of their
/// indices: `InvalidDescriptor` for a valid one that the copy does not take.
fn check_leaves(table: &[u64; ENTRIES], bits: u8) -> Result<(), TableError> {
    let mut index = 0;
    while index < ENTRIES {
        if is_valid(table[index]) && !copyable(table[index], bits) {
            return Err(TableError::InvalidDescriptor);
        }
        index += 1;
    }
    Ok(())
}

/// The walk of the level 2 table `table` of the source, whose `used`
/// tables are at `base`.
fn walk_level2<const N: usize>(
    pool: &[[u64; ENTRIES]; N],
    used: usize,
    base: u64,
    bits: u8,
    table: usize,
    levels: &mut [u8; N],
) -> Result<(), TableError> {
    let mut index = 0;
    while index < ENTRIES {
        let entry = pool[table][index];
        if is_valid(entry) {
            let leaves = reach(entry, base, used, levels)?;
            levels[leaves] = LEAVES;
            check_leaves(&pool[leaves], bits)?;
        }
        index += 1;
    }
    Ok(())
}

/// The walk of the root of the source, whose `used` tables are at `base`.
fn walk_root<const N: usize>(
    pool: &[[u64; ENTRIES]; N],
    used: usize,
    base: u64,
    bits: u8,
    levels: &mut [u8; N],
) -> Result<(), TableError> {
    let mut index = 0;
    while index < ENTRIES {
        let entry = pool[0][index];
        if is_valid(entry) {
            let table = reach(entry, base, used, levels)?;
            levels[table] = LEVEL2;
            walk_level2(pool, used, base, bits, table, levels)?;
        }
        index += 1;
    }
    Ok(())
}

/// Whether the walk reached every table below `used`.
fn all_reached<const N: usize>(levels: &[u8; N], used: usize) -> bool {
    let mut table = 0;
    while table < used {
        if levels[table] == UNREACHED {
            return false;
        }
        table += 1;
    }
    true
}

/// The first valid entry of the tables below `used` from entry `entry` of
/// table `table` on, in the order of the tables and of their entries, or
/// `(used, 0)` when none is left.
fn next_valid<const N: usize>(
    pool: &[[u64; ENTRIES]; N],
    used: usize,
    mut table: usize,
    mut entry: usize,
) -> (usize, usize) {
    while table < used {
        if entry < ENTRIES {
            if is_valid(pool[table][entry]) {
                return (table, entry);
            }
            entry += 1;
        } else {
            table += 1;
            entry = 0;
        }
    }
    (used, 0)
}

impl<const N: usize, const UPPER: bool> Tables<N, UPPER> {
    /// Fills the set, the target, with a private copy of `source`, another
    /// set of its region and capacity whose pool is at `source_base`; the
    /// target's pool is at `base`, and `bits` is the physical width of both.
    /// It checks, in this order: the pool of the source and then that of
    /// the target; the overlap of the two pools and the record of the
    /// source (`TableBacking`); the walk of the source; and that the walk
    /// reached every table in use of the source (`TableBacking`). The
    /// target takes the record of the source. No CPU may hold the root of
    /// the target and no TLB a translation of it.
    // Called by the modules creation and lifecycle of the core, which are
    // planned.
    #[allow(dead_code)]
    pub(crate) fn clone_kernel_from<'a>(
        &'a mut self,
        source: &'a Self,
        source_base: u64,
        base: u64,
        bits: u8,
    ) -> Result<ClonePlan<'a, N, UPPER>, TableError> {
        check_pool(N, source_base, bits)?;
        check_pool(N, base, bits)?;
        let size = N as u64 * PAGE_SIZE;
        if source_base < base + size && base < source_base + size {
            return Err(TableError::TableBacking);
        }
        if source.used == 0 || source.used > N {
            return Err(TableError::TableBacking);
        }
        let mut levels = [UNREACHED; N];
        levels[0] = ROOT;
        walk_root(&source.pool, source.used, source_base, bits, &mut levels)?;
        if !all_reached(&levels, source.used) {
            return Err(TableError::TableBacking);
        }
        let zero_tables = self.in_use();
        self.used = source.used;
        Ok(ClonePlan {
            source,
            source_base,
            base,
            levels,
            zero_tables,
            zeroed: 0,
            table: 0,
            entry: 0,
            done: false,
        })
    }
}

impl<const N: usize, const UPPER: bool> ClonePlan<'_, N, UPPER> {
    /// The next step of the plan, or none after its `Sync`. The entry that
    /// built the plan checked the source, so no step fails.
    // The iterator implements `next` alone: the provided methods of
    // `Iterator` would reach library functions without a model.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Step> {
        if self.zeroed < self.zero_tables {
            let table = self.zeroed;
            self.zeroed += 1;
            return Some(Step::Zero(table));
        }
        if self.done {
            return None;
        }
        let used = self.source.used;
        let (table, entry) = next_valid(&self.source.pool, used, self.table, self.entry);
        if table >= used {
            self.done = true;
            return Some(Step::Sync);
        }
        self.table = table;
        self.entry = entry + 1;
        let d = self.source.pool[table][entry];
        if self.levels[table] == LEAVES {
            return Some(Step::Store(table, entry, d));
        }
        let index = (output_address(d) - self.source_base) / PAGE_SIZE;
        let address = table_address(self.base, index as usize);
        Some(Step::Store(table, entry, table_descriptor(address)))
    }
}
