//! The write entries of a set that return a write plan of at most seven
//! steps: `map_page`, `map_block` and `unmap_page`, and `reset`.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! Each entry checks every rule before it writes, so that a failure changes
//! nothing. The write phase records the new tables, the tables of the
//! lowest free indices, and returns the plan: it writes each new table
//! before the store of the table descriptor that makes it reachable, with a
//! `Fence` before that store, and ends with `Sync`; the plan of
//! `unmap_page` clears the leaf and invalidates its translation.

use super::encoding::{
    BLOCK, block_descriptor, is_valid, output_address, table_descriptor, type_bits,
};
use super::walk::{check_entry, check_physical, index1, index2, index3, table_address};
use super::{
    BLOCK_SIZE, Kind, MAX_PLAN_STEPS, PAGE_SIZE, Step, TableError, Tables, WritePlan, descriptor,
};

/// The step after the last of a plan, which is not part of it.
const PAD: Step = Step::Sync;

/// The plan of the first `len` of `steps`.
fn plan(steps: [Step; MAX_PLAN_STEPS], len: usize) -> WritePlan {
    WritePlan {
        zero_tables: 0,
        steps,
        len,
    }
}

/// The plan of the two steps `first` and `last`.
fn two_steps(first: Step, last: Step) -> WritePlan {
    plan([first, last, PAD, PAD, PAD, PAD, PAD], 2)
}

impl<const N: usize, const UPPER: bool> Tables<N, UPPER> {
    /// The tables of the pool that are not in use.
    pub(super) fn free_tables(&self) -> usize {
        if self.used < N { N - self.used } else { 0 }
    }

    /// Empties the set: the root alone stays in use, and the plan zeroes
    /// every table in use, in the order of their indices. It checks
    /// nothing: no CPU may hold the root and no TLB a translation of it.
    // Called by the modules creation and lifecycle of the core, which are
    // planned.
    #[allow(dead_code)]
    pub(crate) fn reset(&mut self) -> WritePlan {
        let zero_tables = self.in_use();
        self.used = 1;
        WritePlan {
            zero_tables,
            steps: [PAD; MAX_PLAN_STEPS],
            len: 0,
        }
    }

    /// Maps the page `va` of the region to the physical page `pa` with
    /// `kind`, in the set whose pool is at `base`, of physical width
    /// `bits`.
    // Called by the modules vm and creation of the core, which are planned;
    // on a layout of one page, `kernel_map` gives the plan of this function.
    #[allow(dead_code)]
    pub(crate) fn map_page(
        &mut self,
        va: u64,
        pa: u64,
        kind: Kind,
        base: u64,
        bits: u8,
    ) -> Result<WritePlan, TableError> {
        check_entry(UPPER, N, va, PAGE_SIZE, base, bits)?;
        check_physical(pa, PAGE_SIZE, bits)?;
        let page = descriptor(kind, pa);
        match self.walk_level2(va, base)? {
            Some((table, entry)) => self.map_below(table, entry, va, page, base),
            None => {
                if self.free_tables() < 2 {
                    return Err(TableError::OutOfTables);
                }
                let level2 = self.used;
                let level3 = self.used + 1;
                self.used += 2;
                Ok(plan(
                    [
                        Step::Zero(level3),
                        Step::Store(level3, index3(va), page),
                        Step::Zero(level2),
                        Step::Store(
                            level2,
                            index2(va),
                            table_descriptor(table_address(base, level3)),
                        ),
                        Step::Fence,
                        Step::Store(0, index1(va), table_descriptor(table_address(base, level2))),
                        Step::Sync,
                    ],
                    7,
                ))
            }
        }
    }

    /// The part of `map_page` below the level 2 table `table`, whose entry
    /// for `va` is `entry`.
    fn map_below(
        &mut self,
        table: usize,
        entry: u64,
        va: u64,
        page: u64,
        base: u64,
    ) -> Result<WritePlan, TableError> {
        if !is_valid(entry) {
            if self.free_tables() < 1 {
                return Err(TableError::OutOfTables);
            }
            let level3 = self.used;
            self.used += 1;
            return Ok(plan(
                [
                    Step::Zero(level3),
                    Step::Store(level3, index3(va), page),
                    Step::Fence,
                    Step::Store(
                        table,
                        index2(va),
                        table_descriptor(table_address(base, level3)),
                    ),
                    Step::Sync,
                    PAD,
                    PAD,
                ],
                5,
            ));
        }
        if type_bits(entry) == BLOCK {
            return Err(TableError::AlreadyMapped);
        }
        let level3 = match self.child(entry, base) {
            Some(level3) => level3,
            None => return Err(TableError::TableBacking),
        };
        if is_valid(self.pool[level3][index3(va)]) {
            return Err(TableError::AlreadyMapped);
        }
        Ok(two_steps(Step::Store(level3, index3(va), page), Step::Sync))
    }

    /// Maps the block slot `va` to the physical block `pa` as `ReadWrite`
    /// with one level 2 descriptor. It never replaces a level 3 table by a
    /// block.
    // No module of the core calls it yet; on usable ranges of one block,
    // `direct_map` gives the plan of this function.
    #[allow(dead_code)]
    pub(crate) fn map_block(
        &mut self,
        va: u64,
        pa: u64,
        base: u64,
        bits: u8,
    ) -> Result<WritePlan, TableError> {
        check_entry(UPPER, N, va, BLOCK_SIZE, base, bits)?;
        check_physical(pa, BLOCK_SIZE, bits)?;
        let block = block_descriptor(pa);
        let (table, entry) = match self.walk_level2(va, base)? {
            Some(found) => found,
            None => {
                if self.free_tables() < 1 {
                    return Err(TableError::OutOfTables);
                }
                let level2 = self.used;
                self.used += 1;
                return Ok(plan(
                    [
                        Step::Zero(level2),
                        Step::Store(level2, index2(va), block),
                        Step::Fence,
                        Step::Store(0, index1(va), table_descriptor(table_address(base, level2))),
                        Step::Sync,
                        PAD,
                        PAD,
                    ],
                    5,
                ));
            }
        };
        if is_valid(entry) && type_bits(entry) != BLOCK {
            if let None = self.child(entry, base) {
                return Err(TableError::TableBacking);
            }
        }
        if is_valid(entry) {
            return Err(TableError::AlreadyMapped);
        }
        Ok(two_steps(Step::Store(table, index2(va), block), Step::Sync))
    }

    /// Removes the page leaf of `va` and gives its physical page; the
    /// tables under the leaf stay in use. The plan clears the leaf and
    /// invalidates the translation of `va`.
    // Called by the module vm of the core, which is planned.
    #[allow(dead_code)]
    pub(crate) fn unmap_page(
        &mut self,
        va: u64,
        base: u64,
        bits: u8,
    ) -> Result<(WritePlan, u64), TableError> {
        check_entry(UPPER, N, va, PAGE_SIZE, base, bits)?;
        let (level3, leaf) = self.page_leaf(va, base)?;
        let plan = two_steps(Step::Store(level3, index3(va), 0), Step::Invalidate(va));
        Ok((plan, output_address(leaf)))
    }
}
