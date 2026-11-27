//! The machinery of the two maps of the boot wiring, `kernel_map` and
//! `direct_map`: the place of a leaf in a set, the checks of the leaves with
//! the count of the new tables, and the cursor that gives the steps of a map
//! one at a time in the order of its plan.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! A leaf maps its physical address `pa` at `pa` in the lower region and at
//! `DIRECT_BASE | pa` in the upper. Every leaf of a map that passed its
//! checks lies below `2^39`, where both addresses have the table indices of
//! `pa`, so the module walks and indexes the set by `pa`. A new table is
//! the one of the lowest free index, taken in the order in which the leaves
//! in address order first need it: the level 2 table of a 1 GiB slot whose
//! root entry is invalid at its first leaf, and the level 3 table of a
//! 2 MiB slot of pages whose level 2 entry is invalid, or that lies under a
//! new level 2 table, at its first page.
//!
//! The cursor holds no list of leaves. Each step asks the input of its map
//! for the first leaf at or above an address and below a limit, and the
//! cursor keeps the address and the tables that the plan has reached. Under
//! a new level 2 table the plan writes the new level 3 tables before the
//! entries of the level 2 table, so the cursor goes through the 1 GiB slot
//! twice: its pages first, then the first leaf of each 2 MiB slot.

pub(super) mod direct;
pub(super) mod layout;
#[cfg(test)]
pub(super) mod tests;

use super::encoding::{BLOCK, is_valid, table_descriptor, type_bits};
use super::walk::{index1, index2, index3, table_address};
use super::{BLOCK_SIZE, PAGE_SIZE, Step, TableError, Tables};

/// A 1 GiB slot, the span of a root entry.
const GIB_SIZE: u64 = 1 << 30;

/// The slot of no leaf: no slot starts at this address.
const NO_SLOT: u64 = u64::MAX;

/// The limit of a search that only the end of the map bounds.
const NO_LIMIT: u64 = u64::MAX;

/// A leaf of a map: its physical address, its descriptor, and whether it is
/// a block, at level 2, or a page, at level 3.
#[derive(Clone, Copy)]
pub(super) struct Leaf {
    pa: u64,
    desc: u64,
    block: bool,
}

/// Where the walk of the set before a map puts one of its leaves.
enum LeafPlace {
    /// The root entry is invalid: the leaf needs a new level 2 table.
    Root,
    /// The level 2 entry, in table `t2` of the set, is invalid.
    Level2(usize),
    /// The level 3 entry of the page, in table `t3` of the set under table
    /// `t2`, is invalid.
    Level3(usize, usize),
}

impl<const N: usize, const UPPER: bool> Tables<N, UPPER> {
    /// The place of the leaf at `pa`, a block when `block`, in the set at
    /// `base`, with the rules of `map_page` and `map_block`: `TableBacking`
    /// for a valid root entry, or a valid level 2 entry other than a block,
    /// that points at no table in use; `AlreadyMapped` for a valid level 2
    /// entry where a block goes, and a block or a valid level 3 entry where
    /// a page goes.
    fn place(&self, base: u64, pa: u64, block: bool) -> Result<LeafPlace, TableError> {
        let (table, entry) = match self.walk_level2(pa, base)? {
            Some(found) => found,
            None => return Ok(LeafPlace::Root),
        };
        if !is_valid(entry) {
            return Ok(LeafPlace::Level2(table));
        }
        if type_bits(entry) == BLOCK {
            return Err(TableError::AlreadyMapped);
        }
        let child = match self.child(entry, base) {
            Some(child) => child,
            None => return Err(TableError::TableBacking),
        };
        if block || is_valid(self.pool[child][index3(pa)]) {
            return Err(TableError::AlreadyMapped);
        }
        Ok(LeafPlace::Level3(table, child))
    }
}

/// The checks of a map so far: the end of the ranges before the current
/// one, and the new tables of the leaves checked, as their number with the
/// 1 GiB slot of the latest new level 2 table and the 2 MiB slot of the
/// latest new level 3 table. The number starts from 0 whatever the record
/// of the set, so that it stays within `usize` on any record.
pub(super) struct MapCheck {
    reach: u64,
    new_tables: usize,
    gib: u64,
    slot: u64,
}

impl MapCheck {
    /// The checks before the first range, with no new table.
    fn new() -> MapCheck {
        MapCheck {
            reach: 0,
            new_tables: 0,
            gib: NO_SLOT,
            slot: NO_SLOT,
        }
    }

    /// Records a range that passed its checks and ends at `end`.
    fn passed(&mut self, end: u64) {
        if end > self.reach {
            self.reach = end;
        }
    }
}

/// The checks of the leaf at `pa`, a block when `block`, after the leaves
/// before it: its walk (`TableBacking`, `AlreadyMapped`), then
/// `AlreadyMapped` when an earlier range holds it or `guard` says that it
/// holds a guard address; then the count of the new tables that it needs.
fn check_leaf<const N: usize, const UPPER: bool>(
    set: &Tables<N, UPPER>,
    base: u64,
    check: &mut MapCheck,
    pa: u64,
    block: bool,
    guard: bool,
) -> Result<(), TableError> {
    let place = set.place(base, pa, block)?;
    // The ranges come in the order of their starts, so an earlier range
    // shares an address with the leaf exactly when it ends above it.
    if pa < check.reach || guard {
        return Err(TableError::AlreadyMapped);
    }
    match place {
        LeafPlace::Root => {
            let gib = pa & !(GIB_SIZE - 1);
            if gib != check.gib {
                check.gib = gib;
                check.new_tables += 1;
            }
        }
        LeafPlace::Level2(_) => {}
        LeafPlace::Level3(_, _) => return Ok(()),
    }
    // The negation is the condition itself: a flag from a `match` whose arms
    // give a negation and a literal does not type-check in Lean.
    if !block {
        let slot = pa & !(BLOCK_SIZE - 1);
        if slot != check.slot {
            check.slot = slot;
            check.new_tables += 1;
        }
    }
    Ok(())
}

/// The write phase of a map whose leaves passed their checks:
/// `OutOfTables` when the pool has fewer free tables than the new tables of
/// the whole plan; otherwise the set records them, and the cursor of the
/// plan starts before the first leaf, with the new tables from the old
/// record on. As the new tables fit in the free ones, the new record does
/// not leave `usize`.
pub(super) fn write_phase<const N: usize, const UPPER: bool>(
    set: &mut Tables<N, UPPER>,
    check: MapCheck,
) -> Result<MapCursor, TableError> {
    if set.free_tables() < check.new_tables {
        return Err(TableError::OutOfTables);
    }
    let next = set.used;
    set.used = next + check.new_tables;
    Ok(MapCursor {
        phase: MapPhase::Leaf,
        from: 0,
        next,
        gib: NO_SLOT,
        slot: NO_SLOT,
        t2: 0,
        t3: 0,
    })
}

/// The part of the plan in which the cursor is.
enum MapPhase {
    /// The first leaf of a 2 MiB slot, at or above `from`.
    Leaf,
    /// The pages of `slot` in its level 3 table `t3` of the set; after them,
    /// the next leaf.
    HeldPages,
    /// The pages of `slot` in its new level 3 table `t3`, under the level 2
    /// table `t2` of the set; after them, `Fence`.
    NewPages,
    /// The store of the table descriptor of `t3` into `t2`.
    NewTable,
    /// The pages of the 1 GiB slot `gib` of the new level 2 table `t2`, each
    /// 2 MiB slot in a new level 3 table, the latest `t3`; after them,
    /// `Zero(t2)`.
    Children,
    /// The entries of `t2` at or above `from`, `t3` being the level 3 table
    /// of the next slot of pages; after them, `Fence`.
    Entries,
    /// The store of the table descriptor of `t2` into the root.
    Root,
    /// After `Sync`.
    Done,
}

/// What the cursor gives for the leaf that its search found.
pub(super) enum MapTurn {
    /// A step of the plan.
    Give(Step),
    /// Nothing more: the plan gave its `Sync`.
    End,
    /// No step yet: the cursor took a new level 2 table at a block and needs
    /// the first page of the 1 GiB slot, for [`MapCursor::children`].
    Seek,
}

/// The position of a map plan between two of its steps.
pub(super) struct MapCursor {
    /// The part of the plan.
    phase: MapPhase,
    /// The address from which the next leaf is looked for.
    from: u64,
    /// The next free table.
    next: usize,
    /// The 1 GiB slot of the latest leaf.
    gib: u64,
    /// The 2 MiB slot of the pages that the cursor is in.
    slot: u64,
    /// The level 2 table of `gib`.
    t2: usize,
    /// The level 3 table of `slot`.
    t3: usize,
}

impl MapCursor {
    /// The search that the next step needs: the first leaf at or above
    /// `from` and below `limit`, a page when `pages`; the limit is 0 when the
    /// step needs no leaf.
    fn search(&self) -> (u64, u64, bool) {
        match self.phase {
            MapPhase::Leaf | MapPhase::HeldPages => (self.from, NO_LIMIT, false),
            MapPhase::NewPages => (self.from, self.slot + BLOCK_SIZE, false),
            MapPhase::Children => (self.from, self.gib + GIB_SIZE, true),
            MapPhase::Entries => (self.from, self.gib + GIB_SIZE, false),
            MapPhase::NewTable | MapPhase::Root | MapPhase::Done => (self.from, 0, false),
        }
    }

    /// The next step of the plan of the set at `base`, from the leaf that
    /// the search of [`MapCursor::search`] found.
    fn take<const N: usize, const UPPER: bool>(
        &mut self,
        set: &Tables<N, UPPER>,
        base: u64,
        found: Option<Leaf>,
    ) -> MapTurn {
        match self.phase {
            MapPhase::Leaf => self.leaf(set, base, found),
            MapPhase::HeldPages => self.held_page(set, base, found),
            MapPhase::NewPages => MapTurn::Give(self.new_page(found)),
            MapPhase::NewTable => {
                self.phase = MapPhase::Leaf;
                self.from = self.slot + BLOCK_SIZE;
                let table = table_descriptor(table_address(base, self.t3));
                MapTurn::Give(Step::Store(self.t2, index2(self.slot), table))
            }
            MapPhase::Children => MapTurn::Give(self.children(found)),
            MapPhase::Entries => MapTurn::Give(self.entry(base, found)),
            MapPhase::Root => {
                self.phase = MapPhase::Leaf;
                self.from = self.gib + GIB_SIZE;
                let table = table_descriptor(table_address(base, self.t2));
                MapTurn::Give(Step::Store(0, index1(self.gib), table))
            }
            MapPhase::Done => MapTurn::End,
        }
    }

    /// The step of the first leaf of a 2 MiB slot, from its place in the
    /// set; after the last leaf, `Sync`.
    fn leaf<const N: usize, const UPPER: bool>(
        &mut self,
        set: &Tables<N, UPPER>,
        base: u64,
        found: Option<Leaf>,
    ) -> MapTurn {
        let leaf = match found {
            Some(leaf) => leaf,
            None => {
                self.phase = MapPhase::Done;
                return MapTurn::Give(Step::Sync);
            }
        };
        // The checks of the map passed, so the walk does not fail.
        let place = match set.place(base, leaf.pa, leaf.block) {
            Ok(place) => place,
            Err(_) => LeafPlace::Root,
        };
        self.gib = leaf.pa & !(GIB_SIZE - 1);
        self.slot = leaf.pa & !(BLOCK_SIZE - 1);
        match place {
            LeafPlace::Root => {
                self.t2 = self.next;
                self.next += 1;
                self.phase = MapPhase::Children;
                self.slot = NO_SLOT;
                self.from = leaf.pa;
                if leaf.block {
                    MapTurn::Seek
                } else {
                    MapTurn::Give(self.children(Some(leaf)))
                }
            }
            LeafPlace::Level2(t2) => {
                self.t2 = t2;
                if leaf.block {
                    self.from = leaf.pa + BLOCK_SIZE;
                    return MapTurn::Give(Step::Store(t2, index2(leaf.pa), leaf.desc));
                }
                self.t3 = self.next;
                self.next += 1;
                self.phase = MapPhase::NewPages;
                self.from = leaf.pa;
                MapTurn::Give(Step::Zero(self.t3))
            }
            LeafPlace::Level3(t2, t3) => {
                self.t2 = t2;
                self.t3 = t3;
                self.phase = MapPhase::HeldPages;
                self.from = leaf.pa + PAGE_SIZE;
                MapTurn::Give(Step::Store(t3, index3(leaf.pa), leaf.desc))
            }
        }
    }

    /// The store of the next page of `slot` into its level 3 table of the
    /// set; for a leaf of another slot, or none, the step of [`Self::leaf`].
    fn held_page<const N: usize, const UPPER: bool>(
        &mut self,
        set: &Tables<N, UPPER>,
        base: u64,
        found: Option<Leaf>,
    ) -> MapTurn {
        if let Some(page) = found {
            if page.pa & !(BLOCK_SIZE - 1) == self.slot {
                self.from = page.pa + PAGE_SIZE;
                return MapTurn::Give(Step::Store(self.t3, index3(page.pa), page.desc));
            }
        }
        self.phase = MapPhase::Leaf;
        self.leaf(set, base, found)
    }

    /// The store of the next page of `slot` into its new level 3 table, or
    /// `Fence` after the last.
    fn new_page(&mut self, found: Option<Leaf>) -> Step {
        match found {
            Some(page) => {
                self.from = page.pa + PAGE_SIZE;
                Step::Store(self.t3, index3(page.pa), page.desc)
            }
            None => {
                self.phase = MapPhase::NewTable;
                Step::Fence
            }
        }
    }

    /// The step of the first page at or above `from` of the 1 GiB slot of a
    /// new level 2 table: the store of a page of `slot` into `t3`, or else
    /// `Zero` of the new level 3 table of the slot of the page; with no page
    /// left, `Zero(t2)`, and the entries of `t2` come next.
    fn children(&mut self, found: Option<Leaf>) -> Step {
        match found {
            Some(page) => {
                let slot = page.pa & !(BLOCK_SIZE - 1);
                if slot == self.slot {
                    self.from = page.pa + PAGE_SIZE;
                    return Step::Store(self.t3, index3(page.pa), page.desc);
                }
                self.slot = slot;
                self.t3 = self.next;
                self.next += 1;
                self.from = page.pa;
                Step::Zero(self.t3)
            }
            None => {
                self.phase = MapPhase::Entries;
                self.from = self.gib;
                self.t3 = self.t2 + 1;
                Step::Zero(self.t2)
            }
        }
    }

    /// The store of the entry of `t2` for the 2 MiB slot of the leaf that
    /// starts it: its block, or the table descriptor of the slot's level 3
    /// table, which the tables of the slots of pages before it precede;
    /// `Fence` after the last.
    fn entry(&mut self, base: u64, found: Option<Leaf>) -> Step {
        match found {
            Some(leaf) => {
                self.from = (leaf.pa & !(BLOCK_SIZE - 1)) + BLOCK_SIZE;
                if leaf.block {
                    return Step::Store(self.t2, index2(leaf.pa), leaf.desc);
                }
                let table = self.t3;
                self.t3 += 1;
                let entry = table_descriptor(table_address(base, table));
                Step::Store(self.t2, index2(leaf.pa), entry)
            }
            None => {
                self.phase = MapPhase::Root;
                Step::Fence
            }
        }
    }
}
