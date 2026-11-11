//! A table of slots whose capacity is fixed when it is made, with a
//! generation for each slot.

use crate::handle;

/// The number of slots that a table can hold.
pub const SLOTS: u32 = 4;

/// A table: its capacity, the slots in use from the first, and the
/// generation of each slot.
pub struct Table {
    capacity: u32,
    used: u32,
    generations: [u32; 4],
}

impl Table {
    /// A table of `capacity` slots, none in use, when it holds at least one
    /// slot and at most [`SLOTS`].
    pub fn new(capacity: u32) -> Option<Table> {
        if capacity == 0 || capacity > SLOTS {
            return None;
        }
        Some(Table {
            capacity,
            used: 0,
            generations: [0; 4],
        })
    }

    /// The index of the next slot, which is then in use, unless every slot
    /// of the capacity is.
    pub fn alloc(&mut self) -> Option<u32> {
        if self.used < self.capacity {
            let index = self.used;
            self.used += 1;
            return Some(index);
        }
        None
    }

    /// Moves the slot `index` to its next generation, when it is a slot of
    /// the capacity and its generation does not overflow, and says whether
    /// it did.
    pub fn retire(&mut self, index: u32) -> bool {
        if index >= self.capacity {
            return false;
        }
        match self.generations[index as usize].checked_add(1) {
            Some(later) => {
                self.generations[index as usize] = later;
                true
            }
            None => false,
        }
    }

    /// Whether `handle` names a slot of the capacity at its current
    /// generation.
    pub fn is_current(&self, handle: u32) -> bool {
        let index = handle::index(handle);
        index < self.capacity && self.generations[index as usize] == handle::generation(handle)
    }

    /// The number of slots of the capacity whose generation is not 0.
    pub fn retired(&self) -> u32 {
        let mut slot = 0;
        let mut count = 0;
        while slot < self.capacity {
            if self.generations[slot as usize] != 0 {
                count += 1;
            }
            slot += 1;
        }
        count
    }
}
