//! Checked arithmetic on budgets and ranges.

/// What is left of the budget `left` after a charge of `cost`, unless the
/// charge exceeds it.
pub fn charge(left: u32, cost: u32) -> Option<u32> {
    left.checked_sub(cost)
}

/// The share of each of `parts` in `total`, rounded down, unless there are
/// no parts.
pub fn split(total: u32, parts: u32) -> Option<u32> {
    if parts == 0 {
        return None;
    }
    Some(total / parts)
}

/// Whether the range of `length` from `base` ends at or before `limit`,
/// without overflowing.
pub fn fits(base: u32, length: u32, limit: u32) -> bool {
    match base.checked_add(length) {
        Some(end) => end <= limit,
        None => false,
    }
}

/// The number of bits set in `word`, through a function of the standard
/// library that the proof tools do not model.
pub fn weight(word: u32) -> u32 {
    word.count_ones()
}
