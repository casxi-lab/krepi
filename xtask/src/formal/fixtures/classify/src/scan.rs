//! A loop whose condition matches, through `matches!`, on the `Ordering` of
//! a comparison made with `?`.

use core::cmp::Ordering;

pub struct Exhausted;

pub fn take(budget: &mut u32) -> Result<(), Exhausted> {
    if *budget == 0 {
        Err(Exhausted)
    } else {
        *budget -= 1;
        Ok(())
    }
}

pub fn compare(x: u32, bound: u32, budget: &mut u32) -> Result<Ordering, Exhausted> {
    take(budget)?;
    Ok(if x < bound {
        Ordering::Less
    } else if x == bound {
        Ordering::Equal
    } else {
        Ordering::Greater
    })
}

pub fn halve(x: u32, budget: &mut u32) -> Result<(u32, u32), Exhausted> {
    let mut x = x;
    let mut halvings = 0u32;
    while matches!(compare(x, 1, budget)?, Ordering::Greater) {
        take(budget)?;
        x /= 2;
        halvings += 1;
    }
    Ok((x, halvings))
}
