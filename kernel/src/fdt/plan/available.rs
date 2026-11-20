//! The usable ranges of a boot memory map: the managed banks without the
//! union of the reservations, in address order.
//!
//! Feature: krepi.platform.device-tree
//!
//! The iterator keeps a cursor that only moves forward within a managed
//! bank. At the cursor, either reservations hold it, and it moves to the
//! furthest end of those, or to the end of the bank, or none does, and the
//! range from it to the nearest start of a reservation above it, or to the
//! end of the bank, is usable. So no usable range bridges two banks or a
//! hole, and each is maximal.

use super::super::{AvailableRanges, Cursor, Span};

/// The furthest end of the reservations that hold `at`, or none when none
/// holds it.
fn furthest_holding(reservations: &[Span], at: u64) -> Option<u64> {
    let mut held = false;
    let mut end = 0;
    let mut index = 0;
    while index < reservations.len() {
        let reservation = reservations[index];
        let reservation_end = reservation.start + reservation.size;
        if reservation.start <= at && at < reservation_end && (!held || reservation_end > end) {
            end = reservation_end;
            held = true;
        }
        index += 1;
    }
    if held { Some(end) } else { None }
}

/// The nearest start of a reservation above `at`, or `stop` when no
/// reservation starts between them.
fn nearest_start(reservations: &[Span], at: u64, stop: u64) -> u64 {
    let mut nearest = stop;
    let mut index = 0;
    while index < reservations.len() {
        let start = reservations[index].start;
        if at < start && start < nearest {
            nearest = start;
        }
        index += 1;
    }
    nearest
}

/// The next usable range from `cursor` and the cursor after it, or none
/// after the last managed bank.
fn available_step(
    managed: &[Span],
    reservations: &[Span],
    cursor: Cursor,
) -> (Cursor, Option<Span>) {
    let mut cursor = cursor;
    while cursor.bank < managed.len() {
        let bank = managed[cursor.bank];
        let stop = bank.start + bank.size;
        let at = if cursor.at > bank.start {
            cursor.at
        } else {
            bank.start
        };
        if at >= stop {
            cursor = Cursor {
                bank: cursor.bank + 1,
                at: 0,
            };
        } else {
            match furthest_holding(reservations, at) {
                Some(end) => {
                    cursor.at = if end < stop { end } else { stop };
                }
                None => {
                    let end = nearest_start(reservations, at, stop);
                    let range = Span {
                        start: at,
                        size: end - at,
                    };
                    cursor.at = end;
                    return (cursor, Some(range));
                }
            }
        }
    }
    (cursor, None)
}

impl AvailableRanges<'_> {
    /// The next usable range, or none after the last. The entry that built
    /// the boot memory map checked its banks and reservations, so the walk
    /// does not fail.
    // The iterator implements `next` alone: the provided methods of
    // `Iterator` would reach library functions without a model.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Span> {
        let (cursor, range) = available_step(self.managed, self.reservations, self.cursor);
        self.cursor = cursor;
        range
    }
}
