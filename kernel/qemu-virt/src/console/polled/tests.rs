//! The tests of the polled writes, taken from the prototype tree with their
//! expected values.
//!
//! Feature: krepi.platform.qemu-virt-boot

use super::*;
use core::{cell::Cell, fmt};

#[test]
fn long_record_survives_more_polls_at_the_same_device_rate() {
    let payload = [b'x'; 900];
    let text = core::str::from_utf8(&payload).unwrap();
    for step in [1_u64, 32] {
        let clock = Cell::new(0_u64);
        let mut next_ready = 0;
        let mut polls = 0;
        let mut output = [0_u8; 902];
        let mut used = 0;
        let result = write_polled(
            format_args!("{text}\n"),
            1024,
            3000,
            2_000_000,
            || {
                clock.set(clock.get() + step);
                clock.get()
            },
            |byte| {
                polls += 1;
                if clock.get() < next_ready {
                    return false;
                }
                output[used] = byte;
                used += 1;
                next_ready = clock.get() + 2000;
                true
            },
        );
        assert_eq!(result, Ok(902));
        assert_eq!(&output[..900], &payload);
        assert_eq!(&output[900..], b"\r\n");
        if step == 1 {
            assert!(polls > 1_000_000);
        }
        assert!(clock.get() < 2_000_000);
    }
}

#[test]
fn deadline_stops_a_busy_device_before_its_poll_cap() {
    let mut clock = 0;
    let mut attempts = 0;
    let result = write_polled(
        format_args!("x"),
        1,
        100,
        5,
        || {
            clock += 1;
            clock
        },
        |_| {
            attempts += 1;
            false
        },
    );
    assert_eq!(result, Err(PolledError::Deadline));
    assert_eq!(attempts, 4);
}

#[test]
fn stopped_clock_still_has_a_finite_stall_bound() {
    let mut attempts = 0;
    assert_eq!(
        write_polled(
            format_args!("x"),
            1,
            7,
            5,
            || 123,
            |_| {
                attempts += 1;
                false
            }
        ),
        Err(PolledError::PollLimit)
    );
    assert_eq!(attempts, 7);
}

#[test]
fn deadline_is_not_renewed_after_success_and_handles_counter_wrap() {
    let mut clock = u64::MAX - 3;
    let mut output = [0_u8; 4];
    let mut used = 0;
    let result = write_polled(
        format_args!("abcd"),
        4,
        7,
        4,
        || {
            clock = clock.wrapping_add(1);
            clock
        },
        |byte| {
            output[used] = byte;
            used += 1;
            true
        },
    );
    assert_eq!(result, Err(PolledError::Deadline));
    assert_eq!(&output[..used], b"abc");
}

#[test]
fn crlf_counts_against_the_byte_limit() {
    for (limit, expected, result) in [
        (3, &b"A\r\n"[..], Ok(3)),
        (2, &b"A\r"[..], Err(PolledError::ByteLimit)),
    ] {
        let mut output = [0_u8; 3];
        let mut used = 0;
        assert_eq!(
            write_polled(
                format_args!("A\n"),
                limit,
                1,
                5,
                || 0,
                |byte| {
                    output[used] = byte;
                    used += 1;
                    true
                }
            ),
            result
        );
        assert_eq!(&output[..used], expected);
    }
}

#[test]
fn ignored_formatter_errors_cannot_restart_output() {
    struct IgnoreErrors;
    impl fmt::Display for IgnoreErrors {
        fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
            let _ = output.write_str("abc");
            let _ = output.write_str("z");
            Ok(())
        }
    }
    let mut count = 0;
    assert_eq!(
        write_polled(
            format_args!("{IgnoreErrors}"),
            2,
            1,
            5,
            || 0,
            |_| {
                count += 1;
                true
            }
        ),
        Err(PolledError::ByteLimit)
    );
    assert_eq!(count, 2);
}

#[test]
fn invalid_budgets_never_touch_clock_or_device() {
    for (attempts, ticks) in [(0, 1), (1, 0), (1, 1 << 63)] {
        assert_eq!(
            write_polled(
                format_args!("x"),
                1,
                attempts,
                ticks,
                || panic!("invalid clock use"),
                |_| panic!("invalid device use")
            ),
            Err(PolledError::InvalidBudget)
        );
    }
}

#[test]
fn formatter_failure_is_not_silently_accepted() {
    struct BadFormat;
    impl fmt::Display for BadFormat {
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            Err(fmt::Error)
        }
    }
    assert_eq!(
        write_polled(
            format_args!("{BadFormat}"),
            8,
            1,
            5,
            || 0,
            |_| panic!("unexpected output")
        ),
        Err(PolledError::Formatting)
    );
}
