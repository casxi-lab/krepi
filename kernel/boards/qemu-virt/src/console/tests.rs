//! The tests of the console: the examples of the QEMU virt boot feature
//! document and the boundaries of a write.
//!
//! Feature: krepi.platform.qemu-virt-boot

use super::*;

/// The bounds of the tests: those of QEMU virt.
const BOUNDS: Bounds = crate::CONSOLE_BOUNDS;

/// A counter frequency of 62.5 MHz.
const FREQUENCY: u64 = 62_500_000;

/// A device that takes every byte into `output`.
fn ready(output: &mut Vec<u8>) -> impl FnMut(u8) -> bool + '_ {
    |byte| {
        output.push(byte);
        true
    }
}

mod examples {
    use super::*;

    /// A record is written with each LF as CR LF.
    #[test]
    fn ex1_a_record_ends_in_cr_lf() {
        let mut output = Vec::new();
        let result = print(
            format_args!("CASXI_READY\n"),
            &BOUNDS,
            FREQUENCY,
            || 0,
            ready(&mut output),
        );
        assert_eq!(result, Ok(13));
        assert_eq!(output, b"CASXI_READY\r\n");
    }

    /// A device that never takes a byte stops the write once the byte has
    /// been refused one million times, and the failure marker reports it.
    #[test]
    fn ex2_a_stalled_device_fails_the_write_and_is_reported() {
        let mut attempts = 0;
        let result = print(
            format_args!("CASXI_READY\n"),
            &BOUNDS,
            FREQUENCY,
            || 0,
            |_| {
                attempts += 1;
                false
            },
        );
        assert_eq!(result, Err(PolledError::PollLimit));
        assert_eq!(attempts, 1_000_000);
        let mut output = Vec::new();
        let emission = report_failure(PolledError::PollLimit, &BOUNDS, ready(&mut output));
        assert_eq!(
            output,
            b"\r\nCASXI_UART_FAIL reason=stalled\r\nCASXI_HALTED\r\n"
        );
        assert_eq!(
            emission,
            Emission {
                bytes_written: 48,
                attempts: 48
            }
        );
    }

    /// A received carriage return is echoed as CR LF; any other byte,
    /// including LF and a byte that is not ASCII, as it is.
    #[test]
    fn ex3_the_echo_adds_lf_after_cr_only() {
        let mut output = Vec::new();
        for byte in *b"ok\r\n\xff" {
            let (bytes, count) = echo(byte);
            assert_eq!(
                write(
                    &bytes[..count],
                    &BOUNDS,
                    FREQUENCY,
                    || 0,
                    ready(&mut output)
                ),
                Ok(count)
            );
        }
        assert_eq!(output, b"ok\r\n\n\xff");
    }
}

mod boundaries {
    use super::*;

    /// Each failure has its own marker, and every marker starts on a new
    /// line and ends with the halt line.
    #[test]
    fn each_failure_has_its_marker() {
        for (error, reason) in [
            (PolledError::InvalidBudget, "clock"),
            (PolledError::ByteLimit, "length"),
            (PolledError::Deadline, "deadline"),
            (PolledError::PollLimit, "stalled"),
            (PolledError::Formatting, "format"),
        ] {
            let expected = format!("\r\nCASXI_UART_FAIL reason={reason}\r\nCASXI_HALTED\r\n");
            assert_eq!(failure_marker(error), expected.as_bytes());
        }
    }

    /// The failure marker takes at most the failure attempts in all, however
    /// often the device refuses a byte.
    #[test]
    fn the_failure_marker_is_bounded_by_its_attempts() {
        let mut calls = 0;
        let emission = report_failure(PolledError::Deadline, &BOUNDS, |_| {
            calls += 1;
            false
        });
        assert_eq!(calls, 1_000_000);
        assert_eq!(
            emission,
            Emission {
                bytes_written: 0,
                attempts: 1_000_000
            }
        );
    }

    /// The window of a record is 250 ms on the counter: 15,625,000 ticks at
    /// 62.5 MHz and 250,000,000 at 1 GHz, rounded down otherwise. A window
    /// that does not fit gives `u64::MAX` ticks, which a write refuses
    /// without touching the device.
    #[test]
    fn the_window_is_converted_to_ticks() {
        assert_eq!(window_ticks(FREQUENCY, 250), 15_625_000);
        assert_eq!(window_ticks(1_000_000_000, 250), 250_000_000);
        assert_eq!(window_ticks(3, 250), 0);
        assert_eq!(window_ticks(u64::MAX, u64::MAX), u64::MAX);
        let result = write(
            b"x",
            &Bounds {
                window_ms: u64::MAX,
                ..BOUNDS
            },
            u64::MAX,
            || panic!("no clock use"),
            |_| panic!("no device use"),
        );
        assert_eq!(result, Err(PolledError::InvalidBudget));
    }

    /// A counter that does not reach the window gives a window of 0 ticks,
    /// which a write refuses without touching the device.
    #[test]
    fn a_counter_too_slow_for_the_window_is_refused() {
        let result = print(
            format_args!("x"),
            &BOUNDS,
            3,
            || panic!("no clock use"),
            |_| panic!("no device use"),
        );
        assert_eq!(result, Err(PolledError::InvalidBudget));
    }

    /// A write of bytes writes LF as it is, keeps the byte limit of a
    /// record and stops at the deadline.
    #[test]
    fn a_write_of_bytes_keeps_the_bounds_of_a_record() {
        let mut output = Vec::new();
        assert_eq!(
            write(b"a\nb", &BOUNDS, FREQUENCY, || 0, ready(&mut output)),
            Ok(3)
        );
        assert_eq!(output, b"a\nb");

        let long = [b'x'; RECORD_BYTES + 1];
        let mut count = 0;
        let result = write(
            &long,
            &BOUNDS,
            FREQUENCY,
            || 0,
            |_| {
                count += 1;
                true
            },
        );
        assert_eq!(result, Err(PolledError::ByteLimit));
        assert_eq!(count, RECORD_BYTES);

        let mut clock = 0;
        let mut written = 0;
        let result = write(
            b"abc",
            &BOUNDS,
            FREQUENCY,
            || {
                clock += 10_000_000;
                clock
            },
            |_| {
                written += 1;
                true
            },
        );
        assert_eq!(result, Err(PolledError::Deadline));
        assert_eq!(written, 1);
    }
}

mod panic_record {
    use super::*;

    /// The location of the panics of these tests.
    const LOCATION: PanicLocation<'static> = PanicLocation {
        file: "boards/qemu-virt/src/main.rs",
        line: 77,
        column: 9,
    };

    /// A panic with a static message and a location writes the message, the
    /// location and the halt line, each a record that ends in CR LF.
    #[test]
    fn a_static_message_is_written_with_its_location() {
        let mut output = Vec::new();
        let result = report_panic(
            Some("BSS not initialized"),
            Some(LOCATION),
            &BOUNDS,
            FREQUENCY,
            || 0,
            ready(&mut output),
        );
        let expected: &[u8] = b"\r\nCASXI_PANIC BSS not initialized\r\n\
            CASXI_PANIC_LOCATION file=boards/qemu-virt/src/main.rs line=77 column=9\r\n\
            CASXI_HALTED\r\n";
        assert_eq!(output, expected);
        assert_eq!(result, Ok(expected.len()));
    }

    /// A panic without a static message writes the fixed text in its place.
    #[test]
    fn a_dynamic_message_is_replaced_by_the_fixed_text() {
        let mut output = Vec::new();
        let result = report_panic(
            None,
            Some(LOCATION),
            &BOUNDS,
            FREQUENCY,
            || 0,
            ready(&mut output),
        );
        let expected: &[u8] = b"\r\nCASXI_PANIC dynamic_panic_message_omitted\r\n\
            CASXI_PANIC_LOCATION file=boards/qemu-virt/src/main.rs line=77 column=9\r\n\
            CASXI_HALTED\r\n";
        assert_eq!(output, expected);
        assert_eq!(result, Ok(expected.len()));
    }

    /// A panic without a location writes no location record.
    #[test]
    fn a_panic_without_a_location_has_no_location_record() {
        let mut output = Vec::new();
        let result = report_panic(None, None, &BOUNDS, FREQUENCY, || 0, ready(&mut output));
        let expected: &[u8] = b"\r\nCASXI_PANIC dynamic_panic_message_omitted\r\nCASXI_HALTED\r\n";
        assert_eq!(output, expected);
        assert_eq!(result, Ok(expected.len()));
    }

    /// A message too long for one record fails that record with its byte
    /// limit, and no record follows it.
    #[test]
    fn a_message_too_long_for_a_record_ends_the_panic_record() {
        let long = "x".repeat(RECORD_BYTES);
        let mut output = Vec::new();
        let result = report_panic(
            Some(&long),
            Some(LOCATION),
            &BOUNDS,
            FREQUENCY,
            || 0,
            ready(&mut output),
        );
        assert_eq!(result, Err(PolledError::ByteLimit));
        assert_eq!(output.len(), RECORD_BYTES);
        assert!(output.starts_with(b"\r\nCASXI_PANIC xxx"));
        assert!(
            output[2..]
                .iter()
                .all(|&byte| byte != b'\r' && byte != b'\n')
        );
    }
}
