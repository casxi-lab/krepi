//! The tests of the bounded writes, taken from the prototype tree with their
//! expected values.
//!
//! Feature: krepi.platform.qemu-virt-boot

use super::*;

#[test]
fn permanently_full_output_spends_only_the_total_budget() {
    let mut calls = 0;
    let result = emit_bounded(b"abc", 7, |byte| {
        calls += 1;
        assert_eq!(byte, b'a');
        false
    });
    assert_eq!(calls, 7);
    assert_eq!(
        result,
        Emission {
            bytes_written: 0,
            attempts: 7,
        }
    );
}

#[test]
fn intermittent_output_retries_without_skipping_or_transforming_bytes() {
    let mut accepted = [0; 3];
    let mut accepted_len = 0;
    let mut calls = 0;
    let result = emit_bounded(b"a\r\n", 9, |byte| {
        calls += 1;
        if calls % 2 == 1 {
            false
        } else {
            accepted[accepted_len] = byte;
            accepted_len += 1;
            true
        }
    });
    assert_eq!(&accepted, b"a\r\n");
    assert_eq!(
        result,
        Emission {
            bytes_written: 3,
            attempts: 6,
        }
    );
}

#[test]
fn successful_writes_also_consume_attempts() {
    let mut accepted = [0; 2];
    let mut count = 0;
    let result = emit_bounded(b"abcd", 2, |byte| {
        accepted[count] = byte;
        count += 1;
        true
    });
    assert_eq!(&accepted, b"ab");
    assert_eq!(
        result,
        Emission {
            bytes_written: 2,
            attempts: 2,
        }
    );
}

#[test]
fn empty_output_and_zero_budget_never_call_device() {
    for (bytes, budget) in [(b"".as_slice(), usize::MAX), (b"abc".as_slice(), 0)] {
        assert_eq!(
            emit_bounded(bytes, budget, |_| panic!("must not touch device")),
            Emission {
                bytes_written: 0,
                attempts: 0,
            }
        );
    }
}
