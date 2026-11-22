//! The tests of the MMU adapter: the register values that `enable` writes
//! and the physical address size that `physical_width` reads, with the
//! values written from the contract of the page tables and the field
//! positions of the AArch64 registers, and the steps of a write plan of at
//! most seven steps.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

/// The field of `width` bits from bit `shift` of `value`.
fn field(value: u64, shift: u32, width: u32) -> u64 {
    (value >> shift) & ((1 << width) - 1)
}

#[test]
fn translation_control_of_qemu_virt_is_written_out() {
    assert_eq!(translation_control(40, false), Some(0x0000_0002_b019_3019));
    assert_eq!(translation_control(40, true), Some(0x0000_0002_b519_3519));
}

#[test]
fn translation_control_sets_the_fields_of_the_contract() {
    for (bits, size) in [(32, 0), (36, 1), (40, 2), (42, 3), (44, 4), (48, 5)] {
        for caches in [false, true] {
            let value = translation_control(bits, caches).unwrap();
            let cacheability = if caches { 0b01 } else { 0b00 };
            // (shift, width, value) of T0SZ, EPD0, IRGN0, ORGN0, SH0, TG0,
            // T1SZ, A1, EPD1, IRGN1, ORGN1, SH1, TG1, IPS, AS, TBI0, TBI1,
            // HA and HD.
            let fields = [
                (0, 6, 25),
                (7, 1, 0),
                (8, 2, cacheability),
                (10, 2, cacheability),
                (12, 2, 0b11),
                (14, 2, 0b00),
                (16, 6, 25),
                (22, 1, 0),
                (23, 1, 0),
                (24, 2, cacheability),
                (26, 2, cacheability),
                (28, 2, 0b11),
                (30, 2, 0b10),
                (32, 3, size),
                (36, 1, 0),
                (37, 1, 0),
                (38, 1, 0),
                (39, 1, 0),
                (40, 1, 0),
            ];
            let mut rest = value;
            for (shift, width, expected) in fields {
                assert_eq!(
                    field(value, shift, width),
                    expected,
                    "{bits} bits, bit {shift}"
                );
                rest &= !(((1 << width) - 1) << shift);
            }
            assert_eq!(rest, 0, "{bits} bits: no other field is set");
        }
    }
}

#[test]
fn translation_control_refuses_other_widths() {
    for bits in [0, 31, 33, 35, 39, 41, 43, 47, 49, 52, 56, 255] {
        assert_eq!(translation_control(bits, false), None, "{bits} bits");
        assert_eq!(translation_control(bits, true), None, "{bits} bits");
    }
}

#[test]
fn memory_attributes_put_device_at_index_0_and_normal_at_index_1() {
    assert_eq!(memory_attributes(false), 0x0000_0000_0000_4400);
    assert_eq!(memory_attributes(true), 0x0000_0000_0000_ff00);
}

#[test]
fn system_control_sets_the_caches_only_when_asked() {
    // M (bit 0) and WXN (bit 19), with C (bit 2) and I (bit 12) for caches.
    assert_eq!(system_control_bits(false), 0x8_0001);
    assert_eq!(system_control_bits(true), 0x8_1005);
}

#[test]
fn physical_width_follows_the_physical_address_range() {
    let widths = [32, 36, 40, 42, 44, 48];
    for granule in [0b0000, 0b0001] {
        for (range, bits) in widths.into_iter().enumerate() {
            let features = (granule << 28) | range as u64;
            assert_eq!(width_of(features), Some(bits), "PARange {range}");
        }
        for range in [6, 7, 15] {
            assert_eq!(width_of((granule << 28) | range), None, "PARange {range}");
        }
    }
    // The fields other than TGran4 and PARange do not count.
    assert_eq!(width_of(0xffff_ffff_0fff_fff2), Some(40));
    // A CPU without the 4 KiB granule, or with a reserved TGran4.
    for granule in [0b0010, 0b1111] {
        assert_eq!(width_of((granule << 28) | 2), None, "TGran4 {granule:#b}");
    }
}

/// The steps that `steps` gives, after which it gives none again.
fn all_steps<const N: usize>(mut steps: WriteSteps<N>) -> Vec<Step> {
    let given: Vec<Step> = core::iter::from_fn(|| steps.next_step()).collect();
    assert_eq!(steps.next_step(), None);
    given
}

#[test]
fn write_steps_give_the_zeroed_tables_first() {
    let store = Step::Store(1, 3, 0x4000_1003);
    let mut steps = [Step::Sync; 7];
    steps[..3].copy_from_slice(&[store, Step::Fence, Step::Sync]);
    let plan = WritePlan {
        zero_tables: 2,
        steps,
        len: 3,
    };
    let expected = [Step::Zero(0), Step::Zero(1), store, Step::Fence, Step::Sync];
    assert_eq!(all_steps(WriteSteps::<4>::new(plan)), expected);
}

#[test]
fn write_steps_of_a_reset_and_of_an_overlong_plan() {
    let reset = WritePlan {
        zero_tables: 3,
        steps: [Step::Sync; 7],
        len: 0,
    };
    let zeros = [Step::Zero(0), Step::Zero(1), Step::Zero(2)];
    assert_eq!(all_steps(WriteSteps::<4>::new(reset)), zeros);
    let overlong = WritePlan {
        zero_tables: 0,
        steps: [Step::Fence; 7],
        len: 9,
    };
    assert_eq!(all_steps(WriteSteps::<4>::new(overlong)), [Step::Fence; 7]);
}
