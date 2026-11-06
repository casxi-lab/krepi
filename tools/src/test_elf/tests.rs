use super::*;
use crate::elf::{Symbol, parse_elf, symbol_address, symbol_at};
use crate::hex;
use crate::scratch::Scratch;

/// The size of the image in bytes, as the pinned version of `object` lays
/// it out.
const SIZE: usize = 8_760;
/// The file offset and size of `.text`, which its program header gives.
const TEXT: std::ops::Range<usize> = 0x1000..0x1000 + 0x7e;

/// The little-endian field of `N` bytes at `offset`.
fn field<const N: usize>(image: &[u8], offset: usize) -> u64 {
    let mut bytes = [0u8; 8];
    bytes[..N].copy_from_slice(&image[offset..offset + N]);
    u64::from_le_bytes(bytes)
}

/// The ELF reader accepts the image: the build-id is the start of the
/// SHA-256 digest of `.text`, `_start` is the one function, sized up to the
/// message, and `.text` is the one executable range.
#[test]
fn the_image_is_read_by_the_elf_reader() {
    let image = image();
    let snapshot = parse_elf(image.clone()).expect("the ELF reader accepts the test image");
    assert_eq!(
        snapshot.build_id,
        hex(&Sha256::digest(&image[TEXT])[..20]),
        "the build-id is the first 20 bytes of the digest of .text"
    );
    assert_eq!(
        snapshot.symbols,
        [Symbol {
            name: "_start".to_string(),
            address: 0x4020_0000,
            size: 0x48,
            section_end: 0x4020_007e,
        }]
    );
    assert_eq!(snapshot.executable, [(0x4020_0000, 0x4020_007e)]);
    // The PSCI call lies in `_start`; the message, an object, in no function.
    let name = |address| symbol_at(&snapshot, address).map(|symbol| symbol.name.as_str());
    assert_eq!(name(0x4020_003c), Some("_start"));
    assert_eq!(name(0x4020_0048), None);
    assert_eq!(snapshot.data, image);
}

/// The program starts at the entry. The program headers load `.text` there,
/// read and execute, and the note read-only on the next page; the program
/// is the AArch64 encoding of the instructions below, taken from the Arm
/// Architecture Reference Manual, and the message follows it. The image is
/// the same on every call.
#[test]
fn the_image_loads_the_program_at_its_entry() {
    let image = image();
    assert_eq!(image.len(), SIZE);
    assert_eq!(image, super::image());
    assert_eq!(field::<8>(&image, 24), 0x4020_0000, "e_entry");
    let (phoff, phnum) = (field::<8>(&image, 32) as usize, field::<2>(&image, 56));
    assert_eq!(phnum, 2, "e_phnum");
    // (type, flags, offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align)
    let header = |index: usize| {
        let base = phoff + 56 * index;
        (
            field::<4>(&image, base),
            field::<4>(&image, base + 4),
            field::<8>(&image, base + 8),
            field::<8>(&image, base + 16),
            field::<8>(&image, base + 24),
            field::<8>(&image, base + 32),
            field::<8>(&image, base + 40),
            field::<8>(&image, base + 48),
        )
    };
    assert_eq!(
        header(0),
        (1, 5, 0x1000, 0x4020_0000, 0x4020_0000, 0x7e, 0x7e, 0x1000),
        "PT_LOAD, read and execute: .text"
    );
    assert_eq!(
        header(1),
        (1, 4, 0x2000, 0x4020_1000, 0x4020_1000, 36, 36, 0x1000),
        "PT_LOAD, read-only: the build-id note"
    );
    let program: Vec<u64> = (0..18)
        .map(|index| field::<4>(&image, TEXT.start + 4 * index))
        .collect();
    assert_eq!(
        program,
        [
            0xd2a1_2000, // movz x0, #0x0900, lsl #16
            0x5280_6021, // movz w1, #0x301
            0xb900_3001, // str w1, [x0, #0x30]
            // adr x1, #0x3c: immlo 0 in bits 30:29, immhi 0x3c >> 2 = 0xf in
            // bits 23:5, Rd 1: 0x1000_0000 | 0xf << 5 | 1.
            0x1000_01e1,
            // movz x2, #54: sf 1, opc 10, hw 0, imm16 54 in bits 20:5, Rd 2:
            // 0xd280_0000 | 54 << 5 | 2.
            0xd280_06c2,
            0xb940_1803, // ldr w3, [x0, #0x18]
            0x372f_ffe3, // tbnz w3, #5, -4
            0x3840_1423, // ldrb w3, [x1], #1
            0xb900_0003, // str w3, [x0]
            0xf100_0442, // subs x2, x2, #1
            0x54ff_ff61, // b.ne -20
            0xb940_1803, // ldr w3, [x0, #0x18]
            0x371f_ffe3, // tbnz w3, #3, -4
            0x5280_0100, // movz w0, #8
            // movk w0, #0x8400, lsl #16: sf 0, opc 11, hw 1, imm16 0x8400,
            // Rd 0: 0x7280_0000 | 1 << 21 | 0x8400 << 5. With the line above,
            // w0 = 0x8400_0008, PSCI SYSTEM_OFF.
            0x72b0_8000,
            0xd400_0002, // hvc #0
            0xd503_207f, // wfi
            0x17ff_ffff, // b -4
        ]
    );
    assert_eq!(
        &image[0x1048..TEXT.end],
        b"krepi test image: PL011 output, then PSCI SYSTEM_OFF\r\n"
    );
    assert_eq!(&image[0x1048..TEXT.end], MESSAGE);
    assert_eq!(LOAD_ADDRESS, 0x4020_0000);
}

/// `write` creates a new file with the image, in whose symbol table the
/// symbol lookup of the fixture patching finds `_start` at the entry and
/// `message` after the program, and refuses an existing file, which it
/// leaves as it is.
#[test]
fn writing_refuses_an_existing_file() {
    let scratch = Scratch::new("test-elf");
    let path = scratch.path("test.elf");
    write(&path).expect("write the test image");
    assert_eq!(scratch.read("test.elf"), image());
    assert_eq!(symbol_address(&path, "_start"), Ok(0x4020_0000));
    assert_eq!(symbol_address(&path, "message"), Ok(0x4020_0048));
    std::fs::write(&path, b"kept").unwrap();
    assert_eq!(
        write(&path),
        Err(Failure(format!("{path:?}: File exists (os error 17)")))
    );
    assert_eq!(scratch.read("test.elf"), b"kept");
    let missing = scratch.path("missing/test.elf");
    assert_eq!(
        write(&missing),
        Err(Failure(format!(
            "{missing:?}: No such file or directory (os error 2)"
        )))
    );
}
