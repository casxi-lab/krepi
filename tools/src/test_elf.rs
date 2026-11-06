//! The test image: an AArch64 executable for QEMU virt that writes one line
//! to the PL011 UART and then powers the machine off.
//!
//! The program runs at EL1 with the MMU off from [`LOAD_ADDRESS`]. It
//! enables the UART of QEMU virt at `0x0900_0000`, writes [`MESSAGE`] byte by
//! byte, each once the transmit FIFO has room, waits until the UART is no
//! longer busy, and calls PSCI `SYSTEM_OFF` (function ID `0x8400_0008`)
//! through `hvc #0`. On QEMU virt without EL2 and EL3 and without firmware,
//! QEMU itself implements PSCI on the HVC conduit, so the call ends QEMU with
//! status 0. Should the call return, the program waits for interrupts
//! forever. The image runs only on QEMU virt: its addresses are QEMU's.
//!
//! Ordinary host code writes the image. The program is a list of reviewed
//! instruction words in their AArch64 encoding, and the ELF writer of the
//! `object` crate lays out and encodes the executable around it: the ELF
//! header, two program headers, five sections, among them the symbol table
//! and the string tables, and their headers. No assembler, compiler or
//! linker for a bare-metal target is involved. The first load segment, read
//! and execute, holds `.text`, the program followed by the message; the
//! second, read-only, holds the GNU build-id note, whose 20 bytes are the
//! start of the SHA-256 digest of `.text`. Each segment starts a 4 KiB page,
//! in the file and in memory. The symbol table holds the function `_start`
//! and the object `message`. The ELF reader of [`crate::elf`] accepts the
//! image.

use crate::Failure;
use crate::serial_capture::write_new;
use object::elf;
use object::write::elf::{FileHeader, ProgramHeader, SectionHeader, Sym, Writer};
use object::{Endianness, U32, bytes_of};
use sha2::{Digest, Sha256};
use std::path::Path;

/// The address at which the program is loaded and starts. QEMU's direct
/// boot of an ELF image places the device tree at the start of RAM,
/// `0x4000_0000`, below an image that lies above it; the 2 MiB in between
/// leave it room.
pub const LOAD_ADDRESS: u64 = 0x4020_0000;

/// The line that the program writes to the UART.
pub const MESSAGE: &[u8] = b"krepi test image: PL011 output, then PSCI SYSTEM_OFF\r\n";

/// The offset of the message from the start of `.text`: it follows the
/// program's 18 instructions.
const MESSAGE_OFFSET: u32 = 18 * 4;

/// The offset of `adr x1, message` from the start of `.text`.
const ADR_OFFSET: u32 = 0x0c;

const _: () = assert!(MESSAGE.len() < 1 << 16, "the length is a 16-bit immediate");

/// `adr x<rd>, #<offset>`: `0x1000_0000` with the low two bits of `offset`
/// in bits 30:29 (`immlo`), the rest in bits 23:5 (`immhi`), and `rd` in bits
/// 4:0.
const fn adr(rd: u32, offset: u32) -> u32 {
    0x1000_0000 | (offset & 3) << 29 | (offset >> 2 & 0x7_ffff) << 5 | rd
}

/// `movz x<rd>, #<value>`: `0xd280_0000` with the 16-bit `value` in bits
/// 20:5 and `rd` in bits 4:0.
const fn movz_x(rd: u32, value: u32) -> u32 {
    0xd280_0000 | (value & 0xffff) << 5 | rd
}

/// The program, one AArch64 instruction word for each 4 bytes from the start.
const PROGRAM: [u32; 18] = [
    0xd2a1_2000, // 0x00: movz x0, #0x0900, lsl #16    UART base 0x0900_0000
    0x5280_6021, // 0x04: movz w1, #0x301              UARTCR: UARTEN, TXE, RXE
    0xb900_3001, // 0x08: str w1, [x0, #0x30]          enable the UART
    adr(1, MESSAGE_OFFSET - ADR_OFFSET), // 0x0c: adr x1, message
    movz_x(2, MESSAGE.len() as u32), // 0x10: movz x2, #<length>
    0xb940_1803, // 0x14: ldr w3, [x0, #0x18]          UARTFR
    0x372f_ffe3, // 0x18: tbnz w3, #5, 0x14            wait while TXFF is set
    0x3840_1423, // 0x1c: ldrb w3, [x1], #1            next byte
    0xb900_0003, // 0x20: str w3, [x0]                 UARTDR
    0xf100_0442, // 0x24: subs x2, x2, #1
    0x54ff_ff61, // 0x28: b.ne 0x14
    0xb940_1803, // 0x2c: ldr w3, [x0, #0x18]          UARTFR
    0x371f_ffe3, // 0x30: tbnz w3, #3, 0x2c            wait while BUSY is set
    0x5280_0100, // 0x34: movz w0, #0x0008
    0x72b0_8000, // 0x38: movk w0, #0x8400, lsl #16    PSCI SYSTEM_OFF
    0xd400_0002, // 0x3c: hvc #0
    0xd503_207f, // 0x40: wfi
    0x17ff_ffff, // 0x44: b 0x40
];

/// The alignment of each load segment, in the file and in memory: one 4 KiB
/// page, so that the read-only note shares no page with the program.
const PAGE: u64 = 0x1000;

/// The length of the build-id: the start of the SHA-256 digest of `.text`,
/// as long as the SHA-1 build-id that the ELF reader requires.
const BUILD_ID_BYTES: usize = 20;

/// `.text`: the program, each instruction word little-endian, followed by
/// the message.
fn text() -> Vec<u8> {
    let mut text: Vec<u8> = PROGRAM.iter().flat_map(|word| word.to_le_bytes()).collect();
    text.extend_from_slice(MESSAGE);
    text
}

/// The GNU build-id note of `text`: the note header, the name `GNU` with its
/// terminating NUL, which fills four bytes, and the first 20 bytes of the
/// SHA-256 digest of `text`.
fn build_id_note(text: &[u8]) -> Vec<u8> {
    let endian = Endianness::Little;
    let header = elf::NoteHeader64 {
        n_namesz: U32::new(endian, elf::ELF_NOTE_GNU.len() as u32 + 1),
        n_descsz: U32::new(endian, BUILD_ID_BYTES as u32),
        n_type: U32::new(endian, elf::NT_GNU_BUILD_ID),
    };
    let mut note = bytes_of(&header).to_vec();
    note.extend_from_slice(elf::ELF_NOTE_GNU);
    note.push(0);
    note.extend_from_slice(&Sha256::digest(text)[..BUILD_ID_BYTES]);
    note
}

/// The bytes of the test image, the same on every call and every host:
/// 8,760 bytes with the pinned version of `object`.
pub fn image() -> Vec<u8> {
    layout().expect("the fixed names and sizes of the test image suit the ELF writer")
}

/// Writes the test image with the two-phase ELF writer of `object`. The
/// first phase reserves the section and symbol indices, the names and the
/// file range of each part in the order of the file; the second writes the
/// parts in the same order. Sections are 1 `.text`, 2 `.note.gnu.build-id`,
/// 3 `.symtab`, 4 `.strtab` and 5 `.shstrtab`.
fn layout() -> object::write::Result<Vec<u8>> {
    let text = text();
    let note = build_id_note(&text);
    let mut image = Vec::new();
    let mut writer = Writer::new(Endianness::Little, true, &mut image);
    writer.reserve_file_header();
    writer.reserve_program_headers(2);
    let text_name = writer.add_section_name(b".text");
    let text_index = writer.reserve_section_index();
    let note_name = writer.add_section_name(b".note.gnu.build-id");
    writer.reserve_section_index();
    let message_name = writer.add_string(b"message");
    let start_name = writer.add_string(b"_start");
    // Symbol 0 is the null symbol; the local object precedes the global
    // function, so the first global symbol is 2.
    writer.reserve_symbol_index(Some(text_index));
    writer.reserve_symbol_index(Some(text_index));
    writer.reserve_symtab_section_index();
    writer.reserve_strtab_section_index();
    writer.reserve_shstrtab_section_index();
    let text_offset = writer.reserve(text.len() as u64, PAGE);
    let note_offset = writer.reserve(note.len() as u64, PAGE);
    writer.reserve_symtab();
    writer.reserve_strtab()?;
    writer.reserve_shstrtab()?;
    writer.reserve_section_headers();

    // The note lies as far from the text in memory as in the file.
    let note_address = LOAD_ADDRESS + (note_offset - text_offset);
    let load = |p_flags, p_offset, address, size: usize| ProgramHeader {
        p_type: elf::PT_LOAD,
        p_flags,
        p_offset,
        p_vaddr: address,
        p_paddr: address,
        p_filesz: size as u64,
        p_memsz: size as u64,
        p_align: PAGE,
    };
    let symbol = |st_name, st_info, st_value, st_size| Sym {
        section: Some(text_index.0),
        st_name,
        st_info,
        st_other: elf::STV_DEFAULT.into(),
        st_shndx: elf::SHN_UNDEF,
        st_value,
        st_size,
    };
    writer.write_file_header(&FileHeader {
        os_abi: elf::ELFOSABI_NONE,
        abi_version: 0,
        e_type: elf::ET_EXEC,
        e_machine: elf::EM_AARCH64,
        e_entry: LOAD_ADDRESS,
        e_flags: elf::FileFlags(0),
    })?;
    writer.write_align_program_headers();
    writer.write_program_header(&load(
        elf::PF_R | elf::PF_X,
        text_offset,
        LOAD_ADDRESS,
        text.len(),
    ));
    writer.write_program_header(&load(elf::PF_R, note_offset, note_address, note.len()));
    writer.pad_until(text_offset);
    writer.write(&text);
    writer.pad_until(note_offset);
    writer.write(&note);
    writer.write_null_symbol();
    writer.write_symbol(&symbol(
        writer.string_offset(Some(message_name)),
        elf::STB_LOCAL | elf::STT_OBJECT,
        LOAD_ADDRESS + u64::from(MESSAGE_OFFSET),
        MESSAGE.len() as u64,
    ));
    writer.write_symbol(&symbol(
        writer.string_offset(Some(start_name)),
        elf::STB_GLOBAL | elf::STT_FUNC,
        LOAD_ADDRESS,
        u64::from(MESSAGE_OFFSET),
    ));
    writer.write_strtab();
    writer.write_shstrtab();
    writer.write_null_section_header();
    writer.write_section_header(&SectionHeader {
        sh_name: writer.section_name_offset(Some(text_name)),
        sh_type: elf::SHT_PROGBITS,
        sh_flags: elf::SHF_ALLOC | elf::SHF_EXECINSTR,
        sh_addr: LOAD_ADDRESS,
        sh_offset: text_offset,
        sh_size: text.len() as u64,
        sh_addralign: 4,
        ..SectionHeader::default()
    });
    writer.write_section_header(&SectionHeader {
        sh_name: writer.section_name_offset(Some(note_name)),
        sh_type: elf::SHT_NOTE,
        sh_flags: elf::SHF_ALLOC,
        sh_addr: note_address,
        sh_offset: note_offset,
        sh_size: note.len() as u64,
        sh_addralign: 4,
        ..SectionHeader::default()
    });
    writer.write_symtab_section_header(2);
    writer.write_strtab_section_header();
    writer.write_shstrtab_section_header();
    debug_assert_eq!(writer.len(), writer.reserved_len());
    Ok(image)
}

/// Writes [`image`] to the new file `path`, which must not exist. An
/// existing file is refused, `"<path>": File exists (os error 17)`, and
/// left as it is; another error names the path in the same way.
pub fn write(path: &Path) -> Result<(), Failure> {
    write_new(path, &image())
}

#[cfg(test)]
mod tests;
