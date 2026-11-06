//! Bounded ELF64 reading for diagnostics: the headers, section names, the
//! GNU build-id note and the function symbols of a little-endian AArch64
//! executable, and the patching of one checked word of a fixture image. This
//! is an offline reader of files on the host, not a loader.

use crate::Failure;
use std::path::Path;

pub const MAX_ELF_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_SECTIONS: usize = 4096;
pub const MAX_SYMBOLS: usize = 262_144;
pub const MAX_NAME_BYTES: usize = 4096;

/// A function symbol with the end of its section, for zero-size assembly
/// symbols.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    pub name: String,
    pub address: u64,
    pub size: u64,
    pub section_end: u64,
}

/// The verified bytes of one ELF with what symbolization needs from them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElfSnapshot {
    pub data: Vec<u8>,
    pub build_id: String,
    /// Sorted by address, then name.
    pub symbols: Vec<Symbol>,
    /// `[start, end)` file-backed ranges of executable load segments.
    pub executable: Vec<(u64, u64)>,
}

fn require(condition: bool, message: impl FnOnce() -> String) -> Result<(), Failure> {
    if condition {
        Ok(())
    } else {
        Err(Failure::new(message()))
    }
}

struct Reader<'a> {
    data: &'a [u8],
}

impl<'a> Reader<'a> {
    fn bounded(&self, offset: u64, size: u64, label: &str) -> Result<&'a [u8], Failure> {
        let length = self.data.len() as u64;
        require(offset <= length && size <= length - offset, || {
            format!("missing or truncated {label}")
        })?;
        Ok(&self.data[offset as usize..(offset + size) as usize])
    }

    fn u16(&self, offset: usize) -> u16 {
        u16::from_le_bytes(self.data[offset..offset + 2].try_into().expect("two bytes"))
    }

    fn u32(&self, offset: usize) -> u32 {
        u32::from_le_bytes(
            self.data[offset..offset + 4]
                .try_into()
                .expect("four bytes"),
        )
    }

    fn u64(&self, offset: usize) -> u64 {
        u64::from_le_bytes(
            self.data[offset..offset + 8]
                .try_into()
                .expect("eight bytes"),
        )
    }
}

/// A NUL-terminated name of at most `MAX_NAME_BYTES` bytes at `offset`.
fn string_at(strings: &[u8], offset: u64) -> Result<String, Failure> {
    require(offset < strings.len() as u64, || {
        "string offset outside table".to_string()
    })?;
    let start = offset as usize;
    let window = &strings[start..strings.len().min(start + MAX_NAME_BYTES + 1)];
    let end = window
        .iter()
        .position(|&b| b == 0)
        .ok_or_else(|| Failure::new("unterminated or oversized ELF name"))?;
    String::from_utf8(window[..end].to_vec())
        .map_err(|_| Failure::new("ELF name is not valid UTF-8"))
}

#[derive(Clone, Copy)]
struct Load {
    start: u64,
    end: u64,
    rights: u32,
    offset: u64,
    filesz: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Section {
    name: u32,
    kind: u32,
    flags: u64,
    addr: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    align: u64,
    entsize: u64,
}

/// Reads only the ELF64 headers, section names, GNU note and function symbols.
pub fn parse_elf(data: Vec<u8>) -> Result<ElfSnapshot, Failure> {
    require(data.len() <= MAX_ELF_BYTES, || {
        "ELF exceeds 64 MiB limit".to_string()
    })?;
    let r = Reader { data: &data };
    require(
        data.len() >= 64 && data[..7] == *b"\x7fELF\x02\x01\x01",
        || "expected little-endian ELF64".to_string(),
    )?;
    let (kind, machine, version) = (r.u16(16), r.u16(18), r.u32(20));
    let phoff = r.u64(32);
    let shoff = r.u64(40);
    let flags = r.u32(48);
    let (ehsize, phsize, phnum, shsize, shnum, names) = (
        r.u16(52),
        r.u16(54),
        r.u16(56) as u64,
        r.u16(58),
        r.u16(60) as u64,
        r.u16(62) as u64,
    );
    require(
        (kind, machine, version, flags, ehsize) == (2, 183, 1, 0, 64),
        || "expected AArch64 executable".to_string(),
    )?;
    require(
        phsize == 56 && phnum > 0 && phnum <= 64 && phoff >= 64,
        || "invalid program headers".to_string(),
    )?;
    r.bounded(phoff, 56 * phnum, "program headers")?;
    let mut loads: Vec<Load> = Vec::new();
    for index in 0..phnum {
        let base = (phoff + 56 * index) as usize;
        let (ptype, permissions) = (r.u32(base), r.u32(base + 4));
        let (offset, va, filesz, memsz) = (
            r.u64(base + 8),
            r.u64(base + 16),
            r.u64(base + 32),
            r.u64(base + 40),
        );
        require(ptype != 2 && ptype != 3, || {
            "dynamic ELF is unsupported".to_string()
        })?;
        if ptype == 1 {
            require(filesz <= memsz && va <= u64::MAX - memsz, || {
                "invalid load range".to_string()
            })?;
            r.bounded(offset, filesz, "load segment")?;
            require(permissions & 1 == 0 || permissions & 2 == 0, || {
                "writable executable segment".to_string()
            })?;
            loads.push(Load {
                start: va,
                end: va + memsz,
                rights: permissions,
                offset,
                filesz,
            });
        }
    }
    let executable: Vec<(u64, u64)> = loads
        .iter()
        .filter(|load| load.rights & 1 != 0)
        .map(|load| (load.start, load.start + load.filesz))
        .collect();
    require(!executable.is_empty(), || {
        "missing executable load segment".to_string()
    })?;
    require(
        shsize == 64
            && shnum > 0
            && shnum <= MAX_SECTIONS as u64
            && shoff >= 64
            && names > 0
            && names < shnum,
        || "missing or unsupported section headers".to_string(),
    )?;
    r.bounded(shoff, 64 * shnum, "section headers")?;
    let sections: Vec<Section> = (0..shnum)
        .map(|index| {
            let base = (shoff + 64 * index) as usize;
            Section {
                name: r.u32(base),
                kind: r.u32(base + 4),
                flags: r.u64(base + 8),
                addr: r.u64(base + 16),
                offset: r.u64(base + 24),
                size: r.u64(base + 32),
                link: r.u32(base + 40),
                info: r.u32(base + 44),
                align: r.u64(base + 48),
                entsize: r.u64(base + 56),
            }
        })
        .collect();
    let null = Section {
        name: 0,
        kind: 0,
        flags: 0,
        addr: 0,
        offset: 0,
        size: 0,
        link: 0,
        info: 0,
        align: 0,
        entsize: 0,
    };
    require(sections[0] == null, || "invalid null section".to_string())?;
    let table = sections[names as usize];
    require(table.kind == 3, || "invalid section-name table".to_string())?;
    let strings = r.bounded(table.offset, table.size, "section names")?;
    let mut named: Vec<(String, Section)> = Vec::new();
    let mut symtabs: Vec<Section> = Vec::new();
    for section in &sections[1..] {
        let name = string_at(strings, u64::from(section.name))?;
        require(!named.iter().any(|(known, _)| *known == name), || {
            "duplicate section name".to_string()
        })?;
        if section.kind != 8 {
            r.bounded(section.offset, section.size, &format!("section {name}"))?;
        }
        if section.kind == 2 {
            symtabs.push(*section);
        }
        named.push((name, *section));
    }
    let note = named
        .iter()
        .find(|(name, _)| name == ".note.gnu.build-id")
        .map(|(_, section)| *section)
        .ok_or_else(|| Failure::new("missing GNU build-id note"))?;
    require(
        note.kind == 7
            && note.flags == 2
            && note.size == 36
            && (4..=4096).contains(&note.align)
            && note.align & (note.align - 1) == 0,
        || "expected allocated, read-only 36-byte GNU SHA1 build-id note".to_string(),
    )?;
    let raw_note = r.bounded(note.offset, note.size, "GNU build-id note")?;
    let words = (
        u32::from_le_bytes(raw_note[0..4].try_into().expect("word")),
        u32::from_le_bytes(raw_note[4..8].try_into().expect("word")),
        u32::from_le_bytes(raw_note[8..12].try_into().expect("word")),
    );
    require(words == (4, 20, 3) && raw_note[12..16] == *b"GNU\0", || {
        "invalid GNU SHA1 build-id note".to_string()
    })?;
    // The note address is an unchecked header field, so the sums that place it
    // in a segment are checked rather than allowed to overflow.
    require(
        loads.iter().any(|load| {
            load.rights == 4
                && load.start <= note.addr
                && note.addr.checked_add(36).is_some_and(|end| end <= load.end)
                && load.offset.checked_add(note.addr - load.start) == Some(note.offset)
                && note.addr - load.start + 36 <= load.filesz
        }),
        || "build-id note is not mapped read-only".to_string(),
    )?;
    let build_id: String = raw_note[16..36]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    require(build_id != "0".repeat(40), || {
        "empty GNU build-id descriptor".to_string()
    })?;
    require(symtabs.len() == 1, || {
        "one unstripped symbol table is required".to_string()
    })?;
    let symtab = symtabs[0];
    require(
        symtab.entsize == 24
            && symtab.size.is_multiple_of(24)
            && symtab.size / 24 <= MAX_SYMBOLS as u64,
        || "invalid or oversized symbol table".to_string(),
    )?;
    require(
        symtab.link > 0
            && u64::from(symtab.link) < shnum
            && sections[symtab.link as usize].kind == 3,
        || "invalid symbol string table".to_string(),
    )?;
    let link = sections[symtab.link as usize];
    let strings = r.bounded(link.offset, link.size, "symbol strings")?;
    let mut symbols: Vec<Symbol> = Vec::new();
    let mut offset = symtab.offset;
    while offset < symtab.offset + symtab.size {
        let base = offset as usize;
        let name_offset = r.u32(base);
        let info = data[base + 4];
        let index = u64::from(r.u16(base + 6));
        let address = r.u64(base + 8);
        let size = r.u64(base + 16);
        offset += 24;
        let name = string_at(strings, u64::from(name_offset))?;
        if info & 15 != 2 || index == 0 || index >= shnum {
            continue;
        }
        let section = sections[index as usize];
        let end = section.addr.wrapping_add(section.size);
        require(
            section.flags & 6 == 6
                && section.addr <= address
                && address < end
                && size <= end - address,
            || "function symbol is outside executable section".to_string(),
        )?;
        require(
            executable
                .iter()
                .any(|&(start, stop)| start <= address && address < stop && address + size <= stop),
            || "function symbol is outside executable segment".to_string(),
        )?;
        symbols.push(Symbol {
            name,
            address,
            size,
            section_end: end,
        });
    }
    require(!symbols.is_empty(), || {
        "missing function symbols".to_string()
    })?;
    symbols.sort_by(|a, b| (a.address, &a.name).cmp(&(b.address, &b.name)));
    Ok(ElfSnapshot {
        data,
        build_id,
        symbols,
        executable,
    })
}

/// Reads at most `MAX_ELF_BYTES + 1` bytes and parses them.
pub fn read_elf(path: &Path) -> Result<ElfSnapshot, Failure> {
    use std::io::Read;
    let mut file = std::fs::File::open(path)?;
    let mut data = Vec::new();
    file.by_ref()
        .take(MAX_ELF_BYTES as u64 + 1)
        .read_to_end(&mut data)?;
    parse_elf(data)
}

/// The function symbol containing `address`, preferring the highest start,
/// then sized symbols, then the greatest name. A zero-size assembly function
/// ends at the next function or at its section end.
pub fn symbol_at(snapshot: &ElfSnapshot, address: u64) -> Option<&Symbol> {
    let starts: Vec<u64> = snapshot.symbols.iter().map(|s| s.address).collect();
    let upper = starts.partition_point(|&start| start <= address);
    snapshot.symbols[..upper]
        .iter()
        .filter(|symbol| {
            let mut stop = if symbol.size != 0 {
                symbol.address + symbol.size
            } else {
                symbol.section_end
            };
            if symbol.size == 0 {
                let following = starts.partition_point(|&start| start <= symbol.address);
                if following < starts.len() {
                    stop = stop.min(starts[following]);
                }
            }
            address < stop
        })
        .max_by(|a, b| (a.address, a.size != 0, &a.name).cmp(&(b.address, b.size != 0, &b.name)))
}

// --- fixture patching -------------------------------------------------------------

const FIXTURE_MAX_BYTES: usize = 16 * 1024 * 1024;

/// Reads a diagnostic fixture image within the 16 MiB bound.
fn read_fixture(source: &Path) -> Result<Vec<u8>, Failure> {
    use std::io::Read;
    let mut file = std::fs::File::open(source)?;
    let mut data = Vec::new();
    file.by_ref()
        .take(FIXTURE_MAX_BYTES as u64 + 1)
        .read_to_end(&mut data)?;
    require(data.len() >= 64 && data.len() <= FIXTURE_MAX_BYTES, || {
        "ELF outside the fixture size bound".to_string()
    })?;
    Ok(data)
}

/// The address of `symbol` in `source`, which must be allocated.
pub fn symbol_address(source: &Path, symbol: &str) -> Result<u64, Failure> {
    let patched = patch_symbol(source, None, symbol, 0, 0, 0)?;
    patched
        .get("address")
        .and_then(crate::report::Value::as_u64)
        .ok_or_else(|| Failure::new("Missing or duplicated target symbol"))
}

/// Patches one checked file-backed `u32` at `symbol` in a fresh ELF fixture,
/// or, with no destination, only locates the symbol.
pub fn patch_symbol(
    source: &Path,
    destination: Option<&Path>,
    symbol: &str,
    expected: u32,
    replacement: u32,
    permission: u32,
) -> Result<crate::report::Value, Failure> {
    require(destination.is_none_or(|d| !d.exists()), || {
        "Negative ELF destination already exists".to_string()
    })?;
    let mut data = read_fixture(source)?;
    require(data[..7] == *b"\x7fELF\x02\x01\x01", || {
        "Expected little-endian ELF64".to_string()
    })?;
    let r = Reader { data: &data };
    require(
        (r.u16(16), r.u16(18), r.u32(20)) == (2, 183, 1) && r.u16(52) == 64,
        || "Expected AArch64 executable ELF".to_string(),
    )?;
    let (phoff, shoff) = (r.u64(32), r.u64(40));
    let (phsize, phnum, shsize, shnum) = (r.u16(54), r.u16(56) as u64, r.u16(58), r.u16(60) as u64);
    require(
        phsize == 56 && (1..=32).contains(&phnum) && shsize == 64 && (1..=4096).contains(&shnum),
        || "Invalid bounded ELF header tables".to_string(),
    )?;
    let region = |offset: u64, size: u64| -> Result<(), Failure> {
        let length = data.len() as u64;
        require(offset <= length && size <= length - offset, || {
            "ELF range exceeds file".to_string()
        })
    };
    region(phoff, 56 * phnum)?;
    region(shoff, 64 * shnum)?;
    let sections: Vec<[u64; 10]> = (0..shnum)
        .map(|index| {
            let base = (shoff + 64 * index) as usize;
            [
                u64::from(r.u32(base)),
                u64::from(r.u32(base + 4)),
                r.u64(base + 8),
                r.u64(base + 16),
                r.u64(base + 24),
                r.u64(base + 32),
                u64::from(r.u32(base + 40)),
                u64::from(r.u32(base + 44)),
                r.u64(base + 48),
                r.u64(base + 56),
            ]
        })
        .collect();
    let symtabs: Vec<&[u64; 10]> = sections.iter().filter(|s| s[1] == 2).collect();
    require(symtabs.len() == 1, || {
        "Expected one ELF symbol table".to_string()
    })?;
    let symtab = *symtabs[0];
    require(
        symtab[9] == 24
            && symtab[5].is_multiple_of(24)
            && symtab[5] / 24 <= 65536
            && symtab[6] > 0
            && symtab[6] < shnum,
        || "Invalid ELF symbol table".to_string(),
    )?;
    let strings = sections[symtab[6] as usize];
    require(strings[1] == 3, || {
        "Symbol names do not reference a string table".to_string()
    })?;
    region(strings[4], strings[5])?;
    region(symtab[4], symtab[5])?;
    let names = &data[strings[4] as usize..(strings[4] + strings[5]) as usize];
    let mut target = symbol.as_bytes().to_vec();
    target.push(0);
    let mut matches: Vec<([u64; 10], u64)> = Vec::new();
    let mut offset = symtab[4];
    while offset < symtab[4] + symtab[5] {
        let base = offset as usize;
        let name = r.u32(base) as usize;
        let section_index = u64::from(r.u16(base + 6));
        let (value, size) = (r.u64(base + 8), r.u64(base + 16));
        offset += 24;
        require(name < names.len(), || {
            "ELF symbol name is out of bounds".to_string()
        })?;
        if names[name..].starts_with(&target) {
            require(
                section_index > 0 && section_index < shnum && (size == 0 || size >= 4),
                || "Undefined or short target symbol".to_string(),
            )?;
            matches.push((sections[section_index as usize], value));
        }
    }
    require(matches.len() == 1, || {
        "Missing or duplicated target symbol".to_string()
    })?;
    let (section, address) = matches[0];
    let mut result = crate::report::Value::object();
    let Some(destination) = destination else {
        require(
            section[2] & 2 != 0
                && section[3] <= address
                && address < section[3].wrapping_add(section[5]),
            || "Symbol is outside its allocated section".to_string(),
        )?;
        result.set("address", address);
        return Ok(result);
    };
    require(
        address.is_multiple_of(4)
            && address.checked_add(4).is_some()
            && section[1] == 1
            && section[2] & 2 != 0
            && section[3] <= address
            && address + 4 <= section[3].wrapping_add(section[5]),
        || "Target symbol is not aligned, allocated, and file-backed".to_string(),
    )?;
    // The section's file offset is not range-checked, so a sum past the
    // largest offset agrees with no load mapping.
    let section_offset = section[4].checked_add(address - section[3]);
    let mut candidates: Vec<u64> = Vec::new();
    for index in 0..phnum {
        let base = (phoff + 56 * index) as usize;
        if r.u32(base) != 1 {
            continue;
        }
        let flags = u64::from(r.u32(base + 4));
        let (seg_offset, virtual_address, physical, file_size, memory_size) = (
            r.u64(base + 8),
            r.u64(base + 16),
            r.u64(base + 24),
            r.u64(base + 32),
            r.u64(base + 40),
        );
        require(
            file_size <= memory_size && virtual_address.checked_add(memory_size).is_some(),
            || "Invalid ELF load bounds".to_string(),
        )?;
        region(seg_offset, file_size)?;
        if virtual_address <= address && address + 4 <= virtual_address + file_size {
            require(
                physical == virtual_address
                    && flags & u64::from(permission) == u64::from(permission),
                || "Target load identity or permissions disagree".to_string(),
            )?;
            // The word lies in the file-backed part, which the region check
            // placed inside the file, so the sum stays below the file length.
            candidates.push(seg_offset + (address - virtual_address));
        }
    }
    require(
        section_offset.is_some_and(|offset| candidates == [offset]),
        || "Target section and unique load mapping disagree".to_string(),
    )?;
    let file_offset = candidates[0] as usize;
    let original = u32::from_le_bytes(
        data[file_offset..file_offset + 4]
            .try_into()
            .expect("four bytes"),
    );
    require(original == expected, || {
        "Target symbol contents do not match the intended fixture".to_string()
    })?;
    let before_hash = crate::sha256::hex(&data);
    data[file_offset..file_offset + 4].copy_from_slice(&replacement.to_le_bytes());
    std::fs::write(destination, &data)?;
    result.set("symbol", symbol);
    result.set("address", address);
    result.set("file_offset", file_offset);
    result.set("before", format!("{expected:#x}"));
    result.set("after", format!("{replacement:#x}"));
    result.set(
        "file",
        destination
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default(),
    );
    result.set("source_sha256", before_hash);
    result.set("sha256", crate::sha256::hex(&data));
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::report::Value;
    use crate::scratch::Scratch;

    const TEXT_ADDR: u64 = 0x4020_0000;
    const NOTE_ADDR: u64 = 0x4030_0000;
    const TEXT_OFF: usize = 0x1000;
    const NOTE_OFF: usize = 0x2000;
    const SYMTAB_OFF: usize = 0x2100;
    const STRTAB_OFF: usize = 0x2200;
    const SHSTRTAB_OFF: usize = 0x2300;
    const SHOFF: usize = 0x3000;
    const BUILD_ID: &str = "0102030405060708090a0b0c0d0e0f1011121314";

    fn put<const N: usize>(data: &mut [u8], offset: usize, bytes: [u8; N]) {
        data[offset..offset + N].copy_from_slice(&bytes);
    }

    fn section(data: &mut [u8], index: usize, fields: [u64; 10]) {
        let base = SHOFF + index * 64;
        put(data, base, (fields[0] as u32).to_le_bytes());
        put(data, base + 4, (fields[1] as u32).to_le_bytes());
        put(data, base + 8, fields[2].to_le_bytes());
        put(data, base + 16, fields[3].to_le_bytes());
        put(data, base + 24, fields[4].to_le_bytes());
        put(data, base + 32, fields[5].to_le_bytes());
        put(data, base + 40, (fields[6] as u32).to_le_bytes());
        put(data, base + 44, (fields[7] as u32).to_le_bytes());
        put(data, base + 48, fields[8].to_le_bytes());
        put(data, base + 56, fields[9].to_le_bytes());
    }

    fn symbol(
        data: &mut [u8],
        index: usize,
        name: u32,
        info: u8,
        shndx: u16,
        value: u64,
        size: u64,
    ) {
        let base = SYMTAB_OFF + index * 24;
        put(data, base, name.to_le_bytes());
        data[base + 4] = info;
        put(data, base + 6, shndx.to_le_bytes());
        put(data, base + 8, value.to_le_bytes());
        put(data, base + 16, size.to_le_bytes());
    }

    /// A minimal AArch64 ELF64: one executable load segment holding `.text`,
    /// one read-only segment holding the GNU build-id note, and four symbols:
    /// `kernel_main` (0x40 bytes), a zero-size `asm_entry` ending at
    /// `after_asm`, and a data object that is not a function.
    fn synthetic_elf() -> Vec<u8> {
        let mut data = vec![0u8; SHOFF + 6 * 64];
        data[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        put(&mut data, 16, 2u16.to_le_bytes());
        put(&mut data, 18, 183u16.to_le_bytes());
        put(&mut data, 20, 1u32.to_le_bytes());
        put(&mut data, 24, TEXT_ADDR.to_le_bytes());
        put(&mut data, 32, 64u64.to_le_bytes());
        put(&mut data, 40, (SHOFF as u64).to_le_bytes());
        put(&mut data, 52, 64u16.to_le_bytes());
        put(&mut data, 54, 56u16.to_le_bytes());
        put(&mut data, 56, 2u16.to_le_bytes());
        put(&mut data, 58, 64u16.to_le_bytes());
        put(&mut data, 60, 6u16.to_le_bytes());
        put(&mut data, 62, 5u16.to_le_bytes());
        for (index, (flags, offset, addr, size)) in [
            (5u32, TEXT_OFF, TEXT_ADDR, 0x100u64),
            (4u32, NOTE_OFF, NOTE_ADDR, 0x40),
        ]
        .into_iter()
        .enumerate()
        {
            let base = 64 + index * 56;
            put(&mut data, base, 1u32.to_le_bytes());
            put(&mut data, base + 4, flags.to_le_bytes());
            put(&mut data, base + 8, (offset as u64).to_le_bytes());
            put(&mut data, base + 16, addr.to_le_bytes());
            put(&mut data, base + 24, addr.to_le_bytes());
            put(&mut data, base + 32, size.to_le_bytes());
            put(&mut data, base + 40, size.to_le_bytes());
            put(&mut data, base + 48, 0x1000u64.to_le_bytes());
        }
        put(&mut data, NOTE_OFF, 4u32.to_le_bytes());
        put(&mut data, NOTE_OFF + 4, 20u32.to_le_bytes());
        put(&mut data, NOTE_OFF + 8, 3u32.to_le_bytes());
        data[NOTE_OFF + 12..NOTE_OFF + 16].copy_from_slice(b"GNU\0");
        for (index, byte) in (1u8..=20).enumerate() {
            data[NOTE_OFF + 16 + index] = byte;
        }
        let strtab = b"\0kernel_main\0asm_entry\0after_asm\0data_obj\0";
        data[STRTAB_OFF..STRTAB_OFF + strtab.len()].copy_from_slice(strtab);
        let shstrtab = b"\0.text\0.note.gnu.build-id\0.symtab\0.strtab\0.shstrtab\0";
        data[SHSTRTAB_OFF..SHSTRTAB_OFF + shstrtab.len()].copy_from_slice(shstrtab);
        symbol(&mut data, 1, 1, 0x12, 1, TEXT_ADDR, 0x40);
        symbol(&mut data, 2, 13, 0x12, 1, TEXT_ADDR + 0x40, 0);
        symbol(&mut data, 3, 23, 0x12, 1, TEXT_ADDR + 0x80, 0x20);
        symbol(&mut data, 4, 33, 0x11, 1, TEXT_ADDR + 0xc0, 8);
        section(
            &mut data,
            1,
            [1, 1, 6, TEXT_ADDR, TEXT_OFF as u64, 0x100, 0, 0, 4, 0],
        );
        section(
            &mut data,
            2,
            [7, 7, 2, NOTE_ADDR, NOTE_OFF as u64, 36, 0, 0, 4, 0],
        );
        section(
            &mut data,
            3,
            [26, 2, 0, 0, SYMTAB_OFF as u64, 5 * 24, 4, 0, 8, 24],
        );
        section(
            &mut data,
            4,
            [
                34,
                3,
                0,
                0,
                STRTAB_OFF as u64,
                strtab.len() as u64,
                0,
                0,
                1,
                0,
            ],
        );
        section(
            &mut data,
            5,
            [
                42,
                3,
                0,
                0,
                SHSTRTAB_OFF as u64,
                shstrtab.len() as u64,
                0,
                0,
                1,
                0,
            ],
        );
        data
    }

    fn mutated(offset: usize, bytes: &[u8]) -> Vec<u8> {
        let mut data = synthetic_elf();
        data[offset..offset + bytes.len()].copy_from_slice(bytes);
        data
    }

    fn message(error: Result<impl std::fmt::Debug, Failure>) -> String {
        match error {
            Err(Failure(message)) => message,
            Ok(value) => panic!("unexpected success: {value:?}"),
        }
    }

    #[test]
    fn a_synthetic_image_yields_its_build_id_segments_and_function_symbols() {
        let snapshot = parse_elf(synthetic_elf()).unwrap();
        assert_eq!(snapshot.build_id, BUILD_ID);
        let end = TEXT_ADDR + 0x100;
        // The data object is not a function symbol.
        assert_eq!(
            snapshot.symbols,
            [
                Symbol {
                    name: "kernel_main".to_string(),
                    address: TEXT_ADDR,
                    size: 0x40,
                    section_end: end,
                },
                Symbol {
                    name: "asm_entry".to_string(),
                    address: TEXT_ADDR + 0x40,
                    size: 0,
                    section_end: end,
                },
                Symbol {
                    name: "after_asm".to_string(),
                    address: TEXT_ADDR + 0x80,
                    size: 0x20,
                    section_end: end,
                },
            ]
        );
        assert_eq!(snapshot.executable, [(TEXT_ADDR, end)]);
        assert_eq!(snapshot.data, synthetic_elf());
    }

    #[test]
    fn an_address_resolves_to_the_function_that_contains_it() {
        let snapshot = parse_elf(synthetic_elf()).unwrap();
        let name = |address: u64| symbol_at(&snapshot, address).map(|s| s.name.clone());
        assert_eq!(name(TEXT_ADDR).as_deref(), Some("kernel_main"));
        assert_eq!(name(TEXT_ADDR + 0x3c).as_deref(), Some("kernel_main"));
        // A sized function ends where the zero-size one after it starts, and a
        // zero-size assembly function ends where the next function starts.
        assert_eq!(name(TEXT_ADDR + 0x40).as_deref(), Some("asm_entry"));
        assert_eq!(name(TEXT_ADDR + 0x44).as_deref(), Some("asm_entry"));
        assert_eq!(name(TEXT_ADDR + 0x80).as_deref(), Some("after_asm"));
        assert_eq!(name(TEXT_ADDR + 0x90).as_deref(), Some("after_asm"));
        // Past the end of a sized function, and outside every function.
        assert_eq!(name(TEXT_ADDR + 0xa0), None);
        assert_eq!(name(TEXT_ADDR + 0xf0), None);
        assert_eq!(name(0), None);
    }

    #[test]
    fn a_malformed_image_is_rejected_with_its_reason() {
        let note = SHOFF + 2 * 64;
        let rodata = 64 + 56;
        // The read-only segment ends at the top of the address space, and the
        // note address lies inside it, but not where the note's file offset is.
        let mut beyond = synthetic_elf();
        put(&mut beyond, rodata + 16, (u64::MAX - 100).to_le_bytes());
        put(&mut beyond, rodata + 40, 100u64.to_le_bytes());
        put(&mut beyond, note + 16, (u64::MAX - 50).to_le_bytes());
        let cases = [
            // Note addresses whose placement sums exceed 64 bits.
            (
                mutated(note + 16, &(u64::MAX - 8).to_le_bytes()),
                "build-id note is not mapped read-only",
            ),
            (beyond, "build-id note is not mapped read-only"),
            (
                mutated(note, &0u32.to_le_bytes()),
                "missing GNU build-id note",
            ),
            (
                mutated(note + 4, &1u32.to_le_bytes()),
                "expected allocated, read-only 36-byte GNU SHA1 build-id note",
            ),
            (
                mutated(note + 8, &3u64.to_le_bytes()),
                "expected allocated, read-only 36-byte GNU SHA1 build-id note",
            ),
            (
                mutated(note + 48, &2u64.to_le_bytes()),
                "expected allocated, read-only 36-byte GNU SHA1 build-id note",
            ),
            (
                mutated(NOTE_OFF + 4, &16u32.to_le_bytes()),
                "invalid GNU SHA1 build-id note",
            ),
            (
                mutated(NOTE_OFF + 12, &[0, 0, 0, 0]),
                "invalid GNU SHA1 build-id note",
            ),
            (
                mutated(NOTE_OFF + 16, &[0u8; 20]),
                "empty GNU build-id descriptor",
            ),
            (
                mutated(note + 16, &TEXT_ADDR.to_le_bytes()),
                "build-id note is not mapped read-only",
            ),
            (
                mutated(60, &((MAX_SECTIONS + 1) as u16).to_le_bytes()),
                "missing or unsupported section headers",
            ),
            (
                mutated(SHOFF + 64, &0xffff_ffffu32.to_le_bytes()),
                "string offset outside table",
            ),
            (
                mutated(SHOFF + 3 * 64 + 40, &6u32.to_le_bytes()),
                "invalid symbol string table",
            ),
            (
                mutated(64 + 4, &7u32.to_le_bytes()),
                "writable executable segment",
            ),
            (
                mutated(SYMTAB_OFF + 24 + 8, &(TEXT_ADDR + 0x100).to_le_bytes()),
                "function symbol is outside executable section",
            ),
        ];
        for (data, expected) in cases {
            assert_eq!(message(parse_elf(data)), expected);
        }
        for (length, expected) in [
            (63, "expected little-endian ELF64"),
            (64 + 55, "missing or truncated program headers"),
            (SHOFF + 6 * 64 - 1, "missing or truncated section headers"),
        ] {
            assert_eq!(
                message(parse_elf(synthetic_elf()[..length].to_vec())),
                expected,
                "{length}"
            );
        }
        assert_eq!(
            message(parse_elf(vec![0; MAX_ELF_BYTES + 1])),
            "ELF exceeds 64 MiB limit"
        );
        // A note at the start of a read-only segment that ends at the top of
        // the address space is still mapped.
        let mut top = synthetic_elf();
        put(&mut top, rodata + 16, (u64::MAX - 0x40).to_le_bytes());
        put(&mut top, note + 16, (u64::MAX - 0x40).to_le_bytes());
        assert_eq!(parse_elf(top).map(|s| s.build_id), Ok(BUILD_ID.to_string()));
    }

    #[test]
    fn a_file_is_read_and_parsed_like_its_bytes() {
        let scratch = Scratch::new("elf-read");
        let path = scratch.write("image.elf", &synthetic_elf());
        let snapshot = read_elf(&path).unwrap();
        assert_eq!(snapshot, parse_elf(synthetic_elf()).unwrap());
        let main = snapshot
            .symbols
            .iter()
            .find(|s| s.name == "kernel_main")
            .expect("kernel_main")
            .address;
        assert_eq!(
            symbol_at(&snapshot, main).map(|s| s.name.as_str()),
            Some("kernel_main")
        );
        // A file beyond the limit is read only to one byte past it.
        let large = scratch.path("large.elf");
        std::fs::File::create(&large)
            .and_then(|file| file.set_len(MAX_ELF_BYTES as u64 + 4096))
            .unwrap();
        assert_eq!(message(read_elf(&large)), "ELF exceeds 64 MiB limit");
        // A file that cannot be opened fails with the text of its error.
        let missing = scratch.path("missing.elf");
        let error = std::fs::File::open(&missing).unwrap_err();
        assert_eq!(read_elf(&missing), Err(Failure::from(error)));
    }

    #[test]
    fn a_symbol_address_is_found_only_for_one_allocated_symbol() {
        let scratch = Scratch::new("elf-address");
        let path = scratch.write("image.elf", &synthetic_elf());
        assert_eq!(symbol_address(&path, "kernel_main"), Ok(TEXT_ADDR));
        assert_eq!(symbol_address(&path, "data_obj"), Ok(TEXT_ADDR + 0xc0));
        let missing = Err(Failure::new("Missing or duplicated target symbol"));
        // A name matches whole, never as a prefix.
        assert_eq!(symbol_address(&path, "kernel"), missing);
        assert_eq!(symbol_address(&path, "absent"), missing);
        let mut duplicated = synthetic_elf();
        put(&mut duplicated, SYMTAB_OFF + 2 * 24, 1u32.to_le_bytes());
        let duplicated = scratch.write("duplicated.elf", &duplicated);
        assert_eq!(symbol_address(&duplicated, "kernel_main"), missing);
        let outside = scratch.write(
            "outside.elf",
            &mutated(SYMTAB_OFF + 4 * 24 + 8, &(TEXT_ADDR + 0x100).to_le_bytes()),
        );
        assert_eq!(
            message(symbol_address(&outside, "data_obj")),
            "Symbol is outside its allocated section"
        );
        let short = scratch.write("short.elf", &synthetic_elf()[..63]);
        assert_eq!(
            message(symbol_address(&short, "kernel_main")),
            "ELF outside the fixture size bound"
        );
    }

    #[test]
    fn a_patch_replaces_one_checked_word_in_a_new_file() {
        let scratch = Scratch::new("elf-patch");
        let source = scratch.write("image.elf", &synthetic_elf());
        let destination = scratch.path("patched.elf");
        let nop = 0xd503_201fu32;
        let result = patch_symbol(&source, Some(&destination), "kernel_main", 0, nop, 5).unwrap();
        let mut patched = synthetic_elf();
        patched[TEXT_OFF..TEXT_OFF + 4].copy_from_slice(&nop.to_le_bytes());
        assert_eq!(std::fs::read(&destination).unwrap(), patched);
        assert_eq!(std::fs::read(&source).unwrap(), synthetic_elf());
        let mut expected = Value::object();
        expected.set("symbol", "kernel_main");
        expected.set("address", TEXT_ADDR);
        expected.set("file_offset", TEXT_OFF);
        expected.set("before", "0x0");
        expected.set("after", "0xd503201f");
        expected.set("file", "patched.elf");
        expected.set("source_sha256", crate::sha256::hex(&synthetic_elf()));
        expected.set("sha256", crate::sha256::hex(&patched));
        assert_eq!(result, expected);
    }

    #[test]
    fn a_word_on_the_top_page_of_the_address_space_is_patched() {
        let scratch = Scratch::new("elf-top");
        let top = 0xffff_ffff_ffff_f000u64;
        let mut image = synthetic_elf();
        // The text segment, its section and `kernel_main` move to the top
        // page, where an address plus a file offset exceeds 64 bits.
        put(&mut image, 64 + 16, top.to_le_bytes());
        put(&mut image, 64 + 24, top.to_le_bytes());
        put(&mut image, SHOFF + 64 + 16, top.to_le_bytes());
        put(&mut image, SYMTAB_OFF + 24 + 8, top.to_le_bytes());
        let source = scratch.write("top.elf", &image);
        assert_eq!(symbol_address(&source, "kernel_main"), Ok(top));
        let destination = scratch.path("patched.elf");
        let nop = 0xd503_201fu32;
        let result = patch_symbol(&source, Some(&destination), "kernel_main", 0, nop, 5).unwrap();
        assert_eq!(result.get("address").and_then(Value::as_u64), Some(top));
        assert_eq!(
            result.get("file_offset").and_then(Value::as_u64),
            Some(TEXT_OFF as u64)
        );
        image[TEXT_OFF..TEXT_OFF + 4].copy_from_slice(&nop.to_le_bytes());
        assert_eq!(std::fs::read(&destination).unwrap(), image);
    }

    #[test]
    fn a_patch_is_refused_unless_every_check_holds() {
        let scratch = Scratch::new("elf-refuse");
        let source = scratch.write("image.elf", &synthetic_elf());
        let refused = |source: &Path, name: &str, symbol: &str, expected: u32, permission: u32| {
            let destination = scratch.path(name);
            let text = message(patch_symbol(
                source,
                Some(&destination),
                symbol,
                expected,
                1,
                permission,
            ));
            assert!(!destination.exists(), "{name} was written");
            text
        };
        // An existing destination is never overwritten.
        let existing = scratch.write("existing.elf", b"keep");
        assert_eq!(
            message(patch_symbol(
                &source,
                Some(&existing),
                "kernel_main",
                0,
                1,
                5
            )),
            "Negative ELF destination already exists"
        );
        assert_eq!(std::fs::read(&existing).unwrap(), b"keep");
        assert_eq!(
            refused(&source, "contents.elf", "kernel_main", 1, 5),
            "Target symbol contents do not match the intended fixture"
        );
        // The load segment is readable and executable but not writable.
        assert_eq!(
            refused(&source, "rights.elf", "kernel_main", 0, 2),
            "Target load identity or permissions disagree"
        );
        let unaligned = scratch.write(
            "unaligned.elf",
            &mutated(SYMTAB_OFF + 4 * 24 + 8, &(TEXT_ADDR + 0xc2).to_le_bytes()),
        );
        assert_eq!(
            refused(&unaligned, "aligned.elf", "data_obj", 0, 5),
            "Target symbol is not aligned, allocated, and file-backed"
        );
        let mut moved = synthetic_elf();
        // The text segment's physical address no longer equals its virtual one.
        put(&mut moved, 64 + 24, 0u64.to_le_bytes());
        let moved = scratch.write("moved.elf", &moved);
        assert_eq!(
            refused(&moved, "identity.elf", "kernel_main", 0, 5),
            "Target load identity or permissions disagree"
        );
        // A section file offset whose sum with the symbol's offset exceeds 64
        // bits agrees with no load mapping.
        let far = scratch.write(
            "far.elf",
            &mutated(SHOFF + 64 + 24, &(u64::MAX - 8).to_le_bytes()),
        );
        assert_eq!(
            refused(&far, "far-patched.elf", "kernel_main", 0, 5),
            "Target section and unique load mapping disagree"
        );
    }
}
