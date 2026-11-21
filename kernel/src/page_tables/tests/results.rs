//! The frozen vectors of the component: every line of
//! `verification/vectors/memory/page-tables.vectors` is read in the vector
//! notation of the contract and of the specification, its calls are made on
//! the code, and the output is written in the same notation and compared
//! with the expected output of the line. When `KREPI_VECTOR_RESULTS` names a
//! directory, the outputs are written to `memory/page-tables.results` below
//! it, one line for each case in the order of the vector file, for the
//! comparison with the replay of the specification.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The expected outputs are the literals of the vector file; nothing here
//! computes them. An input that the notation does not allow gives an output
//! that starts with `result=malformed`, which no expected output is.
//!
//! A line continues from the state that the lines before it left when it has
//! their sets and boot memory map and its earlier calls are theirs followed
//! by their calls, as they are in each vector. The calls that only read are
//! left out of that comparison, and the calls of the loops of `pt-17` and
//! `own-22` are counted as runs, so that each of the three large vectors
//! costs one pass.

use super::*;
use core::fmt::Debug;
use std::boxed::Box;
use std::format;
use std::string::{String, ToString};

/// The vector file of the component, below the repository root.
const VECTORS: &str = "verification/vectors/memory/page-tables.vectors";

/// The cases of the vector file: 47 vectors with lines.
const LINES: usize = 9382;

/// The result file below the directory of `KREPI_VECTOR_RESULTS`.
const RESULTS: &str = "memory/page-tables.results";

/// A number written as `0x` and hexadecimal digits, or as decimal digits.
fn number(text: &str) -> Option<u64> {
    match text.strip_prefix("0x") {
        Some(digits) => u64::from_str_radix(digits, 16).ok(),
        None => text.parse().ok(),
    }
}

/// A physical width.
fn width(text: &str) -> Option<u8> {
    u8::try_from(number(text)?).ok()
}

/// A span `<start>+<size>`.
fn span_of(text: &str) -> Option<Span> {
    let (start, size) = text.split_once('+')?;
    Some(span(number(start)?, number(size)?))
}

/// A range `<start>+<length>` that `PhysRange::new` builds.
fn phys(text: &str) -> Option<PhysRange> {
    let s = span_of(text)?;
    PhysRange::new(s.start, s.size).ok()
}

/// The items of a list joined by `separator`, none for `-`.
fn items(text: &str, separator: char) -> Vec<&str> {
    match text {
        "-" | "" => Vec::new(),
        _ => text.split(separator).collect(),
    }
}

/// The kinds, which the notation writes by their names.
const KINDS: [Kind; 9] = [
    Kind::ReadExecute,
    Kind::ReadOnly,
    Kind::ReadWrite,
    Kind::KernelPrivateReadWrite,
    Kind::Device,
    Kind::UserReadExecute,
    Kind::UserReadOnly,
    Kind::UserReadWrite,
    Kind::UserDevice,
];

/// A kind by its name.
fn kind(text: &str) -> Option<Kind> {
    KINDS.into_iter().find(|k| format!("{k:?}") == text)
}

/// A firmware reservation `<span>/<flag>`.
fn region(text: &str) -> Option<ReservedRegion> {
    let (span, flag) = text.split_once('/')?;
    let (no_map, reusable) = (flag == "no-map", flag == "reusable");
    let span = span_of(span).filter(|_| no_map || reusable || flag == "none")?;
    Some(ReservedRegion {
        span,
        no_map,
        reusable,
    })
}

/// An exclusion `<range>/<owner>`.
fn exclusion(text: &str) -> Option<Exclusion> {
    let (range, owner) = text.split_once('/')?;
    let owner = match owner {
        "firmware" => Excluder::Firmware,
        "image" => Excluder::Image,
        "boot" => Excluder::BootStorage,
        _ => return None,
    };
    let range = phys(range)?;
    Some(Exclusion { range, owner })
}

/// A placement `low` or `high` with the window, a range or `-`.
fn placement(direction: &str, window: &str) -> Option<Placement> {
    let direction = match direction {
        "low" => Direction::Low,
        "high" => Direction::High,
        _ => return None,
    };
    let window = match window {
        "-" => None,
        range => Some(phys(range)?),
    };
    Some(Placement { direction, window })
}

/// A call `<entry>(<arguments>)`, maybe followed by `.` and a field: the
/// entry, the arguments split at the commas outside brackets, and the field.
fn parse(text: &str) -> Option<(&str, Vec<&str>, Option<&str>)> {
    let (entry, rest) = text.split_once('(')?;
    let close = rest.rfind(')')?;
    let field = match &rest[close + 1..] {
        "" => None,
        more => Some(more.strip_prefix('.')?),
    };
    let (mut args, mut depth, mut from) = (Vec::new(), 0, 0);
    for (at, c) in rest[..close].char_indices() {
        match c {
            '[' => depth += 1,
            ']' => depth -= 1,
            ',' if depth == 0 => {
                args.push(&rest[from..at]);
                from = at + 1;
            }
            _ => {}
        }
    }
    args.push(&rest[from..close]);
    Some((entry, args, field))
}

/// The items of a list in brackets, `[]` for none.
fn bracketed(text: &str) -> Option<Vec<&str>> {
    let inner = text.strip_prefix('[')?.strip_suffix(']')?;
    Some(items(inner, ','))
}

/// A set of one of the shapes of the vector file.
enum Set {
    L3(Box<Tables<3, false>>),
    L4(Box<Tables<4, false>>),
    L6(Box<Tables<6, false>>),
    L10(Box<Tables<10, false>>),
    U2(Box<Tables<2, true>>),
    U3(Box<Tables<3, true>>),
    U8(Box<Tables<8, true>>),
    U9(Box<Tables<9, true>>),
    U16(Box<Tables<16, true>>),
}

/// `$body` with `$t` bound to the tables of a set.
macro_rules! any_set {
    ($set:expr, $t:ident => $body:expr) => {
        match $set {
            Set::L3($t) => $body,
            Set::L4($t) => $body,
            Set::L6($t) => $body,
            Set::L10($t) => $body,
            Set::U2($t) => $body,
            Set::U3($t) => $body,
            Set::U8($t) => $body,
            Set::U9($t) => $body,
            Set::U16($t) => $body,
        }
    };
}

/// Some `$body` with `$t` bound to the tables of an upper set, or none.
macro_rules! upper_set {
    ($set:expr, $t:ident => $body:expr) => {
        match $set {
            Set::U2($t) => Some($body),
            Set::U3($t) => Some($body),
            Set::U8($t) => Some($body),
            Set::U9($t) => Some($body),
            Set::U16($t) => Some($body),
            _ => None,
        }
    };
}

/// Some `$body` with `$t` and `$s` bound to two sets of one shape, or none.
macro_rules! same_sets {
    ($a:expr, $b:expr, $t:ident, $s:ident => $body:expr) => {
        match ($a, $b) {
            (Set::L3($t), Set::L3($s)) => Some($body),
            (Set::L4($t), Set::L4($s)) => Some($body),
            (Set::L6($t), Set::L6($s)) => Some($body),
            (Set::L10($t), Set::L10($s)) => Some($body),
            (Set::U2($t), Set::U2($s)) => Some($body),
            (Set::U3($t), Set::U3($s)) => Some($body),
            (Set::U8($t), Set::U8($s)) => Some($body),
            (Set::U9($t), Set::U9($s)) => Some($body),
            (Set::U16($t), Set::U16($s)) => Some($body),
            _ => None,
        }
    };
}

/// A set of zero storage of the region `region` and `n` tables.
fn new_set(region: &str, n: u64) -> Option<Set> {
    Some(match (region, n) {
        ("lower", 3) => Set::L3(Box::new(set())),
        ("lower", 4) => Set::L4(Box::new(set())),
        ("lower", 6) => Set::L6(Box::new(set())),
        ("lower", 10) => Set::L10(Box::new(set())),
        ("upper", 2) => Set::U2(Box::new(set())),
        ("upper", 3) => Set::U3(Box::new(set())),
        ("upper", 8) => Set::U8(Box::new(set())),
        ("upper", 9) => Set::U9(Box::new(set())),
        ("upper", 16) => Set::U16(Box::new(set())),
        _ => return None,
    })
}

/// The storage and the record of a set.
fn image(set: &Set) -> (Vec<u64>, usize) {
    any_set!(set, t => (t.pool.iter().flatten().copied().collect(), t.used))
}

/// The exclusion records of the tables of the vector file.
const X: usize = EXCLUSION_RECORDS;

/// A page ownership table of one of the capacities of the vector file.
enum Table {
    T0(Box<Ownership<0, X>>),
    T1(Box<Ownership<1, X>>),
    T2(Box<Ownership<2, X>>),
    T4(Box<Ownership<4, X>>),
    T6(Box<Ownership<6, X>>),
    T8(Box<Ownership<8, X>>),
    T12(Box<Ownership<12, X>>),
    T128(Box<Ownership<128, X>>),
}

/// `$body` with `$t` bound to a page ownership table.
macro_rules! any_table {
    ($table:expr, $t:ident => $body:expr) => {
        match $table {
            Table::T0($t) => $body,
            Table::T1($t) => $body,
            Table::T2($t) => $body,
            Table::T4($t) => $body,
            Table::T6($t) => $body,
            Table::T8($t) => $body,
            Table::T12($t) => $body,
            Table::T128($t) => $body,
        }
    };
}

/// The outcome of `Ownership::new` for one capacity.
type Made<T> = Result<T, OwnershipError>;

/// A page ownership table of the capacity `E`, boxed.
fn boxed<const E: usize>(a: u64, b: &[PhysRange], x: &[Exclusion]) -> Made<Box<Ownership<E, X>>> {
    Ownership::new(a, b, x).map(Box::new)
}

/// `Ownership::new` with the capacity `e`, or none for another capacity.
fn new_table(e: u64, a: u64, b: &[PhysRange], x: &[Exclusion]) -> Option<Made<Table>> {
    Some(match e {
        0 => boxed(a, b, x).map(Table::T0),
        1 => boxed(a, b, x).map(Table::T1),
        2 => boxed(a, b, x).map(Table::T2),
        4 => boxed(a, b, x).map(Table::T4),
        6 => boxed(a, b, x).map(Table::T6),
        8 => boxed(a, b, x).map(Table::T8),
        12 => boxed(a, b, x).map(Table::T12),
        128 => boxed(a, b, x).map(Table::T128),
        _ => return None,
    })
}

/// A value that a case names.
enum Value {
    Choice(Choice),
    Receipt(Allocation),
    Reservation(Reservation),
    Packet(Initialized),
}

/// The value of `name`.
fn named<'b, T>(list: &'b mut [(&str, T)], name: &str) -> Option<&'b mut T> {
    let found = list.iter_mut().find(|(n, _)| *n == name);
    found.map(|(_, value)| value)
}

/// Gives `name` the value `value`.
fn bind<'a, T>(list: &mut Vec<(&'a str, T)>, name: &'a str, value: T) {
    match named(list, name) {
        Some(slot) => *slot = value,
        None => list.push((name, value)),
    }
}

/// Takes the value of `name`.
fn take<T>(list: &mut Vec<(&str, T)>, name: &str) -> Option<T> {
    let at = list.iter().position(|(n, _)| *n == name)?;
    Some(list.remove(at).1)
}

/// The output of a refused call.
fn error(e: impl Debug) -> String {
    format!("err={e:?}")
}

/// `ok` followed by the fields of the value, or the error.
fn outcome<T, E: Debug>(result: Result<T, E>, fields: impl FnOnce(T) -> String) -> String {
    match result {
        Ok(value) => format!("ok{}", fields(value)),
        Err(e) => error(e),
    }
}

/// No fields.
fn none<T>(_: T) -> String {
    String::new()
}

/// A range in the notation.
fn show(r: PhysRange) -> String {
    format!("{:#x}+{:#x}", r.start, r.len)
}

/// The fields of a receipt.
fn receipt(a: &Allocation) -> String {
    let (arena, owner, generation) = (a.arena, a.owner, a.generation);
    let range = show(a.range);
    format!(" arena={arena:#x} owner={owner:#x} generation={generation:#x} range={range}")
}

/// The fields of a reservation.
fn reservation(r: &Reservation) -> String {
    let (fields, attempted, failures) = (receipt(&r.allocation), r.attempted, r.failures);
    format!("{fields} attempted={attempted} failures={failures}")
}

/// The fields of the statistics.
fn statistics(s: Stats) -> String {
    let (managed, free, allocated) = (s.managed, s.free, s.allocated);
    let (allocations, free_extents, largest) = (s.allocations, s.free_extents, s.largest_free);
    let bytes = format!(" managed={managed:#x} free={free:#x} allocated={allocated:#x}");
    let counts = format!(" allocations={allocations} free_extents={free_extents}");
    let (extents, capacity) = (s.extents, s.capacity);
    format!("{bytes}{counts} largest_free={largest:#x} extents={extents} capacity={capacity}")
}

/// The check of `dm-04` of the 2 MiB block at `pa` of a direct map: one
/// block that maps it, or its pages, each mapping its own address or not
/// mapped; each with AP[2], AP[1] and nG 0 and PXN and UXN 1.
fn translate<const N: usize>(t: &Tables<N, true>, pa: u64, base: u64, bits: u8) -> String {
    let good =
        |d: u64, at: u64| d & 0x0000_ffff_ffff_f000 == at && d & 0x8c0 == 0 && d >> 53 & 3 == 3;
    if let Ok(d) = t.lookup_block(DIRECT_BASE | pa, base, bits) {
        return match good(d, pa) {
            true => "map=block".to_string(),
            false => format!("map=wrong page={pa:#x}"),
        };
    }
    let mut absent = Vec::new();
    for page in (pa..pa + BLOCK_SIZE).step_by(PAGE_SIZE as usize) {
        match t.lookup_page(DIRECT_BASE | page, base, bits) {
            Ok(d) if good(d, page) => {}
            Err(TableError::NotMapped) => absent.push(format!("{page:#x}")),
            _ => return format!("map=wrong page={page:#x}"),
        }
    }
    match absent.len() {
        512 => "map=none".to_string(),
        0 => "map=pages absent=-".to_string(),
        _ => format!("map=pages absent={}", absent.join(",")),
    }
}

/// The state of a case: its sets, its boot memory map, its page ownership
/// tables and values by name, and the live receipts of the loop of
/// `own-22`.
#[derive(Default)]
struct State<'a> {
    sets: Vec<(&'a str, Set)>,
    memory: Option<MemoryPlan>,
    tables: Vec<(&'a str, Table)>,
    values: Vec<(&'a str, Value)>,
    live: Vec<Allocation>,
}

impl<'a> State<'a> {
    /// The state of the fields `sets=` and `memory=` of an input.
    fn start(fields: &[(&'a str, &'a str)]) -> Option<State<'a>> {
        let field = |key: &str| fields.iter().find(|f| f.0 == key).map(|f| f.1);
        let mut state = State::default();
        for declared in items(field("sets")?, ',') {
            let parts: Vec<&str> = declared.split(':').collect();
            let mut new = new_set(parts.get(1)?, number(parts.get(2)?)?)?;
            if let Some(record) = parts.get(3) {
                let record = number(record)? as usize;
                any_set!(&mut new, t => t.used = record);
            }
            state.sets.push((parts[0], new));
        }
        if let Some(kind) = field("memory") {
            let spans = |key| -> Option<Vec<Span>> {
                items(field(key)?, ',').into_iter().map(span_of).collect()
            };
            let (ram, boot): (Vec<Span>, Vec<Span>) = (spans("ram")?, spans("boot")?);
            let firmware = items(field("firmware")?, ',').into_iter().map(region);
            let firmware: Vec<ReservedRegion> = firmware.collect::<Option<_>>()?;
            let plan = match kind {
                "MemoryPlan::new" => {
                    let window = span_of(field("window")?)?;
                    MemoryPlan::new(window, &ram, &boot, &firmware)
                }
                "MemoryPlan::all_ram" => MemoryPlan::all_ram(&ram, &boot, &firmware),
                _ => return None,
            };
            state.memory = Some(plan.ok()?);
        }
        Some(state)
    }

    /// The output of the call `text`, with its field when it names one.
    fn run(&mut self, text: &'a str) -> String {
        let malformed = format!("result=malformed {text}");
        let Some((entry, args, field)) = parse(text) else {
            return malformed;
        };
        let on_set = self.on_set(entry, &args);
        let Some(output) = on_set.or_else(|| self.on_table(entry, &args)) else {
            return malformed;
        };
        match (field, output.strip_prefix("ok ")) {
            (Some(name), Some(fields)) => {
                let mut pairs = fields.split(' ');
                let named = pairs.find(|f| f.split('=').next() == Some(name));
                named.map_or(malformed, ToString::to_string)
            }
            _ => output,
        }
    }

    /// `count` calls of `map_block` from `v` and `p`, 2 MiB apart, each on
    /// the set that the calls before it left: `ok`, or the first error.
    fn blocks(&mut self, s: &str, v: u64, p: u64, count: u64, at: (u64, u8)) -> Option<String> {
        let mut first = None;
        any_set!(named(&mut self.sets, s)?, t => for i in 0..count {
            let (v, p) = (v.wrapping_add(i * BLOCK_SIZE), p.wrapping_add(i * BLOCK_SIZE));
            first = first.or(block(t, v, p, at.0, at.1).err());
        });
        Some(first.map_or("ok".to_string(), error))
    }

    /// A call on a set, or none for any other call.
    fn on_set(&mut self, entry: &str, args: &[&'a str]) -> Option<String> {
        let sets = &mut self.sets;
        Some(match (entry, args) {
            ("descriptor", &[k, a]) => {
                format!("ok descriptor={:#x}", descriptor(kind(k)?, number(a)?))
            }
            ("map_page", &[s, v, p, k, b, w]) => {
                let (v, p, k, b, w) = (number(v)?, number(p)?, kind(k)?, number(b)?, width(w)?);
                any_set!(named(sets, s)?, t => outcome(map(t, v, p, k, b, w), none))
            }
            ("map_block", &[s, v, p, b, w]) => {
                self.blocks(s, number(v)?, number(p)?, 1, (number(b)?, width(w)?))?
            }
            ("map_blocks", &[s, v, p, n, b, w]) => {
                let (v, p, n) = (number(v)?, number(p)?, number(n)?);
                self.blocks(s, v, p, n, (number(b)?, width(w)?))?
            }
            ("unmap_page", &[s, v, b, w]) => {
                let (v, b, w) = (number(v)?, number(b)?, width(w)?);
                let page = |page| format!(" page={page:#x}");
                any_set!(named(sets, s)?, t => outcome(unmap(t, v, b, w), page))
            }
            ("lookup_page" | "lookup_block", &[s, v, b, w]) => {
                let (v, b, w) = (number(v)?, number(b)?, width(w)?);
                let found = any_set!(named(sets, s)?, t => match entry {
                    "lookup_page" => t.lookup_page(v, b, w),
                    _ => t.lookup_block(v, b, w),
                });
                outcome(found, |d| format!(" descriptor={d:#x}"))
            }
            ("used", &[s]) => format!("ok used={}", any_set!(named(sets, s)?, t => t.used())),
            ("reset", &[s]) => any_set!(named(sets, s)?, t => {
                let plan = t.reset();
                apply(t, plan);
                "ok".to_string()
            }),
            ("set_entry", &[s, i, j, d]) => {
                let (i, j, d) = (number(i)? as usize, number(j)? as usize, number(d)?);
                any_set!(named(sets, s)?, t => *t.pool.get_mut(i)?.get_mut(j)? = d);
                "ok".to_string()
            }
            ("set_used", &[s, record]) => {
                let record = number(record)? as usize;
                any_set!(named(sets, s)?, t => t.used = record);
                "ok".to_string()
            }
            ("clone_kernel_from", &[target, source, sb, b, w]) => {
                let (sb, b, w) = (number(sb)?, number(b)?, width(w)?);
                let at = sets.iter().position(|(n, _)| *n == target)?;
                let (name, mut set) = sets.remove(at);
                let copied = named(sets, source).and_then(|source| {
                    same_sets!(&mut set, &*source, t, s => outcome(copy(t, s, sb, b, w), none))
                });
                sets.insert(at, (name, set));
                copied?
            }
            ("direct_map", &[s, b, w]) => {
                let (memory, b, w) = (self.memory.as_ref()?, number(b)?, width(w)?);
                let counts = |steps: Vec<Step>| {
                    let (bytes, blocks, pages) = counts(&steps);
                    format!(" bytes={bytes:#x} blocks={blocks} pages={pages}")
                };
                upper_set!(named(sets, s)?, t => outcome(direct(t, memory, b, w), counts))?
            }
            ("translate_block", &[s, pa, b, w]) => {
                let (pa, b, w) = (number(pa)?, number(b)?, width(w)?);
                upper_set!(named(sets, s)?, t => translate(t, pa, b, w))?
            }
            _ => return None,
        })
    }

    /// Step `s` of the loop of `own-22` on the table `name`: with
    /// `s mod 3 ≠ 0` and a live receipt, the release by its owner of the live
    /// one at position `7 s mod n` of the `n` live ones; otherwise owner 7
    /// takes `s mod 5 + 1` pages at an alignment of `2^(s mod 4)` pages, high
    /// when `s` is even and low when it is odd, with the zeroing complete.
    fn mixed_step(&mut self, name: &str, s: u64) -> Option<String> {
        let table = named(&mut self.tables, name)?;
        let n = self.live.len() as u64;
        let done = if s % 3 != 0 && n > 0 {
            let a = self.live[(7 * s % n) as usize];
            let released = any_table!(&mut *table, t => t.release(a.owner, a));
            released.map(|()| {
                self.live.remove((7 * s % n) as usize);
                "released".to_string()
            })
        } else {
            let placement = if s % 2 == 0 { HIGH } else { LOW };
            let pages = s % 5 + 1;
            let taken =
                any_table!(&mut *table, t => allocate(t, 7, pages, 1 << (s % 4), placement));
            taken.map(|a| {
                self.live.push(a);
                format!("start={:#x}", a.range.start)
            })
        };
        let free = any_table!(table, t => t.stats().free);
        Some(format!("{} free={free:#x}", done.unwrap_or_else(error)))
    }

    /// The first `count` steps of the loop of `own-22` on the table `name`,
    /// from step 0 and no live receipt.
    fn steps(&mut self, name: &str, count: u64) -> Option<String> {
        self.live.clear();
        for s in 0..count {
            self.mixed_step(name, s)?;
        }
        Some("ok".to_string())
    }

    /// A call of the page ownership table or of physical ranges, or none for
    /// any other call.
    fn on_table(&mut self, entry: &str, args: &[&'a str]) -> Option<String> {
        let (tables, values) = (&mut self.tables, &mut self.values);
        Some(match (entry, args) {
            ("PhysRange::new", &[s, l]) => outcome(PhysRange::new(number(s)?, number(l)?), |r| {
                format!(" range={}", show(r))
            }),
            ("end", &[r]) => format!("ok end={:#x}", phys(r)?.end()),
            ("contains", &[r, o]) => format!("ok contains={}", phys(r)?.contains(phys(o)?)),
            ("overlaps", &[r, o]) => format!("ok overlaps={}", phys(r)?.overlaps(phys(o)?)),
            ("Ownership::new", &[t, arena, e, banks, exclusions]) => {
                let banks = bracketed(banks)?.into_iter().map(phys);
                let banks: Vec<PhysRange> = banks.collect::<Option<_>>()?;
                let exclusions = bracketed(exclusions)?.into_iter().map(exclusion);
                let exclusions: Vec<Exclusion> = exclusions.collect::<Option<_>>()?;
                let made = new_table(number(e)?, number(arena)?, &banks, &exclusions)?;
                outcome(made, |made| {
                    bind(tables, t, made);
                    String::new()
                })
            }
            ("set_generation", &[t, g]) => {
                let g = number(g)?;
                any_table!(named(tables, t)?, t => t.counter = Counter::Next(g));
                "ok".to_string()
            }
            ("choose", &[t, c, o, n, a, d, w]) => {
                let (o, n, a, p) = (number(o)?, number(n)?, number(a)?, placement(d, w)?);
                let chosen = any_table!(named(tables, t)?, t => t.choose(o, n, a, p));
                outcome(chosen, |choice| {
                    let range = format!(" range={}", show(choice.range));
                    bind(values, c, Value::Choice(choice));
                    range
                })
            }
            ("reserve", &[t, r, o, n, a, d, w]) => {
                let (o, n, a, p) = (number(o)?, number(n)?, number(a)?, placement(d, w)?);
                let reserved = any_table!(named(tables, t)?, t => t.reserve(o, n, a, p));
                outcome(reserved, |held| {
                    let fields = reservation(&held);
                    bind(values, r, Value::Reservation(held));
                    fields
                })
            }
            ("assign", &[t, a, c, zeroed]) => {
                let zeroed = zeroed.parse().ok()?;
                let Some(Value::Choice(choice)) = take(values, c) else {
                    return None;
                };
                let assigned = any_table!(named(tables, t)?, t => t.assign(choice, zeroed));
                outcome(assigned, |x| {
                    bind(values, a, Value::Receipt(x));
                    receipt(&x)
                })
            }
            ("Reservation::initialized", &[x, r, zeroed]) => {
                let zeroed = zeroed.parse().ok()?;
                let Some(Value::Reservation(held)) = take(values, r) else {
                    return None;
                };
                match held.initialized(zeroed) {
                    Ok(packet) => {
                        let fields = receipt(&packet.allocation);
                        let output =
                            format!("ok value=packet{fields} failures={}", packet.failures);
                        bind(values, x, Value::Packet(packet));
                        output
                    }
                    Err(held) => {
                        let output = format!("ok value=reservation{}", reservation(&held));
                        bind(values, r, Value::Reservation(held));
                        output
                    }
                }
            }
            ("publish", &[t, a, owner, x]) => {
                let owner = number(owner)?;
                let Some(Value::Packet(packet)) = take(values, x) else {
                    return None;
                };
                match any_table!(named(tables, t)?, t => t.publish(owner, packet)) {
                    Ok(y) => {
                        bind(values, a, Value::Receipt(y));
                        format!("ok{}", receipt(&y))
                    }
                    Err((e, packet)) => {
                        bind(values, x, Value::Packet(packet));
                        error(e)
                    }
                }
            }
            ("cancel", &[t, owner, r]) => {
                let owner = number(owner)?;
                let Some(Value::Reservation(held)) = take(values, r) else {
                    return None;
                };
                match any_table!(named(tables, t)?, t => t.cancel(owner, held)) {
                    Ok(()) => "ok".to_string(),
                    Err((e, held)) => {
                        bind(values, r, Value::Reservation(held));
                        error(e)
                    }
                }
            }
            ("release" | "validate", &[t, owner, x]) => {
                let owner = number(owner)?;
                let (a, state) = match named(values, x)? {
                    Value::Receipt(a) => (*a, HoldState::Published),
                    Value::Packet(packet) => (packet.allocation, HoldState::Reserved),
                    _ => return None,
                };
                let checked = any_table!(named(tables, t)?, t => match (entry, state) {
                    ("release", HoldState::Published) => t.release(owner, a),
                    ("validate", _) => t.validate(owner, a, state),
                    _ => return None,
                });
                outcome(checked, none)
            }
            ("stats", &[t]) => format!(
                "ok{}",
                statistics(any_table!(named(tables, t)?, t => t.stats()))
            ),
            ("mixed_steps", &[t, _, n]) => self.steps(t, number(n)?)?,
            ("mixed_step", &[t, _, s]) => self.mixed_step(t, number(s)?)?,
            ("release_all", &[t, _]) => {
                let table = named(tables, t)?;
                let mut first = Ok(());
                while first.is_ok() && !self.live.is_empty() {
                    let a = self.live.remove(0);
                    first = any_table!(&mut *table, t => t.release(a.owner, a));
                }
                self.live.clear();
                outcome(first, none)
            }
            _ => return None,
        })
    }

    /// The output of the item `item` of `ask=` after the call, with the
    /// storage and the records of the sets `before` it.
    fn ask(&mut self, item: &str, before: &[(&str, (Vec<u64>, usize))]) -> Option<String> {
        let (what, args, _) = parse(item)?;
        let name = *args.first()?;
        let set = named(&mut self.sets, name)?;
        let value = match (what, &args[..]) {
            ("unchanged", [_]) => {
                let earlier = &before.iter().find(|b| b.0 == name)?.1;
                (image(set) == *earlier).to_string()
            }
            ("zero", [_]) => {
                any_set!(set, t => t.pool.iter().flatten().all(|&d| d == 0)).to_string()
            }
            ("entry", &[_, i, j]) => {
                let (i, j) = (number(i)? as usize, number(j)? as usize);
                format!("{:#x}", any_set!(set, t => *t.pool.get(i)?.get(j)?))
            }
            _ => return None,
        };
        Some(format!("{item}={value}"))
    }
}

/// An earlier call as the reuse of a state compares them.
#[derive(Clone, Copy, PartialEq)]
enum Item<'a> {
    /// A call that may change the state.
    Call(&'a str),
    /// `map_blocks(set,v,p,count,base,bits)`.
    Blocks(&'a str, u64, u64, u64, &'a str, &'a str),
    /// `mixed_steps(t,l,count)`.
    Steps(&'a str, &'a str, u64),
}

/// The calls that only read the state, each between spaces.
const READS: &str = " lookup_page lookup_block used descriptor translate_block stats validate \
                     PhysRange::new end contains overlaps ";

/// Appends the call `text` to the earlier calls `done`: a call that only
/// reads is left out, and a call that continues a run of `map_block` calls
/// or of the steps of `own-22` lengthens the run.
fn push<'a>(done: &mut Vec<Item<'a>>, text: &'a str) {
    let Some((entry, args, _)) = parse(text) else {
        return done.push(Item::Call(text));
    };
    let blocks = |s, v, p, n, b, w| Some(Item::Blocks(s, number(v)?, number(p)?, number(n)?, b, w));
    let item = match (entry, &args[..]) {
        (entry, _) if READS.contains(&format!(" {entry} ")) => return,
        ("map_block", &[s, v, p, b, w]) => blocks(s, v, p, "1", b, w),
        ("map_blocks", &[s, v, p, n, b, w]) => blocks(s, v, p, n, b, w),
        ("mixed_steps", &[t, l, n]) => number(n).map(|n| Item::Steps(t, l, n)),
        ("mixed_step", &[t, l, s]) => match (done.last_mut(), number(s)) {
            (Some(Item::Steps(t0, l0, n)), Some(s)) if (*t0, *l0, *n) == (t, l, s) => {
                *n += 1;
                return;
            }
            (_, Some(0)) => Some(Item::Steps(t, l, 1)),
            _ => None,
        },
        _ => None,
    };
    match (done.last_mut(), item.unwrap_or(Item::Call(text))) {
        (_, Item::Blocks(.., 0, _, _) | Item::Steps(_, _, 0)) => {}
        (Some(Item::Blocks(s0, v0, p0, n0, b0, w0)), Item::Blocks(s, v, p, n, b, w))
            if (*s0, *b0, *w0) == (s, b, w)
                && v == v0.wrapping_add(*n0 * BLOCK_SIZE)
                && p == p0.wrapping_add(*n0 * BLOCK_SIZE) =>
        {
            *n0 += n
        }
        (_, item) => done.push(item),
    }
}

/// The lines run so far: the state, the sets and boot memory map of the
/// input that made it, and the calls that it has run.
#[derive(Default)]
struct Run<'a> {
    state: State<'a>,
    key: &'a str,
    done: Vec<Item<'a>>,
}

impl<'a> Run<'a> {
    /// The output of the case of the input `input`.
    fn case(&mut self, input: &'a str) -> Option<String> {
        let fields: Vec<(&str, &str)> =
            input.split(' ').filter_map(|f| f.split_once('=')).collect();
        let field = |key: &str| fields.iter().find(|f| f.0 == key).map(|f| f.1);
        let key = &input[..input.find(" do=")?];
        let mut want = Vec::new();
        for call in items(field("do")?, ';') {
            push(&mut want, call);
        }
        if self.key != key || !want.starts_with(&self.done) {
            (self.state, self.key) = (State::start(&fields)?, key);
            self.done.clear();
        }
        for &item in &want[self.done.len()..] {
            let output = match item {
                Item::Call(call) => self.state.run(call),
                Item::Blocks(s, v, p, n, b, w) => {
                    self.state.blocks(s, v, p, n, (number(b)?, width(w)?))?
                }
                Item::Steps(t, _, n) => self.state.steps(t, n)?,
            };
            if output.starts_with("result=malformed") {
                return None;
            }
        }
        self.done = want;
        let asks = items(field("ask")?, ';');
        let unchanged = asks.iter().any(|a| a.starts_with("unchanged("));
        let before = self.state.sets.iter().filter(|_| unchanged);
        let before: Vec<_> = before.map(|(n, s)| (*n, image(s))).collect();
        let call = field("call")?;
        let mut output = self.state.run(call);
        push(&mut self.done, call);
        for ask in asks {
            output.push(' ');
            output.push_str(&self.state.ask(ask, &before)?);
        }
        Some(output)
    }
}

/// Every case of the vector file gives its expected output; the outputs are
/// written to the result file when `KREPI_VECTOR_RESULTS` names a directory.
#[test]
fn results_of_the_frozen_vectors() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let text = std::fs::read_to_string(root.join(VECTORS)).expect("the vector file");
    let (mut results, mut differences, mut lines) = (String::new(), Vec::new(), 0);
    let mut run = Run::default();
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let parts: Vec<&str> = line.split('\t').collect();
        let [id, input, expected] = parts[..] else {
            panic!("a malformed vector line: {line}");
        };
        let output = run.case(input).unwrap_or_else(|| {
            run.key = "";
            "result=malformed input".to_string()
        });
        if output != expected {
            differences.push(format!("{id}: expected {expected}, got {output}"));
        }
        results.push_str(&format!("{id}\t{output}\n"));
        lines += 1;
    }
    assert_eq!(lines, LINES);
    let (count, shown) = (
        differences.len(),
        differences[..differences.len().min(20)].join("\n"),
    );
    assert_eq!(count, 0, "cases differ, the first:\n{shown}");
    if let Some(directory) = std::env::var_os("KREPI_VECTOR_RESULTS") {
        let path = std::path::Path::new(&directory).join(RESULTS);
        std::fs::create_dir_all(path.parent().expect("a directory")).expect("the directory");
        std::fs::write(&path, results).expect("the result file");
    }
}
