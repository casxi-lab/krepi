//! The frozen vectors of the component: every line of
//! `verification/vectors/boot-platform/fdt.vectors` is read in the notation
//! of the contract's `Legacy test vectors` section, its entry is called on
//! the code, and the output is written in the same notation and compared
//! with the expected output of the line. When `KREPI_VECTOR_RESULTS` names
//! a directory, the outputs are written to `boot-platform/fdt.results`
//! below it, one line for each vector in the order of the vector file, for
//! the comparison with the replay of the specification.
//!
//! Feature: krepi.platform.device-tree
//!
//! The expected outputs are the literals of the vector file; nothing here
//! computes them. An input that the notation does not allow gives an output
//! that starts with `result=malformed`, which no expected output is.

use super::*;
use std::format;
use std::string::{String, ToString};

/// The fields `key=value` of an input, in their order; a field without `=`
/// is not one.
fn fields(input: &str) -> Vec<(&str, &str)> {
    input
        .split(' ')
        .filter_map(|field| field.split_once('='))
        .collect()
}

/// The value of the field `key`.
fn field<'a>(fields: &[(&'a str, &'a str)], key: &str) -> Option<&'a str> {
    fields
        .iter()
        .find(|(name, _)| *name == key)
        .map(|(_, value)| *value)
}

/// The value of a lowercase hexadecimal digit.
fn hex_digit(digit: char) -> Option<u32> {
    match digit {
        '0'..='9' | 'a'..='f' => digit.to_digit(16),
        _ => None,
    }
}

/// The bytes of lowercase hexadecimal digits, two for each byte.
fn hex_bytes(text: &str) -> Option<Vec<u8>> {
    let digits: Vec<char> = text.chars().collect();
    if !digits.len().is_multiple_of(2) {
        return None;
    }
    digits
        .chunks(2)
        .map(|pair| Some((hex_digit(pair[0])? * 16 + hex_digit(pair[1])?) as u8))
        .collect()
}

/// A number written as `0x` and lowercase hexadecimal digits, or as decimal
/// digits.
fn number(text: &str) -> Option<u128> {
    let (digits, radix) = match text.strip_prefix("0x") {
        Some(digits) => (digits, 16),
        None => (text, 10),
    };
    if digits.is_empty() {
        return None;
    }
    let mut value: u128 = 0;
    for digit in digits.chars() {
        let digit = if radix == 16 {
            hex_digit(digit)?
        } else {
            digit.to_digit(10)?
        };
        value = value.checked_mul(radix)?.checked_add(digit as u128)?;
    }
    Some(value)
}

fn number64(text: &str) -> Option<u64> {
    u64::try_from(number(text)?).ok()
}

fn number32(text: &str) -> Option<u32> {
    u32::try_from(number(text)?).ok()
}

/// A span `<start>+<size>`.
fn span(text: &str) -> Option<Span> {
    let pieces: Vec<&str> = text.split('+').collect();
    match pieces[..] {
        [start, size] => Some(Span {
            start: number64(start)?,
            size: number64(size)?,
        }),
        _ => None,
    }
}

/// A list of spans joined by `,`, or `-` for none.
fn spans(text: &str) -> Option<Vec<Span>> {
    if text == "-" {
        return Some(Vec::new());
    }
    text.split(',').map(span).collect()
}

/// A reserved region `<span>/<flag>`.
fn region(text: &str) -> Option<ReservedRegion> {
    let pieces: Vec<&str> = text.split('/').collect();
    let (span, no_map, reusable) = match pieces[..] {
        [span, "no-map"] => (span, true, false),
        [span, "reusable"] => (span, false, true),
        [span, "none"] => (span, false, false),
        _ => return None,
    };
    Some(ReservedRegion {
        span: self::span(span)?,
        no_map,
        reusable,
    })
}

/// A list of reserved regions joined by `,`, or `-` for none.
fn regions(text: &str) -> Option<Vec<ReservedRegion>> {
    if text == "-" {
        return Some(Vec::new());
    }
    text.split(',').map(region).collect()
}

/// A query `<name>(<argument>)`: its name and its argument.
fn query(text: &str) -> Option<(&str, &str)> {
    let (name, rest) = text.split_once('(')?;
    Some((name, rest.strip_suffix(')')?))
}

fn profile(text: &str) -> Option<CpuProfile> {
    match text {
        "QemuHvc" => Some(CpuProfile::QemuHvc),
        "QemuSmc" => Some(CpuProfile::QemuSmc),
        "Pi5" => Some(CpuProfile::Pi5),
        _ => None,
    }
}

fn hex(value: u64) -> String {
    format!("{value:#x}")
}

fn span_text(span: Span) -> String {
    format!("{}+{}", hex(span.start), hex(span.size))
}

fn spans_text(spans: &[Span]) -> String {
    if spans.is_empty() {
        return "-".to_string();
    }
    spans
        .iter()
        .map(|span| span_text(*span))
        .collect::<Vec<_>>()
        .join(",")
}

fn region_text(region: &ReservedRegion) -> String {
    let flag = if region.no_map {
        "no-map"
    } else if region.reusable {
        "reusable"
    } else {
        "none"
    };
    format!("{}/{flag}", span_text(region.span))
}

fn regions_text(regions: &[ReservedRegion]) -> String {
    if regions.is_empty() {
        return "-".to_string();
    }
    regions
        .iter()
        .map(region_text)
        .collect::<Vec<_>>()
        .join(",")
}

fn bool_text(value: bool) -> String {
    value.to_string()
}

fn profile_text(profile: CpuProfile) -> String {
    format!("{profile:?}")
}

fn kind_text(kind: MappingKind) -> String {
    format!("{kind:?}")
}

/// The value of a query that may fail.
fn query_text<T>(result: Result<T, Error>, text: impl Fn(T) -> String) -> String {
    match result {
        Ok(value) => text(value),
        Err(error) => format!("Error::{error:?}"),
    }
}

/// The output of a rejection that names its error.
fn error_text(error: Error) -> String {
    format!("result=err error=Error::{error:?}")
}

/// The output of a case whose entry gave `result`, whose error `name`
/// writes as `<type>::<variant>`: a case that asks nothing gives
/// `result=ok` or `result=err`; one that asks `error` gives `result=ok` or
/// the error; one that asks fields and queries gives the error, or each of
/// them with the value that `answer` gives it.
fn outcome_as<T, E>(
    result: Result<T, E>,
    name: impl Fn(E) -> String,
    ask: &[&str],
    answer: impl Fn(&T, &str) -> Option<String>,
) -> String {
    match result {
        Err(error) if ask.is_empty() => {
            let _ = name(error);
            "result=err".to_string()
        }
        Err(error) => format!("result=err error={}", name(error)),
        Ok(_) if ask.is_empty() || ask == ["error"] => "result=ok".to_string(),
        Ok(value) => {
            let mut output = "result=ok".to_string();
            for asked in ask {
                match answer(&value, asked) {
                    Some(text) => output.push_str(&format!(" {asked}={text}")),
                    None => return "result=malformed ask".to_string(),
                }
            }
            output
        }
    }
}

/// [`outcome_as`] for an entry whose error is an [`Error`].
fn outcome<T>(
    result: Result<T, Error>,
    ask: &[&str],
    answer: impl Fn(&T, &str) -> Option<String>,
) -> String {
    outcome_as(result, |error| format!("Error::{error:?}"), ask, answer)
}

/// The entries of a `reg`, in order.
fn reg_entries(reg: Reg<'_>) -> Vec<Span> {
    let mut reg = reg;
    let mut entries = Vec::new();
    while let Some(entry) = reg.next() {
        entries.push(entry);
    }
    entries
}

/// The fields and queries of a `Reg`.
fn reg_answer(reg: &Reg<'_>, asked: &str) -> Option<String> {
    let entries = reg_entries(*reg);
    if asked == "entries" {
        return Some(spans_text(&entries));
    }
    let ("end", index) = query(asked)? else {
        return None;
    };
    let index = usize::try_from(number(index)?).ok()?;
    Some(match entries.get(index) {
        None => "-".to_string(),
        Some(entry) => query_text(entry.end(), hex),
    })
}

/// The fields and queries of an address map.
fn map_answer(map: &AddressMap<'_>, asked: &str) -> Option<String> {
    if asked == "kind" {
        return Some(kind_text(map.kind()));
    }
    let (name, argument) = query(asked)?;
    let request = span(argument)?;
    match name {
        "to_parent" => Some(query_text(map.to_parent(request), span_text)),
        "to_child" => Some(query_text(map.to_child(request), span_text)),
        _ => None,
    }
}

/// The fields of a memory map.
fn memory_answer(
    ram: &[Span],
    reserved: &[ReservedRegion],
    dynamic: u64,
    asked: &str,
) -> Option<String> {
    match asked {
        "ram" => Some(spans_text(ram)),
        "reserved" => Some(regions_text(reserved)),
        "dynamic" => Some(dynamic.to_string()),
        _ => None,
    }
}

/// The fields and queries of a Pi 5 boot memory.
fn pi5_answer(memory: &Pi5BootMemory, asked: &str) -> Option<String> {
    match asked {
        "dtb" => return Some(span_text(memory.dtb())),
        "image" => return Some(span_text(memory.image())),
        "ram_bytes" => return Some(hex(memory.ram_bytes())),
        _ => {}
    }
    if let Some(("is_available", argument)) = query(asked) {
        let request = span(argument)?;
        return Some(query_text(memory.is_available(request), bool_text));
    }
    memory_answer(memory.ram(), memory.reserved(), memory.dynamic(), asked)
}

/// The fields and queries of a CPU topology.
fn topology_answer(topology: &CpuTopology, asked: &str) -> Option<String> {
    match asked {
        "count" => return Some(topology.count().to_string()),
        "profile" => return Some(profile_text(topology.profile())),
        _ => {}
    }
    let ("affinity", index) = query(asked)? else {
        return None;
    };
    let index = number64(index)?;
    Some(match topology.affinity(index) {
        Some(affinity) => hex(affinity),
        None => "-".to_string(),
    })
}

/// The usable ranges of a boot memory map, in order.
fn available(plan: &MemoryPlan) -> Vec<Span> {
    let mut ranges = plan.available_ranges();
    let mut spans = Vec::new();
    while let Some(range) = ranges.next() {
        spans.push(range);
    }
    spans
}

/// The fields and queries of a boot memory map.
fn plan_answer(plan: &MemoryPlan, asked: &str) -> Option<String> {
    let usable = available(plan);
    match asked {
        "ram" => return Some(spans_text(plan.ram())),
        "managed" => return Some(spans_text(plan.managed_banks())),
        "boot" => return Some(spans_text(plan.boot_ranges())),
        "firmware" => return Some(spans_text(plan.firmware_ranges())),
        "reservations" => return Some(spans_text(plan.reservations())),
        "available" => return Some(spans_text(&usable)),
        "described_bytes" => return Some(hex(plan.described_bytes())),
        "managed_bytes" => return Some(hex(plan.managed_bytes())),
        "available_bytes" => return Some(hex(usable.iter().map(|range| range.size).sum())),
        _ => {}
    }
    let (name, argument) = query(asked)?;
    let request = span(argument)?;
    match name {
        "contains_ram" => Some(bool_text(plan.contains_ram(request))),
        "is_available" => Some(bool_text(plan.is_available(request))),
        "permits_backing" => Some(bool_text(plan.permits_backing(request))),
        "available_count" => {
            let end = request.start as u128 + request.size as u128;
            let holding = usable.iter().filter(|range| {
                range.start <= request.start && end <= range.start as u128 + range.size as u128
            });
            Some(holding.count().to_string())
        }
        _ => None,
    }
}

/// The output of a case of a boot memory map, whose error is a
/// [`PlanError`].
fn plan_outcome(result: Result<MemoryPlan, PlanError>, ask: &[&str]) -> String {
    outcome_as(
        result,
        |error| format!("PlanError::{error:?}"),
        ask,
        plan_answer,
    )
}

/// The entries that a case of the parse may ask on an accepted tree.
const TREE_CALLS: [&str; 4] = ["discover_memory", "reg", "ranges", "dma_ranges"];

/// `entry=parse`.
fn parse_case(dtb: &[u8], ask: &[&str]) -> String {
    if !ask.is_empty() && ask.iter().all(|asked| TREE_CALLS.contains(asked)) {
        if let Ok(tree) = Fdt::parse(dtb) {
            if ask.contains(&"discover_memory") {
                let _ = tree.discover_memory();
            }
            for node in all_nodes(tree) {
                if ask.contains(&"reg") {
                    let _ = node.reg();
                }
                if ask.contains(&"ranges") {
                    let _ = node.ranges();
                }
                if ask.contains(&"dma_ranges") {
                    let _ = node.dma_ranges();
                }
            }
        }
        return "result=returned".to_string();
    }
    outcome(Fdt::parse(dtb), ask, |tree, asked| {
        (asked == "total_size").then(|| tree.total_size().to_string())
    })
}

/// The node `path` of the tree `tree`, or the output of the failure.
fn node_of<'a>(tree: Fdt<'a>, path: &str) -> Result<Node<'a>, String> {
    match tree.find_node(path) {
        Err(error) => Err(error_text(error)),
        Ok(None) => Err("result=err node=-".to_string()),
        Ok(Some(node)) => Ok(node),
    }
}

/// A case of an entry on a node of the tree `tree`.
fn node_case(tree: Fdt<'_>, entry: &str, fields: &[(&str, &str)], ask: &[&str]) -> String {
    let Some(path) = field(fields, "node") else {
        return "result=malformed node".to_string();
    };
    let node = match node_of(tree, path) {
        Ok(node) => node,
        Err(output) => return output,
    };
    match entry {
        "string_property" => {
            let Some(name) = field(fields, "name") else {
                return "result=malformed name".to_string();
            };
            outcome(node.string_property(name), ask, |value, asked| {
                (asked == "value").then(|| match value {
                    Some(bytes) => String::from_utf8_lossy(bytes).into_owned(),
                    None => "-".to_string(),
                })
            })
        }
        "translate_reg" => {
            let Some(request) = field(fields, "span").and_then(span) else {
                return "result=malformed span".to_string();
            };
            outcome(node.translate_reg(request), ask, |translated, asked| {
                (asked == "span").then(|| span_text(*translated))
            })
        }
        "reg" => outcome(node.reg(), ask, reg_answer),
        "ranges" => outcome(node.ranges(), ask, map_answer),
        "dma_ranges" => outcome(node.dma_ranges(), ask, map_answer),
        _ => "result=malformed entry".to_string(),
    }
}

/// A case of `discover_pi5_boot_memory`, `find_available` or `from_pi5` on
/// the tree `tree`.
fn pi5_case(tree: Fdt<'_>, entry: &str, fields: &[(&str, &str)], ask: &[&str]) -> Option<String> {
    let dtb_address = number64(field(fields, "dtb_address")?)?;
    let image = span(field(fields, "image")?)?;
    let memory = tree.discover_pi5_boot_memory(dtb_address, image);
    if entry == "discover_pi5_boot_memory" {
        return Some(outcome(memory, ask, pi5_answer));
    }
    if entry == "from_pi5" {
        let window = span(field(fields, "window")?)?;
        let more = spans(field(fields, "more")?)?;
        let plan = match memory {
            Err(error) => Err(format!("Error::{error:?}")),
            Ok(memory) => MemoryPlan::from_pi5(&memory, window, &more)
                .map_err(|error| format!("PlanError::{error:?}")),
        };
        return Some(outcome_as(plan, |name| name, ask, plan_answer));
    }
    let size = number64(field(fields, "size")?)?;
    let alignment = number64(field(fields, "alignment")?)?;
    let minimum = number64(field(fields, "minimum")?)?;
    let limit = number64(field(fields, "limit")?)?;
    let selected = memory.and_then(|memory| {
        let span = memory.find_available(size, alignment, minimum, limit)?;
        Ok((memory, span))
    });
    Some(outcome(selected, ask, |(memory, selected), asked| {
        if asked == "span" {
            Some(match selected {
                Some(span) => span_text(*span),
                None => "-".to_string(),
            })
        } else {
            pi5_answer(memory, asked)
        }
    }))
}

/// A case of an entry on the tree `tree`.
fn tree_case(tree: Fdt<'_>, entry: &str, fields: &[(&str, &str)], ask: &[&str]) -> String {
    match entry {
        "discover_memory" => outcome(tree.discover_memory(), ask, |memory, asked| {
            memory_answer(memory.ram(), memory.reserved(), memory.dynamic(), asked)
        }),
        "discover_pi5_boot_memory" | "find_available" | "from_pi5" => {
            pi5_case(tree, entry, fields, ask)
                .unwrap_or_else(|| "result=malformed input".to_string())
        }
        "discover_cpus" | "validate_qemu_timers" => {
            let Some(profile) = field(fields, "profile").and_then(profile) else {
                return "result=malformed profile".to_string();
            };
            let topology = tree.discover_cpus(profile);
            if entry == "discover_cpus" {
                return outcome(topology, ask, topology_answer);
            }
            let Some(interrupts) = field(fields, "interrupts").and_then(hex_bytes) else {
                return "result=malformed interrupts".to_string();
            };
            let checked = topology.and_then(|topology| topology.validate_qemu_timers(&interrupts));
            outcome(checked, ask, |_, _| None)
        }
        _ => node_case(tree, entry, fields, ask),
    }
}

/// A case of an entry without a tree, or none for another entry or a
/// malformed input.
fn value_case(entry: &str, fields: &[(&str, &str)], ask: &[&str]) -> Option<String> {
    let cells = |key: &str| field(fields, key).and_then(number32);
    match entry {
        "cells_u64" => {
            let bytes = hex_bytes(field(fields, "bytes")?)?;
            let count = cells("cells")?;
            Some(outcome(cells_u64(&bytes, count), ask, |value, asked| {
                (asked == "value").then(|| hex(*value))
            }))
        }
        "Reg::new" => {
            let bytes = hex_bytes(field(fields, "bytes")?)?;
            let (address, size) = (cells("address_cells")?, cells("size_cells")?);
            Some(outcome(Reg::new(&bytes, address, size), ask, reg_answer))
        }
        "AddressMap::new" => {
            let bytes = match field(fields, "bytes")? {
                "-" => None,
                text => Some(hex_bytes(text)?),
            };
            let (child, parent, size) = (
                cells("child_cells")?,
                cells("parent_cells")?,
                cells("size_cells")?,
            );
            let map = AddressMap::new(bytes.as_deref(), child, parent, size);
            Some(outcome(map, ask, map_answer))
        }
        "logical_id" => {
            let profile = profile(field(fields, "profile")?)?;
            let mpidr = number64(field(fields, "mpidr")?)?;
            let id: Result<Option<u64>, Error> = Ok(profile.logical_id(mpidr));
            Some(outcome(id, ask, |id, asked| {
                (asked == "id").then(|| match id {
                    Some(id) => id.to_string(),
                    None => "-".to_string(),
                })
            }))
        }
        "all_ram" => {
            let ram = spans(field(fields, "ram")?)?;
            let boot = spans(field(fields, "boot")?)?;
            let firmware = regions(field(fields, "firmware")?)?;
            Some(plan_outcome(
                MemoryPlan::all_ram(&ram, &boot, &firmware),
                ask,
            ))
        }
        "MemoryPlan::new" => {
            let window = span(field(fields, "window")?)?;
            let ram = spans(field(fields, "ram")?)?;
            let boot = spans(field(fields, "boot")?)?;
            let firmware = regions(field(fields, "firmware")?)?;
            Some(plan_outcome(
                MemoryPlan::new(window, &ram, &boot, &firmware),
                ask,
            ))
        }
        _ => None,
    }
}

/// The entries without a tree.
const VALUE_ENTRIES: [&str; 6] = [
    "cells_u64",
    "Reg::new",
    "AddressMap::new",
    "logical_id",
    "all_ram",
    "MemoryPlan::new",
];

/// The output of the code for the input of one vector.
fn run_case(input: &str) -> String {
    let fields = fields(input);
    let Some(entry) = field(&fields, "entry") else {
        return "result=malformed entry".to_string();
    };
    let ask: Vec<&str> = match field(&fields, "ask") {
        None | Some("") => Vec::new(),
        Some(ask) => ask.split(',').collect(),
    };
    if VALUE_ENTRIES.contains(&entry) {
        return value_case(entry, &fields, &ask)
            .unwrap_or_else(|| "result=malformed input".to_string());
    }
    let Some(dtb) = field(&fields, "dtb").and_then(hex_bytes) else {
        return "result=malformed dtb".to_string();
    };
    if entry == "parse" {
        return parse_case(&dtb, &ask);
    }
    match Fdt::parse(&dtb) {
        Err(error) => error_text(error),
        Ok(tree) => tree_case(tree, entry, &fields, &ask),
    }
}

/// The vector file of the component, below the repository root.
const VECTORS: &str = "verification/vectors/boot-platform/fdt.vectors";

/// The number of vectors of the file: 53 vectors with lines, 849 lines.
const LINES: usize = 849;

/// The result file below the directory of `KREPI_VECTOR_RESULTS`.
const RESULTS: &str = "boot-platform/fdt.results";

#[test]
fn the_frozen_vectors_give_their_expected_outputs() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let text = std::fs::read_to_string(root.join(VECTORS)).expect("the vector file");
    let mut results = String::new();
    let mut differences = Vec::new();
    let mut lines = 0;
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let parts: Vec<&str> = line.split('\t').collect();
        let [id, input, expected] = parts[..] else {
            panic!("a malformed vector line: {line}");
        };
        let output = run_case(input);
        if output != expected {
            differences.push(format!("{id}: expected {expected}, got {output}"));
        }
        results.push_str(&format!("{id}\t{output}\n"));
        lines += 1;
    }
    assert_eq!(lines, LINES);
    assert!(
        differences.is_empty(),
        "{} vectors differ:\n{}",
        differences.len(),
        differences.join("\n")
    );
    if let Some(directory) = std::env::var_os("KREPI_VECTOR_RESULTS") {
        let path = std::path::Path::new(&directory).join(RESULTS);
        std::fs::create_dir_all(path.parent().expect("a directory")).expect("the directory");
        std::fs::write(&path, results).expect("the result file");
    }
}
