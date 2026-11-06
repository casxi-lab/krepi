//! Line matchers over raw serial bytes, and the parsers of the serial
//! records that a guest prints: the ready and halt lines, the CPU identity,
//! the breakpoint exception, the fault trace of a fatal diagnostic, object
//! records, build-ids and records of `key=value` fields.
//!
//! The records are those of the prototype kernel, whose names start with
//! `CASXI_`. The QEMU and board captures read them until the kernel of this
//! repository defines its own records.
//!
//! A line is a run of bytes terminated by `\n`, with one optional `\r` before
//! the terminator, that starts at the start of the buffer or after a `\n`. A
//! match reports the byte range of the line including its terminator, so that
//! a caller can continue scanning after it. A line without its terminator is
//! not complete and matches nothing.
//!
//! Messages write the bytes of a rejected line, token or record with the
//! escapes of `<[u8]>::escape_ascii`, and a list of names in Rust's debug
//! form.

use crate::Failure;
use crate::report::{Map, Value};
use serde_json::json;

/// A matched line: `start` is the first byte of the line, `end` the byte after
/// its terminator, both relative to the scanned slice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Match {
    pub start: usize,
    pub end: usize,
    pub captures: Vec<Vec<u8>>,
}

/// Iterates over complete lines of `buffer`, yielding `(start, content, end)`
/// where `content` excludes the terminator and one optional trailing `\r`.
pub fn lines(buffer: &[u8]) -> impl Iterator<Item = (usize, &[u8], usize)> {
    let mut position = 0;
    std::iter::from_fn(move || {
        if position >= buffer.len() {
            return None;
        }
        let rest = &buffer[position..];
        let newline = rest.iter().position(|&b| b == b'\n')?;
        let start = position;
        let end = position + newline + 1;
        let mut content = &rest[..newline];
        if let Some(stripped) = content.strip_suffix(b"\r") {
            content = stripped;
        }
        position = end;
        Some((start, content, end))
    })
}

/// The first complete line whose content satisfies `predicate`.
pub fn find_line<F>(buffer: &[u8], predicate: F) -> Option<Match>
where
    F: Fn(&[u8]) -> Option<Vec<Vec<u8>>>,
{
    for (start, content, end) in lines(buffer) {
        if let Some(captures) = predicate(content) {
            return Some(Match {
                start,
                end,
                captures,
            });
        }
    }
    None
}

/// A line equal to `expected`, ignoring a leading `\r` left by echoed input.
pub fn exact_line(buffer: &[u8], expected: &[u8]) -> Option<Match> {
    find_line(buffer, |content| {
        let content = content.strip_prefix(b"\r").unwrap_or(content);
        (content == expected).then(Vec::new)
    })
}

/// `CASXI_READY`.
pub fn ready(buffer: &[u8]) -> Option<Match> {
    exact_line(buffer, b"CASXI_READY")
}

/// A matcher for the exact line `text`, for callers that need a closure-free
/// `wait_for` argument.
pub fn ready_line_named(text: &'static str) -> impl Fn(&[u8]) -> Option<Match> {
    move |buffer| exact_line(buffer, text.as_bytes())
}

/// `CASXI_HALTED`.
pub fn halted(buffer: &[u8]) -> Option<Match> {
    exact_line(buffer, b"CASXI_HALTED")
}

/// `CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x<16 hex>[ rest]`;
/// the capture is the ELR hex digits.
pub fn brk_exception(buffer: &[u8]) -> Option<Match> {
    const PREFIX: &[u8] = b"CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x";
    find_line(buffer, |content| {
        let rest = content.strip_prefix(PREFIX)?;
        if rest.len() < 16 || !rest[..16].iter().all(u8::is_ascii_hexdigit) {
            return None;
        }
        match &rest[16..] {
            [] => Some(vec![rest[..16].to_vec()]),
            [b' ', tail @ ..] if !tail.is_empty() && !tail.contains(&b'\r') => {
                Some(vec![rest[..16].to_vec()])
            }
            _ => None,
        }
    })
}

/// The lines of `output` that start with `prefix`, where a line ends at
/// `\n` or `\r`.
pub fn records_with_prefix<'a>(output: &'a [u8], prefix: &[u8]) -> Vec<&'a [u8]> {
    output
        .split(|&b| b == b'\n' || b == b'\r')
        .filter(|line| line.starts_with(prefix))
        .collect()
}

/// The CPU identity record `CASXI_CPU model=cortex-a76 midr=0x<16 hex>`:
/// exactly one record, implementer Arm and part Cortex-A76 independent of
/// variant and revision. Returns `(model, midr)` with `midr` as `0x` and 16
/// lowercase hex digits.
pub fn check_cpu_identity(output: &[u8]) -> Result<(String, String), Failure> {
    let records = records_with_prefix(output, b"CASXI_CPU");
    if records.len() != 1 {
        return Err(Failure::new(format!(
            "Expected one CPU identity record, got {}",
            records.len()
        )));
    }
    let record = records[0];
    let invalid = || {
        Failure::new(format!(
            "Invalid CPU identity record: {}",
            record.escape_ascii()
        ))
    };
    let rest = record
        .strip_prefix(b"CASXI_CPU model=cortex-a76 midr=0x")
        .ok_or_else(invalid)?;
    if rest.len() != 16 || !rest.iter().all(u8::is_ascii_hexdigit) {
        return Err(invalid());
    }
    let midr = u64::from_str_radix(std::str::from_utf8(rest).map_err(|_| invalid())?, 16)
        .map_err(|_| invalid())?;
    if midr & 0xff00_fff0 != 0x4100_d0b0 {
        return Err(Failure::new(format!(
            "CPU identity is not Arm Cortex-A76: MIDR={midr:#018x}"
        )));
    }
    Ok(("cortex-a76".to_string(), format!("{midr:#018x}")))
}

// --- bounded fault traces --------------------------------------------------------

/// The raw register record that opens a fault trace. Hexadecimal fields keep
/// their sixteen digits without the `0x` prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FaultRegisters {
    pub build_id: String,
    pub source: String,
    pub pc: String,
    pub sp: String,
    pub fp: String,
    pub lr: String,
}

/// The `CASXI_TRACE` record that closes the frame chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceStop {
    pub frames: usize,
    pub reason: String,
    pub fp: u64,
}

/// Strict parser of the fault trace a fatal diagnostic prints: one
/// `CASXI_DIAG` register record, at most sixteen `CASXI_BT` frames whose frame
/// pointers are aligned, above SP and increasing, one `CASXI_TRACE` stop whose
/// count and reason agree with the frames, then `CASXI_HALTED` and nothing
/// else. `feed` takes one line at a time and returns true at the halt.
#[derive(Debug, Default)]
pub struct DiagnosticCheck {
    header: Option<FaultRegisters>,
    frames: Vec<(u64, u64)>,
    stop: Option<TraceStop>,
    halted: bool,
}

const STOP_REASONS: [&str; 8] = [
    "end",
    "invalid_bounds",
    "misaligned",
    "address_overflow",
    "out_of_bounds",
    "non_increasing",
    "unreadable",
    "depth_limit",
];

fn take_literal<'a>(rest: &'a [u8], literal: &[u8]) -> Option<&'a [u8]> {
    rest.strip_prefix(literal)
}

/// Exactly `count` lowercase hexadecimal digits.
fn take_hex(rest: &[u8], count: usize) -> Option<(&str, &[u8])> {
    let digits = rest.get(..count)?;
    if !digits
        .iter()
        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
    {
        return None;
    }
    Some((std::str::from_utf8(digits).ok()?, &rest[count..]))
}

/// One or more of `[a-z_]`.
fn take_word(rest: &[u8]) -> Option<(&str, &[u8])> {
    let count = rest
        .iter()
        .take_while(|b| b.is_ascii_lowercase() || **b == b'_')
        .count();
    if count == 0 {
        return None;
    }
    Some((std::str::from_utf8(&rest[..count]).ok()?, &rest[count..]))
}

fn parse_header(line: &[u8]) -> Option<FaultRegisters> {
    let rest = take_literal(line, b"CASXI_DIAG build_id=")?;
    let (build_id, rest) = take_hex(rest, 40)?;
    let rest = take_literal(rest, b" source=")?;
    let (source, rest) = take_word(rest)?;
    if !["exception", "panic", "probe"].contains(&source) {
        return None;
    }
    let rest = take_literal(rest, b" pc=0x")?;
    let (pc, rest) = take_hex(rest, 16)?;
    let rest = take_literal(rest, b" sp=0x")?;
    let (sp, rest) = take_hex(rest, 16)?;
    let rest = take_literal(rest, b" fp=0x")?;
    let (fp, rest) = take_hex(rest, 16)?;
    let rest = take_literal(rest, b" lr=0x")?;
    let (lr, rest) = take_hex(rest, 16)?;
    let rest = take_literal(rest, b" process=none thread=none epoch=none")?;
    rest.is_empty().then(|| FaultRegisters {
        build_id: build_id.to_string(),
        source: source.to_string(),
        pc: pc.to_string(),
        sp: sp.to_string(),
        fp: fp.to_string(),
        lr: lr.to_string(),
    })
}

fn parse_frame(line: &[u8]) -> Option<(Option<usize>, u64, u64)> {
    let rest = take_literal(line, b"CASXI_BT index=")?;
    let count = rest.iter().take_while(|b| b.is_ascii_digit()).count();
    if count == 0 {
        return None;
    }
    let index = std::str::from_utf8(&rest[..count]).ok()?.parse().ok();
    let rest = take_literal(&rest[count..], b" fp=0x")?;
    let (fp, rest) = take_hex(rest, 16)?;
    let rest = take_literal(rest, b" lr=0x")?;
    let (lr, rest) = take_hex(rest, 16)?;
    rest.is_empty()
        .then(|| (index, hex_value(fp), hex_value(lr)))
}

fn parse_stop(line: &[u8]) -> Option<(Option<usize>, String, u64)> {
    let rest = take_literal(line, b"CASXI_TRACE frames=")?;
    let count = rest.iter().take_while(|b| b.is_ascii_digit()).count();
    if count == 0 {
        return None;
    }
    let frames = std::str::from_utf8(&rest[..count]).ok()?.parse().ok();
    let rest = take_literal(&rest[count..], b" stop=")?;
    let (reason, rest) = take_word(rest)?;
    let rest = take_literal(rest, b" stop_fp=0x")?;
    let (fp, rest) = take_hex(rest, 16)?;
    rest.is_empty()
        .then(|| (frames, reason.to_string(), hex_value(fp)))
}

/// The value of up to sixteen validated hexadecimal digits.
pub fn hex_value(digits: &str) -> u64 {
    u64::from_str_radix(digits, 16).expect("validated hexadecimal digits")
}

impl DiagnosticCheck {
    pub fn new() -> Self {
        Self::default()
    }

    /// The register record, once the header line has been accepted.
    pub fn registers(&self) -> Option<&FaultRegisters> {
        self.header.as_ref()
    }

    /// True once `CASXI_HALTED` closed the trace.
    pub fn halted(&self) -> bool {
        self.halted
    }

    /// Accepts one line (without terminator); true once `CASXI_HALTED` closed
    /// a complete trace.
    pub fn feed(&mut self, line: &[u8]) -> Result<bool, Failure> {
        if self.halted {
            return Err(Failure::new("Output after HALTED"));
        }
        let Some(header) = &self.header else {
            let parsed = parse_header(line).ok_or_else(|| {
                Failure::new(format!(
                    "Expected build-bound raw register record: {}",
                    line.escape_ascii()
                ))
            })?;
            self.header = Some(parsed);
            return Ok(false);
        };
        if let Some((index, fp, lr)) = parse_frame(line) {
            if self.stop.is_some()
                || index != Some(self.frames.len())
                || index.is_none_or(|index| index >= 16)
                || fp % 16 != 0
            {
                return Err(Failure::new(
                    "Invalid trace sequence, frame alignment or depth",
                ));
            }
            if self.frames.is_empty() && fp != hex_value(&header.fp) {
                return Err(Failure::new("First frame does not match saved FP"));
            }
            if fp < hex_value(&header.sp) || self.frames.last().is_some_and(|last| fp <= last.0) {
                return Err(Failure::new("Frame chain crossed SP or failed to advance"));
            }
            self.frames.push((fp, lr));
        } else if let Some((frames, reason, fp)) = parse_stop(line) {
            if self.stop.is_some() || frames != Some(self.frames.len()) {
                return Err(Failure::new("Trace stop count mismatch or duplicate"));
            }
            if !STOP_REASONS.contains(&reason.as_str())
                || (reason == "end" && fp != 0)
                || (reason == "depth_limit" && frames != Some(16))
            {
                return Err(Failure::new("Invalid trace stop reason/bound"));
            }
            self.stop = Some(TraceStop {
                frames: self.frames.len(),
                reason,
                fp,
            });
        } else if line == b"CASXI_HALTED" && self.stop.is_some() {
            self.halted = true;
            return Ok(true);
        } else {
            return Err(Failure::new(format!(
                "Unexpected diagnostic output: {}",
                line.escape_ascii()
            )));
        }
        Ok(false)
    }

    /// The trace as a report records it: `registers`, `frames` and `stop`,
    /// each with its keys in the order of its record.
    pub fn result(&self) -> Result<Value, Failure> {
        let (Some(header), Some(stop)) = (&self.header, &self.stop) else {
            return Err(Failure::new("Incomplete trace"));
        };
        let frames: Vec<Value> = self
            .frames
            .iter()
            .map(|(fp, lr)| json!({ "fp": fp, "lr": lr }))
            .collect();
        Ok(json!({
            "registers": {
                "build_id": header.build_id,
                "source": header.source,
                "pc": header.pc,
                "sp": header.sp,
                "fp": header.fp,
                "lr": header.lr,
            },
            "frames": frames,
            "stop": {
                "frames": stop.frames,
                "reason": stop.reason,
                "fp": stop.fp,
            },
        }))
    }
}

/// `marker key=value ...` records with exactly the `expected` field names:
/// ASCII keys and values, none empty, none repeated. Fields are separated by
/// the bytes that `u8::is_ascii_whitespace` accepts: space, `\t`, `\n`,
/// `\x0c` and `\r`, but not the vertical tab `\x0b`, which stays inside its
/// token. The result keeps record order.
///
/// A token without `=` is `Malformed <marker> field: <token>`, an empty name
/// or value or a repeated name is `Empty or duplicate field: <token>`, with
/// the token's bytes escaped, and a set of names other than the expected one
/// is `Unexpected <marker> fields: <names>`, the names of the record sorted
/// by their bytes in Rust's debug form, such as `["a", "b"]`.
pub fn parse_fields(
    line: &[u8],
    marker: &str,
    expected: &[&str],
) -> Result<Vec<(String, String)>, Failure> {
    let tokens: Vec<&[u8]> = line
        .split(|b| b.is_ascii_whitespace())
        .filter(|t| !t.is_empty())
        .collect();
    if tokens.is_empty() || tokens[0] != marker.as_bytes() {
        return Err(Failure::new(format!("Missing {marker} record")));
    }
    let mut fields: Vec<(String, String)> = Vec::new();
    for token in &tokens[1..] {
        let Some(split) = token.iter().position(|&b| b == b'=') else {
            return Err(Failure::new(format!(
                "Malformed {marker} field: {}",
                token.escape_ascii()
            )));
        };
        let (key, value) = (&token[..split], &token[split + 1..]);
        if !key.is_ascii() || !value.is_ascii() {
            return Err(Failure::new(format!("Non-ASCII {marker} record")));
        }
        let (name, text) = (
            String::from_utf8_lossy(key).into_owned(),
            String::from_utf8_lossy(value).into_owned(),
        );
        if name.is_empty() || text.is_empty() || fields.iter().any(|(k, _)| *k == name) {
            return Err(Failure::new(format!(
                "Empty or duplicate field: {}",
                token.escape_ascii()
            )));
        }
        fields.push((name, text));
    }
    let mut names: Vec<&str> = fields.iter().map(|(k, _)| k.as_str()).collect();
    names.sort_unstable();
    let mut wanted: Vec<&str> = expected.to_vec();
    wanted.sort_unstable();
    wanted.dedup();
    if names != wanted {
        return Err(Failure::new(format!(
            "Unexpected {marker} fields: {names:?}"
        )));
    }
    Ok(fields)
}

// --- object records and trace transcripts ------------------------------------------

/// The fields of a `CASXI_OBJECTS` record, each of which the record holds
/// exactly once.
pub const OBJECT_FIELDS: [&str; 12] = [
    "cycle",
    "selftest",
    "checks",
    "root_process",
    "root_thread",
    "processes",
    "threads",
    "reserved_processes",
    "reserved_threads",
    "temporary_generation",
    "created_processes",
    "reaped_processes",
];

/// `name=value` pairs of one `CASXI_OBJECTS` record in record order: every
/// field of [`OBJECT_FIELDS`] present exactly once and no other, every field
/// but `selftest` a decimal count below 2^64, retained root handles, two
/// reserved slots of each kind and eighteen self-test checks.
pub fn object_fields(raw: &[u8]) -> Result<Vec<(String, String)>, Failure> {
    let text = String::from_utf8_lossy(raw);
    let mut pairs: Vec<(String, String)> = Vec::new();
    for part in text.split_ascii_whitespace().skip(1) {
        let (key, value) = part
            .split_once('=')
            .ok_or_else(|| Failure::new("Malformed object record"))?;
        pairs.push((key.to_string(), value.to_string()));
    }
    let mut names: Vec<&str> = pairs.iter().map(|(k, _)| k.as_str()).collect();
    names.sort_unstable();
    let mut expected: Vec<&str> = OBJECT_FIELDS.to_vec();
    expected.sort_unstable();
    if names != expected {
        return Err(Failure::new("Missing/duplicate/unexpected object fields"));
    }
    for (key, value) in &pairs {
        if key == "selftest" {
            continue;
        }
        let numeric = !value.is_empty()
            && value.bytes().all(|b| b.is_ascii_digit())
            && value.parse::<u64>().is_ok();
        if !numeric {
            return Err(Failure::new(format!("Invalid object field {key}")));
        }
    }
    let field = |name: &str| object_field(&pairs, name).unwrap_or("");
    let positive = |name: &str| field(name).parse::<u64>().map(|v| v > 0).unwrap_or(false);
    if !(positive("root_process")
        && positive("root_thread")
        && field("reserved_processes") == "2"
        && field("reserved_threads") == "2"
        && field("checks") == "18")
    {
        return Err(Failure::new(
            "Missing retained root/reserve/selftest coverage",
        ));
    }
    Ok(pairs)
}

/// The value of `name` in parsed object fields.
pub fn object_field<'a>(fields: &'a [(String, String)], name: &str) -> Option<&'a str> {
    fields
        .iter()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value.as_str())
}

/// Object fields as a report records them: an object of strings in record
/// order.
pub fn fields_value(fields: &[(String, String)]) -> Value {
    let mut value = Map::new();
    for (key, text) in fields {
        value.insert(key.clone(), Value::String(text.clone()));
    }
    Value::Object(value)
}

/// The lines of `raw`, split at `\n`, at `\r` and at `\r\n`, which counts as
/// one terminator. A terminator at the end of `raw` ends the last line and is
/// not followed by an empty one.
pub fn split_lines(raw: &[u8]) -> Vec<&[u8]> {
    let mut lines = Vec::new();
    let mut start = 0;
    let mut index = 0;
    while index < raw.len() {
        match raw[index] {
            b'\n' => {
                lines.push(&raw[start..index]);
                index += 1;
                start = index;
            }
            b'\r' => {
                lines.push(&raw[start..index]);
                index += if raw.get(index + 1) == Some(&b'\n') {
                    2
                } else {
                    1
                };
                start = index;
            }
            _ => index += 1,
        }
    }
    if start < raw.len() {
        lines.push(&raw[start..]);
    }
    lines
}

/// Every `CASXI_BUILD build_id=<40 hex>` identity in `buffer`.
pub fn build_ids(buffer: &[u8]) -> Vec<String> {
    const PREFIX: &[u8] = b"CASXI_BUILD build_id=";
    let mut found = Vec::new();
    let mut position = 0;
    while position + PREFIX.len() <= buffer.len() {
        if buffer[position..].starts_with(PREFIX) {
            let digits = &buffer[position + PREFIX.len()..];
            if digits.len() >= 40
                && digits[..40]
                    .iter()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
            {
                found.push(String::from_utf8_lossy(&digits[..40]).into_owned());
                position += PREFIX.len() + 40;
                continue;
            }
        }
        position += 1;
    }
    found
}

/// The first `CASXI_EXCEPTION vector=4 ESR=0x<16 hex> ELR=0x<16 hex>` in
/// `raw`; the ELR digits.
fn raw_exception_elr(raw: &[u8]) -> Option<String> {
    const PREFIX: &[u8] = b"CASXI_EXCEPTION vector=4 ESR=0x";
    let hex = |b: &u8| b.is_ascii_digit() || (b'a'..=b'f').contains(b);
    let mut position = 0;
    while position + PREFIX.len() <= raw.len() {
        if raw[position..].starts_with(PREFIX) {
            let rest = &raw[position + PREFIX.len()..];
            if rest.len() >= 16 + 7 + 16
                && rest[..16].iter().all(hex)
                && &rest[16..23] == b" ELR=0x"
                && rest[23..39].iter().all(hex)
            {
                return Some(String::from_utf8_lossy(&rest[23..39]).into_owned());
            }
        }
        position += 1;
    }
    None
}

/// Parses the one fault trace in a transcript: exactly one `CASXI_DIAG`
/// header, the frames and stop after it, which [`DiagnosticCheck`] checks
/// line by line, the halt if and only if `require_halt`, the expected
/// `source`, and for an exception a `pc` equal to the ELR of the raw
/// exception record.
pub fn trace(raw: &[u8], expected_source: &str, require_halt: bool) -> Result<Value, Failure> {
    let lines = split_lines(raw);
    let starts: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.starts_with(b"CASXI_DIAG "))
        .map(|(index, _)| index)
        .collect();
    if starts.len() != 1 {
        return Err(Failure::new("Missing/duplicate diagnostic header"));
    }
    let mut check = DiagnosticCheck::new();
    for line in &lines[starts[0]..] {
        if !line.is_empty() {
            check.feed(line)?;
        }
    }
    let result = check.result()?;
    if check.halted() != require_halt {
        return Err(Failure::new("Wrong trace halt boundary"));
    }
    let registers = check.registers().expect("result requires a header");
    if registers.source != expected_source {
        return Err(Failure::new("Wrong trace source"));
    }
    if expected_source == "exception"
        && raw_exception_elr(raw).as_deref() != Some(registers.pc.as_str())
    {
        return Err(Failure::new("Raw exception ELR and diagnostic PC differ"));
    }
    Ok(result)
}

#[cfg(test)]
mod tests;
