//! Report values and their JSON text, and the UTC time stamps that reports
//! record.
//!
//! The JSON text has the form of the receipt of `cargo xtask check`: objects
//! keep the order in which their keys were set, nested values are indented
//! by two spaces, quotes, backslashes and control characters are escaped,
//! and every other character is kept as UTF-8.

use std::fmt::Write as _;
use std::time::{SystemTime, UNIX_EPOCH};

/// A JSON value with ordered object keys.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i64),
    UInt(u64),
    /// An unsigned integer beyond 64 bits.
    Big(u128),
    Float(f64),
    Str(String),
    Array(Vec<Value>),
    Object(Vec<(String, Value)>),
}

impl Value {
    pub fn object() -> Self {
        Value::Object(Vec::new())
    }

    /// Sets `key`, replacing an existing entry in place.
    pub fn set(&mut self, key: &str, value: impl Into<Value>) {
        let Value::Object(entries) = self else {
            panic!("set on a non-object value");
        };
        let value = value.into();
        match entries.iter_mut().find(|(k, _)| k == key) {
            Some(entry) => entry.1 = value,
            None => entries.push((key.to_string(), value)),
        }
    }

    /// Sets `key` as the first entry of an object; an existing entry is
    /// replaced in place.
    pub fn insert_front(&mut self, key: &str, value: impl Into<Value>) {
        let Value::Object(entries) = self else {
            panic!("insert_front on a non-object value");
        };
        let value = value.into();
        match entries.iter_mut().find(|(k, _)| k == key) {
            Some(entry) => entry.1 = value,
            None => entries.insert(0, (key.to_string(), value)),
        }
    }

    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        match self {
            Value::Object(entries) => entries.iter_mut().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        match self {
            Value::Object(entries) => entries.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    pub fn push(&mut self, value: impl Into<Value>) {
        let Value::Array(items) = self else {
            panic!("push on a non-array value");
        };
        items.push(value.into());
    }

    pub fn as_array_mut(&mut self) -> Option<&mut Vec<Value>> {
        match self {
            Value::Array(items) => Some(items),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }

    /// A non-negative integer of either integer variant.
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Value::Int(i) => u64::try_from(*i).ok(),
            Value::UInt(i) => Some(*i),
            Value::Big(i) => u64::try_from(*i).ok(),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Value]> {
        match self {
            Value::Array(items) => Some(items),
            _ => None,
        }
    }

    /// The JSON text of the value with two-space indentation and a final
    /// newline.
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        self.write(&mut out, 0);
        out.push('\n');
        out
    }

    /// The same value with the keys of every object sorted by their UTF-8
    /// bytes, which is the order of their code points.
    pub fn sorted(&self) -> Value {
        match self {
            Value::Array(items) => Value::Array(items.iter().map(Value::sorted).collect()),
            Value::Object(entries) => {
                let mut sorted: Vec<(String, Value)> = entries
                    .iter()
                    .map(|(k, v)| (k.clone(), v.sorted()))
                    .collect();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                Value::Object(sorted)
            }
            other => other.clone(),
        }
    }

    fn write(&self, out: &mut String, depth: usize) {
        match self {
            Value::Null => out.push_str("null"),
            Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Value::Int(i) => write!(out, "{i}").expect("write to string"),
            Value::UInt(i) => write!(out, "{i}").expect("write to string"),
            Value::Big(i) => write!(out, "{i}").expect("write to string"),
            Value::Float(f) => write_float(out, *f),
            Value::Str(s) => write_string(out, s),
            Value::Array(items) => {
                if items.is_empty() {
                    out.push_str("[]");
                    return;
                }
                out.push('[');
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    out.push('\n');
                    indent(out, depth + 1);
                    item.write(out, depth + 1);
                }
                out.push('\n');
                indent(out, depth);
                out.push(']');
            }
            Value::Object(entries) => {
                if entries.is_empty() {
                    out.push_str("{}");
                    return;
                }
                out.push('{');
                for (index, (key, value)) in entries.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    out.push('\n');
                    indent(out, depth + 1);
                    write_string(out, key);
                    out.push_str(": ");
                    value.write(out, depth + 1);
                }
                out.push('\n');
                indent(out, depth);
                out.push('}');
            }
        }
    }
}

fn indent(out: &mut String, depth: usize) {
    for _ in 0..depth {
        out.push_str("  ");
    }
}

/// A finite float in its shortest round-trip digits: positional, with at
/// least one fractional digit, for decimal exponents from -4 to 15, and
/// otherwise scientific with an unpadded exponent that carries a sign only
/// when it is negative (`1e-5`, `1e16`). JSON has no form for a NaN or an
/// infinity, so they are written as `null`.
fn write_float(out: &mut String, value: f64) {
    if !value.is_finite() {
        out.push_str("null");
        return;
    }
    let scientific = format!("{value:e}");
    let (mantissa, exponent) = scientific.split_once('e').expect("scientific form");
    let exponent: i32 = exponent.parse().expect("decimal exponent");
    let (sign, mantissa) = match mantissa.strip_prefix('-') {
        Some(rest) => ("-", rest),
        None => ("", mantissa),
    };
    let digits: String = mantissa.chars().filter(|c| *c != '.').collect();
    out.push_str(sign);
    if (-4..16).contains(&exponent) {
        if exponent < 0 {
            out.push_str("0.");
            out.push_str(&"0".repeat((-exponent - 1) as usize));
            out.push_str(&digits);
        } else {
            let point = exponent as usize + 1;
            if digits.len() <= point {
                out.push_str(&digits);
                out.push_str(&"0".repeat(point - digits.len()));
                out.push_str(".0");
            } else {
                out.push_str(&digits[..point]);
                out.push('.');
                out.push_str(&digits[point..]);
            }
        }
    } else {
        out.push_str(&digits[..1]);
        if digits.len() > 1 {
            out.push('.');
            out.push_str(&digits[1..]);
        }
        write!(out, "e{exponent}").expect("write to string");
    }
}

/// A JSON string literal: quotes and backslashes are escaped, line feed,
/// carriage return and tab by their short escapes, every other C0 control
/// character and DEL as `\u00XX`, and everything else is kept as UTF-8.
fn write_string(out: &mut String, value: &str) {
    out.push('"');
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if u32::from(c) < 0x20 || c == '\u{7f}' => {
                write!(out, "\\u{:04x}", u32::from(c)).expect("write to string");
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}
impl From<i64> for Value {
    fn from(i: i64) -> Self {
        Value::Int(i)
    }
}
impl From<i32> for Value {
    fn from(i: i32) -> Self {
        Value::Int(i64::from(i))
    }
}
impl From<usize> for Value {
    fn from(i: usize) -> Self {
        Value::Int(i as i64)
    }
}

impl From<u64> for Value {
    fn from(i: u64) -> Self {
        Value::UInt(i)
    }
}

impl From<u32> for Value {
    fn from(i: u32) -> Self {
        Value::UInt(u64::from(i))
    }
}
impl From<f64> for Value {
    fn from(f: f64) -> Self {
        Value::Float(f)
    }
}
impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::Str(s.to_string())
    }
}
impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::Str(s)
    }
}
impl From<Vec<Value>> for Value {
    fn from(items: Vec<Value>) -> Self {
        Value::Array(items)
    }
}
impl From<Vec<String>> for Value {
    fn from(items: Vec<String>) -> Self {
        Value::Array(items.into_iter().map(Value::Str).collect())
    }
}

/// The UTC calendar fields of `time` as `(year, month, day, hour, minute,
/// second, microsecond)`; a time before 1970 counts as the start of 1970.
fn utc_fields(time: SystemTime) -> (i64, u32, u32, u64, u64, u64, u64) {
    let since = time.duration_since(UNIX_EPOCH).unwrap_or_default();
    let seconds = since.as_secs();
    let micros = u64::from(since.subsec_micros());
    let (year, month, day) = civil_from_days((seconds / 86_400) as i64);
    let rest = seconds % 86_400;
    (
        year,
        month,
        day,
        rest / 3600,
        rest % 3600 / 60,
        rest % 60,
        micros,
    )
}

/// `time` in UTC as RFC 3339 with six fraction digits and the offset `Z`,
/// such as `2026-10-14T07:45:17.000123Z`.
pub fn utc_text(time: SystemTime) -> String {
    let (y, mo, d, h, mi, s, us) = utc_fields(time);
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{us:06}Z")
}

/// `time` in UTC in the basic ISO 8601 form `%Y%m%dT%H%M%S.%fZ`, such as
/// `20261014T074517.000123Z`, for names of run directories.
pub fn utc_stamp_of(time: SystemTime) -> String {
    let (y, mo, d, h, mi, s, us) = utc_fields(time);
    format!("{y:04}{mo:02}{d:02}T{h:02}{mi:02}{s:02}.{us:06}Z")
}

/// The current time as [`utc_text`] writes it.
pub fn utc_now() -> String {
    utc_text(SystemTime::now())
}

/// The current time as [`utc_stamp_of`] writes it.
pub fn utc_stamp() -> String {
    utc_stamp_of(SystemTime::now())
}

/// The proleptic Gregorian date of a count of days since 1970-01-01.
fn civil_from_days(days: i64) -> (i64, u32, u32) {
    let shifted = days + 719_468;
    let era = shifted.div_euclid(146_097);
    let day_of_era = shifted.rem_euclid(146_097);
    let year_of_era =
        (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = (day_of_year - (153 * month_index + 2) / 5 + 1) as u32;
    let month = if month_index < 10 {
        month_index + 3
    } else {
        month_index - 9
    } as u32;
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    (year, month, day)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn float_text(value: f64) -> String {
        Value::Float(value).to_json().trim_end().to_string()
    }

    #[test]
    fn floats_print_in_their_shortest_round_trip_form() {
        for (value, text) in [
            (1.0, "1.0"),
            (60000.0, "60000.0"),
            (0.1, "0.1"),
            (-2.5, "-2.5"),
            (0.0001, "0.0001"),
            (1e-5, "1e-5"),
            (8.392747792833824e-8, "8.392747792833824e-8"),
            (123456789012345.67, "123456789012345.67"),
            (1e15, "1000000000000000.0"),
            (1e16, "1e16"),
            (1.5e300, "1.5e300"),
            (5e-324, "5e-324"),
            (73.5, "73.5"),
            (0.0, "0.0"),
            (12345.678901234567, "12345.678901234567"),
        ] {
            assert_eq!(float_text(value), text);
        }
    }

    #[test]
    fn negative_zero_and_values_without_a_json_form() {
        assert_eq!(float_text(-0.0), "-0.0");
        assert_eq!(float_text(-1e-7), "-1e-7");
        assert_eq!(float_text(f64::NAN), "null");
        assert_eq!(float_text(f64::INFINITY), "null");
        assert_eq!(float_text(f64::NEG_INFINITY), "null");
    }

    #[test]
    fn json_has_two_space_indentation_and_keeps_text_as_utf8() {
        let mut report = Value::object();
        report.set("schema_version", 1);
        report.set("status", "PASS");
        report.set("runs", Value::Array(Vec::new()));
        report.set("elapsed_seconds", 0.5);
        report.set("note", "a\"b\\c\n\u{1}é");
        let mut inner = Value::object();
        inner.set("ok", true);
        inner.set("none", Value::Null);
        report.set("inner", inner);
        assert_eq!(
            report.to_json(),
            "{\n  \"schema_version\": 1,\n  \"status\": \"PASS\",\n  \"runs\": [],\n  \"elapsed_seconds\": 0.5,\n  \"note\": \"a\\\"b\\\\c\\n\\u0001é\",\n  \"inner\": {\n    \"ok\": true,\n    \"none\": null\n  }\n}\n"
        );
    }

    #[test]
    fn control_characters_and_del_are_escaped_and_other_text_is_kept() {
        let text = Value::from("\u{0}\u{8}\t\u{c}\r\u{1b}\u{7f} casξ ✓ \u{80}\u{2028}");
        assert_eq!(
            text.to_json(),
            "\"\\u0000\\u0008\\t\\u000c\\r\\u001b\\u007f casξ ✓ \u{80}\u{2028}\"\n"
        );
        let mut keys = Value::object();
        keys.set("port\u{7f}", "/dev/tty\u{e9}");
        assert_eq!(
            keys.to_json(),
            "{\n  \"port\\u007f\": \"/dev/tty\u{e9}\"\n}\n"
        );
    }

    #[test]
    fn arrays_nest_and_integers_of_every_width_print_in_decimal() {
        let mut value = Value::Array(Vec::new());
        value.push(-3i64);
        value.push(u64::MAX);
        value.push(Value::Big(u128::MAX));
        value.push(Value::from(vec!["a".to_string()]));
        assert_eq!(
            value.to_json(),
            "[\n  -3,\n  18446744073709551615,\n  340282366920938463463374607431768211455,\n  [\n    \"a\"\n  ]\n]\n"
        );
    }

    #[test]
    fn set_replaces_in_place() {
        let mut v = Value::object();
        v.set("a", 1);
        v.set("b", 2);
        v.set("a", 3);
        assert_eq!(
            v,
            Value::Object(vec![
                ("a".into(), Value::Int(3)),
                ("b".into(), Value::Int(2))
            ])
        );
        v.insert_front("c", 4);
        v.insert_front("b", 5);
        assert_eq!(
            v,
            Value::Object(vec![
                ("c".into(), Value::Int(4)),
                ("a".into(), Value::Int(3)),
                ("b".into(), Value::Int(5))
            ])
        );
    }

    #[test]
    fn sorting_orders_the_keys_of_every_object_by_code_point() {
        let mut inner = Value::object();
        inner.set("z", 1);
        inner.set("é", 2);
        inner.set("A", 3);
        let mut outer = Value::object();
        outer.set("b", Value::Array(vec![inner]));
        outer.set("a", Value::Null);
        let keys = |value: &Value| match value {
            Value::Object(entries) => entries.iter().map(|(k, _)| k.clone()).collect(),
            _ => Vec::new(),
        };
        let sorted = outer.sorted();
        assert_eq!(keys(&sorted), ["a", "b"]);
        let nested = &sorted.get("b").and_then(Value::as_array).unwrap()[0];
        assert_eq!(keys(nested), ["A", "z", "é"]);
    }

    #[test]
    fn integers_read_back_as_u64_only_when_they_fit() {
        assert_eq!(Value::Int(-1).as_u64(), None);
        assert_eq!(Value::Int(7).as_u64(), Some(7));
        assert_eq!(Value::UInt(u64::MAX).as_u64(), Some(u64::MAX));
        assert_eq!(Value::Big(u128::from(u64::MAX) + 1).as_u64(), None);
        assert_eq!(Value::Float(1.0).as_u64(), None);
    }

    #[test]
    fn timestamps_are_rfc_3339_and_basic_iso_8601_in_utc() {
        // 2026-10-14 is day 20,740 after 1970-01-01.
        let time =
            UNIX_EPOCH + Duration::new(20_740 * 86_400 + 7 * 3600 + 45 * 60 + 17, 123_456_789);
        assert_eq!(utc_text(time), "2026-10-14T07:45:17.123456Z");
        assert_eq!(utc_stamp_of(time), "20261014T074517.123456Z");
        let whole = UNIX_EPOCH + Duration::from_secs(951_782_400);
        assert_eq!(utc_text(whole), "2000-02-29T00:00:00.000000Z");
        assert_eq!(utc_text(UNIX_EPOCH), "1970-01-01T00:00:00.000000Z");
        let before = UNIX_EPOCH - Duration::from_secs(1);
        assert_eq!(utc_text(before), "1970-01-01T00:00:00.000000Z");
        assert_eq!(civil_from_days(20_740), (2026, 10, 14));
        assert_eq!(civil_from_days(-1), (1969, 12, 31));
        // The current time has the same shapes; only its value is unknown.
        assert_eq!(utc_now().len(), "2026-10-14T07:45:17.123456Z".len());
        assert!(utc_now().ends_with('Z'));
        assert_eq!(utc_stamp().len(), "20261014T074517.123456Z".len());
    }
}
