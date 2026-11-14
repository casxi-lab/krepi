//! The waiver record `verification/waivers.json`, as "Waivers" in
//! `docs/formal-verification.md` describes it: each waiver names the
//! registered targets that it covers, why, the author of the pull request
//! that adds it, and the last UTC date on which it holds.

use serde::Deserialize;
use time::{Date, Month};

use super::{lean, registry::Target};

/// The waiver record: schema 1 and its waivers.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct File {
    schema: u32,
    waivers: Vec<Waiver>,
}

/// A waiver of the targets of `scope` through the UTC date `expires`.
#[derive(Debug, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Waiver {
    pub reason: String,
    pub scope: Vec<String>,
    pub expires: String,
    pub author: String,
}

/// The waivers of the waiver record `text`, none without a record, or its
/// problems: a schema other than 1 or an unknown field, and a waiver with a
/// blank reason or author, an empty scope, a name in it that `targets` does
/// not register, or an expiry that is no date of the calendar.
pub fn parse(text: Option<&str>, targets: &[Target]) -> Result<Vec<Waiver>, String> {
    let text = text.unwrap_or(r#"{"schema": 1, "waivers": []}"#);
    let file: File = lean::registry(text, |file: &File| file.schema)?;
    let mut problems = Vec::new();
    for (at, waiver) in file.waivers.iter().enumerate() {
        let fields = [("reason", &waiver.reason), ("author", &waiver.author)];
        let blank = (fields.into_iter()).filter(|(_, value)| value.trim().is_empty());
        let mut found = Vec::from_iter(blank.map(|(field, _)| format!("its {field} is blank")));
        let empty = (waiver.scope.is_empty()).then(|| "its scope is empty".to_string());
        let unknown = (waiver.scope.iter()).filter(|n| !targets.iter().any(|t| t.name == **n));
        let unknown = unknown.map(|name| format!("{name:?} is no registered target"));
        let expires = &waiver.expires;
        let not = format!("its expiry {expires:?} is no date YYYY-MM-DD");
        let not = (!is_date(expires)).then_some(not);
        found.extend(empty.into_iter().chain(unknown).chain(not));
        problems.extend(found.iter().map(|found| format!("waiver {at}: {found}")));
    }
    let waivers = problems.is_empty().then_some(file.waivers);
    waivers.ok_or(problems.join("; "))
}

/// Whether `text` is a date of the calendar written `YYYY-MM-DD`, as the
/// crate writes it: such texts sort as their dates do.
fn is_date(text: &str) -> bool {
    let number = |at: std::ops::Range<usize>| text.get(at)?.parse::<i32>().ok();
    let part = |at| u8::try_from(number(at)?).ok();
    let month = || Month::try_from(part(5..7)?).ok();
    let date = || Date::from_calendar_date(number(0..4)?, month()?, part(8..10)?).ok();
    date().is_some_and(|date| date.to_string() == text)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::formal::{Layout, registry};

    /// The formal target `a` and the planned target `b`.
    fn targets() -> Vec<Target> {
        let text =
            json!({"schema": 2, "targets": [{"name": "a"}, {"name": "b", "state": "planned"}]});
        registry::parse(&text.to_string())
            .expect("a registry")
            .targets
    }

    /// A waiver of `scope` until `expires`.
    fn waiver(scope: &[&str], expires: &str) -> serde_json::Value {
        json!({"reason": "The proofs wait for a fix of the tool.", "scope": scope, "expires": expires, "author": "someone"})
    }

    fn parsed(waivers: &[serde_json::Value]) -> Result<Vec<Waiver>, String> {
        let text = json!({"schema": 1, "waivers": waivers}).to_string();
        parse(Some(&text), &targets())
    }

    #[test]
    fn a_missing_or_the_committed_waiver_record_has_no_waivers() {
        assert_eq!(parse(None, &targets()), Ok(Vec::new()));
        let committed = include_str!("../../../verification/waivers.json");
        assert_eq!(parse(Some(committed), &[]), Ok(Vec::new()));
        assert_eq!(Layout::PRODUCTION.waivers, "verification/waivers.json");
    }

    #[test]
    fn a_waiver_names_registered_targets_planned_ones_included_until_a_date() {
        let found = parsed(&[waiver(&["a", "b", "a"], "2024-02-29")]);
        let expected = Waiver {
            reason: "The proofs wait for a fix of the tool.".to_string(),
            scope: ["a", "b", "a"].map(String::from).into(),
            expires: "2024-02-29".to_string(),
            author: "someone".to_string(),
        };
        assert_eq!(found, Ok(vec![expected]));
    }

    #[test]
    fn a_waiver_record_breaks_its_rules_with_each_problem() {
        let mut blank = waiver(&[], "2026-02-29");
        (blank["reason"], blank["author"]) = (json!(" "), json!(""));
        let unknown = waiver(&["a", "x"], "2026-1-01");
        assert_eq!(
            parsed(&[waiver(&["a"], "9999-12-31"), blank, unknown]),
            Err([
                "waiver 1: its reason is blank",
                "waiver 1: its author is blank",
                "waiver 1: its scope is empty",
                "waiver 1: its expiry \"2026-02-29\" is no date YYYY-MM-DD",
                "waiver 2: \"x\" is no registered target",
                "waiver 2: its expiry \"2026-1-01\" is no date YYYY-MM-DD",
            ]
            .join("; "))
        );
        let mut extra = waiver(&["a"], "2026-01-01");
        extra["approved"] = json!(true);
        let error = parsed(&[extra]).expect_err("an unknown field");
        assert!(error.starts_with("unknown field `approved`"), "{error}");
        let other = json!({"schema": 2, "waivers": []}).to_string();
        let error = parse(Some(&other), &targets());
        assert_eq!(error, Err("schema 2 where 1 is expected".to_string()));
    }

    #[test]
    fn an_expiry_is_a_date_of_the_calendar_in_its_written_form() {
        for date in ["1970-01-01", "2024-02-29", "2026-12-31", "9999-12-31"] {
            assert!(is_date(date), "{date}");
        }
        for text in [
            "",
            "2026-02-29",
            "2026-13-01",
            "2026-00-10",
            "2026-04-31",
            "2026-1-01",
            "+026-01-01",
            "2026/01/01",
            "2026-01-01 ",
            "20260-01-01",
        ] {
            assert!(!is_date(text), "{text:?}");
        }
    }
}
