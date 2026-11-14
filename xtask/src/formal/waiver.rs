//! The waiver record `verification/waivers.json`, what its waivers leave
//! out of the base round and how they conclude a merge, as "Waivers" in
//! `docs/formal-verification.md` describes them.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use time::{Date, Month, UtcDateTime};

use super::receipt::{Merge, Receipt, Waived};
use super::registry::{State, Target};
use super::{Layout, base, guard, lean, merge, mutants, outcome::Status};

/// The waiver record: schema 1 and its waivers.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct File {
    schema: u32,
    waivers: Vec<Waiver>,
}

/// A waiver of the targets of `scope` through the UTC date `expires`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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
        let not = format!("its expiry {:?} is no date YYYY-MM-DD", waiver.expires);
        let not = (!is_date(&waiver.expires)).then_some(not);
        found.extend(empty.into_iter().chain(unknown).chain(not));
        problems.extend(found.iter().map(|found| format!("waiver {at}: {found}")));
    }
    let waivers = problems.is_empty().then_some(file.waivers);
    waivers.ok_or(problems.join("; "))
}

/// The waivers of the record of `layout` below `root`, with the registered
/// `targets`: none when it cannot be read, as without a record.
pub fn read(root: &Path, layout: &Layout, targets: &[Target]) -> Result<Vec<Waiver>, String> {
    let text = fs::read_to_string(root.join(layout.waivers)).ok();
    parse(text.as_deref(), targets).map_err(|error| format!("{}: {error}", layout.waivers))
}

/// The UTC date of the clock reading `now`, `YYYY-MM-DD`, or why there is
/// none: a reading before 1970-01-01 or after 9999-12-31.
pub fn today(now: SystemTime) -> Result<String, String> {
    let since = (now.duration_since(UNIX_EPOCH)).map_err(|_| "the clock reads before 1970")?;
    let seconds = i64::try_from(since.as_secs()).unwrap_or(i64::MAX);
    let at = UtcDateTime::from_unix_timestamp(seconds).map_err(|error| error.to_string())?;
    Ok(at.date().to_string())
}

/// The targets of the `waivers` that hold on `date`, their expiry included.
pub fn holding(waivers: &[Waiver], date: &str) -> BTreeSet<String> {
    let holds = (waivers.iter()).filter(|waiver| date <= waiver.expires.as_str());
    holds.flat_map(|waiver| waiver.scope.clone()).collect()
}

/// The modules that waivers leave out of the base round, each with the
/// waived target that leaves it out.
pub type LeftOut = BTreeMap<String, String>;

/// What the waivers of the targets `waived` leave out of the base round of
/// the registered `targets`: the proof modules of the waived formal targets
/// that no other formal target lists, and their generated modules, by the
/// prefix `<generated>.<module>.`.
pub fn left_out(layout: &Layout, targets: &[Target], waived: &BTreeSet<String>) -> LeftOut {
    let formal = (targets.iter()).filter(|target| target.state == State::Formal);
    let (out, kept): (Vec<_>, Vec<_>) = formal.partition(|t| waived.contains(&t.name));
    let kept = BTreeSet::from_iter(kept.into_iter().flat_map(|t| t.proof_modules.clone()));
    let mut modules = LeftOut::new();
    for target in out {
        let generated = (target.module.iter()).map(|m| format!("{}.{m}.", layout.generated));
        let own = (target.proof_modules.iter()).filter(|m| !kept.contains(*m));
        modules.extend((own.cloned().chain(generated)).map(|m| (m, target.name.clone())));
    }
    modules
}

/// Concludes `merged`, whose status, units, problems and waiver date are
/// set, with the `waivers`, `targets` and `statements` of the checkout and
/// its `kept` receipts: the units and parts of the targets of the waivers
/// that hold, and the `base/<theorem>` of each statement in a module that
/// they leave out, are recorded and not required. It passes when it has no
/// problem, every other unit is `VERIFIED` and no other part has a failure,
/// and is then `REJECTED` when it used a waiver.
pub fn conclude(
    merged: &mut Merge,
    layout: &Layout,
    kept: &[&Receipt],
    waivers: &[Waiver],
    targets: &[Target],
    statements: &[guard::Statement],
) {
    let holds = |w: &&Waiver| merged.waiver_date.as_ref().is_some_and(|d| *d <= w.expires);
    let waived = BTreeSet::from_iter(waivers.iter().filter(holds).flat_map(|w| w.scope.clone()));
    // The target of each unit that is not VERIFIED and part with a failure.
    let left = left_out(layout, targets, &waived);
    let modules = BTreeMap::from_iter(statements.iter().map(|s| (base::unit(&s.theorem), s)));
    let owner = |unit: &String| match modules.get(unit) {
        Some(statement) => left.get(&statement.module).cloned(),
        None => merge::target(mutants::owner(unit)).map(String::from),
    };
    let units = (merged.units.iter()).filter(|(_, unit)| unit.status != Status::Verified);
    let parts = (kept.iter()).filter(|receipt| !receipt.failures.is_empty());
    let parts = parts.map(|receipt| owner(&receipt.shard.clone().unwrap_or_default()));
    let failing = Vec::from_iter(units.map(|(unit, _)| owner(unit)).chain(parts));
    let covered = |owner: &Option<String>| owner.as_ref().is_some_and(|o| waived.contains(o));
    merged.passes = merged.problems.is_empty() && failing.iter().all(covered);
    let used = |w: &Waiver| (w.scope.iter()).any(|name| failing.contains(&Some(name.clone())));
    let held = (waivers.iter().filter(holds)).map(|w| (w.clone(), used(w)));
    merged.waivers = Vec::from_iter(held.map(|(waiver, used)| Waived { waiver, used }));
    let rejected = merged.passes && merged.waivers.iter().any(|waived| waived.used);
    merged.status = [merged.status, Status::Rejected][usize::from(rejected)];
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
pub(crate) mod tests {
    use std::time::Duration;

    use serde_json::json;

    use super::*;
    use crate::formal::fixture::Fixture;
    use crate::formal::registry;
    use crate::scratch::Scratch;

    /// Writes the waiver record of `fixture` with a waiver of `target` until
    /// `expires`, and commits it.
    pub(crate) fn waive(fixture: &Fixture, target: &str, expires: &str) {
        let file = json!({"schema": 1, "waivers": [waiver(&[target], expires)]});
        fixture.write(Layout::PRODUCTION.waivers, &format!("{file}\n"));
        fixture.commit_all();
    }

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

    #[test]
    fn a_record_that_cannot_be_read_has_no_waivers_and_one_that_breaks_its_rules_is_an_error() {
        let scratch = Scratch::temporary("waiver-read");
        let read_in = |layout: &Layout| read(&scratch.0, layout, &targets());
        assert_eq!(read_in(&Layout::PRODUCTION), Ok(Vec::new()));
        // A directory in its place cannot be read, and the calibration layout
        // names no record.
        fs::create_dir_all(scratch.0.join(Layout::PRODUCTION.waivers)).expect("a directory");
        assert_eq!(read_in(&Layout::PRODUCTION), Ok(Vec::new()));
        assert_eq!(read_in(&Layout::CALIBRATION), Ok(Vec::new()));
        fs::remove_dir(scratch.0.join(Layout::PRODUCTION.waivers)).expect("remove it");
        let file = json!({"schema": 1, "waivers": [waiver(&["a"], "9999-12-31")]});
        scratch.write(Layout::PRODUCTION.waivers, &file.to_string());
        assert_eq!(read_in(&Layout::CALIBRATION), Ok(Vec::new()));
        let found = read_in(&Layout::PRODUCTION).expect("the waivers");
        assert_eq!(
            holding(&found, "2026-11-13"),
            BTreeSet::from(["a".to_string()])
        );
        scratch.write(Layout::PRODUCTION.waivers, "{");
        let error = read_in(&Layout::PRODUCTION).expect_err("a record that does not parse");
        assert!(error.starts_with("verification/waivers.json: "), "{error}");
    }

    #[test]
    fn a_waiver_holds_through_its_expiry_date_in_utc() {
        let waivers = [
            parsed(&[waiver(&["a"], "2026-11-13")]),
            parsed(&[waiver(&["b", "a"], "2026-12-01")]),
        ];
        let waivers = Vec::from_iter(waivers.into_iter().flat_map(|w| w.expect("a waiver")));
        let names = |names: &[&str]| BTreeSet::from_iter(names.iter().map(|n| n.to_string()));
        assert_eq!(holding(&waivers, "2026-11-12"), names(&["a", "b"]));
        assert_eq!(holding(&waivers, "2026-11-13"), names(&["a", "b"]));
        assert_eq!(holding(&waivers, "2026-11-14"), names(&["a", "b"]));
        assert_eq!(holding(&waivers, "2026-12-02"), names(&[]));
        assert_eq!(holding(&waivers[..1], "2026-11-14"), names(&[]));
        // The last second of a day and the first of the next, and readings
        // that give no date.
        let at = |seconds: u64| today(UNIX_EPOCH + Duration::from_secs(seconds));
        assert_eq!(at(0), Ok("1970-01-01".to_string()));
        assert_eq!(at(1_794_614_399), Ok("2026-11-13".to_string()));
        assert_eq!(at(1_794_614_400), Ok("2026-11-14".to_string()));
        assert_eq!(at(253_402_300_799), Ok("9999-12-31".to_string()));
        assert!(at(253_402_300_800).is_err());
        let before = today(UNIX_EPOCH - Duration::from_secs(1));
        assert_eq!(before, Err("the clock reads before 1970".to_string()));
    }

    #[test]
    fn a_waiver_leaves_out_the_proof_modules_that_no_other_formal_target_lists() {
        let text = json!({"schema": 2, "targets": [
            {"name": "t", "module": "T", "proof_modules": ["P.A", "P.Shared"]},
            {"name": "u", "module": "U", "proof_modules": ["P.Shared", "P.B"]},
            {"name": "p", "state": "planned", "module": "Q", "proof_modules": ["P.C"]},
        ]});
        let targets = registry::parse(&text.to_string())
            .expect("a registry")
            .targets;
        let names = |names: &[&str]| BTreeSet::from_iter(names.iter().map(|n| n.to_string()));
        let left = |waived: &[&str]| left_out(&Layout::PRODUCTION, &targets, &names(waived));
        let entries = |entries: &[(&str, &str)]| {
            LeftOut::from_iter(entries.iter().map(|(m, t)| (m.to_string(), t.to_string())))
        };
        assert_eq!(left(&[]), LeftOut::new());
        assert_eq!(
            left(&["t", "p"]),
            entries(&[("KrepiGen.T.", "t"), ("P.A", "t")])
        );
        // A module of two waived targets is left out with one of them.
        let both = left(&["t", "u"]);
        let modules = ["KrepiGen.T.", "KrepiGen.U.", "P.A", "P.B", "P.Shared"];
        assert_eq!(Vec::from_iter(both.keys()), modules);
    }
}
