//! The receipt of `cargo xtask formal run`, schema 5, the record of
//! `cargo xtask formal merge`, schema 2, as "Receipt" and "Shards and merge"
//! in `docs/formal-verification.md` document them, and
//! `cargo xtask formal receipt`, which judges a record against the checkout,
//! as "Current and fresh records" there describes.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, SystemTime};

use clap::{ArgMatches, value_parser};
use serde::{Deserialize, Serialize};

use super::outcome::{self, Class, Site, Status, word};
use super::paths::{self, Snapshot};
use super::process::LimitBy;
use super::qualify::Expect;
use super::registry::State;
use super::waiver::{self, Waiver};
use super::{Layout, guard, merge, toolchain};

pub const SCHEMA: u32 = 5;

pub const COMMAND: &str = "cargo xtask formal run";

/// The receipt of one run; its fields are written in this order.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Receipt {
    pub schema: u32,
    pub command: String,
    pub status: Status,
    pub complete: bool,
    pub trigger: Trigger,
    pub targets: Vec<String>,
    pub shard: Option<String>,
    pub host: Option<String>,
    pub image: Option<Image>,
    pub run: String,
    pub directory: String,
    pub started: u64,
    pub seconds: f64,
    pub commit: Option<String>,
    pub tree: Option<String>,
    pub inputs: Inputs,
    pub budgets: Budgets,
    pub resources: Resources,
    pub phases: BTreeMap<String, Phase>,
    pub units: BTreeMap<String, Unit>,
    pub qualification: Option<Qualification>,
    pub base: Option<super::base::Record>,
    pub proof_targets: BTreeMap<String, Target>,
    pub guard: Option<super::guard::Record>,
    pub commands: Vec<Command>,
    pub failures: Vec<Failure>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Mode {
    Required,
    ForcedFull,
    Weekly,
    Scoped,
    #[default]
    Manual,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Trigger {
    pub mode: Mode,
    pub event: Option<String>,
    #[serde(rename = "ref")]
    pub reference: Option<String>,
    pub run_id: Option<String>,
    pub attempt: Option<String>,
}

/// The variable through which a job of CI gives the trigger of its run.
pub const TRIGGER: &str = "KREPI_FORMAL_TRIGGER";

/// The mode that [`TRIGGER`] gives through `var`: `MANUAL` when it is unset
/// or empty, `REQUIRED`, `FORCED_FULL` or `WEEKLY`, and otherwise why not.
pub fn mode(var: &dyn Fn(&str) -> Option<String>) -> Result<Mode, String> {
    let Some(value) = var(TRIGGER).filter(|value| !value.is_empty()) else {
        return Ok(Mode::Manual);
    };
    let modes = [Mode::Required, Mode::ForcedFull, Mode::Weekly];
    let found = modes.into_iter().find(|mode| word(mode) == value);
    let not = format!("{TRIGGER} is {value:?}, not REQUIRED, FORCED_FULL or WEEKLY");
    found.ok_or(not)
}

/// The image of a run on the CI host: the reference that the job gave, the
/// gate's effective user, whether that user can write the installation, or
/// `None` before the check, and its version manifest and `/etc/os-release`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Image {
    pub reference: Option<String>,
    pub uid: u32,
    pub writable: Option<bool>,
    pub versions_sha256: Option<String>,
    pub versions: Option<String>,
    pub os_release: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Inputs {
    pub before: Option<Snapshot>,
    pub after: Option<Snapshot>,
    pub clean_after: Option<bool>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Budgets {
    pub gate_seconds: u64,
    pub receipt_margin_seconds: u64,
}

/// The bytes available on the file system of the run directory at the
/// start and the least that the run read, every second, until its second
/// snapshot, the largest maximum resident set of one collected process, and
/// the `memory.peak` of the gate's cgroup, page cache included; each `None`
/// when the host does not report it.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Resources {
    pub disk_available_at_start: Option<u64>,
    pub disk_least_available: Option<u64>,
    pub largest_process_max_rss: Option<u64>,
    pub cgroup_memory_peak: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Phase {
    pub budget_seconds: u64,
    pub seconds: f64,
    pub ran: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Unit {
    pub phase: String,
    pub status: Status,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Command {
    pub sequence: u32,
    pub phase: Option<String>,
    pub unit: Option<String>,
    pub site: Site,
    pub argv: Vec<String>,
    pub cwd: String,
    pub class: Class,
    pub reason: Option<String>,
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub timed_out: bool,
    pub limit_seconds: f64,
    pub limit: LimitBy,
    pub seconds: f64,
    pub group_survived: bool,
    pub stdout: Option<Log>,
    pub stderr: Option<Log>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Qualification {
    pub cases_sha256: String,
    pub extraction_sha256: String,
    pub cases: BTreeMap<String, QualificationCase>,
    pub theorems: BTreeMap<String, QualificationTheorem>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct QualificationCase {
    pub unit: String,
    pub module: String,
    pub parts: Vec<String>,
    pub expect: Expect,
    pub models: Option<String>,
    pub observed: Observed,
    pub type_errors: Option<TypeErrors>,
    pub differences: Vec<String>,
    pub generated: BTreeMap<String, String>,
    pub declarations: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Observed {
    pub complete: bool,
    pub diagnostics: Vec<String>,
    pub external_functions: Vec<String>,
    pub external_types: Vec<String>,
    pub loop_sources: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeErrors {
    pub file: String,
    pub errors: u64,
    pub in_file: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct QualificationTheorem {
    pub case: String,
    pub unit: String,
    pub axioms: Option<Vec<String>>,
}

/// A target that the run extracted: its unit, or none for a target that
/// only the base round needs, its state, budget and the seconds of its
/// commands, what its extraction gave, the SHA-256 of each file that Aeneas
/// wrote, the declarations of its templates that stay axioms, its proof
/// modules, whether its generated definitions type-check, the seconds of
/// each mutant and its problems.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Target {
    pub unit: Option<String>,
    pub state: State,
    pub budget_seconds: u64,
    pub seconds: f64,
    pub observed: Observed,
    pub generated: BTreeMap<String, String>,
    pub declarations: Vec<String>,
    pub proof_modules: Vec<String>,
    pub typed: bool,
    pub mutants: BTreeMap<String, f64>,
    pub problems: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Log {
    pub path: String,
    pub bytes: u64,
    pub sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Failure {
    pub status: Status,
    pub message: String,
}

/// The schema of the record of `cargo xtask formal merge`.
pub const MERGE_SCHEMA: u32 = 2;

/// The record of a merge; its fields are written in this order.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Merge {
    pub schema: u32,
    pub status: Status,
    pub complete: bool,
    pub passes: bool,
    pub commit: Option<String>,
    pub tree: Option<String>,
    pub inputs: Option<Snapshot>,
    pub image: Option<String>,
    pub trigger: Option<Mode>,
    #[serde(rename = "ref")]
    pub reference: Option<String>,
    pub run_id: Option<String>,
    pub planned_statements: Option<u64>,
    pub waiver_date: Option<String>,
    pub waivers: Vec<Waived>,
    pub parts: Vec<Part>,
    pub units: BTreeMap<String, Unit>,
    pub slowest_part_seconds: f64,
    pub merge_seconds: f64,
    pub merge_from: String,
    pub wall_clock_seconds: f64,
    pub over_80_percent: bool,
    pub problems: Vec<String>,
}

/// A receipt that a merge was given, by its path: the SHA-256 of the file
/// and, when it parses, its shard, the run and attempt of its job, whether a
/// later attempt supersedes it, its status, completeness, seconds and cgroup
/// memory peak, and whether these are above the limits that the merge flags.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Part {
    pub receipt: String,
    pub sha256: Option<String>,
    pub shard: Option<String>,
    pub run_id: Option<String>,
    pub attempt: Option<String>,
    pub superseded: bool,
    pub status: Option<Status>,
    pub complete: bool,
    pub seconds: f64,
    pub cgroup_memory_peak: Option<u64>,
    pub over_seconds: bool,
    pub over_memory: Option<bool>,
}

/// A waiver that held on the date of a merge, and whether the merge used
/// it: a unit of its targets is not `VERIFIED`, or a part of them has a
/// failure.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Waived {
    pub waiver: Waiver,
    pub used: bool,
}

impl Waived {
    /// The line of the waiver, its texts escaped: its targets, expiry and
    /// author, whether the merge used it, and its reason.
    pub fn line(&self) -> String {
        let w = &self.waiver;
        let texts = [&w.scope.join(", "), &w.expires, &w.author, &w.reason];
        let [scope, expires, author, reason] = texts.map(|text| text.escape_debug().to_string());
        let used = ["unused", "used"][usize::from(self.used)];
        format!("waiver of {scope} until {expires} by {author}, {used}: {reason}")
    }
}

/// `duration` in seconds, rounded to milliseconds, as the receipt writes
/// times so that it reads back as it was written.
pub fn seconds(duration: Duration) -> f64 {
    (duration.as_secs_f64() * 1_000.0).round() / 1_000.0
}

/// The text of `receipt` or of a merge record, with a final line break.
pub fn render<T: Serialize>(receipt: &T) -> String {
    let text = serde_json::to_string_pretty(receipt);
    text.expect("a receipt has string keys and finite numbers") + "\n"
}

/// The words and the exit code of a verdict of `cargo xtask formal receipt`.
pub type Verdict = (&'static str, u8);

/// The command line of `cargo xtask formal receipt`, with `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let record = clap::arg!([RECORD] "The record, by default artifacts/formal/merge/record.json");
    let record = record.value_parser(value_parser!(PathBuf));
    let fresh = clap::arg!(--"require-fresh" "Also require a fresh record, of a run of CI");
    let command = clap::Command::new("receipt").about(about);
    command.args([record, fresh])
}

/// `cargo xtask formal receipt` in `root`: judges the merge record that
/// `matches` names, or `record.json` of [`merge::DIR`], prints its summary
/// and exits with the code of the verdict.
pub fn command(root: &Path, layout: &Layout, matches: &ArgMatches) -> ExitCode {
    let path = matches.get_one::<PathBuf>("RECORD").cloned();
    let path = path.unwrap_or(root.join(merge::DIR).join("record.json"));
    let text = fs::read_to_string(&path);
    let text = text.map_err(|error| format!("cannot read {}: {error}", path.display()));
    let record = text.and_then(|text| read(&text));
    let ((words, code), reasons) = match &record {
        Ok(record) => judge(root, layout, record, matches.get_flag("require-fresh")),
        Err(reason) => (("not CURRENT", 1), vec![reason.clone()]),
    };
    print!("{}", summary(&record.unwrap_or_default(), words, &reasons));
    ExitCode::from(code)
}

/// The summary of the verdict `words` on `record`: the commit and trigger
/// of the record, each waiver that it recorded and each of the `reasons`
/// against it, escaped.
fn summary(record: &Merge, words: &str, reasons: &[String]) -> String {
    let text = |t: &Option<String>| t.as_deref().unwrap_or("none").escape_debug().to_string();
    let mode = (record.trigger).map_or("none".to_string(), |mode| word(&mode));
    let [commit, refname, run] = [&record.commit, &record.reference, &record.run_id].map(text);
    let head = format!("formal receipt: {words}\ncommit {commit}\ntrigger {mode} {refname} {run}");
    let waivers = record.waivers.iter().map(|waived| waived.line());
    let reasons = (reasons.iter()).map(|reason| reason.escape_debug().to_string());
    let lines = waivers.chain(reasons).map(|line| format!("- {line}\n"));
    format!("{head}\n{}", String::from_iter(lines))
}

/// The merge record `text`, or why it is none of schema [`MERGE_SCHEMA`].
fn read(text: &str) -> Result<Merge, String> {
    let not = |error: serde_json::Error| format!("the record does not parse: {error}");
    let value: serde_json::Value = serde_json::from_str(text).map_err(not)?;
    let schema = &value["schema"];
    let other = format!("the record has schema {schema} where {MERGE_SCHEMA} is expected");
    (*schema == MERGE_SCHEMA).then_some(()).ok_or(other)?;
    serde_json::from_value(value).map_err(not)
}

/// The verdict on the merge `record` for the checkout `root` in `layout`,
/// with `--require-fresh` when `fresh`, by its words and exit code, and each
/// reason against it.
pub fn judge(root: &Path, layout: &Layout, record: &Merge, fresh: bool) -> (Verdict, Vec<String>) {
    // The record has the gate inputs, the pinned image and the units of the
    // checkout, whose gate inputs are clean.
    let (inputs, mut git) = (paths::gate_inputs(layout), guard::Standalone(root));
    let mut reasons = Vec::new();
    let head = paths::snapshot(&mut git, &inputs).and_then(|(_, _, snapshot)| {
        let changes = paths::changes(&mut git, &inputs)?.join(", ");
        let dirty = format!("the gate inputs of the checkout are not clean: {changes}");
        reasons.extend((!changes.is_empty()).then_some(dirty));
        let theirs = record.inputs.clone().unwrap_or_default();
        let all = BTreeSet::from_iter(theirs.keys().chain(snapshot.keys()));
        let other = (all.into_iter()).filter(|input| theirs.get(*input) != snapshot.get(*input));
        let other = Vec::from_iter(other.map(String::as_str)).join(", ");
        let differ = format!("the gate inputs {other} of the record are not those of the checkout");
        reasons.extend((!other.is_empty()).then_some(differ));
        Ok(())
    });
    reasons.extend((head.err()).map(|error| format!("cannot read the checkout: {error}")));
    let pin = fs::read_to_string(root.join(layout.image_pin)).ok();
    let pinned = (pin.as_deref().and_then(toolchain::image_pin)).map(|(_, reference)| reference);
    let none = |value: &Option<String>| value.clone().unwrap_or("none".to_string());
    let (image, pin) = (none(&record.image), none(&pinned));
    let image = format!("the image {image} of the record is not the pinned image {pin}");
    reasons.extend((pinned.is_none() || pinned != record.image).then_some(image));
    let units = (record.units.iter()).map(|(unit, u)| (unit.clone(), (u.status, u.reason.clone())));
    reasons.extend(outcome::account(&merge::registered(root, layout), units.collect(), None).1);
    // It concludes VERIFIED, complete and passing; or else it is waived when
    // that is the only reason against it, and it passes within the waivers
    // that it used, which still hold.
    let (status, problems) = (word(&record.status), record.problems.iter());
    let not = |holds: bool| ["not ", ""][usize::from(holds)];
    let (complete, passing) = (not(record.complete), not(record.passes));
    let concluded = format!("the record is {status}, {complete}complete and {passing}passing");
    let verified = record.status == Status::Verified && record.complete && record.passes;
    reasons.extend((!verified).then_some(concluded));
    reasons.extend(problems.map(|problem| format!("the record has the problem: {problem}")));
    let current = reasons.is_empty();
    let used = Vec::from_iter(record.waivers.iter().filter(|w| w.used).map(|w| &w.waiver));
    let today = waiver::today(SystemTime::now());
    reasons.extend(today.clone().err().filter(|_| !used.is_empty()));
    let expired = (used.iter()).filter(|w| today.as_ref().is_ok_and(|today| *today > w.expires));
    let expired = expired.map(|w| (w.scope.join(", "), &w.expires));
    reasons.extend(expired.map(|(s, on)| format!("the used waiver of {s} expired on {on}")));
    let waived = !verified && record.passes && !used.is_empty() && reasons.len() == 1;
    // A fresh record is of a run of CI without planned statements or waivers.
    if fresh {
        let modes = [Mode::Required, Mode::ForcedFull, Mode::Weekly];
        let ci = modes.map(Some).contains(&record.trigger) && record.run_id.is_some();
        let mode = (record.trigger).map_or("none".to_string(), |mode| word(&mode));
        let without = [" without a run ID", ""][usize::from(record.run_id.is_some())];
        let trigger = format!("the record has the trigger {mode}{without}, not one of CI");
        reasons.extend((!ci).then_some(trigger));
        let planned = serde_json::Value::from(record.planned_statements);
        let planned = format!("the record has planned_statements {planned} where 0 is required");
        reasons.extend((record.planned_statements != Some(0)).then_some(planned));
        for Waived { waiver: w, .. } in &record.waivers {
            let (scope, date) = (w.scope.join(", "), &w.expires);
            let left = format!("the record left out {scope} under the waiver until {date}");
            reasons.push(left);
        }
    }
    let verdict = match (current, fresh) {
        (true, false) => ("CURRENT", 0),
        (true, true) if reasons.is_empty() => ("CURRENT and fresh", 0),
        (true, true) => ("CURRENT, not fresh", 1),
        (false, false) if waived => ("WAIVED", 3),
        _ => ("not CURRENT", 1),
    };
    (verdict, reasons)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use serde_json::json;

    use super::*;
    use crate::formal::base::{Hash, Heartbeats, Leanchecker, Record, Theorem};
    use crate::formal::fixture::Fixture;
    use crate::formal::guard::State;
    use crate::formal::lean::Kind;
    use crate::formal::merge::tests as merging;
    use crate::formal::outcome::conventions::SITES;
    use crate::formal::outcome::word;
    use crate::formal::paths::Entry;
    use crate::formal::run::tests::{gate, register, root_package};
    use crate::formal::waiver::tests::waive;

    fn entry(mode: &str, kind: &str, digit: char) -> Option<Entry> {
        Some(Entry {
            mode: mode.to_string(),
            kind: kind.to_string(),
            oid: digit.to_string().repeat(40),
        })
    }

    fn command(sequence: u32, site: Site, class: Class) -> Command {
        Command {
            sequence,
            phase: Some("base".to_string()),
            unit: Some("base".to_string()),
            site,
            argv: vec![word(&site), "--flag".to_string()],
            cwd: "artifacts/formal/runs/1-2/work/source".to_string(),
            class,
            reason: (class != Class::Passed).then(|| format!("{} failed", word(&site))),
            exit_code: Some(1),
            signal: None,
            timed_out: false,
            limit_seconds: 3_599.875,
            limit: LimitBy::Phase,
            seconds: 0.125,
            group_survived: false,
            stdout: Some(Log {
                path: format!("logs/{sequence:04}-{}.stdout", word(&site)),
                bytes: 3,
                sha256: "7".repeat(64),
            }),
            stderr: None,
        }
    }

    /// A receipt with every field set and every word of the schema used,
    /// apart from the modes of the trigger.
    fn full(mode: Mode) -> Receipt {
        let statuses = [
            Status::Verified,
            Status::Rejected,
            Status::Stale,
            Status::ToolFailure,
            Status::Budget,
            Status::NotRun,
            Status::Scoped,
        ];
        let classes = [
            Class::Passed,
            Class::ProofFailure,
            Class::ToolFailure,
            Class::Budget,
            Class::NotRun,
        ];
        let mut commands: Vec<Command> = (1..)
            .zip(SITES)
            .map(|(sequence, site)| command(sequence, site, classes[sequence as usize % 5]))
            .collect();
        commands[0].limit = LimitBy::Cap;
        commands[1].limit = LimitBy::Gate;
        commands[1].exit_code = None;
        commands[1].signal = Some(9);
        commands[2].timed_out = true;
        commands[2].group_survived = true;
        commands[3].phase = None;
        commands[3].unit = None;
        commands[3].stdout = None;
        let inputs = Snapshot::from([
            ("kernel".to_string(), entry("040000", "tree", 'a')),
            (
                "rust-toolchain.toml".to_string(),
                entry("100755", "blob", 'b'),
            ),
            ("verification/qualification".to_string(), None),
        ]);
        Receipt {
            schema: SCHEMA,
            command: COMMAND.to_string(),
            status: Status::ToolFailure,
            complete: false,
            trigger: Trigger {
                mode,
                event: Some("pull_request".to_string()),
                reference: Some("refs/pull/7/merge".to_string()),
                run_id: Some("123".to_string()),
                attempt: Some("2".to_string()),
            },
            targets: vec!["alpha".to_string(), "demo".to_string()],
            shard: Some("target/demo".to_string()),
            host: Some("linux-aarch64".to_string()),
            image: Some(Image {
                reference: Some(format!("ghcr.io/o/r@sha256:{}", "9".repeat(64))),
                uid: 1_001,
                writable: Some(true),
                versions_sha256: Some("a".repeat(64)),
                versions: Some("{\n  \"schema\": 1\n}\n".to_string()),
                os_release: Some("NAME=\"Ubuntu\"\n".to_string()),
            }),
            run: "1700000000-42".to_string(),
            directory: "artifacts/formal/runs/1700000000-42".to_string(),
            started: 1_700_000_000,
            seconds: 12.345,
            commit: Some("c".repeat(40)),
            tree: Some("d".repeat(40)),
            inputs: Inputs {
                before: Some(inputs.clone()),
                after: Some(inputs),
                clean_after: Some(true),
            },
            budgets: Budgets {
                gate_seconds: 7_200,
                receipt_margin_seconds: 300,
            },
            resources: Resources {
                disk_available_at_start: Some(100_000_000_000),
                disk_least_available: Some(99_000_000_000),
                largest_process_max_rss: Some(5_850_000_000),
                cgroup_memory_peak: Some(9_000_000_000),
            },
            phases: BTreeMap::from([(
                "base".to_string(),
                Phase {
                    budget_seconds: 3_600,
                    seconds: 1.5,
                    ran: true,
                },
            )]),
            units: (0..)
                .zip(statuses)
                .map(|(index, status)| {
                    (
                        format!("u{index}"),
                        Unit {
                            phase: "base".to_string(),
                            status,
                            reason: Some(format!("reason {index}")),
                        },
                    )
                })
                .collect(),
            qualification: Some(qualification()),
            base: Some(base()),
            proof_targets: BTreeMap::from([("t".to_string(), target())]),
            guard: Some(guard()),
            commands,
            failures: statuses
                .into_iter()
                .map(|status| Failure {
                    status,
                    message: format!("{status:?}"),
                })
                .collect(),
        }
    }

    /// The record of a target with a mutant.
    fn target() -> Target {
        Target {
            unit: Some("target/t".to_string()),
            state: crate::formal::registry::State::Formal,
            budget_seconds: 3_000,
            seconds: 12.5,
            observed: Observed {
                complete: true,
                ..Observed::default()
            },
            generated: BTreeMap::from([("KrepiGen/T/Funs.lean".to_string(), "9".repeat(64))]),
            declarations: vec!["T.f".to_string()],
            proof_modules: vec!["Krepi.Proofs.T".to_string()],
            typed: true,
            mutants: BTreeMap::from([("m".to_string(), 3.25)]),
            problems: vec!["Krepi.Proofs.T.t depends on sorryAx".to_string()],
        }
    }

    /// The record of a qualification with a case of every expectation.
    fn qualification() -> Qualification {
        let case = |expect, type_errors| QualificationCase {
            unit: "qualification/c".to_string(),
            module: "Qual.C".to_string(),
            parts: vec!["Qual.C.A".to_string(), "Qual.C.B".to_string()],
            expect,
            models: Some("verification/externals/Qual/C".to_string()),
            observed: Observed {
                complete: true,
                diagnostics: vec!["[Warn ] w".to_string()],
                external_functions: vec!["f".to_string()],
                external_types: vec!["t".to_string()],
                loop_sources: vec!["c.f_loop src/lib.rs".to_string()],
            },
            type_errors,
            differences: vec!["diagnostics: expected but absent: x".to_string()],
            generated: BTreeMap::from([("KrepiGen/Qual/C/Funs.lean".to_string(), "8".repeat(64))]),
            declarations: vec!["c.f".to_string()],
        };
        let errors = TypeErrors {
            file: "Funs.lean".to_string(),
            errors: 2,
            in_file: 1,
        };
        Qualification {
            cases_sha256: "1".repeat(64),
            extraction_sha256: "2".repeat(64),
            cases: BTreeMap::from([
                ("a".to_string(), case(Expect::Translated, None)),
                ("b".to_string(), case(Expect::IllTyped, Some(errors))),
                ("c".to_string(), case(Expect::Rejected, None)),
            ]),
            theorems: BTreeMap::from([
                (
                    "Krepi.Qualification.C.t".to_string(),
                    QualificationTheorem {
                        case: "a".to_string(),
                        unit: "qualification/a/Krepi.Qualification.C.t".to_string(),
                        axioms: Some(vec!["propext".to_string()]),
                    },
                ),
                (
                    "Krepi.Qualification.C.u".to_string(),
                    QualificationTheorem {
                        case: "a".to_string(),
                        unit: "qualification/a/Krepi.Qualification.C.u".to_string(),
                        axioms: None,
                    },
                ),
            ]),
        }
    }

    /// The record of a base round with a theorem of every kind and state.
    fn base() -> Record {
        let theorem = |kind, state, axioms: Option<&[&str]>, status| Theorem {
            module: "Krepi.Proofs.C".to_string(),
            kind,
            state,
            axioms: axioms.map(|axioms| axioms.iter().map(|axiom| axiom.to_string()).collect()),
            status,
            problems: vec!["Krepi.Proofs.C.t depends on sorryAx".to_string()],
        };
        let names = |names: &[&str]| names.iter().map(|name| name.to_string()).collect();
        Record {
            statements_sha256: "3".repeat(64),
            axioms_sha256: "4".repeat(64),
            tcb_sha256: "5".repeat(64),
            statement_hash: Hash {
                recorded: "6".repeat(40),
                computed: "7".repeat(40),
            },
            modules: names(&["Krepi.Proofs.C", "KrepiGen.Qual.C.Funs"]),
            own: names(&["Krepi.Proofs.C"]),
            planned: names(&["Krepi.Proofs.C"]),
            theorems: BTreeMap::from([
                (
                    "Krepi.Proofs.C.t".to_string(),
                    theorem(
                        Kind::Target,
                        Some(State::Proved),
                        Some(&["propext"]),
                        Status::Rejected,
                    ),
                ),
                (
                    "Krepi.Proofs.C.u".to_string(),
                    theorem(Kind::Target, Some(State::Planned), None, Status::NotRun),
                ),
                (
                    "Krepi.Qualification.C.v".to_string(),
                    theorem(Kind::Qualification, None, Some(&[]), Status::Verified),
                ),
                (
                    "Krepi.Spec.C.w".to_string(),
                    theorem(Kind::Specification, None, Some(&[]), Status::Verified),
                ),
            ]),
            leanchecker: Leanchecker {
                version: Some("Lean (version 4.35.0, Release)".to_string()),
                sha256: "8".repeat(64),
                mode: "prefix".to_string(),
                prefixes: names(&["Krepi", "KrepiGen"]),
            },
            heartbeats: Heartbeats {
                method: "count_heartbeats".to_string(),
                counts: BTreeMap::from([("Krepi.Proofs.C.t".to_string(), 1_326)]),
                missing: BTreeMap::from([("Krepi/Proofs/D.lean".to_string(), "error".to_string())]),
            },
            problems: vec!["leanchecker Krepi: a problem".to_string()],
        }
    }

    /// The record of the guard of a pull request on which every rule fails
    /// but one.
    fn guard() -> crate::formal::guard::Record {
        let paths = |paths: &[&str]| paths.iter().map(|path| path.to_string()).collect();
        let why = |rule: &str| (rule != "spec-approval").then(|| format!("{rule} fails"));
        crate::formal::guard::Record {
            base: "1".repeat(40),
            head: "2".repeat(40),
            merge_base: "3".repeat(40),
            labels: BTreeSet::from(["ai-proof".to_string(), "proof".to_string()]),
            ai_proof: true,
            statement_hash: "4".repeat(40),
            statement_side: paths(&["verification/Krepi/Spec/C.lean"]),
            proofs: paths(&["verification/Krepi/Proofs/C.lean"]),
            sources: paths(&["kernel/abi/src/lib.rs"]),
            demoted: paths(&["Krepi.Statements.C.S"]),
            restated: paths(&["Krepi.Statements.C.S", "Krepi.Statements.C.T"]),
            raised: paths(&["verification/Krepi/Proofs/C.lean"]),
            registry: BTreeMap::new(),
            rules: [
                "statement-change-needs-spec",
                "spec-approval",
                "no-sources-with-proofs-or-statements",
                "heartbeats-need-review",
                "phase-and-author",
                "proof-of-registered-statements",
            ]
            .map(|rule| (rule.to_string(), why(rule)))
            .into(),
        }
    }

    #[test]
    fn a_receipt_reads_back_as_it_was_written() {
        let modes = [
            Mode::Required,
            Mode::ForcedFull,
            Mode::Weekly,
            Mode::Scoped,
            Mode::Manual,
        ];
        for mode in modes {
            let receipt = full(mode);
            let text = render(&receipt);
            assert!(text.ends_with("}\n"), "{text}");
            let back: Receipt = serde_json::from_str(&text).expect("the receipt reads back");
            assert_eq!(back, receipt);
            assert_eq!(render(&back), text);
        }
        let text = render(&full(Mode::Manual));
        for word in [
            "\"VERIFIED\"",
            "\"REJECTED\"",
            "\"STALE\"",
            "\"TOOL_FAILURE\"",
            "\"BUDGET\"",
            "\"NOT_RUN\"",
            "\"SCOPED\"",
            "\"PASSED\"",
            "\"PROOF_FAILURE\"",
            "\"cap\"",
            "\"phase\"",
            "\"gate\"",
            "\"ref\": \"refs/pull/7/merge\"",
            "\"type\": \"tree\"",
            "\"expect\": \"translated\"",
            "\"expect\": \"ill-typed\"",
            "\"expect\": \"rejected\"",
            "\"kind\": \"target\"",
            "\"kind\": \"qualification\"",
            "\"kind\": \"specification\"",
            "\"state\": \"proved\"",
            "\"state\": \"planned\"",
            "\"state\": null",
            "\"ai_proof\": true",
            "\"spec-approval\": null",
            "\"writable\": true",
            "\"versions\": \"{\\n  \\\"schema\\\": 1\\n}\\n\"",
            "\"cgroup_memory_peak\": 9000000000",
            "\"shard\": \"target/demo\"",
        ] {
            assert!(text.contains(word), "{word} is not in {text}");
        }
        for site in SITES {
            assert!(text.contains(&format!("\"site\": \"{}\"", word(&site))));
        }
    }

    #[test]
    fn the_trigger_variable_gives_the_mode_of_a_ci_run() {
        let mode_of = |value: Option<&str>| {
            mode(&|name: &str| value.filter(|_| name == TRIGGER).map(str::to_string))
        };
        assert_eq!(mode_of(None), Ok(Mode::Manual));
        assert_eq!(mode_of(Some("")), Ok(Mode::Manual));
        for expected in [Mode::Required, Mode::ForcedFull, Mode::Weekly] {
            assert_eq!(mode_of(Some(&word(&expected))), Ok(expected));
        }
        // It gives neither the mode of named targets nor the default by
        // name, nor another spelling, and the value is escaped.
        let not = |value: &str| {
            format!("KREPI_FORMAL_TRIGGER is \"{value}\", not REQUIRED, FORCED_FULL or WEEKLY")
        };
        for value in ["SCOPED", "MANUAL", "weekly", " WEEKLY", "Weekly"] {
            assert_eq!(mode_of(Some(value)), Err(not(value)));
        }
        assert_eq!(mode_of(Some("WEEKLY\n\"")), Err(not("WEEKLY\\n\\\"")));
    }

    #[test]
    fn a_receipt_has_the_documented_layout() {
        let receipt = Receipt {
            schema: SCHEMA,
            command: COMMAND.to_string(),
            status: Status::Verified,
            complete: true,
            trigger: Trigger {
                mode: Mode::Manual,
                event: None,
                reference: None,
                run_id: None,
                attempt: None,
            },
            targets: Vec::new(),
            shard: None,
            host: Some("darwin-arm64".to_string()),
            image: None,
            run: "1700000000-42".to_string(),
            directory: "artifacts/formal/runs/1700000000-42".to_string(),
            started: 1_700_000_000,
            seconds: 0.5,
            commit: Some("c".repeat(40)),
            tree: Some("d".repeat(40)),
            inputs: Inputs {
                // Maps are written in the order of their keys.
                before: Some(Snapshot::from([
                    ("xtask".to_string(), None),
                    ("kernel".to_string(), entry("040000", "tree", 'a')),
                ])),
                after: None,
                clean_after: Some(true),
            },
            budgets: Budgets {
                gate_seconds: 7_200,
                receipt_margin_seconds: 300,
            },
            resources: Resources {
                disk_available_at_start: Some(2_000),
                disk_least_available: Some(1_000),
                largest_process_max_rss: Some(500),
                cgroup_memory_peak: None,
            },
            phases: BTreeMap::new(),
            units: BTreeMap::from([
                (
                    "zeta".to_string(),
                    Unit {
                        phase: "p".to_string(),
                        status: Status::Verified,
                        reason: None,
                    },
                ),
                (
                    "alpha".to_string(),
                    Unit {
                        phase: "p".to_string(),
                        status: Status::NotRun,
                        reason: Some("r".to_string()),
                    },
                ),
            ]),
            qualification: None,
            base: None,
            proof_targets: BTreeMap::new(),
            guard: None,
            commands: vec![Command {
                sequence: 1,
                phase: None,
                unit: None,
                site: Site::Git,
                argv: vec!["git".to_string(), "status".to_string()],
                cwd: ".".to_string(),
                class: Class::Passed,
                reason: None,
                exit_code: Some(0),
                signal: None,
                timed_out: false,
                limit_seconds: 7_199.5,
                limit: LimitBy::Gate,
                seconds: 0.25,
                group_survived: false,
                stdout: Some(Log {
                    path: "logs/0001-git.stdout".to_string(),
                    bytes: 0,
                    sha256: "e".repeat(64),
                }),
                stderr: None,
            }],
            failures: Vec::new(),
        };
        let c = "c".repeat(40);
        let d = "d".repeat(40);
        let a = "a".repeat(40);
        let e = "e".repeat(64);
        let expected = format!(
            r#"{{
  "schema": 5,
  "command": "cargo xtask formal run",
  "status": "VERIFIED",
  "complete": true,
  "trigger": {{
    "mode": "MANUAL",
    "event": null,
    "ref": null,
    "run_id": null,
    "attempt": null
  }},
  "targets": [],
  "shard": null,
  "host": "darwin-arm64",
  "image": null,
  "run": "1700000000-42",
  "directory": "artifacts/formal/runs/1700000000-42",
  "started": 1700000000,
  "seconds": 0.5,
  "commit": "{c}",
  "tree": "{d}",
  "inputs": {{
    "before": {{
      "kernel": {{
        "mode": "040000",
        "type": "tree",
        "oid": "{a}"
      }},
      "xtask": null
    }},
    "after": null,
    "clean_after": true
  }},
  "budgets": {{
    "gate_seconds": 7200,
    "receipt_margin_seconds": 300
  }},
  "resources": {{
    "disk_available_at_start": 2000,
    "disk_least_available": 1000,
    "largest_process_max_rss": 500,
    "cgroup_memory_peak": null
  }},
  "phases": {{}},
  "units": {{
    "alpha": {{
      "phase": "p",
      "status": "NOT_RUN",
      "reason": "r"
    }},
    "zeta": {{
      "phase": "p",
      "status": "VERIFIED",
      "reason": null
    }}
  }},
  "qualification": null,
  "base": null,
  "proof_targets": {{}},
  "guard": null,
  "commands": [
    {{
      "sequence": 1,
      "phase": null,
      "unit": null,
      "site": "git",
      "argv": [
        "git",
        "status"
      ],
      "cwd": ".",
      "class": "PASSED",
      "reason": null,
      "exit_code": 0,
      "signal": null,
      "timed_out": false,
      "limit_seconds": 7199.5,
      "limit": "gate",
      "seconds": 0.25,
      "group_survived": false,
      "stdout": {{
        "path": "logs/0001-git.stdout",
        "bytes": 0,
        "sha256": "{e}"
      }},
      "stderr": null
    }}
  ],
  "failures": []
}}
"#
        );
        assert_eq!(render(&receipt), expected);
    }

    #[test]
    fn a_merge_record_has_the_documented_layout() {
        // The example of "Shards and merge" in docs/formal-verification.md.
        let merged = Merge {
            schema: MERGE_SCHEMA,
            status: Status::Verified,
            complete: true,
            passes: true,
            commit: Some("c".repeat(40)),
            tree: Some("d".repeat(40)),
            inputs: Some(BTreeMap::from([
                ("kernel".to_string(), entry("040000", "tree", 'a')),
                ("xtask".to_string(), None),
            ])),
            image: Some(format!("ghcr.io/o/r@sha256:{}", "9".repeat(64))),
            trigger: Some(Mode::Required),
            reference: Some("refs/pull/7/merge".to_string()),
            run_id: Some("123".to_string()),
            planned_statements: Some(0),
            waiver_date: Some("2026-11-13".to_string()),
            waivers: vec![Waived {
                waiver: Waiver {
                    reason: "The proofs wait for a fix of the tool.".to_string(),
                    scope: vec!["t".to_string()],
                    expires: "2026-12-01".to_string(),
                    author: "someone".to_string(),
                },
                used: false,
            }],
            parts: vec![Part {
                receipt: "artifacts/parts/qualification/receipt.json".to_string(),
                sha256: Some("e".repeat(64)),
                shard: Some("qualification".to_string()),
                run_id: Some("123".to_string()),
                attempt: Some("1".to_string()),
                superseded: false,
                status: Some(Status::Verified),
                complete: true,
                seconds: 1_095.7,
                cgroup_memory_peak: Some(10_429_386_752),
                over_seconds: false,
                over_memory: Some(false),
            }],
            units: BTreeMap::from([(
                "base".to_string(),
                Unit {
                    phase: "base".to_string(),
                    status: Status::Verified,
                    reason: None,
                },
            )]),
            slowest_part_seconds: 1_095.7,
            merge_seconds: 62.0,
            merge_from: "job".to_string(),
            wall_clock_seconds: 1_157.7,
            over_80_percent: false,
            problems: Vec::new(),
        };
        let (a, c, d, e, nine) = (
            "a".repeat(40),
            "c".repeat(40),
            "d".repeat(40),
            "e".repeat(64),
            "9".repeat(64),
        );
        let expected = format!(
            r#"{{
  "schema": 2,
  "status": "VERIFIED",
  "complete": true,
  "passes": true,
  "commit": "{c}",
  "tree": "{d}",
  "inputs": {{
    "kernel": {{
      "mode": "040000",
      "type": "tree",
      "oid": "{a}"
    }},
    "xtask": null
  }},
  "image": "ghcr.io/o/r@sha256:{nine}",
  "trigger": "REQUIRED",
  "ref": "refs/pull/7/merge",
  "run_id": "123",
  "planned_statements": 0,
  "waiver_date": "2026-11-13",
  "waivers": [
    {{
      "waiver": {{
        "reason": "The proofs wait for a fix of the tool.",
        "scope": [
          "t"
        ],
        "expires": "2026-12-01",
        "author": "someone"
      }},
      "used": false
    }}
  ],
  "parts": [
    {{
      "receipt": "artifacts/parts/qualification/receipt.json",
      "sha256": "{e}",
      "shard": "qualification",
      "run_id": "123",
      "attempt": "1",
      "superseded": false,
      "status": "VERIFIED",
      "complete": true,
      "seconds": 1095.7,
      "cgroup_memory_peak": 10429386752,
      "over_seconds": false,
      "over_memory": false
    }}
  ],
  "units": {{
    "base": {{
      "phase": "base",
      "status": "VERIFIED",
      "reason": null
    }}
  }},
  "slowest_part_seconds": 1095.7,
  "merge_seconds": 62.0,
  "merge_from": "job",
  "wall_clock_seconds": 1157.7,
  "over_80_percent": false,
  "problems": []
}}
"#
        );
        assert_eq!(render(&merged), expected);
        let back: Merge = serde_json::from_str(&expected).expect("the record reads back");
        assert_eq!(back, merged);
        let line = "waiver of t until 2026-12-01 by someone, unused: The proofs wait for a fix of the tool.";
        assert_eq!(merged.waivers[0].line(), line);
        // Its texts are escaped, so that none splits a line.
        let mut waived = merged.waivers[0].clone();
        (waived.waiver.author, waived.used) = ("a\nb".to_string(), true);
        waived.waiver.reason = "two\nlines".to_string();
        let line = "waiver of t until 2026-12-01 by a\\nb, used: two\\nlines";
        assert_eq!(waived.line(), line);
    }

    #[test]
    fn times_are_rounded_to_milliseconds() {
        assert_eq!(seconds(Duration::from_micros(1_234_567)), 1.235);
        assert_eq!(seconds(Duration::from_secs(7_200)), 7_200.0);
        assert_eq!(seconds(Duration::ZERO), 0.0);
    }

    /// Commits the pin of the image `merging::image(digit)` in `fixture`.
    fn pin(fixture: &Fixture, digit: char) {
        let (repository, digest) = (
            "ghcr.io/casxi-lab/krepi-formal",
            digit.to_string().repeat(64),
        );
        let pin = json!({"schema": 1, "repository": repository, "digest": format!("sha256:{digest}"),
            "revision": "0".repeat(40)});
        fixture.write(Layout::PRODUCTION.image_pin, &format!("{pin}\n"));
        fixture.commit_all();
    }

    /// The checkout `label` with the formal target `a`, the pin of the image
    /// `merging::image('a')` and a waiver of `a` until `expires`, if given.
    fn pinned(label: &str, expires: Option<&str>) -> Fixture {
        let fixture = merging::checkout(label, r#"[{"name": "a"}]"#);
        pin(&fixture, 'a');
        if let Some(expires) = expires {
            waive(&fixture, "a", expires);
        }
        fixture
    }

    /// The record of the merge of the `VERIFIED` receipts of the
    /// qualification job and of the shard of `a` at the head of `fixture`,
    /// with the trigger `mode` of the run `run`.
    fn merged(fixture: &Fixture, mode: Mode, run: Option<&str>) -> Merge {
        let job = merging::qualification(fixture);
        let shard = merging::receipt(fixture, "target/a", &merging::units_of("a"));
        let paths = [("q", job), ("t", shard)].map(|(name, mut part)| {
            (part.trigger.mode, part.trigger.run_id) = (mode, run.map(String::from));
            merging::write(fixture, name, &part)
        });
        merging::merge_in(fixture, &paths)
    }

    /// The verdict on `record` in `fixture`, with `--require-fresh` when
    /// `fresh`.
    fn judged(fixture: &Fixture, record: &Merge, fresh: bool) -> (Verdict, Vec<String>) {
        judge(fixture.root(), &Layout::PRODUCTION, record, fresh)
    }

    /// The verdict `words` with its exit code `code` and exactly `reasons`.
    fn verdict(words: &'static str, code: u8, reasons: &[&str]) -> (Verdict, Vec<String>) {
        let reasons = Vec::from_iter(reasons.iter().map(|reason| reason.to_string()));
        ((words, code), reasons)
    }

    /// The status, completeness and whether `record` passes.
    fn conclusion(record: &Merge) -> (Status, bool, bool) {
        (record.status, record.complete, record.passes)
    }

    #[test]
    fn require_fresh_refuses_a_checkout_with_a_valid_waiver() {
        let fixture = pinned("receipt-waiver-fresh", Some("9999-12-31"));
        let mut record = merged(&fixture, Mode::ForcedFull, Some("1"));
        assert_eq!(conclusion(&record), (Status::Verified, true, true));
        assert!(!record.waivers[0].used);
        assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
        let left = "the record left out a under the waiver until 9999-12-31";
        let not_fresh = verdict("CURRENT, not fresh", 1, &[left]);
        assert_eq!(judged(&fixture, &record, true), not_fresh);
        // A waiver that has expired since still left its target out of the
        // base round of the run.
        record.waivers[0].waiver.expires = "2000-01-01".to_string();
        assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
        let left = "the record left out a under the waiver until 2000-01-01";
        let not_fresh = verdict("CURRENT, not fresh", 1, &[left]);
        assert_eq!(judged(&fixture, &record, true), not_fresh);
    }

    #[test]
    fn a_changed_gate_input_makes_the_record_not_current() {
        let fixture = pinned("receipt-inputs", None);
        let record = merged(&fixture, Mode::Manual, None);
        assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
        // Paths outside the gate inputs do not count.
        fixture.write("tools/notes.txt", "a tool\n");
        fixture.write(".github/scripts/notes.txt", "a script\n");
        fixture.commit_all();
        assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
        fixture.write("verification/notes.txt", "a change\n");
        fixture.commit_all();
        let other = "the gate inputs verification of the record are not those of the checkout";
        assert_eq!(
            judged(&fixture, &record, false),
            verdict("not CURRENT", 1, &[other])
        );
    }

    #[test]
    fn an_image_other_than_the_pinned_one_makes_the_record_not_current() {
        let fixture = merging::checkout("receipt-image", r#"[{"name": "a"}]"#);
        let (a, b) = (merging::image('a'), merging::image('b'));
        // Without a pin, no image is the pinned one.
        let record = merged(&fixture, Mode::Manual, None);
        let none = format!("the image {a} of the record is not the pinned image none");
        assert_eq!(
            judged(&fixture, &record, false),
            verdict("not CURRENT", 1, &[&none])
        );
        pin(&fixture, 'b');
        let record = merged(&fixture, Mode::Manual, None);
        assert_eq!(conclusion(&record), (Status::Verified, true, true));
        let other = format!("the image {a} of the record is not the pinned image {b}");
        assert_eq!(
            judged(&fixture, &record, false),
            verdict("not CURRENT", 1, &[&other])
        );
    }

    #[test]
    fn a_registered_unit_without_a_conclusion_makes_the_record_not_current() {
        let fixture = pinned("receipt-units", None);
        let mut record = merged(&fixture, Mode::Manual, None);
        let unit = record.units.remove("target/a").expect("the unit");
        let missing = "the unit target/a has no conclusion";
        assert_eq!(
            judged(&fixture, &record, false),
            verdict("not CURRENT", 1, &[missing])
        );
        // A conclusion of a unit that the checkout does not register.
        record.units.insert("target/b".to_string(), unit);
        let unregistered = "the unit target/b has a conclusion but is not registered";
        assert_eq!(
            judged(&fixture, &record, false),
            verdict("not CURRENT", 1, &[missing, unregistered])
        );
    }

    #[test]
    fn require_fresh_refuses_a_record_with_a_planned_statement() {
        let fixture = merging::checkout("receipt-planned", r#"[{"name": "a"}]"#);
        let statements = json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            {"name": "Krepi.Statements.P", "theorem": "Krepi.Proofs.P.p", "module": "Krepi.Proofs.P", "state": "planned"},
        ]});
        fixture.write(Layout::PRODUCTION.statements, &statements.to_string());
        pin(&fixture, 'a');
        let record = merged(&fixture, Mode::Required, Some("1"));
        assert_eq!(record.planned_statements, Some(1));
        assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
        let planned = "the record has planned_statements 1 where 0 is required";
        let not_fresh = verdict("CURRENT, not fresh", 1, &[planned]);
        assert_eq!(judged(&fixture, &record, true), not_fresh);
    }

    #[test]
    fn require_fresh_refuses_a_record_of_named_targets() {
        // The receipt of a run of the named target `demo`, which is SCOPED,
        // merges into a record without a conclusion.
        let fixture = Fixture::new("receipt-named");
        register(&fixture, r#"[{"name": "demo"}]"#);
        root_package(&fixture, "krepi-kernel", "");
        let done = gate(&fixture, &["demo"], Vec::new());
        let named = merging::write(&fixture, "demo", &done.written());
        let record = merging::merge_in(&fixture, &[named]);
        let found = (record.trigger, record.status);
        assert_eq!(found, (Some(Mode::Scoped), Status::ToolFailure));
        let (found, reasons) = judged(&fixture, &record, true);
        assert_eq!(found, ("not CURRENT", 1));
        let scoped = "the record has the trigger SCOPED without a run ID, not one of CI";
        assert!(reasons.iter().any(|reason| reason == scoped), "{reasons:?}");
        // Parts of the mode SCOPED are refused by the trigger alone.
        let fixture = pinned("receipt-scoped", None);
        let record = merged(&fixture, Mode::Scoped, Some("1"));
        assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
        let scoped = "the record has the trigger SCOPED, not one of CI";
        let not_fresh = verdict("CURRENT, not fresh", 1, &[scoped]);
        assert_eq!(judged(&fixture, &record, true), not_fresh);
    }

    #[test]
    fn a_current_record_is_fresh_only_with_the_trigger_of_a_run_of_ci() {
        let fixture = pinned("receipt-fresh", None);
        for mode in [Mode::Required, Mode::ForcedFull, Mode::Weekly] {
            let record = merged(&fixture, mode, Some("7"));
            assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
            let fresh = verdict("CURRENT and fresh", 0, &[]);
            assert_eq!(judged(&fixture, &record, true), fresh);
        }
        for (mode, run, reason) in [
            (Mode::Required, None, "REQUIRED without a run ID"),
            (Mode::Manual, Some("7"), "MANUAL"),
        ] {
            let record = merged(&fixture, mode, run);
            let reason = format!("the record has the trigger {reason}, not one of CI");
            let not_fresh = verdict("CURRENT, not fresh", 1, &[&reason]);
            assert_eq!(judged(&fixture, &record, true), not_fresh);
        }
    }

    #[test]
    fn a_rejected_record_within_waivers_that_hold_today_is_waived() {
        let fixture = pinned("receipt-waived", Some("9999-12-31"));
        let record = merging::merge_in(&fixture, &merging::rejected(&fixture));
        assert_eq!(conclusion(&record), (Status::Rejected, true, true));
        let rejected = "the record is REJECTED, complete and passing";
        let waived = verdict("WAIVED", 3, &[rejected]);
        assert_eq!(judged(&fixture, &record, false), waived);
        // Never with --require-fresh.
        let manual = "the record has the trigger MANUAL without a run ID, not one of CI";
        let left = "the record left out a under the waiver until 9999-12-31";
        let not = verdict("not CURRENT", 1, &[rejected, manual, left]);
        assert_eq!(judged(&fixture, &record, true), not);
        // Not once the waiver that it used has expired.
        let mut expired = record.clone();
        expired.waivers[0].waiver.expires = "2000-01-01".to_string();
        let gone = "the used waiver of a expired on 2000-01-01";
        let not = verdict("not CURRENT", 1, &[rejected, gone]);
        assert_eq!(judged(&fixture, &expired, false), not);
        // Nor when it is not current otherwise, or does not pass.
        let mut stale = record.clone();
        stale.units.remove("target/a");
        let missing = "the unit target/a has no conclusion";
        let not = verdict("not CURRENT", 1, &[missing, rejected]);
        assert_eq!(judged(&fixture, &stale, false), not);
        let mut failing = record;
        failing.passes = false;
        let not = verdict(
            "not CURRENT",
            1,
            &["the record is REJECTED, complete and not passing"],
        );
        assert_eq!(judged(&fixture, &failing, false), not);
    }

    #[test]
    fn a_record_with_problems_is_not_current() {
        let fixture = pinned("receipt-problems", None);
        let mut record = merged(&fixture, Mode::Manual, None);
        (record.status, record.complete) = (Status::ToolFailure, false);
        (record.passes, record.problems) = (false, vec!["a problem".to_string()]);
        let reasons = [
            "the record is TOOL_FAILURE, not complete and not passing",
            "the record has the problem: a problem",
        ];
        assert_eq!(
            judged(&fixture, &record, false),
            verdict("not CURRENT", 1, &reasons)
        );
    }

    #[test]
    fn a_record_of_another_schema_or_that_cannot_be_read_is_not_current() {
        let record = Merge {
            schema: MERGE_SCHEMA,
            ..Merge::default()
        };
        assert_eq!(read(&render(&record)), Ok(record.clone()));
        let mut value = serde_json::to_value(&record).expect("JSON");
        value["schema"] = 1.into();
        let other = "the record has schema 1 where 2 is expected".to_string();
        assert_eq!(read(&value.to_string()), Err(other));
        value.as_object_mut().expect("an object").remove("schema");
        let none = "the record has schema null where 2 is expected".to_string();
        assert_eq!(read(&value.to_string()), Err(none));
        value["schema"] = 2.into();
        value.as_object_mut().expect("an object").remove("passes");
        let error = read(&value.to_string()).expect_err("a missing field");
        assert!(
            error.starts_with("the record does not parse: missing field `passes`"),
            "{error}"
        );
        let error = read("{").expect_err("no JSON");
        assert!(error.starts_with("the record does not parse: "), "{error}");
    }

    #[test]
    fn a_checkout_with_unclean_gate_inputs_is_not_current() {
        let fixture = pinned("receipt-unclean", None);
        let record = merged(&fixture, Mode::Manual, None);
        fixture.write("verification/x", "");
        let dirty = "the gate inputs of the checkout are not clean: ?? verification/x";
        assert_eq!(
            judged(&fixture, &record, false),
            verdict("not CURRENT", 1, &[dirty])
        );
        fs::remove_file(fixture.root().join("verification/x")).expect("remove the file");
        assert_eq!(judged(&fixture, &record, false), verdict("CURRENT", 0, &[]));
        // A head without a commit.
        let branch = fixture.git(&["symbolic-ref", "HEAD"]).trim().to_string();
        fixture.git(&["symbolic-ref", "HEAD", "refs/heads/unborn"]);
        let (found, reasons) = judged(&fixture, &record, false);
        fixture.git(&["symbolic-ref", "HEAD", &branch]);
        assert_eq!(found, ("not CURRENT", 1));
        let unread = |reason: &String| reason.starts_with("cannot read the checkout: ");
        assert!(reasons.len() == 1 && unread(&reasons[0]), "{reasons:?}");
    }

    #[test]
    fn formal_receipt_prints_its_summary_and_exits_with_its_verdict() {
        let fixture = pinned("receipt-command", Some("9999-12-31"));
        let run = |args: &[&str]| {
            let matches = cli("").try_get_matches_from(["receipt"].iter().chain(args));
            super::command(
                fixture.root(),
                &Layout::PRODUCTION,
                &matches.expect("arguments"),
            )
        };
        // The record that `formal merge` writes, at the default path.
        assert_eq!(run(&[]), ExitCode::FAILURE);
        let [q, t] = merging::rejected(&fixture);
        assert_eq!(merging::exit(&fixture, &[&q, &t]), ExitCode::SUCCESS);
        assert_eq!(run(&[]), ExitCode::from(3));
        assert_eq!(run(&["--require-fresh"]), ExitCode::FAILURE);
        // A record by its path.
        let current = merged(&fixture, Mode::Weekly, Some("7"));
        let path = fixture.root().join("artifacts/current.json");
        fs::write(&path, render(&current)).expect("write the record");
        let path = path.to_str().expect("UTF-8");
        assert_eq!(run(&[path]), ExitCode::SUCCESS);
        assert_eq!(run(&[path, "--require-fresh"]), ExitCode::FAILURE);
        // The values of the record and the reasons are escaped.
        let mut record = current;
        record.reference = Some("refs/pull/7/merge\nx".to_string());
        let commit = record.commit.clone().expect("the commit");
        let reasons = ["two\nlines".to_string()];
        assert_eq!(
            summary(&record, "not CURRENT", &reasons),
            format!(
                "formal receipt: not CURRENT\ncommit {commit}\ntrigger WEEKLY refs/pull/7/merge\\nx 7\n\
                - waiver of a until 9999-12-31 by someone, unused: The proofs wait for a fix of the tool.\n\
                - two\\nlines\n"
            )
        );
        let none = "formal receipt: not CURRENT\ncommit none\ntrigger none none none\n";
        assert_eq!(summary(&Merge::default(), "not CURRENT", &[]), none);
    }
}
