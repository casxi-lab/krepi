//! The shards of the proof gate and their merge, as "Shards and merge" in
//! `docs/formal-verification.md` describes: beside the qualification job and
//! the comparator part, every formal target is a shard of its own, named by
//! its unit, whose registered budget, over its workers, is at most the shard
//! limit, the wall-clock limit of the gate less the time of the merge; and
//! `cargo xtask formal merge` combines the receipts of these parts of one
//! commit into the conclusions of the gate and its hard gates, with waivers.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use clap::{ArgMatches, value_parser};

use super::Layout;
use super::outcome::{self, Status, word};
use super::paths::{self, Git};
use super::receipt::{self, Merge, Part, Receipt, SCHEMA};
use super::registry::{self, State, Target};
use super::run::{self, Gate, Phase};
use super::toolchain::sha256;
use super::{base, comparator, guard, qualify, waiver};

/// The wall-clock limit of the gate, from the start of its first job to the
/// end of its merge.
pub const WALL_CLOCK: Duration = Duration::from_secs(3_600);

/// The time of the merge, from the start of its job to the end of
/// `cargo xtask formal merge`.
pub const MERGE: Duration = Duration::from_secs(300);

/// The longest that a shard may take: the wall-clock limit less the merge.
pub const SHARD_LIMIT: Duration = Duration::from_secs(WALL_CLOCK.as_secs() - MERGE.as_secs());

/// The workers of a shard, among which its registered budget is divided.
pub const WORKERS: u64 = 1;

/// The margin of the run of the shard of a target beyond its budget, for
/// its start and its closing steps.
pub const SHARD_MARGIN: Duration = Duration::from_secs(300);

/// The margin of the qualification job beyond the gate's budget, for the
/// extraction of every formal target.
pub const EXTRACTION_MARGIN: Duration = Duration::from_secs(600);

/// The seconds above which a merge flags its synthetic wall clock or a part.
pub const FLAG: Duration = Duration::from_secs(WALL_CLOCK.as_secs() * 4 / 5);

/// The cgroup memory peak above which a merge flags a part: 80% of 16,715,923,456 B.
pub const MEMORY: u64 = 13_372_738_764;

/// The directory of the merge record and its summary, below the root.
pub const DIR: &str = "artifacts/formal/merge";

/// The variable with the Unix time in seconds at which the merge job started.
pub const STARTED: &str = "KREPI_FORMAL_MERGE_STARTED";

/// The shards of the formal targets of `targets`, by name, each with the sum
/// of the registered budgets of its targets: every formal target is a shard
/// of its own, named by its unit.
pub fn shards(targets: &[Target]) -> BTreeMap<String, u64> {
    let mut shards = BTreeMap::new();
    for target in targets.iter().filter(|t| t.state == State::Formal) {
        let budget: &mut u64 = shards.entry(run::target_unit(&target.name)).or_default();
        *budget = budget.saturating_add(target.budget);
    }
    shards
}

/// The problems of the shards of `targets`: a shard whose registered
/// budget per worker, rounded up, is more than the shard limit.
pub fn budget_problems(targets: &[Target]) -> Vec<String> {
    let limit = SHARD_LIMIT.as_secs();
    let over = shards(targets).into_iter().filter_map(|(shard, budget)| {
        let seconds = budget.div_ceil(WORKERS);
        (seconds > limit).then(|| {
            format!(
                "shard {shard}: its registered budget of {budget} s is {seconds} s per worker, more than the shard limit of {limit} s"
            )
        })
    });
    over.collect()
}

/// The target of the shard `shard`, or none for the qualification job.
pub fn target(shard: &str) -> Option<&str> {
    shard.strip_prefix(run::target_unit("").as_str())
}

/// The budget of a run of `shard` in place of the gate's: the gate's and the
/// extraction margin for the qualification job, the comparator's for its part,
/// and for the shard of a target the shard margin, which its budget grows.
pub fn budget(shard: &str) -> Duration {
    let qualification = run::GATE_BUDGET + EXTRACTION_MARGIN;
    let budget = [qualification, SHARD_MARGIN][usize::from(target(shard).is_some())];
    [budget, comparator::BUDGET][usize::from(shard == comparator::PHASE)]
}

/// The shard that `--shard` names: `qualification`, `comparator` or `target/<name>`.
pub fn shard(name: &str) -> Result<String, String> {
    let parts = [qualify::PHASE, comparator::PHASE];
    let valid = parts.contains(&name) || target(name).is_some_and(|t| !t.is_empty());
    let invalid = format!("`{name}` is not {} or target/<name>", parts.join(", "));
    valid.then(|| name.to_string()).ok_or(invalid)
}

/// The hand-written module files that the stages of the shard of a target
/// hold: [`base::handwritten`] of the Lean files of the Lake project at the
/// snapshot commit, which it lists as [`guard::statement_hash`] does for the
/// base round, without the source rules, which the qualification job checks.
pub fn handwritten(gate: &mut Gate) -> Result<Vec<String>, String> {
    let (layout, source) = (*gate.layout(), gate.source());
    let commit = gate.receipt.commit.clone().unwrap_or_default();
    let args = ["ls-tree", "-r", "-z", &commit, "--", layout.project];
    let mut tracked = paths::tree_records(&gate.git(&args, None)?)?;
    tracked.retain(|path, _| !guard::in_calibration(path, &layout));
    Ok(base::handwritten(&layout, &source, &tracked, &[])?.0)
}

/// Each unit that the checkout at `root` registers in `layout`, with its
/// phase: of the qualification, base round, comparator and formal targets.
pub fn registered(root: &Path, layout: &Layout) -> Vec<(String, String)> {
    let [_, finish] = run::target_phases(root, layout, &BTreeSet::new(), None, None);
    let (qualification, base) = (qualify::phase(root, layout), base::phase(root, layout));
    let comparator = comparator::phase(root, layout, None);
    let units = |phase: Phase| (phase.units.into_iter()).map(move |u| (u, phase.name.clone()));
    Vec::from_iter(([qualification, base, comparator, finish].into_iter()).flat_map(units))
}

/// The synthetic wall clock of the slowest part, `slowest` seconds, and of
/// the merge, rounded to milliseconds, and whether it is above [`FLAG`].
fn wall_clock(slowest: f64, merge: f64) -> (f64, bool) {
    let seconds = (((slowest + merge) * 1_000.0).round() / 1_000.0).min(f64::MAX);
    (seconds, seconds > FLAG.as_secs_f64())
}

/// The command line of `cargo xtask formal merge`, with `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let receipts = clap::arg!(<RECEIPT>... "A receipt of the qualification job or of a shard");
    let receipts = receipts.value_parser(value_parser!(PathBuf));
    let calibration = clap::arg!(--calibration "Merge in the layout of the calibration target");
    let command = clap::Command::new("merge").about(about);
    command.args([receipts, calibration])
}

/// `cargo xtask formal merge` in `root`: merges the receipts that `matches`
/// names, with the seconds of its job from [`STARTED`], writes the record
/// and its summary into [`DIR`] and prints the summary. It exits with 0 when
/// the merge passes and 1 otherwise, or with 120, the record on standard
/// error, when it cannot write them.
pub fn command(root: &Path, layout: &Layout, matches: &ArgMatches) -> ExitCode {
    let paths = matches.get_many::<PathBuf>("RECEIPT").into_iter().flatten();
    let started = std::env::var(STARTED).ok().and_then(|s| s.parse().ok());
    let since = started.and_then(|s| UNIX_EPOCH.checked_add(Duration::from_secs(s)));
    let job = since.and_then(|since| SystemTime::now().duration_since(since).ok());
    let merged = merge(root, layout, &Vec::from_iter(paths.cloned()), job);
    let (text, dir, summary) = (receipt::render(&merged), root.join(DIR), summary(&merged));
    let written = (fs::create_dir_all(&dir))
        .and_then(|()| fs::write(dir.join("record.json"), &text))
        .and_then(|()| fs::write(dir.join("summary.md"), &summary));
    print!("{summary}");
    if let Err(error) = written {
        eprint!("cannot write {}: {error}\n{text}", dir.display());
        return ExitCode::from(120);
    }
    ExitCode::from(u8::from(!merged.passes))
}

/// The record of the merge of the receipts at `paths` in the checkout `root`
/// in `layout`, with the seconds `job` of its job before the merge. When
/// every precondition holds, its conclusion is that of a whole run from the
/// failures of the receipts and the units, complete when every receipt is,
/// which [`waiver::conclude`] judges with the waivers of the checkout;
/// otherwise it is `TOOL_FAILURE` and not complete, with each problem.
pub fn merge(root: &Path, layout: &Layout, paths: &[PathBuf], job: Option<Duration>) -> Merge {
    let start = Instant::now();
    let (mut merged, mut receipts, mut problems) = (Merge::default(), Vec::new(), Vec::new());
    for path in paths {
        let shown = path.display().to_string();
        let read = fs::read(path).map_err(|error| format!("cannot read {shown}: {error}"));
        let sha256 = read.as_ref().ok().map(|bytes| sha256(bytes));
        let not = |error| format!("{shown} is not a receipt: {error}");
        let parse = |bytes: Vec<u8>| serde_json::from_slice::<Receipt>(&bytes).map_err(not);
        let mut part = Part::default();
        match read.and_then(parse) {
            Ok(receipt) => {
                (part.shard, part.status) = (receipt.shard.clone(), Some(receipt.status));
                (part.complete, part.seconds) = (receipt.complete, receipt.seconds);
                let trigger = &receipt.trigger;
                (part.run_id, part.attempt) = (trigger.run_id.clone(), trigger.attempt.clone());
                let peak = receipt.resources.cgroup_memory_peak;
                (part.cgroup_memory_peak, part.over_memory) = (peak, peak.map(|p| p > MEMORY));
                part.over_seconds = receipt.seconds > FLAG.as_secs_f64();
                receipts.push((merged.parts.len(), receipt));
            }
            Err(problem) => problems.push(problem),
        }
        (part.receipt, part.sha256) = (shown, sha256);
        merged.parts.push(part);
    }
    // Of the receipts of one part, only that of its latest attempt counts.
    let attempt = |part: &Part| part.attempt.as_ref().and_then(|a| a.parse::<u64>().ok());
    let parts = merged.parts.clone();
    for part in &mut merged.parts {
        let later = |other: &Part| other.shard == part.shard && attempt(other) > attempt(part);
        part.superseded = part.shard.is_some() && parts.iter().any(later);
    }
    receipts.retain(|(index, _)| !merged.parts[*index].superseded);
    // The receipts are of the commit checked out, whose gate inputs are clean,
    // started from its gate inputs and have one trigger.
    let (inputs, mut git) = (paths::gate_inputs(layout), guard::Standalone(root));
    let head = paths::snapshot(&mut git, &inputs).and_then(|(commit, tree, snapshot)| {
        let changes = paths::changes(&mut git, &inputs)?.join(", ");
        let dirty = format!("the gate inputs of the checkout are not clean: {changes}");
        problems.extend((!changes.is_empty()).then_some(dirty));
        merged.inputs = Some(snapshot);
        Ok((Some(commit), Some(tree)))
    });
    let head = head.map_err(|error| problems.push(format!("cannot read the checkout: {error}")));
    let none = |value: &Option<String>| value.clone().unwrap_or("none".to_string());
    let (mut given, mut images, mut triggers) = (BTreeMap::new(), BTreeSet::new(), BTreeSet::new());
    for (index, receipt) in &receipts {
        let shown = &merged.parts[*index].receipt;
        let at = (receipt.commit.clone(), receipt.tree.clone());
        if let Some((commit, tree)) = head.as_ref().ok().filter(|head| **head != at) {
            let at = format!("of commit {} and tree {}", none(&at.0), none(&at.1));
            let checkout = format!("of commit {} and tree {}", none(commit), none(tree));
            problems.push(format!("{shown} is {at}, and the checkout {checkout}"));
        } else if head.is_ok() && receipt.inputs.before != merged.inputs {
            let other = format!("{shown} started from other gate inputs than the checkout");
            problems.push(other);
        }
        let trigger = receipt.trigger.clone();
        triggers.insert((Some(trigger.mode), trigger.reference, trigger.run_id));
        // The axioms of each theorem that the base round of the job audited.
        let theorems = receipt.base.iter().flat_map(|base| &base.theorems);
        let audited = theorems.filter_map(|(t, of)| Some((t.clone(), of.axioms.clone()?)));
        merged.axioms.extend(audited);
        images.insert(receipt.image.as_ref().and_then(|i| i.reference.clone()));
        match (receipt.schema, receipt.shard.as_deref()) {
            (SCHEMA, Some(shard)) => *given.entry(shard).or_insert(0) += 1,
            (SCHEMA, None) => problems.push(format!("{shown} has no shard")),
            (schema, _) => problems.push(format!(
                "{shown}: schema {schema} where {SCHEMA} is expected"
            )),
        }
    }
    if images.len() > 1 || images.contains(&None) {
        let images = Vec::from_iter(images.iter().map(none)).join(", ");
        problems.push(format!("the receipts do not name one image: {images}"));
    }
    let shown = (triggers.iter()).map(|(m, r, i)| format!("{} {} {}", word(m), none(r), none(i)));
    let shown = Vec::from_iter(shown).join(", ");
    let other = format!("the receipts do not have one trigger: {shown}");
    problems.extend((triggers.len() > 1).then_some(other));
    let one = triggers.pop_first().filter(|_| triggers.is_empty());
    (merged.trigger, merged.reference, merged.run_id) = one.unwrap_or_default();
    // Each unit that the checkout registers has exactly one conclusion.
    let read = |path: &str| {
        let text = fs::read_to_string(root.join(path));
        text.map_err(|error| format!("cannot read {path}: {error}"))
    };
    let at = |path: &'static str| move |error: String| format!("{path}: {error}");
    let cases = |text: String| qualify::load_cases(&text, layout).map(drop);
    let statements = |text: String| guard::load_statements(&text, layout);
    let statements = |text| statements(text).map_err(at(layout.statements));
    let registry = |text: String| registry::parse(&text).map_err(at(layout.registry));
    problems.extend(read(layout.cases).and_then(cases).err());
    let statements = (read(layout.statements).and_then(statements)).map(|file| file.statements);
    let statements = statements.map_err(|problem| problems.push(problem)).ok();
    let planned = (statements.iter().flatten()).filter(|s| s.state == guard::State::Planned);
    merged.planned_statements = statements.as_ref().map(|_| planned.count() as u64);
    let targets = read(layout.registry).and_then(registry);
    let targets = targets.map_err(|problem| problems.push(problem));
    let targets = targets.map_or_else(|()| Vec::new(), |registry| registry.targets);
    let concluded = receipts.iter().flat_map(|(_, receipt)| &receipt.units);
    let concluded = concluded.map(|(unit, u)| (unit.clone(), (u.status, u.reason.clone())));
    let registered = registered(root, layout);
    let (units, unaccounted) = outcome::account(&registered, concluded.collect(), None);
    problems.extend(unaccounted);
    // One receipt of the qualification job, the comparator and each formal target's shard.
    let mut expected = BTreeSet::from_iter(shards(&targets).into_keys());
    expected.extend([qualify::PHASE, comparator::PHASE].map(String::from));
    for part in &expected {
        let count = given.remove(part.as_str()).unwrap_or(0);
        let problem = format!("{count} receipts are of the part {part}, where one is expected");
        problems.extend((count != 1).then_some(problem));
    }
    let (registry, other) = (layout.registry, given.keys());
    problems.extend(other.map(|part| format!("{part} is not a part of {registry}")));
    // The qualification job extracted every formal target but those of the
    // waivers of the checkout that hold on the UTC date of the clock.
    let waivers = waiver::read(root, layout, &targets).map_err(|problem| problems.push(problem));
    let date = waiver::today(SystemTime::now()).map_err(|error| problems.push(error));
    let (waivers, date) = (waivers.unwrap_or_default(), date.ok());
    let waived = (date.as_deref()).map_or_else(BTreeSet::new, |d| waiver::holding(&waivers, d));
    let kept = Vec::from_iter(receipts.iter().map(|(_, receipt)| receipt));
    let jobs = (kept.iter()).filter(|r| r.shard.as_deref() == Some(qualify::PHASE));
    let jobs = Vec::from_iter(jobs.filter(|receipt| receipt.failures.is_empty()));
    let formal = (targets.iter()).filter(|t| t.state == State::Formal && !waived.contains(&t.name));
    let missing = formal.filter(|t| jobs.iter().any(|r| !r.proof_targets.contains_key(&t.name)));
    let missing = Vec::from_iter(missing.map(|target| target.name.as_str())).join(", ");
    let missed = format!("the qualification job left out {missing}, which no waiver covers");
    problems.extend((!missing.is_empty()).then_some(missed));
    // The conclusion, which only a merge without a problem synthesizes.
    let failures = receipts.iter().flat_map(|(_, receipt)| &receipt.failures);
    let mut statuses = Vec::from_iter(failures.map(|failure| failure.status));
    statuses.extend(units.values().map(|unit| unit.status));
    let complete = receipts.iter().all(|(_, receipt)| receipt.complete);
    merged.complete = problems.is_empty() && complete;
    statuses.extend((!problems.is_empty()).then_some(Status::ToolFailure));
    merged.status = outcome::run_status(&statuses, statuses.contains(&Status::Scoped));
    merged.image = images.pop_first().filter(|_| images.is_empty()).flatten();
    (merged.commit, merged.tree) = head.unwrap_or_default();
    (merged.schema, merged.units, merged.problems) = (receipt::MERGE_SCHEMA, units, problems);
    merged.waiver_date = date;
    let statements = statements.unwrap_or_default();
    waiver::conclude(&mut merged, layout, &kept, &waivers, &targets, &statements);
    // The synthetic wall clock: the slowest job and the merge to its end. The
    // comparator part runs in the job of the qualification part, after it.
    let in_job = |p: &Part| matches!(p.shard.as_deref(), Some(qualify::PHASE | comparator::PHASE));
    let kept = || merged.parts.iter().filter(|part| !part.superseded);
    let joint: f64 = Iterator::sum(kept().filter(|p| in_job(p)).map(|p| p.seconds));
    merged.slowest_part_seconds = kept().map(|part| part.seconds).fold(joint, f64::max);
    let first = |p: &&mut Part| !p.superseded && p.shard.as_deref() == Some(qualify::PHASE);
    for part in merged.parts.iter_mut().filter(first) {
        part.over_seconds = joint > FLAG.as_secs_f64();
    }
    merged.merge_from = ["command", "job"][usize::from(job.is_some())].to_string();
    merged.merge_seconds = receipt::seconds(job.unwrap_or_default() + start.elapsed());
    let (slowest, seconds) = (merged.slowest_part_seconds, merged.merge_seconds);
    (merged.wall_clock_seconds, merged.over_80_percent) = wall_clock(slowest, seconds);
    merged
}

/// The summary of `merged`: its conclusion, wall clock and trigger, that it
/// passes when it is not `VERIFIED`, and each waiver, flag and problem.
fn summary(merged: &Merge) -> String {
    let (status, seconds) = (word(&merged.status), merged.wall_clock_seconds);
    let complete = ["not ", ""][usize::from(merged.complete)];
    let conclusion = format!("formal merge: {status}, {complete}complete");
    let mut lines = vec![format!("{conclusion}; synthetic wall clock {seconds} s")];
    let text = |t: &Option<String>| format!("{}", t.as_deref().unwrap_or("none").escape_debug());
    let (reference, run) = (text(&merged.reference), text(&merged.run_id));
    let trigger = |mode| format!("- trigger {} {reference} {run}", word(&mode));
    lines.extend(merged.trigger.map(trigger));
    let g = &merged.gates;
    let [a, l, c] =
        [g.axioms, g.leanchecker, g.comparator].map(|p| ["fail", "pass"][usize::from(p)]);
    let checks = format!("- checks: axioms {a}, leanchecker {l}, comparator {c}");
    lines.push(checks);
    let passes = "- passes: every unit and part outside the waivers is VERIFIED".to_string();
    lines.extend((merged.passes && status != "VERIFIED").then_some(passes));
    let waivers = (merged.waivers.iter()).map(|waived| format!("- {}", waived.line()));
    lines.extend(waivers);
    let over = "the synthetic wall clock is above 80% of the wall-clock limit of the gate";
    let over = format!("- {over}, {} s", WALL_CLOCK.as_secs());
    lines.extend(merged.over_80_percent.then_some(over));
    let flag = FLAG.as_secs();
    for part in merged.parts.iter().filter(|part| !part.superseded) {
        let (shard, seconds, peak) = (text(&part.shard), part.seconds, part.cgroup_memory_peak);
        let over = format!("- part {shard}: {seconds} s, its job above {flag} s");
        lines.extend(part.over_seconds.then_some(over));
        let peak = peak.filter(|_| part.over_memory == Some(true));
        lines.extend(peak.map(|p| format!("- part {shard}: memory peak {p} B, above {MEMORY} B")));
    }
    let problems = merged.problems.iter();
    lines.extend(problems.map(|problem| format!("- problem: {}", problem.escape_debug())));
    lines.join("\n") + "\n"
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::formal::fixture::{self, Fixture};
    use crate::formal::outcome::{Class, Site};
    use crate::formal::process::LimitBy;
    use crate::formal::receipt::{Command, Failure, Gates, Image, Inputs, Mode, Unit};
    use crate::formal::registry;
    use crate::formal::run::tests::register;
    use crate::formal::waiver::tests::waive;

    pub(crate) const LAYOUT: &Layout = &Layout::PRODUCTION;

    /// The image that the receipts of the tests name, but where a test
    /// changes it.
    pub(crate) fn image(digit: char) -> String {
        let digest = digit.to_string().repeat(64);
        format!("ghcr.io/casxi-lab/krepi-formal@sha256:{digest}")
    }

    /// A checkout with one qualification case, no proved statement and the
    /// registry of `targets`, a JSON list, committed.
    pub(crate) fn checkout(label: &str, targets: &str) -> Fixture {
        let fixture = fixture::qualification(label, &serde_json::json!([fixture::arithmetic()]));
        let hash = "0".repeat(40);
        let statements = format!("{{\"schema\": 1, \"hash\": \"{hash}\", \"statements\": []}}\n");
        fixture.write("verification/statements.json", &statements);
        register(&fixture, targets);
        fixture
    }

    /// The units of the qualification job of the checkout at `root`.
    fn qualification_units(root: &Path) -> Vec<String> {
        let phases = [qualify::phase(root, LAYOUT), base::phase(root, LAYOUT)];
        Vec::from_iter(phases.into_iter().flat_map(|phase| phase.units))
    }

    /// The commit or tree `rev` of `fixture`.
    fn rev(fixture: &Fixture, rev: &str) -> String {
        fixture.git(&["rev-parse", rev]).trim().to_string()
    }

    /// A complete `VERIFIED` receipt of `shard` at the head of `fixture`,
    /// of 600 s and the image `image('a')`, that started from the gate
    /// inputs of the head and concludes each of `units`.
    pub(crate) fn receipt(fixture: &Fixture, shard: &str, units: &[String]) -> Receipt {
        let unit = |name: &String| {
            let (phase, status, reason) = ("p".to_string(), Status::Verified, None);
            (
                name.clone(),
                Unit {
                    phase,
                    status,
                    reason,
                },
            )
        };
        let reference = Some(image('a'));
        let inputs = paths::gate_inputs(LAYOUT);
        let snapshot = paths::snapshot(&mut guard::Standalone(fixture.root()), &inputs);
        let before = Some(snapshot.expect("the snapshot of the head").2);
        Receipt {
            schema: SCHEMA,
            status: Status::Verified,
            complete: true,
            targets: Vec::from_iter(target(shard).map(String::from)),
            shard: Some(shard.to_string()),
            image: Some(Image {
                reference,
                ..Image::default()
            }),
            seconds: 600.0,
            commit: Some(rev(fixture, "HEAD")),
            tree: Some(rev(fixture, "HEAD^{tree}")),
            inputs: Inputs {
                before,
                ..Inputs::default()
            },
            units: BTreeMap::from_iter(units.iter().map(unit)),
            ..Receipt::default()
        }
    }

    /// The command of a tool, `argv`, of `unit` at `site`, which concluded `class`.
    pub(crate) fn tool(unit: &str, site: Site, argv: &str, class: Class) -> Command {
        Command {
            sequence: 1,
            phase: None,
            unit: Some(unit.to_string()),
            site,
            argv: Vec::from_iter(argv.split(' ').map(String::from)),
            cwd: String::new(),
            class,
            reason: None,
            exit_code: Some(0),
            signal: None,
            timed_out: false,
            limit_seconds: 1.0,
            limit: LimitBy::Phase,
            seconds: 0.0,
            group_survived: false,
            stdout: None,
            stderr: None,
        }
    }

    /// The audit of the base round, concluded `class`.
    pub(crate) fn audit(class: Class) -> Command {
        tool("base", Site::AxiomAudit, "lake env lean Audit.lean", class)
    }

    /// The replay of the base round with `leanchecker --fresh`, concluded `class`.
    pub(crate) fn replay(class: Class) -> Command {
        let argv = "lake env leanchecker --fresh Krepi";
        tool("base", Site::Leanchecker, argv, class)
    }

    /// The receipt of the qualification job of `fixture` at its head, which
    /// extracted every formal target of its registry but those of the
    /// waivers that hold today, as the job does, and none when the registry
    /// cannot be read, and whose base round audited and replayed its stage.
    pub(crate) fn qualification(fixture: &Fixture) -> Receipt {
        let units = qualification_units(fixture.root());
        let mut job = receipt(fixture, qualify::PHASE, &units);
        job.commands = vec![audit(Class::Passed), replay(Class::Passed)];
        let text = fs::read_to_string(fixture.root().join(LAYOUT.registry));
        let parsed = text.ok().and_then(|text| registry::parse(&text).ok());
        let targets = parsed.map(|registry| registry.targets).unwrap_or_default();
        let waivers = waiver::read(fixture.root(), LAYOUT, &targets).unwrap_or_default();
        let today = waiver::today(SystemTime::now()).expect("the date of today");
        let waived = waiver::holding(&waivers, &today);
        let formal = targets
            .into_iter()
            .filter(|target| target.state == State::Formal);
        let extracted = formal.filter(|target| !waived.contains(&target.name));
        let extracted = extracted.map(|target| (target.name, receipt::Target::default()));
        job.proof_targets = extracted.collect();
        job
    }

    /// Writes `receipt` below the ignored `artifacts/parts/` of `fixture`.
    pub(crate) fn write(fixture: &Fixture, name: &str, receipt: &Receipt) -> PathBuf {
        let path = format!("artifacts/parts/{name}.json");
        fixture.write(&path, &receipt::render(receipt));
        fixture.root().join(path)
    }

    /// The merge of the receipts at `paths` [`with_comparator`] in
    /// `fixture`, with 60 s of its job before the command.
    pub(crate) fn merge_in(fixture: &Fixture, paths: &[PathBuf]) -> Merge {
        let paths = with_comparator(fixture, paths);
        merge(
            fixture.root(),
            LAYOUT,
            &paths,
            Some(Duration::from_secs(60)),
        )
    }

    /// `paths`, followed, unless they hold a receipt of the comparator part,
    /// by the receipt of that part beside each receipt of the qualification
    /// job among them, as the job writes it: of the commit, tree, gate
    /// inputs, trigger and image of that receipt, of no seconds, and with the
    /// units of the comparator that the checkout registers, `VERIFIED`.
    pub(crate) fn with_comparator(fixture: &Fixture, paths: &[PathBuf]) -> Vec<PathBuf> {
        let read = |path: &PathBuf| serde_json::from_slice::<Receipt>(&fs::read(path).ok()?).ok();
        let shard = |path: &&PathBuf| read(path).and_then(|receipt| receipt.shard);
        let given = |part: &'static str| {
            let of = move |path: &&PathBuf| shard(path).as_deref() == Some(part);
            BTreeSet::from_iter(paths.iter().filter(of))
        };
        let mut all = paths.to_vec();
        if !given(comparator::PHASE).is_empty() {
            return all;
        }
        let units = comparator::phase(fixture.root(), LAYOUT, None).units;
        let unit = |name: &String| {
            let (phase, status, reason) = (comparator::PHASE.to_string(), Status::Verified, None);
            (
                name.clone(),
                Unit {
                    phase,
                    status,
                    reason,
                },
            )
        };
        for path in given(qualify::PHASE) {
            let job = read(path).expect("a receipt");
            let part = Receipt {
                schema: SCHEMA,
                status: Status::Verified,
                complete: true,
                trigger: job.trigger,
                shard: Some(comparator::PHASE.to_string()),
                image: job.image,
                seconds: 0.0,
                commit: job.commit,
                tree: job.tree,
                inputs: job.inputs,
                units: BTreeMap::from_iter(units.iter().map(unit)),
                ..Receipt::default()
            };
            let name = path.file_stem().expect("a file name").to_string_lossy();
            all.push(write(fixture, &format!("{name}-comparator"), &part));
        }
        all
    }

    /// The units of a target `t` without mutants.
    pub(crate) fn units_of(target: &str) -> Vec<String> {
        vec![format!("target/{target}")]
    }

    /// Asserts that `merged` has no conclusion, for exactly `problems`.
    fn no_conclusion(merged: &Merge, problems: &[String]) {
        assert_eq!(merged.status, Status::ToolFailure);
        assert!(!merged.complete);
        assert_eq!(merged.problems, problems);
    }

    /// Asserts that `merged` is the complete `VERIFIED` conclusion.
    fn verified(merged: &Merge) {
        assert_eq!(merged.problems, Vec::<String>::new());
        assert_eq!((merged.status, merged.complete), (Status::Verified, true));
    }

    /// The problem of a receipt at `path` of a commit and tree other than
    /// those of the checkout.
    fn elsewhere(path: &Path, at: (&str, &str), checkout: (&str, &str)) -> String {
        let (shown, (commit, tree), (head, head_tree)) = (path.display(), at, checkout);
        format!(
            "{shown} is of commit {commit} and tree {tree}, and the checkout of commit {head} and tree {head_tree}"
        )
    }

    /// The path of the receipt of the comparator part that [`with_comparator`]
    /// writes beside the receipt `name` of the qualification job.
    fn comparator_of(fixture: &Fixture, name: &str) -> PathBuf {
        fixture
            .root()
            .join(format!("artifacts/parts/{name}-comparator.json"))
    }

    #[test]
    fn the_comparator_is_a_part_of_every_merge() {
        let target = r#"[{"name": "a", "module": "A", "proof_modules": ["Krepi.Proofs.A"]}]"#;
        let fixture = checkout("merge-comparator", target);
        let statements = serde_json::json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            {"name": "Krepi.Statements.S", "theorem": "Krepi.Proofs.A.s", "module": "Krepi.Proofs.A", "state": "proved"},
            {"name": "Krepi.Statements.R", "theorem": "Krepi.Proofs.R.r", "module": "Krepi.Proofs.R", "state": "proved"},
            {"name": "Krepi.Statements.P", "theorem": "Krepi.Proofs.A.p", "module": "Krepi.Proofs.A", "state": "planned"},
        ]});
        fixture.write(LAYOUT.statements, &statements.to_string());
        fixture.commit_all();
        // Its units are those of the proved statements of the formal target
        // that lists their module, and one for the others.
        let registered = registered(fixture.root(), LAYOUT).into_iter();
        let units = Vec::from_iter(registered.filter(|(_, phase)| phase == comparator::PHASE));
        let unit = |name: &str| (name.to_string(), comparator::PHASE.to_string());
        assert_eq!(units, [unit("comparator"), unit("comparator/a")]);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let names = ["comparator".to_string(), "comparator/a".to_string()];
        let c = write(&fixture, "c", &receipt(&fixture, comparator::PHASE, &names));
        let paths = [q.clone(), c, t.clone()];
        verified(&merge(fixture.root(), LAYOUT, &paths, None));
        // Without its receipt, or with one that misses a unit, the merge has
        // no conclusion.
        let merged = merge(fixture.root(), LAYOUT, &[q.clone(), t.clone()], None);
        let missing = |unit: &str| format!("the unit {unit} has no conclusion");
        let none = "0 receipts are of the part comparator, where one is expected";
        let problems = [
            missing("comparator"),
            missing("comparator/a"),
            none.to_string(),
        ];
        no_conclusion(&merged, &problems);
        let c = write(
            &fixture,
            "c",
            &receipt(&fixture, comparator::PHASE, &names[1..]),
        );
        let merged = merge(fixture.root(), LAYOUT, &[q, c, t], None);
        no_conclusion(&merged, &[missing("comparator")]);
    }

    #[test]
    fn receipts_that_agree_but_are_not_of_the_commit_checked_out_give_no_conclusion() {
        let fixture = checkout("merge-elsewhere", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        verified(&merge_in(&fixture, &[q.clone(), t.clone()]));
        let (c0, t0) = (rev(&fixture, "HEAD"), rev(&fixture, "HEAD^{tree}"));
        // The receipts agree with each other, and the checkout moves on.
        fixture.write("README.md", "moved\n");
        fixture.commit_all();
        let (c1, t1) = (rev(&fixture, "HEAD"), rev(&fixture, "HEAD^{tree}"));
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        let (at, head) = ((c0.as_str(), t0.as_str()), (c1.as_str(), t1.as_str()));
        let c = comparator_of(&fixture, "q");
        let problems = [&q, &t, &c].map(|path| elsewhere(path, at, head));
        no_conclusion(&merged, &problems);
        assert_eq!(merged.commit.as_deref(), Some(c1.as_str()));
    }

    #[test]
    fn receipts_of_different_commits_or_trees_give_no_conclusion() {
        let fixture = checkout("merge-commits", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let (head, tree) = (rev(&fixture, "HEAD"), rev(&fixture, "HEAD^{tree}"));
        let before = rev(&fixture, "HEAD~1");
        let checkout = (head.as_str(), tree.as_str());
        // A shard of the commit before, with the tree of the head.
        let mut shard = receipt(&fixture, "target/a", &units_of("a"));
        shard.commit = Some(before.clone());
        let t = write(&fixture, "t", &shard);
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        no_conclusion(&merged, &[elsewhere(&t, (&before, &tree), checkout)]);
        // A shard of the head with another tree.
        let other = "f".repeat(40);
        let mut shard = receipt(&fixture, "target/a", &units_of("a"));
        shard.tree = Some(other.clone());
        let t = write(&fixture, "t", &shard);
        let merged = merge_in(&fixture, &[q, t.clone()]);
        no_conclusion(&merged, &[elsewhere(&t, (&head, &other), checkout)]);
    }

    #[test]
    fn receipts_of_different_images_or_without_an_image_give_no_conclusion() {
        let fixture = checkout("merge-images", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let shard = receipt(&fixture, "target/a", &units_of("a"));
        let problem = |images: &str| format!("the receipts do not name one image: {images}");
        let (a, b) = (image('a'), image('b'));
        let mut other = shard.clone();
        other.image = Some(Image {
            reference: Some(b.clone()),
            ..Image::default()
        });
        let t = write(&fixture, "t", &other);
        no_conclusion(
            &merge_in(&fixture, &[q.clone(), t]),
            &[problem(&format!("{a}, {b}"))],
        );
        // A receipt without an image, or whose image has no reference.
        for image in [None, Some(Image::default())] {
            let mut other = shard.clone();
            other.image = image;
            let t = write(&fixture, "t", &other);
            let merged = merge_in(&fixture, &[q.clone(), t]);
            no_conclusion(&merged, &[problem(&format!("none, {a}"))]);
        }
        // Two receipts without an image.
        let mut without = qualification(&fixture);
        without.image = None;
        let q = write(&fixture, "q", &without);
        let mut other = shard;
        other.image = None;
        let t = write(&fixture, "t", &other);
        let merged = merge_in(&fixture, &[q, t]);
        no_conclusion(&merged, &[problem("none")]);
        assert_eq!(merged.image, None);
    }

    #[test]
    fn a_qualification_receipt_of_another_commit_gives_no_conclusion() {
        let fixture = checkout("merge-qualification", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let (c0, t0) = (rev(&fixture, "HEAD"), rev(&fixture, "HEAD^{tree}"));
        fixture.write("README.md", "moved\n");
        fixture.commit_all();
        let (c1, t1) = (rev(&fixture, "HEAD"), rev(&fixture, "HEAD^{tree}"));
        // The shard is of the commit checked out.
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t]);
        let (at, head) = ((c0.as_str(), t0.as_str()), (c1.as_str(), t1.as_str()));
        let c = comparator_of(&fixture, "q");
        no_conclusion(&merged, &[elsewhere(&q, at, head), elsewhere(&c, at, head)]);
    }

    #[test]
    fn a_registry_of_two_formal_targets_with_the_receipt_of_one_shard_gives_no_conclusion() {
        let fixture = checkout("merge-missing", r#"[{"name": "a"}, {"name": "b"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q, t]);
        no_conclusion(
            &merged,
            &[
                "the unit target/b has no conclusion".to_string(),
                "0 receipts are of the part target/b, where one is expected".to_string(),
            ],
        );
        assert_eq!(merged.units["target/b"].status, Status::ToolFailure);
    }

    #[test]
    fn a_shard_receipt_without_the_conclusion_of_a_registered_mutant_gives_no_conclusion() {
        let mutant = r#"{"name": "m", "file": "src/lib.rs", "find": "a", "replace": "b",
            "fails": ["Krepi.Proofs.T.f_spec"]}"#;
        let targets = format!(r#"[{{"name": "a", "mutants": [{mutant}]}}]"#);
        let fixture = checkout("merge-mutant", &targets);
        let q = write(&fixture, "q", &qualification(&fixture));
        let all = ["target/a".to_string(), "target/a/mutant/m".to_string()];
        let t = write(&fixture, "t", &receipt(&fixture, "target/a", &all));
        verified(&merge_in(&fixture, &[q.clone(), t]));
        let t = write(&fixture, "t", &receipt(&fixture, "target/a", &all[..1]));
        let merged = merge_in(&fixture, &[q, t]);
        no_conclusion(
            &merged,
            &["the unit target/a/mutant/m has no conclusion".to_string()],
        );
    }

    #[test]
    fn a_shard_of_a_target_outside_the_registry_gives_no_conclusion() {
        let targets = r#"[{"name": "a"}, {"name": "p", "state": "planned"}]"#;
        let fixture = checkout("merge-outside", targets);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let c = write(
            &fixture,
            "c",
            &receipt(&fixture, "target/c", &units_of("c")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t.clone(), c]);
        no_conclusion(
            &merged,
            &[
                "the unit target/c has a conclusion but is not registered".to_string(),
                "target/c is not a part of verification/targets.json".to_string(),
            ],
        );
        // A planned target is no shard.
        let p = write(&fixture, "p", &receipt(&fixture, "target/p", &[]));
        let merged = merge_in(&fixture, &[q, t, p]);
        let problem = "target/p is not a part of verification/targets.json";
        no_conclusion(&merged, &[problem.to_string()]);
    }

    #[test]
    fn a_synthetic_wall_clock_above_2880_s_is_flagged_over_80_percent() {
        let fixture = checkout("merge-clock", r#"[{"name": "a"}]"#);
        let mut q = qualification(&fixture);
        q.seconds = 2_700.0;
        let q = write(&fixture, "q", &q);
        let shard = |seconds: f64| {
            let mut shard = receipt(&fixture, "target/a", &units_of("a"));
            shard.seconds = seconds;
            write(&fixture, "t", &shard)
        };
        // The slowest part and 60 s of the merge stay below 2,880 s.
        let merged = merge_in(&fixture, &[q.clone(), shard(2_800.0)]);
        verified(&merged);
        assert_eq!(merged.slowest_part_seconds, 2_800.0);
        assert!(merged.wall_clock_seconds < 2_880.0 && !merged.over_80_percent);
        assert_eq!(merged.merge_from, "job");
        assert!(merged.merge_seconds >= 60.0);
        // A shard that takes longer pushes the synthetic wall clock above.
        let merged = merge_in(&fixture, &[q.clone(), shard(2_830.0)]);
        verified(&merged);
        assert_eq!(merged.slowest_part_seconds, 2_830.0);
        assert!(merged.wall_clock_seconds > 2_880.0 && merged.over_80_percent);
        let line =
            "- the synthetic wall clock is above 80% of the wall-clock limit of the gate, 3600 s";
        assert!(
            summary(&merged).lines().any(|l| l == line),
            "{}",
            summary(&merged)
        );
        // Without the start of its job, the merge counts its own seconds.
        let alone = merge(fixture.root(), LAYOUT, &[q, shard(10.0)], None);
        assert_eq!(alone.merge_from, "command");
        assert!(alone.merge_seconds < 60.0);
        // The limit is strict.
        assert_eq!(wall_clock(2_800.0, 80.0), (2_880.0, false));
        assert_eq!(wall_clock(2_800.0, 80.001), (2_880.001, true));
    }

    #[test]
    fn without_formal_targets_the_qualification_receipt_alone_concludes_and_a_shard_receipt_fails_it()
     {
        let fixture = checkout("merge-empty", "[]");
        let receipt_q = qualification(&fixture);
        let q = write(&fixture, "q", &receipt_q);
        let merged = merge_in(&fixture, std::slice::from_ref(&q));
        verified(&merged);
        let keys = Vec::from_iter(merged.units.keys().cloned());
        let mut units = qualification_units(fixture.root());
        units.sort();
        assert_eq!(keys, units);
        assert_eq!(merged.parts.len(), 2);
        let bytes = fs::read(&q).expect("the receipt");
        assert_eq!(merged.parts[0].sha256, Some(sha256(&bytes)));
        // A shard where the registry has no formal target.
        let x = write(&fixture, "x", &receipt(&fixture, "target/x", &[]));
        let paths = with_comparator(&fixture, &[q, x]);
        let merged = super::merge(fixture.root(), LAYOUT, &paths, None);
        let problem = "target/x is not a part of verification/targets.json";
        no_conclusion(&merged, &[problem.to_string()]);
    }

    #[test]
    fn of_the_receipts_of_one_part_only_that_of_the_latest_attempt_counts() {
        let fixture = checkout("merge-attempts", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let attempt = |attempt: &str, status: Status| {
            let mut shard = receipt(&fixture, "target/a", &units_of("a"));
            shard.trigger.attempt = Some(attempt.to_string());
            shard.status = status;
            shard.units.get_mut("target/a").expect("the unit").status = status;
            write(&fixture, &format!("t{attempt}"), &shard)
        };
        let (first, second) = (
            attempt("1", Status::Rejected),
            attempt("2", Status::Verified),
        );
        let merged = merge_in(&fixture, &[q.clone(), first.clone(), second]);
        verified(&merged);
        assert_eq!(
            Vec::from_iter(merged.parts.iter().map(|p| p.superseded)),
            [false, true, false, false]
        );
        // Two receipts of one part and of the same attempt.
        let merged = merge_in(&fixture, &[q, first.clone(), first]);
        let problems = [
            "the unit target/a has 2 conclusions",
            "2 receipts are of the part target/a, where one is expected",
        ];
        no_conclusion(&merged, &problems.map(String::from));
    }

    /// The exit of `cargo xtask formal merge` in `fixture` for `paths`
    /// [`with_comparator`].
    pub(crate) fn exit(fixture: &Fixture, paths: &[&PathBuf]) -> ExitCode {
        let paths = with_comparator(
            fixture,
            &Vec::from_iter(paths.iter().map(|p| p.to_path_buf())),
        );
        let args = Vec::from_iter(paths.iter().map(|path| path.to_str().expect("UTF-8")));
        let matches = cli("").try_get_matches_from(["merge"].into_iter().chain(args));
        command(fixture.root(), LAYOUT, &matches.expect("the command line"))
    }

    #[test]
    fn the_conclusion_of_a_merge_is_that_of_a_whole_run_from_its_receipts() {
        let mutant = r#"{"name": "m", "file": "src/lib.rs", "find": "a", "replace": "b",
            "fails": ["Krepi.Proofs.T.f_spec"]}"#;
        let targets = format!(r#"[{{"name": "a", "mutants": [{mutant}]}}]"#);
        let fixture = checkout("merge-conclusion", &targets);
        let q = write(&fixture, "q", &qualification(&fixture));
        let all = ["target/a".to_string(), "target/a/mutant/m".to_string()];
        // A shard whose target and mutant are concluded `units`, with a
        // failure of `failure`, of the status and completeness `run`.
        let shard = |units: [Status; 2], failure: Option<Status>, run: (Status, bool)| {
            let mut shard = receipt(&fixture, "target/a", &all);
            for (unit, status) in all.iter().zip(units) {
                shard.units.get_mut(unit).expect("the unit").status = status;
            }
            let message = "the failure of the run".to_string();
            let failure = failure.map(|status| Failure { status, message });
            (shard.failures, (shard.status, shard.complete)) = (Vec::from_iter(failure), run);
            write(&fixture, "t", &shard)
        };
        let conclusion = |merged: Merge| {
            assert_eq!(merged.problems, Vec::<String>::new());
            (merged.status, merged.complete)
        };
        // A rejected target whose mutant did not run, as a whole run has it.
        let units = [Status::Rejected, Status::NotRun];
        let t = shard(units, None, (Status::Rejected, false));
        let merged = merge_in(&fixture, &[q.clone(), t]);
        assert_eq!(conclusion(merged), (Status::Rejected, false));
        // A target at its budget, whose mutant did not run.
        let units = [Status::Budget, Status::NotRun];
        let t = shard(units, None, (Status::Budget, false));
        let merged = merge_in(&fixture, &[q.clone(), t]);
        assert_eq!(conclusion(merged), (Status::Budget, false));
        // A shard that the disk guard refused, which is NOT_RUN.
        let units = [Status::NotRun, Status::NotRun];
        let t = shard(units, Some(Status::NotRun), (Status::NotRun, false));
        let merged = merge_in(&fixture, &[q.clone(), t]);
        assert_eq!(conclusion(merged), (Status::ToolFailure, false));
        // A shard whose only failure is STALE is complete, and not VERIFIED.
        let units = [Status::Verified, Status::Verified];
        let t = shard(units, Some(Status::Stale), (Status::Stale, true));
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        assert_eq!(conclusion(merged), (Status::Stale, true));
        assert_eq!(exit(&fixture, &[&q, &t]), ExitCode::FAILURE);
    }

    #[test]
    fn exactly_one_receipt_of_the_qualification_job_is_required() {
        let fixture = checkout("merge-qualification-job", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        verified(&merge_in(&fixture, &[q.clone(), t.clone()]));
        // Each unit of the qualification job with `problem`, and `count`
        // receipts of its part.
        let units = qualification_units(fixture.root());
        let problems = |problem: &str, count: usize| {
            let units = units
                .iter()
                .map(|unit| format!("the unit {unit} {problem}"));
            let part =
                format!("{count} receipts are of the part qualification, where one is expected");
            Vec::from_iter(units.chain([part]))
        };
        // Without it, the comparator part is missing too.
        let merged = merge_in(&fixture, std::slice::from_ref(&t));
        let mut missing = problems("has no conclusion", 0);
        let comparator = "0 receipts are of the part comparator, where one is expected";
        missing.insert(missing.len() - 1, comparator.to_string());
        no_conclusion(&merged, &missing);
        let merged = merge_in(&fixture, &[q.clone(), q, t]);
        no_conclusion(&merged, &problems("has 2 conclusions", 2));
    }

    #[test]
    fn a_receipt_that_cannot_be_read_or_is_not_of_a_shard_of_schema_5_gives_no_conclusion() {
        let fixture = checkout("merge-receipts", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let shard = receipt(&fixture, "target/a", &units_of("a"));
        let t = write(&fixture, "t", &shard);
        verified(&merge_in(&fixture, &[q.clone(), t]));
        let none = |part: &str| format!("0 receipts are of the part {part}, where one is expected");
        // A receipt that cannot be read, which has no digest, or that does
        // not parse: the units of its shard have no conclusion.
        let missing = fixture.root().join("artifacts/parts/missing.json");
        fixture.write("artifacts/parts/text.json", "not a receipt\n");
        let text = fixture.root().join("artifacts/parts/text.json");
        let unread = [
            (missing, "cannot read {}: ", None),
            (
                text,
                "{} is not a receipt: ",
                Some(sha256(b"not a receipt\n")),
            ),
        ];
        for (path, start, sha256) in unread {
            let merged = merge_in(&fixture, &[q.clone(), path.clone()]);
            let start = start.replace("{}", &path.display().to_string());
            let first = merged
                .problems
                .first()
                .filter(|first| first.starts_with(&start));
            let first = first.expect("the problem of the receipt").clone();
            let unit = "the unit target/a has no conclusion".to_string();
            no_conclusion(&merged, &[first, unit, none("target/a")]);
            assert_eq!(merged.parts[1].sha256, sha256);
        }
        // A receipt of schema 4, which has no shard, still concludes its
        // units, but is no receipt of its part.
        let mut old = serde_json::to_value(qualification(&fixture)).expect("JSON");
        old["schema"] = 4.into();
        old.as_object_mut().expect("an object").remove("shard");
        fixture.write("artifacts/parts/old.json", &old.to_string());
        let old = fixture.root().join("artifacts/parts/old.json");
        let shown = old.display();
        let merged = merge_in(&fixture, &[old.clone(), write(&fixture, "t", &shard)]);
        let schema = format!("{shown}: schema 4 where 5 is expected");
        no_conclusion(
            &merged,
            &[schema, none("comparator"), none("qualification")],
        );
        // A receipt of schema 5 without a shard.
        let mut unnamed = shard;
        unnamed.shard = None;
        let unnamed = write(&fixture, "unnamed", &unnamed);
        let merged = merge_in(&fixture, &[q, unnamed.clone()]);
        let problem = format!("{} has no shard", unnamed.display());
        no_conclusion(&merged, &[problem, none("target/a")]);
    }

    #[test]
    fn a_dirty_checkout_or_an_unreadable_file_of_it_gives_no_conclusion() {
        let fixture = checkout("merge-checkout", "[]");
        let merged = || {
            let q = write(&fixture, "q", &qualification(&fixture));
            merge_in(&fixture, &[q])
        };
        verified(&merged());
        // An untracked file among the gate inputs.
        fixture.write("verification/x", "");
        let dirty = "the gate inputs of the checkout are not clean: ?? verification/x";
        no_conclusion(&merged(), &[dirty.to_string()]);
        fs::remove_file(fixture.root().join("verification/x")).expect("remove the file");
        verified(&merged());
        // A head without a commit.
        let q = write(&fixture, "q", &qualification(&fixture));
        let branch = fixture.git(&["symbolic-ref", "HEAD"]).trim().to_string();
        fixture.git(&["symbolic-ref", "HEAD", "refs/heads/unborn"]);
        let unborn = merge_in(&fixture, &[q]);
        fixture.git(&["symbolic-ref", "HEAD", &branch]);
        let problem = unborn.problems.first().expect("a problem").clone();
        assert!(
            problem.starts_with("cannot read the checkout: "),
            "{problem}"
        );
        no_conclusion(&unborn, &[problem]);
        assert_eq!((unborn.commit, unborn.tree), (None, None));
        // A file that the merge reads, malformed or missing, committed.
        for path in [LAYOUT.cases, LAYOUT.statements, LAYOUT.registry] {
            let before = fs::read_to_string(fixture.root().join(path)).expect("the file");
            for (text, start) in [
                ("{", format!("{path}: ")),
                ("", format!("cannot read {path}: ")),
            ] {
                match text {
                    "" => fs::remove_file(fixture.root().join(path)).expect("remove the file"),
                    text => fixture.write(path, text),
                }
                fixture.commit_all();
                let merged = merged();
                let problem = merged
                    .problems
                    .first()
                    .filter(|first| first.starts_with(&start));
                let problem = problem
                    .unwrap_or_else(|| panic!("{:?}", merged.problems))
                    .clone();
                no_conclusion(&merged, &[problem]);
                fixture.write(path, &before);
                fixture.commit_all();
            }
        }
        verified(&merged());
    }

    #[test]
    fn a_merge_writes_its_record_and_summary_and_exits_with_its_conclusion() {
        let fixture = checkout("merge-command", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let run = |paths: &[&PathBuf]| exit(&fixture, paths);
        assert_eq!(run(&[&q, &t]), ExitCode::SUCCESS);
        let dir = fixture.root().join(DIR);
        let record = fs::read_to_string(dir.join("record.json")).expect("the record");
        let record: Merge = serde_json::from_str(&record).expect("a merge record");
        verified(&record);
        let summary = fs::read_to_string(dir.join("summary.md")).expect("the summary");
        assert!(summary.starts_with("formal merge: VERIFIED, complete; synthetic wall clock "));
        assert_eq!(run(&[&q]), ExitCode::FAILURE);
        // A merge that cannot write its record exits with 120.
        fs::remove_dir_all(&dir).expect("remove the directory");
        fs::write(&dir, "").expect("a file in its place");
        assert_eq!(run(&[&q, &t]), ExitCode::from(120));
    }

    /// The targets of the registry `text`.
    fn targets(text: &str) -> Vec<Target> {
        registry::parse(text).expect("a registry").targets
    }

    #[test]
    fn the_shard_limit_is_the_wall_clock_limit_of_the_gate_less_the_merge() {
        assert_eq!(SHARD_LIMIT, Duration::from_secs(3_300));
        assert_eq!(MERGE + SHARD_LIMIT, WALL_CLOCK);
        assert_eq!(WORKERS, 1);
    }

    #[test]
    fn the_committed_registries_keep_the_shard_limit() {
        let production = targets(include_str!("../../../verification/targets.json"));
        assert_eq!(budget_problems(&production), Vec::<String>::new());
        assert!(shards(&production).is_empty());
        let calibration = targets(include_str!(
            "../../../verification/qualification/calibration/targets.json"
        ));
        assert_eq!(budget_problems(&calibration), Vec::<String>::new());
        // The planned target of the calibration is no shard.
        assert_eq!(
            shards(&calibration),
            BTreeMap::from([("target/calibration".to_string(), 3_000)])
        );
    }

    #[test]
    fn each_formal_target_is_a_shard_of_its_own_with_its_registered_budget() {
        let registry = |budget: u64| {
            targets(&format!(
                r#"{{"schema": 2, "targets": [
                    {{"name": "a", "budget": {budget}}}, {{"name": "b"}},
                    {{"name": "p", "state": "planned", "budget": 9999}}]}}"#
            ))
        };
        assert_eq!(
            shards(&registry(3_300)),
            BTreeMap::from([
                ("target/a".to_string(), 3_300),
                ("target/b".to_string(), registry::BUDGET)
            ])
        );
        assert_eq!(budget_problems(&registry(3_300)), Vec::<String>::new());
        assert_eq!(
            budget_problems(&registry(3_301)),
            [
                "shard target/a: its registered budget of 3301 s is 3301 s per worker, more than the shard limit of 3300 s"
            ]
        );
    }

    /// The receipts of the qualification job and of the shard of `a`, whose
    /// target the proofs reject and which has no mutants, so that it is
    /// complete, as a run of it is.
    pub(crate) fn rejected(fixture: &Fixture) -> [PathBuf; 2] {
        let mut shard = receipt(fixture, "target/a", &units_of("a"));
        shard.status = Status::Rejected;
        shard.units.get_mut("target/a").expect("the unit").status = Status::Rejected;
        let q = write(fixture, "q", &qualification(fixture));
        [q, write(fixture, "t", &shard)]
    }

    /// The status, completeness and whether `merged` passes, when it has no
    /// problem.
    fn conclusion(merged: &Merge) -> (Status, bool, bool) {
        assert_eq!(merged.problems, Vec::<String>::new());
        (merged.status, merged.complete, merged.passes)
    }

    /// The hard gates of `merged`: the axioms, `leanchecker` and the comparator.
    fn gates(merged: &Merge) -> [bool; 3] {
        let Gates {
            axioms,
            leanchecker,
            comparator,
        } = merged.gates;
        [axioms, leanchecker, comparator]
    }

    /// The theorem of the statement in the proof module of `a` of [`proving`].
    const PROVED: &str = "Krepi.Proofs.A.s";

    /// The checkout `label` with the formal target `a`, whose proof module
    /// proves a statement with [`PROVED`], committed.
    fn proving(label: &str) -> Fixture {
        let target = r#"[{"name": "a", "module": "A", "proof_modules": ["Krepi.Proofs.A"]}]"#;
        let fixture = checkout(label, target);
        let statements = serde_json::json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            {"name": "Krepi.Statements.S", "theorem": PROVED, "module": "Krepi.Proofs.A", "state": "proved"},
        ]});
        fixture.write(LAYOUT.statements, &statements.to_string());
        fixture.commit_all();
        fixture
    }

    /// The receipts of the qualification job of `fixture` of [`proving`],
    /// whose base round concluded the statement `statement`, of the shard of
    /// `a`, whose proofs the shard rejects after its audit concluded `audit`,
    /// and of the comparator part, which concluded `comparator/a` `compared`.
    fn proved_parts(
        fixture: &Fixture,
        statement: Status,
        audit: Class,
        compared: Status,
    ) -> [PathBuf; 3] {
        let mut job = qualification(fixture);
        job.units
            .get_mut(&base::unit(PROVED))
            .expect("the unit")
            .status = statement;
        let mut shard = receipt(fixture, "target/a", &units_of("a"));
        shard.status = Status::Rejected;
        shard.units.get_mut("target/a").expect("the unit").status = Status::Rejected;
        let argv = "lake env lean Audit.lean";
        shard.commands = vec![tool("target/a", Site::AxiomAudit, argv, audit)];
        let mut part = receipt(fixture, comparator::PHASE, &["comparator/a".to_string()]);
        part.units.get_mut("comparator/a").expect("the unit").status = compared;
        [("q", job), ("t", shard), ("c", part)].map(|(name, part)| write(fixture, name, &part))
    }

    #[test]
    fn without_a_waiver_a_rejected_target_fails_the_merge_and_the_gates_it_reaches() {
        let fixture = checkout("merge-unwaived", r#"[{"name": "a"}]"#);
        let [q, t] = rejected(&fixture);
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, false));
        assert_eq!(gates(&merged), [false, true, true]);
        assert_eq!(exit(&fixture, &[&q, &t]), ExitCode::FAILURE);
        // The base round rejected the statement that `a` proves for an axiom,
        // so the comparator did not run on it, and the shard rejects `a`.
        let fixture = proving("merge-unwaived-statement");
        let parts = proved_parts(&fixture, Status::Rejected, Class::Passed, Status::NotRun);
        let merged = merge_in(&fixture, &parts);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, false));
        assert_eq!(gates(&merged), [false, true, false]);
        let summary = summary(&merged);
        let line = "- checks: axioms fail, leanchecker pass, comparator fail";
        assert!(summary.lines().any(|l| l == line), "{summary}");
        let [q, t, c] = &parts;
        assert_eq!(exit(&fixture, &[q, t, c]), ExitCode::FAILURE);
    }

    #[test]
    fn an_expired_waiver_does_not_pass_a_rejected_target() {
        let fixture = checkout("merge-expired", r#"[{"name": "a"}]"#);
        waive(&fixture, "a", "2000-01-01");
        let [q, t] = rejected(&fixture);
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, false));
        assert!(merged.waivers.is_empty());
        let date = merged.waiver_date.as_deref();
        assert!(date.is_some_and(|date| date > "2000-01-01"), "{date:?}");
        assert_eq!(exit(&fixture, &[&q, &t]), ExitCode::FAILURE);
    }

    #[test]
    fn a_valid_waiver_passes_the_merge_and_the_hard_gates_of_a_rejected_target_and_the_record_stays_rejected()
     {
        let fixture = proving("merge-waived");
        waive(&fixture, "a", "9999-12-31");
        // The base round leaves out the statement that `a` proves, so the
        // comparator does not check it either, and the shard rejects `a`
        // after its audit failed.
        let parts = proved_parts(
            &fixture,
            Status::Scoped,
            Class::ProofFailure,
            Status::Scoped,
        );
        let merged = merge_in(&fixture, &parts);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, true));
        assert_eq!(gates(&merged), [true, true, true]);
        assert_eq!(merged.units["target/a"].status, Status::Rejected);
        assert_eq!(merged.units["comparator/a"].status, Status::Scoped);
        let waived = Vec::from_iter(merged.waivers.iter().map(|w| (&w.waiver.scope, w.used)));
        assert_eq!(waived, [(&vec!["a".to_string()], true)]);
        let [q, t, c] = &parts;
        assert_eq!(exit(&fixture, &[q, t, c]), ExitCode::SUCCESS);
        let record = fs::read_to_string(fixture.root().join(DIR).join("record.json"));
        let record: Merge = serde_json::from_str(&record.expect("the record")).expect("a record");
        assert_eq!((record.status, record.passes), (Status::Rejected, true));
        assert_eq!(gates(&record), [true, true, true]);
        let summary = summary(&merged);
        let lines = Vec::from_iter(summary.lines().skip(1));
        assert_eq!(
            lines,
            [
                "- trigger MANUAL none none",
                "- checks: axioms pass, leanchecker pass, comparator pass",
                "- passes: every unit and part outside the waivers is VERIFIED",
                "- waiver of a until 9999-12-31 by someone, used: The proofs wait for a fix of the tool.",
            ]
        );
    }

    #[test]
    fn a_waived_target_whose_mutants_did_not_run_still_passes() {
        let mutant = r#"{"name": "m", "file": "src/lib.rs", "find": "a", "replace": "b",
            "fails": ["Krepi.Proofs.T.f_spec"]}"#;
        let fixture = checkout(
            "merge-waived-mutant",
            &format!(r#"[{{"name": "a", "mutants": [{mutant}]}}]"#),
        );
        waive(&fixture, "a", "9999-12-31");
        let all = ["target/a".to_string(), "target/a/mutant/m".to_string()];
        let mut shard = receipt(&fixture, "target/a", &all);
        (shard.status, shard.complete) = (Status::Rejected, false);
        for (unit, status) in all.iter().zip([Status::Rejected, Status::NotRun]) {
            shard.units.get_mut(unit).expect("the unit").status = status;
        }
        let (q, t) = (
            write(&fixture, "q", &qualification(&fixture)),
            write(&fixture, "t", &shard),
        );
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        assert_eq!(conclusion(&merged), (Status::Rejected, false, true));
        assert!(merged.waivers[0].used);
        assert_eq!(exit(&fixture, &[&q, &t]), ExitCode::SUCCESS);
    }

    #[test]
    fn a_waived_target_that_is_verified_leaves_the_record_verified_and_the_waiver_unused() {
        let fixture = checkout("merge-waived-verified", r#"[{"name": "a"}]"#);
        waive(&fixture, "a", "9999-12-31");
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        assert_eq!(conclusion(&merged), (Status::Verified, true, true));
        assert!(!merged.waivers[0].used);
        let line = "- waiver of a until 9999-12-31 by someone, unused: The proofs wait for a fix of the tool.";
        let summary = summary(&merged);
        assert!(summary.lines().any(|l| l == line), "{summary}");
        assert!(!summary.contains("- passes"), "{summary}");
        assert_eq!(exit(&fixture, &[&q, &t]), ExitCode::SUCCESS);
    }

    #[test]
    fn a_waived_part_with_a_failure_uses_its_waiver_and_another_part_with_one_fails() {
        let fixture = checkout("merge-waived-failure", r#"[{"name": "a"}]"#);
        waive(&fixture, "a", "9999-12-31");
        let stale = |mut receipt: Receipt| {
            let message = "the failure of the run".to_string();
            receipt.failures = vec![Failure {
                status: Status::Stale,
                message,
            }];
            receipt.status = Status::Stale;
            receipt
        };
        let shard = receipt(&fixture, "target/a", &units_of("a"));
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(&fixture, "t", &stale(shard.clone()));
        let merged = merge_in(&fixture, &[q, t.clone()]);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, true));
        assert!(merged.waivers[0].used);
        // A failure of the qualification job is no waived target's.
        let q = write(&fixture, "q", &stale(qualification(&fixture)));
        let t = write(&fixture, "t", &shard);
        let merged = merge_in(&fixture, &[q, t]);
        assert_eq!(conclusion(&merged), (Status::Stale, true, false));
        assert!(!merged.waivers[0].used);
    }

    #[test]
    fn a_qualification_job_that_did_not_extract_a_target_outside_the_waivers_gives_no_conclusion() {
        let fixture = checkout("merge-left-out", r#"[{"name": "a"}, {"name": "b"}]"#);
        waive(&fixture, "b", "9999-12-31");
        let t = write(
            &fixture,
            "a",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let b = write(
            &fixture,
            "b",
            &receipt(&fixture, "target/b", &units_of("b")),
        );
        // The job extracted `a` and left out `b`, or extracted both.
        let mut job = qualification(&fixture);
        assert_eq!(Vec::from_iter(job.proof_targets.keys()), ["a"]);
        let q = write(&fixture, "q", &job);
        verified(&merge_in(&fixture, &[q, t.clone(), b.clone()]));
        job.proof_targets
            .insert("b".to_string(), receipt::Target::default());
        let q = write(&fixture, "q", &job);
        verified(&merge_in(&fixture, &[q, t.clone(), b.clone()]));
        // A job that left out `a`, as under a waiver that has since expired.
        job.proof_targets.remove("a");
        let q = write(&fixture, "q", &job);
        let merged = merge_in(&fixture, &[q, t.clone(), b.clone()]);
        let problem = "the qualification job left out a, which no waiver covers";
        no_conclusion(&merged, &[problem.to_string()]);
        // A job whose extraction stopped keeps its own conclusion.
        let message = "the phase extraction stopped".to_string();
        job.failures = vec![Failure {
            status: Status::ToolFailure,
            message,
        }];
        (job.status, job.complete) = (Status::ToolFailure, false);
        let q = write(&fixture, "q", &job);
        let merged = merge_in(&fixture, &[q, t, b]);
        assert_eq!(conclusion(&merged), (Status::ToolFailure, false, false));
    }

    #[test]
    fn receipts_of_different_triggers_give_no_conclusion() {
        let fixture = checkout("merge-triggers", r#"[{"name": "a"}]"#);
        let triggered = |receipt: &mut Receipt, mode: Mode, run_id: &str, attempt: &str| {
            let trigger = &mut receipt.trigger;
            (trigger.mode, trigger.run_id) = (mode, Some(run_id.to_string()));
            trigger.reference = Some("refs/pull/7/merge".to_string());
            (trigger.event, trigger.attempt) =
                (Some(attempt.to_string()), Some(attempt.to_string()));
        };
        let (mut job, mut shard) = (
            qualification(&fixture),
            receipt(&fixture, "target/a", &units_of("a")),
        );
        triggered(&mut job, Mode::Required, "1", "1");
        let q = write(&fixture, "q", &job);
        // Other attempts and events of one run merge.
        triggered(&mut shard, Mode::Required, "1", "2");
        let merged = merge_in(&fixture, &[q.clone(), write(&fixture, "t", &shard)]);
        verified(&merged);
        let trigger = (
            merged.trigger,
            merged.reference.as_deref(),
            merged.run_id.as_deref(),
        );
        assert_eq!(
            trigger,
            (Some(Mode::Required), Some("refs/pull/7/merge"), Some("1"))
        );
        let line = "- trigger REQUIRED refs/pull/7/merge 1";
        assert!(
            summary(&merged).lines().any(|l| l == line),
            "{}",
            summary(&merged)
        );
        // Another mode, or another run.
        let problem = |other: &str| {
            let one = "REQUIRED refs/pull/7/merge 1";
            format!("the receipts do not have one trigger: {one}, {other}")
        };
        for (mode, run_id, other) in [
            (Mode::Weekly, "1", "WEEKLY refs/pull/7/merge 1"),
            (Mode::Required, "2", "REQUIRED refs/pull/7/merge 2"),
        ] {
            triggered(&mut shard, mode, run_id, "1");
            let merged = merge_in(&fixture, &[q.clone(), write(&fixture, "t", &shard)]);
            no_conclusion(&merged, &[problem(other)]);
            assert_eq!((merged.trigger, merged.run_id), (None, None));
        }
        // The record holds their values as they are, and the summary escapes
        // them once.
        triggered(&mut shard, Mode::Required, "1\n2", "1");
        let merged = merge_in(&fixture, &[q, write(&fixture, "t", &shard)]);
        no_conclusion(&merged, &[problem("REQUIRED refs/pull/7/merge 1\n2")]);
        let line = format!("- problem: {}", problem("REQUIRED refs/pull/7/merge 1\\n2"));
        let summary = summary(&merged);
        assert!(summary.lines().any(|l| l == line), "{summary}");
    }

    #[test]
    fn a_receipt_that_did_not_start_from_the_gate_inputs_of_the_checkout_gives_no_conclusion() {
        let fixture = checkout("merge-inputs", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let mut shard = receipt(&fixture, "target/a", &units_of("a"));
        let merged = merge_in(&fixture, &[q.clone(), write(&fixture, "t", &shard)]);
        verified(&merged);
        assert_eq!(merged.inputs, shard.inputs.before);
        let other = "started from other gate inputs than the checkout";
        for before in [None, Some(Default::default())] {
            shard.inputs.before = before;
            let t = write(&fixture, "t", &shard);
            let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
            no_conclusion(&merged, &[format!("{} {other}", t.display())]);
        }
    }

    #[test]
    fn the_record_flags_parts_over_the_seconds_and_the_memory_limit() {
        let fixture = checkout("merge-flags", r#"[{"name": "a"}, {"name": "b"}]"#);
        let part = |shard: &str, seconds: f64, peak: Option<u64>| {
            let mut receipt = match shard {
                "q" => qualification(&fixture),
                shard => receipt(&fixture, &format!("target/{shard}"), &units_of(shard)),
            };
            (receipt.seconds, receipt.resources.cgroup_memory_peak) = (seconds, peak);
            write(&fixture, shard, &receipt)
        };
        let q = part("q", 2_880.0, Some(MEMORY));
        let a = part("a", 2_880.001, Some(MEMORY + 1));
        let merged = merge_in(&fixture, &[q, a, part("b", 10.0, None)]);
        verified(&merged);
        let flags = Vec::from_iter(
            merged
                .parts
                .iter()
                .map(|p| (p.cgroup_memory_peak, p.over_seconds, p.over_memory)),
        );
        assert_eq!(
            flags,
            [
                (Some(13_372_738_764), false, Some(false)),
                (Some(13_372_738_765), true, Some(true)),
                (None, false, None),
                (None, false, None),
            ]
        );
        let summary = summary(&merged);
        let parts = Vec::from_iter(summary.lines().filter(|line| line.starts_with("- part ")));
        assert_eq!(
            parts,
            [
                "- part target/a: 2880.001 s, its job above 2880 s",
                "- part target/a: memory peak 13372738765 B, above 13372738764 B",
            ]
        );
    }

    #[test]
    fn the_record_counts_the_planned_statements() {
        let fixture = checkout("merge-planned", "[]");
        let statements = serde_json::json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            {"name": "Krepi.Statements.P", "theorem": "Krepi.Proofs.P.p", "module": "Krepi.Proofs.P", "state": "planned"},
            {"name": "Krepi.Statements.Q", "theorem": "Krepi.Proofs.Q.q", "module": "Krepi.Proofs.Q", "state": "proved"},
        ]});
        fixture.write(LAYOUT.statements, &statements.to_string());
        fixture.commit_all();
        let merged = merge_in(&fixture, &[write(&fixture, "q", &qualification(&fixture))]);
        verified(&merged);
        assert_eq!(merged.planned_statements, Some(1));
        assert!(merged.units.contains_key("base/Krepi.Proofs.Q.q"));
        fs::remove_file(fixture.root().join(LAYOUT.statements)).expect("remove the file");
        fixture.commit_all();
        let merged = merge_in(&fixture, &[write(&fixture, "q", &qualification(&fixture))]);
        assert_eq!(
            (merged.status, merged.planned_statements),
            (Status::ToolFailure, None)
        );
    }

    #[test]
    fn a_waiver_record_that_breaks_its_rules_gives_no_conclusion() {
        let fixture = checkout("merge-waiver-record", r#"[{"name": "a"}]"#);
        waive(&fixture, "x", "9999-12-31");
        let [q, t] = rejected(&fixture);
        let merged = merge_in(&fixture, &[q, t]);
        let problem = "verification/waivers.json: waiver 0: \"x\" is no registered target";
        no_conclusion(&merged, &[problem.to_string()]);
        assert!(merged.waivers.is_empty() && !merged.passes);
    }

    #[test]
    fn the_summary_escapes_a_problem_with_a_key_of_the_waiver_record() {
        let fixture = checkout("merge-waiver-key", r#"[{"name": "a"}]"#);
        let file = r#"{"schema": 1, "waivers": [], "x\nformal merge: VERIFIED, complete": 0}"#;
        fixture.write(LAYOUT.waivers, file);
        fixture.commit_all();
        let summary = summary(&merge_in(&fixture, &rejected(&fixture)));
        let lines = Vec::from_iter(summary.lines().skip(1));
        assert_eq!(
            lines,
            [
                "- trigger MANUAL none none",
                "- checks: axioms fail, leanchecker fail, comparator fail",
                "- problem: verification/waivers.json: unknown field `x\\nformal merge: VERIFIED, complete`, expected `schema` or `waivers` at line 1 column 66",
            ]
        );
    }

    #[test]
    fn a_statement_in_a_proof_module_of_a_waived_target_is_recorded_and_not_required() {
        let target = r#"[{"name": "a", "module": "A", "proof_modules": ["Krepi.Proofs.A"]}]"#;
        let fixture = checkout("merge-waived-statement", target);
        let statements = serde_json::json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            {"name": "Krepi.Statements.S", "theorem": "Krepi.Proofs.A.s", "module": "Krepi.Proofs.A", "state": "proved"},
            {"name": "Krepi.Statements.R", "theorem": "Krepi.Proofs.Helper.r", "module": "Krepi.Proofs.Helper", "state": "proved"},
        ]});
        fixture.write(LAYOUT.statements, &statements.to_string());
        waive(&fixture, "a", "9999-12-31");
        // The base round of the job leaves the statements of a module that it
        // leaves out unchecked.
        let scoped = |job: &mut Receipt, theorem: &str| {
            let unit = job.units.get_mut(&base::unit(theorem)).expect("the unit");
            unit.status = Status::Scoped;
        };
        let mut job = qualification(&fixture);
        scoped(&mut job, "Krepi.Proofs.A.s");
        let q = write(&fixture, "q", &job);
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, true));
        assert!(merged.waivers[0].used);
        assert_eq!(exit(&fixture, &[&q, &t]), ExitCode::SUCCESS);
        // A statement of a module that only imports what a waiver leaves out
        // is no waived target's.
        scoped(&mut job, "Krepi.Proofs.Helper.r");
        let q = write(&fixture, "q", &job);
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        assert_eq!(conclusion(&merged), (Status::Scoped, true, false));
        assert_eq!(exit(&fixture, &[&q, &t]), ExitCode::FAILURE);
        // Without a waiver that holds, the statement is required.
        waive(&fixture, "a", "2000-01-01");
        let mut job = qualification(&fixture);
        scoped(&mut job, "Krepi.Proofs.A.s");
        let q = write(&fixture, "q", &job);
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q, t]);
        assert_eq!(conclusion(&merged), (Status::Scoped, true, false));
    }

    #[test]
    fn each_hard_gate_fails_on_its_own_entries() {
        let fixture = proving("merge-gates");
        let parts = |fixture: &Fixture| {
            let shard = receipt(fixture, "target/a", &units_of("a"));
            let compared = receipt(fixture, comparator::PHASE, &["comparator/a".to_string()]);
            (qualification(fixture), shard, compared)
        };
        let gates_of = |fixture: &Fixture, job: &Receipt, shard: &Receipt, compared: &Receipt| {
            let parts = [("q", job), ("t", shard), ("c", compared)];
            let merged = merge_in(
                fixture,
                &parts.map(|(name, part)| write(fixture, name, part)),
            );
            assert_eq!(merged.problems, Vec::<String>::new());
            gates(&merged)
        };
        let (job, shard, compared) = parts(&fixture);
        let all = |job: &Receipt| gates_of(&fixture, job, &shard, &compared);
        assert_eq!(all(&job), [true, true, true]);
        let status = |receipt: &mut Receipt, unit: &str, status: Status| {
            receipt.units.get_mut(unit).expect("the unit").status = status;
        };
        // The axioms: an audit that did not pass, no audit, or a unit of the
        // base round or of a target that is not VERIFIED; a run of the
        // heartbeats is no audit.
        let mut other = job.clone();
        other.commands[0].class = Class::ProofFailure;
        assert_eq!(all(&other), [false, true, true]);
        other.commands.remove(0);
        assert_eq!(all(&other), [false, true, true]);
        let heartbeats = "lake env lean --json .heartbeats/Krepi/Proofs/A.lean";
        let heartbeats = tool("base", Site::AxiomAudit, heartbeats, Class::ProofFailure);
        let mut other = job.clone();
        other.commands.push(heartbeats);
        assert_eq!(all(&other), [true, true, true]);
        for unit in [base::PHASE.to_string(), base::unit(PROVED)] {
            let mut other = job.clone();
            status(&mut other, &unit, Status::Rejected);
            assert_eq!(all(&other), [false, true, true], "{unit}");
        }
        let mut other = shard.clone();
        let argv = "lake env lean Audit.lean";
        other.commands = vec![tool("target/a", Site::AxiomAudit, argv, Class::ToolFailure)];
        assert_eq!(
            gates_of(&fixture, &job, &other, &compared),
            [false, true, true]
        );
        status(&mut other, "target/a", Status::Rejected);
        other.commands.clear();
        assert_eq!(
            gates_of(&fixture, &job, &other, &compared),
            [false, true, true]
        );
        // `leanchecker`: no replay, two, or one that did not pass; the version
        // of Lean is no replay.
        let mut other = job.clone();
        other.commands.pop();
        assert_eq!(all(&other), [true, false, true]);
        other
            .commands
            .extend([replay(Class::Passed), replay(Class::Passed)]);
        assert_eq!(all(&other), [true, false, true]);
        other.commands.pop();
        other.commands[1].class = Class::ProofFailure;
        assert_eq!(all(&other), [true, false, true]);
        let mut other = job.clone();
        let version = tool(
            "base",
            Site::Leanchecker,
            "lean --version",
            Class::ToolFailure,
        );
        other.commands.push(version);
        assert_eq!(all(&other), [true, true, true]);
        // The comparator: a unit that is not VERIFIED.
        for unit_status in [Status::Rejected, Status::NotRun] {
            let mut other = compared.clone();
            status(&mut other, "comparator/a", unit_status);
            let found = gates_of(&fixture, &job, &shard, &other);
            assert_eq!(found, [true, true, false], "{unit_status:?}");
        }
        // Under a waiver of `a`, its commands and units hold, but neither the
        // unit `base` nor a replay does.
        waive(&fixture, "a", "9999-12-31");
        let (mut job, mut shard, mut compared) = parts(&fixture);
        status(&mut job, &base::unit(PROVED), Status::Rejected);
        shard.commands = vec![tool("target/a", Site::AxiomAudit, argv, Class::ToolFailure)];
        status(&mut shard, "target/a", Status::Rejected);
        status(&mut compared, "comparator/a", Status::NotRun);
        assert_eq!(
            gates_of(&fixture, &job, &shard, &compared),
            [true, true, true]
        );
        job.commands[1].class = Class::ProofFailure;
        status(&mut job, base::PHASE, Status::Rejected);
        assert_eq!(
            gates_of(&fixture, &job, &shard, &compared),
            [false, false, true]
        );
    }

    #[test]
    fn a_unit_of_a_mutant_is_no_entry_of_the_hard_gates() {
        let mutant = r#"{"name": "m", "file": "src/lib.rs", "find": "a", "replace": "b",
            "fails": ["Krepi.Proofs.T.f_spec"]}"#;
        let targets = format!(r#"[{{"name": "a", "mutants": [{mutant}]}}]"#);
        let fixture = checkout("merge-gates-mutant", &targets);
        let all = ["target/a".to_string(), "target/a/mutant/m".to_string()];
        let mut shard = receipt(&fixture, "target/a", &all);
        let survived = shard.units.get_mut(&all[1]).expect("the unit");
        survived.status = Status::Rejected;
        let q = write(&fixture, "q", &qualification(&fixture));
        let merged = merge_in(&fixture, &[q, write(&fixture, "t", &shard)]);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, false));
        assert_eq!(gates(&merged), [true, true, true]);
    }

    #[test]
    fn a_statement_left_out_only_through_an_import_fails_the_hard_gates() {
        let target = r#"[{"name": "a", "module": "A", "proof_modules": ["Krepi.Proofs.A"]}]"#;
        let fixture = checkout("merge-gates-import", target);
        let statements = serde_json::json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            {"name": "Krepi.Statements.S", "theorem": "Krepi.Proofs.A.s", "module": "Krepi.Proofs.A", "state": "proved"},
            {"name": "Krepi.Statements.R", "theorem": "Krepi.Proofs.Helper.r", "module": "Krepi.Proofs.Helper", "state": "proved"},
        ]});
        fixture.write(LAYOUT.statements, &statements.to_string());
        waive(&fixture, "a", "9999-12-31");
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let names = ["comparator".to_string(), "comparator/a".to_string()];
        let (mut job, mut part) = (
            qualification(&fixture),
            receipt(&fixture, comparator::PHASE, &names),
        );
        let scoped = |receipt: &mut Receipt, unit: &str| {
            receipt.units.get_mut(unit).expect("the unit").status = Status::Scoped;
        };
        let merged = |job: &Receipt, part: &Receipt| {
            let (q, c) = (write(&fixture, "q", job), write(&fixture, "c", part));
            merge_in(&fixture, &[q, t.clone(), c])
        };
        // The statement in the proof module of `a` is left out and covered.
        scoped(&mut job, &base::unit("Krepi.Proofs.A.s"));
        scoped(&mut part, "comparator/a");
        let waived = merged(&job, &part);
        assert_eq!(conclusion(&waived), (Status::Rejected, true, true));
        assert_eq!(gates(&waived), [true, true, true]);
        // That of a module that only imports what the waiver leaves out is not.
        scoped(&mut job, &base::unit("Krepi.Proofs.Helper.r"));
        scoped(&mut part, "comparator");
        let imported = merged(&job, &part);
        assert_eq!(conclusion(&imported), (Status::Scoped, true, false));
        assert_eq!(gates(&imported), [false, true, false]);
    }

    #[test]
    fn a_problem_of_the_merge_fails_every_hard_gate() {
        let fixture = checkout("merge-gates-problem", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        verified(&merged);
        assert_eq!(gates(&merged), [true, true, true]);
        let line = "- checks: axioms pass, leanchecker pass, comparator pass";
        assert!(summary(&merged).lines().any(|l| l == line));
        fixture.write("verification/x", "");
        let merged = merge_in(&fixture, &[q, t]);
        let dirty = "the gate inputs of the checkout are not clean: ?? verification/x";
        no_conclusion(&merged, &[dirty.to_string()]);
        assert_eq!(gates(&merged), [false, false, false]);
        let line = "- checks: axioms fail, leanchecker fail, comparator fail";
        assert!(summary(&merged).lines().any(|l| l == line));
    }

    #[test]
    fn the_seconds_of_the_comparator_count_toward_the_qualification_job_and_its_flag() {
        let fixture = checkout("merge-job", r#"[{"name": "a"}]"#);
        let part = |name: &str, mut receipt: Receipt, seconds: f64| {
            receipt.seconds = seconds;
            write(&fixture, name, &receipt)
        };
        // The receipts of the qualification, comparator and `a` of `seconds`.
        let merged = |[q, c, t]: [f64; 3]| {
            let q = part("q", qualification(&fixture), q);
            let c = part("c", receipt(&fixture, comparator::PHASE, &[]), c);
            let t = part("t", receipt(&fixture, "target/a", &units_of("a")), t);
            let merged = merge_in(&fixture, &[q, c, t]);
            verified(&merged);
            merged
        };
        let flags = |merged: &Merge| Vec::from_iter(merged.parts.iter().map(|p| p.over_seconds));
        // The job of the qualification and the comparator is the slowest, or
        // the shard is.
        let job = merged([1_500.0, 1_000.0, 2_400.0]);
        assert_eq!(job.slowest_part_seconds, 2_500.0);
        assert_eq!(flags(&job), [false, false, false]);
        assert_eq!(
            merged([1_500.0, 1_000.0, 2_600.0]).slowest_part_seconds,
            2_600.0
        );
        // Their sum above 2,880 s flags the qualification part, and only it.
        assert_eq!(
            flags(&merged([1_500.0, 1_380.0, 10.0])),
            [false, false, false]
        );
        let over = merged([1_500.0, 1_380.5, 10.0]);
        assert_eq!(over.slowest_part_seconds, 2_880.5);
        assert!(over.over_80_percent);
        assert_eq!(flags(&over), [true, false, false]);
        let summary = summary(&over);
        let line = "- part qualification: 1500 s, its job above 2880 s";
        assert!(summary.lines().any(|l| l == line), "{summary}");
        // The comparator part keeps its own flag.
        assert_eq!(flags(&merged([10.0, 2_880.5, 10.0])), [true, true, false]);
    }

    #[test]
    fn the_record_reports_the_axioms_of_each_audited_theorem() {
        let fixture = checkout("merge-axioms", "[]");
        let theorem = |axioms: Option<&[&str]>, status| base::Theorem {
            axioms: axioms.map(|axioms| Vec::from_iter(axioms.iter().map(|a| a.to_string()))),
            status,
            ..base::Theorem::default()
        };
        let theorems = [
            (
                "Krepi.Proofs.A.s",
                theorem(Some(&["propext", "Quot.sound"]), Status::Verified),
            ),
            ("Krepi.Proofs.A.h", theorem(Some(&[]), Status::Verified)),
            (
                "Krepi.Proofs.A.r",
                theorem(Some(&["sorryAx"]), Status::Rejected),
            ),
            ("Krepi.Proofs.B.t", theorem(None, Status::Scoped)),
        ];
        let mut job = qualification(&fixture);
        job.base = Some(base::Record {
            theorems: BTreeMap::from(theorems.map(|(name, t)| (name.to_string(), t))),
            ..base::Record::default()
        });
        let merged = merge_in(&fixture, &[write(&fixture, "q", &job)]);
        verified(&merged);
        let axioms = |axioms: &[&str]| Vec::from_iter(axioms.iter().map(|a| a.to_string()));
        let expected = [
            ("Krepi.Proofs.A.h", axioms(&[])),
            ("Krepi.Proofs.A.r", axioms(&["sorryAx"])),
            ("Krepi.Proofs.A.s", axioms(&["propext", "Quot.sound"])),
        ];
        let expected = BTreeMap::from(expected.map(|(name, axioms)| (name.to_string(), axioms)));
        assert_eq!(merged.axioms, expected);
        // Without a base round, the record has none.
        let merged = merge_in(&fixture, &[write(&fixture, "q", &qualification(&fixture))]);
        assert_eq!(merged.axioms, BTreeMap::new());
    }
}
