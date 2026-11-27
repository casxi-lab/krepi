//! The parts of the proof gate and their merge, as "Shards and merge" in
//! `docs/formal-verification.md` describes: beside the qualification job,
//! every lane of the base round and every formal target is a part of its
//! own, whose registered budget is at most the shard limit, the wall-clock
//! limit of the gate less the time of the merge; and
//! `cargo xtask formal merge` combines the receipts of these parts of one
//! commit into the conclusions of the gate and its hard gates, with waivers.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use clap::{ArgMatches, value_parser};

use super::Layout;
use super::outcome::{self, Class, Site, Status, word};
use super::paths::{self, Git};
use super::receipt::{self, Checks, Job, Merge, Part, Receipt, SCHEMA};
use super::registry::{self, State, Target};
use super::run::{self, Gate, Phase};
use super::toolchain::sha256;
use super::{base, comparator, guard, lean, mutants, qualify, waiver};

/// The wall-clock limit of the gate, from the start of its first job to the
/// end of its merge.
pub const WALL_CLOCK: Duration = Duration::from_secs(3_600);

/// The time of the merge, from the start of its job to the end of
/// `cargo xtask formal merge`.
pub const MERGE: Duration = Duration::from_secs(300);

/// The longest that a shard may take: the wall-clock limit less the merge.
pub const SHARD_LIMIT: Duration = Duration::from_secs(WALL_CLOCK.as_secs() - MERGE.as_secs());

/// The workers of a run that build the mutants of a target side by side.
pub const WORKERS: usize = 2;

/// The margin of the run of a lane, and of the part of a target, beyond its
/// budget, for its start and its closing steps.
pub const SHARD_MARGIN: Duration = Duration::from_secs(300);

/// The margin of the run of a lane beyond its budget, for the extraction of
/// its targets.
pub const EXTRACTION_MARGIN: Duration = Duration::from_secs(600);

/// The seconds above which a merge flags its synthetic wall clock or a job.
pub const FLAG: Duration = Duration::from_secs(WALL_CLOCK.as_secs() * 4 / 5);

/// The cgroup memory peak above which a merge flags a part: 80% of 16,715,923,456 B.
pub const MEMORY: u64 = 13_372_738_764;

/// The directory of the merge record and its summary, below the root.
pub const DIR: &str = "artifacts/formal/merge";

/// The variable with the Unix time in seconds at which the merge job started.
pub const STARTED: &str = "KREPI_FORMAL_MERGE_STARTED";

/// The jobs of the gate in the workflow `formal`, by their keys, each with
/// the keys of the jobs that it needs besides `formal limits`: the
/// qualification job, the job of each lane and that of each part of a target.
pub const NEEDS: [(&str, &[&str]); 3] = [("gate", &[]), ("lane", &[]), ("shard", &[])];

/// The parts of the formal targets of `targets`, by name, each with the
/// registered budget of its target: every formal target has one part,
/// `target/<name>/1`.
pub fn shards(targets: &[Target]) -> BTreeMap<String, u64> {
    let mut shards = BTreeMap::new();
    for target in targets.iter().filter(|t| t.state == State::Formal) {
        let budget: &mut u64 = shards.entry(part(&target.name)).or_default();
        *budget = budget.saturating_add(target.budget);
    }
    shards
}

/// The problems of the parts of `targets`: a part whose registered budget,
/// whatever its workers, is more than the shard limit.
pub fn budget_problems(targets: &[Target]) -> Vec<String> {
    let limit = SHARD_LIMIT.as_secs();
    let over = shards(targets).into_iter().filter_map(|(shard, budget)| {
        (budget > limit).then(|| {
            format!(
                "part {shard}: its registered budget of {budget} s is more than the shard limit of {limit} s"
            )
        })
    });
    over.collect()
}

/// The part of the target `name`, the one part of a target.
pub fn part(name: &str) -> String {
    format!("{}/1", run::target_unit(name))
}

/// The target of the part or unit `name`, `target/<target>` and what may
/// follow it, or none for another part or unit.
pub fn target(name: &str) -> Option<&str> {
    let rest = name.strip_prefix(run::target_unit("").as_str())?;
    Some(rest.split_once('/').map_or(rest, |(target, _)| target))
}

/// The lane of the part `shard`, `lane/<lane>`, or none for another part.
pub fn lane(shard: &str) -> Option<&str> {
    shard.strip_prefix("lane/")
}

/// The budget of a run of `shard` in place of the gate's: the gate's for the
/// qualification job, the shard and extraction margins for a lane, which its
/// registered budget grows, and the shard margin for the part of a target,
/// which the budget of its target grows.
pub fn budget(shard: &str) -> Duration {
    match (lane(shard), target(shard)) {
        (Some(_), _) => SHARD_MARGIN + EXTRACTION_MARGIN,
        (_, Some(_)) => SHARD_MARGIN,
        _ => run::GATE_BUDGET,
    }
}

/// The part that `--shard` names: `qualification`, `lane/<name>` or
/// `target/<name>/1`.
pub fn shard(name: &str) -> Result<String, String> {
    let named = |rest: Option<&str>| rest.is_some_and(|r| !r.is_empty() && !r.contains('/'));
    let part = name
        .strip_suffix("/1")
        .and_then(|part| part.strip_prefix("target/"));
    let valid = name == qualify::PHASE || named(lane(name)) || named(part);
    let invalid = format!(
        "`{name}` is not {}, lane/<name> or target/<name>/1",
        qualify::PHASE
    );
    valid.then(|| name.to_string()).ok_or(invalid)
}

/// The job of the workflow `formal` that runs the part `shard`, and its key
/// in [`NEEDS`].
pub fn job_of(shard: &str) -> (String, &'static str) {
    match (
        lane(shard),
        shard.strip_prefix(run::target_unit("").as_str()),
    ) {
        (Some(lane), _) => (format!("formal lane {lane}"), "lane"),
        (_, Some(part)) => (format!("formal shard {part}"), "shard"),
        _ => ("formal run".to_string(), "gate"),
    }
}

/// The jobs of a merge, each with its key in [`NEEDS`] and its seconds.
pub type Jobs<'a> = BTreeMap<String, (&'a str, f64)>;

/// The longest chain of `jobs` that `needs` gives, a job following each job
/// of a key that its key needs: its jobs, the first first, and the sum of
/// their seconds.
pub fn chain(jobs: &Jobs, needs: &[(&str, &[&str])]) -> (Vec<String>, f64) {
    let mut longest = BTreeMap::<&String, (f64, Vec<String>)>::new();
    for _ in 0..=jobs.len() {
        for (name, (key, seconds)) in jobs {
            let wants = |k: &str| {
                needs
                    .iter()
                    .any(|(of, keys)| of == key && keys.contains(&k))
            };
            let before = jobs.iter().filter(|(_, (k, _))| wants(k));
            let before = before.filter_map(|(job, _)| longest.get(job));
            let before = before.max_by(|a, b| a.0.total_cmp(&b.0));
            let (most, mut path) = before.cloned().unwrap_or_default();
            path.push(name.clone());
            longest.insert(name, (most + seconds, path));
        }
    }
    let most = longest.into_values().max_by(|a, b| a.0.total_cmp(&b.0));
    let (seconds, path) = most.unwrap_or_default();
    (path, seconds)
}

/// `seconds` rounded to milliseconds.
fn rounded(seconds: f64) -> f64 {
    ((seconds * 1_000.0).round() / 1_000.0).min(f64::MAX)
}

/// The hand-written module files that the stages of the part of a target and
/// of a lane hold: [`base::handwritten`] of the Lean files of the Lake
/// project at the snapshot commit, which it lists as
/// [`guard::statement_hash`] does for the base round, without the source
/// rules, which the qualification job checks; and the files that it listed.
pub fn handwritten(gate: &mut Gate) -> Result<(Vec<String>, paths::Files), String> {
    let (layout, source) = (*gate.layout(), gate.source());
    let commit = gate.receipt.commit.clone().unwrap_or_default();
    let args = ["ls-tree", "-r", "-z", &commit, "--", layout.project];
    let mut tracked = paths::tree_records(&gate.git(&args, None)?)?;
    tracked.retain(|path, _| !guard::in_calibration(path, &layout));
    Ok((
        base::handwritten(&layout, &source, &tracked, &[])?.0,
        tracked,
    ))
}

/// The receipts of `kept` with a base round: of the qualification job and of the lanes.
fn rounds<'a>(kept: &'a [&'a Receipt]) -> impl Iterator<Item = &'a Receipt> {
    let round = |shard: &str| shard == qualify::PHASE || lane(shard).is_some();
    (kept.iter().copied()).filter(move |receipt| receipt.shard.as_deref().is_some_and(round))
}

/// The commands of `receipt` at `site` with the argument `arg`.
fn commands<'a>(receipt: &'a Receipt, site: Site, arg: &str) -> Vec<&'a receipt::Command> {
    let of = |c: &&receipt::Command| c.site == site && c.argv.iter().any(|a| a == arg);
    Vec::from_iter(receipt.commands.iter().filter(of))
}

/// Whether each receipt of `kept` with a base round has an audit.
pub fn audited(kept: &[&Receipt]) -> bool {
    rounds(kept).all(|receipt| !commands(receipt, Site::AxiomAudit, lean::AUDIT).is_empty())
}

/// Whether each receipt of `kept` with a base round has exactly one replay
/// with `leanchecker`, `--fresh` of its root module `root`, which passed.
pub fn replayed(kept: &[&Receipt], root: &str) -> bool {
    let fresh = ["--fresh", root].map(str::to_string);
    let fine = |c: &&receipt::Command| c.argv.ends_with(&fresh) && c.class == Class::Passed;
    let one = |r| matches!(commands(r, Site::Leanchecker, "leanchecker")[..], [c] if fine(&c));
    rounds(kept).all(one)
}

/// Each unit that the checkout at `root` registers in `layout`, with its
/// phase and the part that concludes it: of the qualification and the base
/// round of the qualification job, of the base round and the comparator of
/// each lane, and of the part of each formal target.
pub fn owned(root: &Path, layout: &Layout) -> Vec<(String, String, String)> {
    let [_, finish] = run::target_phases(root, layout, &BTreeSet::new(), None, None);
    let of = |phase: Phase, part: String| {
        let name = phase.name;
        (phase.units.into_iter()).map(move |unit| (unit, name.clone(), part.clone()))
    };
    let lanes = base::lanes(root, layout).unwrap_or_default();
    let q = qualify::PHASE.to_string();
    let mut units = Vec::from_iter(of(qualify::phase(root, layout), q.clone()));
    units.extend(of(base::phase(root, layout, Some(qualify::PHASE)), q));
    for part in lanes.iter().map(|lane| format!("lane/{}", lane.name)) {
        units.extend(of(base::phase(root, layout, Some(&part)), part));
    }
    let compared = comparator::units(root, layout).unwrap_or_default();
    let compared = compared.into_iter().map(|(unit, (part, _))| (unit, part));
    units.extend(compared.map(|(unit, part)| (unit, comparator::PHASE.to_string(), part)));
    for unit in finish.units {
        let of_target = target(mutants::owner(&unit)).map(part).unwrap_or_default();
        units.push((unit, finish.name.clone(), of_target));
    }
    units
}

/// Each unit that the checkout at `root` registers in `layout`, with its
/// phase, as [`owned`] gives them.
pub fn registered(root: &Path, layout: &Layout) -> Vec<(String, String)> {
    let owned = owned(root, layout).into_iter();
    Vec::from_iter(owned.map(|(unit, phase, _)| (unit, phase)))
}
/// The command line of `cargo xtask formal merge`, with `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let receipts = clap::arg!(<RECEIPT>... "A receipt of the qualification job, a lane or a part");
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
                part.job = receipt.shard.as_deref().map(|shard| job_of(shard).0);
                (part.complete, part.seconds) = (receipt.complete, receipt.seconds);
                let trigger = &receipt.trigger;
                (part.run_id, part.attempt) = (trigger.run_id.clone(), trigger.attempt.clone());
                let peak = receipt.resources.cgroup_memory_peak;
                (part.cgroup_memory_peak, part.over_memory) = (peak, peak.map(|p| p > MEMORY));
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
    let lanes = base::lanes(root, layout).map_err(|problem| problems.push(problem));
    let owned = owned(root, layout);
    let registered = owned
        .iter()
        .map(|(unit, phase, _)| (unit.clone(), phase.clone()));
    let registered = Vec::from_iter(registered);
    let (units, unaccounted) = outcome::account(&registered, concluded.collect(), None);
    problems.extend(unaccounted);
    // Each unit has its conclusion from the receipt of its part.
    let parts = BTreeMap::from_iter(owned.iter().map(|(unit, _, part)| (unit, part)));
    for (index, receipt) in receipts
        .iter()
        .filter(|(_, receipt)| receipt.shard.is_some())
    {
        let other = |(_, part): &(&String, &String)| receipt.shard.as_ref() != Some(*part);
        let of = (receipt.units.keys()).filter_map(|unit| Some((unit, *parts.get(unit)?)));
        let shown = &merged.parts[*index].receipt;
        let found = of
            .filter(other)
            .map(|(unit, part)| format!("{unit} of {part}"));
        problems.extend(found.map(|unit| format!("{shown} concludes {unit}")));
    }
    // One receipt of the qualification job, of each lane and of each part of a formal target.
    let mut expected = BTreeSet::from_iter(shards(&targets).into_keys());
    expected.extend((lanes.iter().flatten()).map(|lane| format!("lane/{}", lane.name)));
    expected.insert(qualify::PHASE.to_string());
    for part in &expected {
        let count = given.remove(part.as_str()).unwrap_or(0);
        let problem = format!("{count} receipts are of the part {part}, where one is expected");
        problems.extend((count != 1).then_some(problem));
    }
    problems.extend(
        given
            .keys()
            .map(|part| format!("{part} is not a part of the checkout")),
    );
    // The waivers of the checkout that hold on the UTC date of the clock.
    let waivers = waiver::read(root, layout, &targets).map_err(|problem| problems.push(problem));
    let date = waiver::today(SystemTime::now()).map_err(|error| problems.push(error));
    let (waivers, date) = (waivers.unwrap_or_default(), date.ok());
    let waived = (date.as_deref()).map_or_else(BTreeSet::new, |d| waiver::holding(&waivers, d));
    let kept = Vec::from_iter(receipts.iter().map(|(_, receipt)| receipt));
    merged.checks = check(&kept, &targets, &waived, &mut problems);
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
    // The jobs, each with the seconds of its receipts, and the synthetic wall
    // clock: the longest chain of jobs that `needs` gives and the merge to its end.
    let (flag, mut jobs) = (FLAG.as_secs_f64(), BTreeMap::new());
    for part in merged.parts.iter().filter(|part| !part.superseded) {
        let Some((name, key)) = part.shard.as_deref().map(job_of) else {
            continue;
        };
        let (_, seconds, peak) = jobs.entry(name).or_insert((key, 0.0, None));
        let more = (*peak).max(part.cgroup_memory_peak);
        (*seconds, *peak) = (*seconds + part.seconds, more);
    }
    let keyed = jobs
        .iter()
        .map(|(name, (key, seconds, _))| (name.clone(), (*key, *seconds)));
    let (chain, seconds) = chain(&Jobs::from_iter(keyed), &NEEDS);
    (merged.chain, merged.chain_seconds) = (chain, rounded(seconds));
    for (name, (_, seconds, peak)) in jobs {
        let mut job = Job::default();
        (job.seconds, job.over_seconds) = (rounded(seconds), seconds > flag);
        (job.cgroup_memory_peak, job.over_memory) = (peak, peak.map(|peak| peak > MEMORY));
        merged.jobs.insert(name, job);
    }
    for part in merged.parts.iter_mut().filter(|part| !part.superseded) {
        let job = part.job.as_ref().and_then(|job| merged.jobs.get(job));
        part.over_seconds = job.is_some_and(|job| job.over_seconds);
    }
    merged.merge_from = ["command", "job"][usize::from(job.is_some())].to_string();
    merged.merge_seconds = receipt::seconds(job.unwrap_or_default() + start.elapsed());
    merged.wall_clock_seconds = rounded(merged.chain_seconds + merged.merge_seconds);
    merged.over_80_percent = merged.wall_clock_seconds > flag;
    merged
}

/// The checks of the hand-written modules of the `kept` receipts, with the
/// registry's `targets` and those `waived`, each failure a problem of
/// `problems`: coverage, the modules that the lanes and the qualification job
/// hold do not overlap and are those that the job lists; names, no public
/// constant of theirs is in two of them but a theorem of one type and
/// universe parameters, which Lean imports from both; waivers, each lane
/// leaves out what the closure of the job gives of its modules; extraction,
/// the lane of each formal target outside the waivers extracted it. They fail
/// without the receipt of the job, whose absence is a problem already.
fn check(
    kept: &[&Receipt],
    targets: &[Target],
    waived: &BTreeSet<String>,
    problems: &mut Vec<String>,
) -> Checks {
    let job = kept
        .iter()
        .find(|r| r.shard.as_deref() == Some(qualify::PHASE));
    let lists = job.and_then(|job| Some((job.handwritten.as_ref()?, job.left_out.as_ref()?)));
    let Some((listed, closure)) = lists else {
        let none = "the receipt of the qualification job lists no hand-written modules";
        problems.extend(job.map(|_| none.to_string()));
        return Checks::default();
    };
    let held = kept
        .iter()
        .filter_map(|r| Some((r.shard.as_deref()?, r.lane.as_ref()?, *r)));
    let (held, mut found) = (Vec::from_iter(held), <[Vec<String>; 4]>::default());
    let (mut holders, mut declared) = (BTreeMap::<_, Vec<_>>::new(), BTreeMap::<_, Vec<_>>::new());
    for (part, lane, _) in &held {
        (lane.modules.iter()).for_each(|module| holders.entry(module).or_default().push(*part));
        // A constant is `<name> <kind> <fingerprint>`.
        for entry in &lane.constants {
            let at = (entry.rmatch_indices(' ').nth(1)).map_or(entry.len(), |(at, _)| at);
            (declared.entry(&entry[..at]).or_default()).push((*part, entry[at..].trim_start()));
        }
    }
    for (module, parts) in &holders {
        let (parts, of) = (
            parts.join(", "),
            format!("the hand-written module {module}"),
        );
        found[0].extend((parts.contains(',')).then(|| format!("{of} is held by {parts}")));
        let unlisted = format!("{of} of {parts} is not in the list of the qualification job");
        found[0].extend((!listed.contains_key(*module)).then_some(unlisted));
    }
    let unheld = listed.keys().filter(|module| !holders.contains_key(module));
    found[0].extend(unheld.map(|m| format!("the hand-written module {m} is held by no part")));
    for (name, parts) in declared.iter().filter(|(_, parts)| parts.len() > 1) {
        let sign = parts[0].1;
        let same = sign.starts_with("theorem ") && (parts.iter()).all(|(_, s)| *s == sign);
        let parts = Vec::from_iter(parts.iter().map(|(part, _)| *part)).join(", ");
        let conflict = format!("the public constant {name} is declared by {parts}");
        found[1].extend((!same).then_some(conflict));
    }
    let shown = |left: &BTreeMap<String, String>| Vec::from_iter(left.keys().cloned()).join(", ");
    for (part, lane, _) in held.iter().filter(|(part, ..)| lane(part).is_some()) {
        let closure = closure
            .iter()
            .filter(|(module, _)| lane.modules.contains(module));
        let closure = BTreeMap::from_iter(closure.map(|(m, t)| (m.clone(), t.clone())));
        let (left, wanted) = (shown(&lane.left_out), shown(&closure));
        let other = format!("{part} leaves out [{left}], where the waivers leave out [{wanted}]");
        found[2].extend((lane.left_out != closure).then_some(other));
    }
    let formal = (targets.iter()).filter(|t| t.state == State::Formal && !waived.contains(&t.name));
    for target in formal {
        let of = |lane: &receipt::Lane| target.module.iter().any(|m| lane.components.contains(m));
        let by = (held.iter()).find(|(part, lane, _)| self::lane(part).is_some() && of(lane));
        let extracted = by.is_some_and(|(.., r)| r.proof_targets.contains_key(&target.name));
        let missed = format!(
            "the formal target {} is not extracted by its lane",
            target.name
        );
        found[3].extend((!extracted).then_some(missed));
    }
    let [coverage, names, waivers, extraction] = found.each_ref().map(Vec::is_empty);
    problems.extend(found.into_iter().flatten());
    let mut checks = Checks::default();
    (checks.coverage, checks.names, checks.waivers) = (coverage, names, waivers);
    checks.extraction = extraction;
    checks
}

/// The summary of `merged`: its conclusion, wall clock and trigger, its hard
/// gates, that it passes when it is not `VERIFIED`, and each waiver, flag
/// and problem.
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
    for (name, job) in merged.jobs.iter().filter(|(_, job)| job.over_seconds) {
        lines.push(format!(
            "- job {}: {} s, above {flag} s",
            name.escape_debug(),
            job.seconds
        ));
    }
    for part in merged.parts.iter().filter(|part| !part.superseded) {
        let (shard, peak) = (text(&part.shard), part.cgroup_memory_peak);
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
    use crate::formal::run::tests::register;
    use crate::formal::waiver::tests::waive;
    use crate::formal::{lanes, registry};

    pub(crate) const LAYOUT: &Layout = &Layout::PRODUCTION;

    /// The image that the receipts of the tests name, but where a test
    /// changes it.
    pub(crate) fn image(digit: char) -> String {
        let digest = digit.to_string().repeat(64);
        format!("ghcr.io/casxi-lab/krepi-formal@sha256:{digest}")
    }

    /// A checkout with one qualification case, no proved statement, the
    /// registry of `targets`, a JSON list, in which a target without a module
    /// has the module of its name in capitals, and the one lane `x` with the
    /// module of each target, committed.
    pub(crate) fn checkout(label: &str, targets: &str) -> Fixture {
        let fixture = fixture::qualification(label, &serde_json::json!([fixture::arithmetic()]));
        let hash = "0".repeat(40);
        let statements = format!("{{\"schema\": 1, \"hash\": \"{hash}\", \"statements\": []}}\n");
        fixture.write("verification/statements.json", &statements);
        let mut targets: serde_json::Value = serde_json::from_str(targets).expect("a list");
        for target in targets.as_array_mut().expect("a list") {
            let module = target["name"].as_str().unwrap_or_default().to_uppercase();
            target
                .as_object_mut()
                .expect("a target")
                .entry("module")
                .or_insert(module.into());
        }
        let modules = targets
            .as_array()
            .expect("a list")
            .iter()
            .map(|t| t["module"].clone());
        let lane = serde_json::json!({"name": "x", "components": Vec::from_iter(modules)});
        let lanes = serde_json::json!({"schema": 1, "lanes": [lane]});
        fixture.write(LAYOUT.lanes, &format!("{lanes:#}\n"));
        register(&fixture, &targets.to_string());
        fixture
    }

    /// The units of the part `part` that the checkout at `root` registers.
    pub(crate) fn units_of_part(root: &Path, part: &str) -> Vec<String> {
        let owned = owned(root, LAYOUT)
            .into_iter()
            .filter(|(_, _, of)| of == part);
        Vec::from_iter(owned.map(|(unit, ..)| unit))
    }

    /// The units of the qualification job of the checkout at `root`.
    fn qualification_units(root: &Path) -> Vec<String> {
        units_of_part(root, qualify::PHASE)
    }

    /// The hand-written modules of the checkout at `root`, with their homes.
    fn homes_of(root: &Path) -> lanes::Homes {
        let below = root.join(LAYOUT.project);
        let files = walkdir::WalkDir::new(below.join(LAYOUT.namespace))
            .into_iter()
            .flatten();
        let lean = files.filter(|entry| entry.path().extension().is_some_and(|e| e == "lean"));
        let module = |path: &Path| {
            let file = path.strip_prefix(&below).expect("below the project");
            file.with_extension("").to_string_lossy().replace('/', ".")
        };
        base::homes(LAYOUT, lean.map(|entry| module(entry.path())))
    }

    /// The hand-written modules of the checkout at `root` that `part` holds.
    fn held_by(root: &Path, part: &str) -> Vec<String> {
        let lanes = base::lanes(root, LAYOUT).unwrap_or_default();
        let homes = homes_of(root);
        let held = |m: &&String| base::part_of(&lanes, m, homes.get(*m)).as_deref() == Some(part);
        Vec::from_iter(homes.keys().filter(held).cloned())
    }

    /// The commit or tree `rev` of `fixture`.
    fn rev(fixture: &Fixture, rev: &str) -> String {
        fixture.git(&["rev-parse", rev]).trim().to_string()
    }

    /// A complete `VERIFIED` receipt of `shard` at the head of `fixture`,
    /// of 600 s and the image `image('a')`, that started from the gate
    /// inputs of the head and concludes each of `units`.
    /// Each of `units`, `VERIFIED` without a reason.
    fn verified_units(units: &[String]) -> BTreeMap<String, Unit> {
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
        BTreeMap::from_iter(units.iter().map(unit))
    }

    pub(crate) fn receipt(fixture: &Fixture, shard: &str, units: &[String]) -> Receipt {
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
            units: verified_units(units),
            ..Receipt::default()
        }
    }

    /// The command of a tool, `argv`, of `unit` at `site`, which concluded `class`.
    pub(crate) fn tool(unit: &str, site: Site, argv: &str, class: Class) -> Command {
        Command {
            sequence: 1,
            started: 0.0,
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

    /// The audit of the base round of the qualification job, concluded `class`.
    pub(crate) fn audit(class: Class) -> Command {
        audit_of("base", class)
    }

    /// The audit of the base round of `unit`, concluded `class`.
    pub(crate) fn audit_of(unit: &str, class: Class) -> Command {
        tool(unit, Site::AxiomAudit, "lake env lean Audit.lean", class)
    }

    /// The replay of the base round of the qualification job with
    /// `leanchecker --fresh`, concluded `class`.
    pub(crate) fn replay(class: Class) -> Command {
        replay_of("base", class)
    }

    /// The replay of the base round of `unit` with `leanchecker --fresh`,
    /// concluded `class`.
    pub(crate) fn replay_of(unit: &str, class: Class) -> Command {
        let argv = "lake env leanchecker --fresh Krepi";
        tool(unit, Site::Leanchecker, argv, class)
    }

    /// The formal targets of the registry of `fixture`, those of the waivers
    /// that hold today, and what these leave out of the base rounds, with none
    /// when the registry cannot be read.
    fn waived(fixture: &Fixture) -> (Vec<Target>, BTreeSet<String>, waiver::LeftOut) {
        let text = fs::read_to_string(fixture.root().join(LAYOUT.registry));
        let parsed = text.ok().and_then(|text| registry::parse(&text).ok());
        let targets = parsed.map(|registry| registry.targets).unwrap_or_default();
        let waivers = waiver::read(fixture.root(), LAYOUT, &targets).unwrap_or_default();
        let today = waiver::today(SystemTime::now()).expect("the date of today");
        let waived = waiver::holding(&waivers, &today);
        let left = waiver::left_out(LAYOUT, &targets, &waived);
        let formal = targets.into_iter().filter(|t| t.state == State::Formal);
        (formal.collect(), waived, left)
    }

    /// The receipt of the qualification job of `fixture` at its head, whose
    /// base round audited and replayed its stage, which lists the hand-written
    /// modules of the checkout with their homes and what the waivers that hold
    /// today leave out, and holds the modules of the qualification cases.
    pub(crate) fn qualification(fixture: &Fixture) -> Receipt {
        let units = qualification_units(fixture.root());
        let mut job = receipt(fixture, qualify::PHASE, &units);
        job.commands = vec![audit(Class::Passed), replay(Class::Passed)];
        let home = |home: &lanes::Home| match home {
            lanes::Home::Component(component) => component.clone(),
            other => format!("{other:?}").to_lowercase(),
        };
        let homes = homes_of(fixture.root()).into_iter();
        job.handwritten = Some(homes.map(|(module, h)| (module, home(&h))).collect());
        job.left_out = Some(waived(fixture).2);
        let modules = held_by(fixture.root(), qualify::PHASE);
        let name = qualify::PHASE.to_string();
        job.lane = Some(receipt::Lane {
            name,
            modules,
            ..receipt::Lane::default()
        });
        job
    }

    /// The receipt of the lane `lane` of `fixture` beside the receipt `job` of
    /// the qualification job, as its comparator run writes it: of the commit,
    /// tree, gate inputs, trigger and image of `job`, of no seconds, with the
    /// units of the lane that the checkout registers, `VERIFIED`, an audit and
    /// a replay of its root, its modules and the formal targets of its
    /// components outside the waivers that hold today, which it extracted.
    pub(crate) fn lane_of(fixture: &Fixture, job: &Receipt, lane: &lanes::Lane) -> Receipt {
        let part = format!("lane/{}", lane.name);
        let mut receipt = job.clone();
        (receipt.shard, receipt.seconds) = (Some(part.clone()), 0.0);
        (receipt.handwritten, receipt.left_out) = (None, None);
        receipt.units = verified_units(&units_of_part(fixture.root(), &part));
        let round = base::unit_of(Some(&part));
        receipt.commands = vec![
            audit_of(&round, Class::Passed),
            replay_of(&round, Class::Passed),
        ];
        let (formal, waived, left) = waived(fixture);
        let modules = held_by(fixture.root(), &part);
        let left_out = left
            .into_iter()
            .filter(|(module, _)| modules.contains(module));
        let left_out = left_out.collect();
        let ours = |t: &Target| t.module.iter().any(|m| lane.components.contains(m));
        let extracted = formal
            .into_iter()
            .filter(|t| ours(t) && !waived.contains(&t.name));
        let targets = extracted.map(|t| (t.name, receipt::Role::Formal));
        let (name, components) = (lane.name.clone(), lane.components.clone());
        let held = receipt::Lane {
            name,
            components,
            modules,
            left_out,
            targets: targets.collect(),
            ..receipt::Lane::default()
        };
        let extracted = held
            .targets
            .keys()
            .map(|name| (name.clone(), receipt::Target::default()));
        (receipt.proof_targets, receipt.lane) = (extracted.collect(), Some(held));
        receipt
    }

    /// Writes `receipt` below the ignored `artifacts/parts/` of `fixture`.
    pub(crate) fn write(fixture: &Fixture, name: &str, receipt: &Receipt) -> PathBuf {
        let path = format!("artifacts/parts/{name}.json");
        fixture.write(&path, &receipt::render(receipt));
        fixture.root().join(path)
    }

    /// The merge of the receipts at `paths` [`with_lanes`] in `fixture`, with
    /// 60 s of its job before the command.
    pub(crate) fn merge_in(fixture: &Fixture, paths: &[PathBuf]) -> Merge {
        let paths = with_lanes(fixture, paths);
        merge(
            fixture.root(),
            LAYOUT,
            &paths,
            Some(Duration::from_secs(60)),
        )
    }

    /// `paths`, followed, for each lane of the checkout that they hold no
    /// receipt of, by the receipt of the lane ([`lane_of`]) beside each
    /// receipt of the qualification job among them, named after it.
    pub(crate) fn with_lanes(fixture: &Fixture, paths: &[PathBuf]) -> Vec<PathBuf> {
        let read = |path: &PathBuf| serde_json::from_slice::<Receipt>(&fs::read(path).ok()?).ok();
        let shard = |path: &PathBuf| read(path).and_then(|receipt| receipt.shard);
        let shards = BTreeSet::from_iter(paths.iter().filter_map(shard));
        let lanes = base::lanes(fixture.root(), LAYOUT).unwrap_or_default();
        let missing = lanes
            .iter()
            .filter(|l| !shards.contains(&format!("lane/{}", l.name)));
        let missing = Vec::from_iter(missing);
        let mut all = paths.to_vec();
        let jobs = paths
            .iter()
            .filter(|path| shard(path).as_deref() == Some(qualify::PHASE));
        for path in jobs {
            let job = read(path).expect("a receipt");
            let name = path.file_stem().expect("a file name").to_string_lossy();
            for lane in &missing {
                let receipt = lane_of(fixture, &job, lane);
                all.push(write(
                    fixture,
                    &format!("{name}-lane-{}", lane.name),
                    &receipt,
                ));
            }
        }
        all
    }

    /// Holds the modules of the statements of `fixture` in its lane `x`,
    /// committed.
    fn hold(fixture: &Fixture) {
        let text = fs::read_to_string(fixture.root().join(LAYOUT.statements)).expect("statements");
        let statements: serde_json::Value = serde_json::from_str(&text).expect("JSON");
        let all = statements["statements"].as_array().into_iter().flatten();
        let modules = BTreeSet::from_iter(all.filter_map(|s| s["module"].as_str()));
        let text = fs::read_to_string(fixture.root().join(LAYOUT.lanes)).expect("the lanes");
        let mut lanes: serde_json::Value = serde_json::from_str(&text).expect("JSON");
        lanes["lanes"][0]["modules"] = serde_json::json!(modules);
        fixture.write(LAYOUT.lanes, &format!("{lanes:#}\n"));
        fixture.commit_all();
    }

    /// The receipt of the lane `x` of `fixture` beside the receipt `job`.
    fn lane_x(fixture: &Fixture, job: &Receipt) -> Receipt {
        let lanes = base::lanes(fixture.root(), LAYOUT).expect("the lanes");
        lane_of(fixture, job, &lanes[0])
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

    /// The path of the receipt of the lane `x` that [`with_lanes`] writes
    /// beside the receipt `name` of the qualification job.
    fn lane_beside(fixture: &Fixture, name: &str) -> PathBuf {
        fixture
            .root()
            .join(format!("artifacts/parts/{name}-lane-x.json"))
    }

    #[test]
    fn each_proved_statement_is_in_the_comparator_units_of_the_lane_of_its_module_alone() {
        let target = r#"[{"name": "a", "module": "A", "proof_modules": ["Krepi.Proofs.A"]}]"#;
        let fixture = checkout("merge-comparator", target);
        let statements = serde_json::json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            {"name": "Krepi.Statements.S", "theorem": "Krepi.Proofs.A.s", "module": "Krepi.Proofs.A", "state": "proved"},
            {"name": "Krepi.Statements.R", "theorem": "Krepi.Proofs.R.r", "module": "Krepi.Proofs.R", "state": "proved"},
            {"name": "Krepi.Statements.P", "theorem": "Krepi.Proofs.A.p", "module": "Krepi.Proofs.A", "state": "planned"},
        ]});
        fixture.write(LAYOUT.statements, &statements.to_string());
        hold(&fixture);
        // Its units are those of the proved statements of the formal target
        // that lists their module, and one for the others of the lane of
        // their modules, both concluded by that lane.
        let compared = |root: &Path| {
            let owned = owned(root, LAYOUT).into_iter();
            Vec::from_iter(owned.filter(|(_, phase, _)| phase == comparator::PHASE))
        };
        let unit = |name: &str, part: &str| {
            (
                name.to_string(),
                comparator::PHASE.to_string(),
                part.to_string(),
            )
        };
        let expected = [
            unit("comparator/a", "lane/x"),
            unit("comparator/lane/x", "lane/x"),
        ];
        assert_eq!(compared(fixture.root()), expected);
        // The receipts of the head, the lane `x` as `edit` changes it, and
        // the receipts `more`.
        let merged = |edit: &dyn Fn(&mut Receipt), more: &[Receipt]| {
            let job = qualification(&fixture);
            let mut lane = lane_x(&fixture, &job);
            edit(&mut lane);
            let t = receipt(&fixture, "target/a/1", &units_of("a"));
            let parts = [("q", job), ("t", t), ("x", lane)].into_iter();
            let mut paths = Vec::from_iter(parts.map(|(name, part)| write(&fixture, name, &part)));
            let more = more.iter().enumerate();
            paths.extend(more.map(|(at, part)| write(&fixture, &format!("y{at}"), part)));
            merge(fixture.root(), LAYOUT, &paths, None)
        };
        verified(&merged(&|_| {}, &[]));
        // A proved statement in the comparator units of no lane: the receipt
        // of the lane misses its unit, or its module is in no lane, which
        // leaves it in `comparator`, of no part.
        let missing = |lane: &mut Receipt| drop(lane.units.remove("comparator/lane/x"));
        let none = |unit: &str| format!("the unit {unit} has no conclusion");
        no_conclusion(&merged(&missing, &[]), &[none("comparator/lane/x")]);
        let text = fs::read_to_string(fixture.root().join(LAYOUT.lanes)).expect("the lanes");
        let held = text.replace("\"Krepi.Proofs.R\"", "\"Krepi.Proofs.Other\"");
        fixture.write(LAYOUT.lanes, &held);
        fixture.commit_all();
        assert_eq!(compared(fixture.root())[0], unit("comparator", ""));
        no_conclusion(&merged(&|_| {}, &[]), &[none("comparator")]);
        fixture.write(LAYOUT.lanes, &text);
        fixture.commit_all();
        // A proved statement in the comparator units of two lanes: another
        // lane that concludes its unit gives it two conclusions, one of them
        // for another part.
        let lanes = text.replace(
            "\"lanes\": [",
            "\"lanes\": [{\"name\": \"y\", \"components\": []}, ",
        );
        fixture.write(LAYOUT.lanes, &lanes);
        fixture.commit_all();
        let job = qualification(&fixture);
        let both = base::lanes(fixture.root(), LAYOUT).expect("the lanes");
        let mut other = lane_of(&fixture, &job, &both[0]);
        assert_eq!(other.shard.as_deref(), Some("lane/y"));
        other
            .units
            .extend(verified_units(&["comparator/lane/x".to_string()]));
        let shown = fixture.root().join("artifacts/parts/y0.json");
        let problems = [
            "the unit comparator/lane/x has 2 conclusions".to_string(),
            format!("{} concludes comparator/lane/x of lane/x", shown.display()),
        ];
        let lane_x =
            |lane: &mut Receipt| *lane = lane_of(&fixture, &qualification(&fixture), &both[1]);
        no_conclusion(&merged(&lane_x, &[other]), &problems);
        fixture.write(LAYOUT.lanes, &text);
        fixture.commit_all();
        // A receipt of a lane with a unit of the qualification cases.
        let case = |lane: &mut Receipt| {
            lane.units
                .extend(verified_units(&["qualification/arithmetic".to_string()]));
        };
        let x = fixture.root().join("artifacts/parts/x.json");
        let problems = [
            "the unit qualification/arithmetic has 2 conclusions".to_string(),
            format!(
                "{} concludes qualification/arithmetic of qualification",
                x.display()
            ),
        ];
        no_conclusion(&merged(&case, &[]), &problems);
    }

    #[test]
    fn the_receipts_of_the_parts_are_those_of_the_qualification_job_each_lane_and_each_part() {
        let fixture = checkout("merge-lanes", r#"[{"name": "a"}]"#);
        let job = qualification(&fixture);
        let (q, lane) = (write(&fixture, "q", &job), lane_x(&fixture, &job));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let x = write(&fixture, "x", &lane);
        verified(&merge(
            fixture.root(),
            LAYOUT,
            &[q.clone(), t.clone(), x.clone()],
            None,
        ));
        // Without the receipt of a lane.
        let merged = merge(fixture.root(), LAYOUT, &[q.clone(), t.clone()], None);
        let problems = [
            "the unit base/lane/x has no conclusion".to_string(),
            "0 receipts are of the part lane/x, where one is expected".to_string(),
            "the formal target a is not extracted by its lane".to_string(),
        ];
        no_conclusion(&merged, &problems);
        // With the receipt of a part that the checkout does not register.
        let mut other = lane.clone();
        (other.shard, other.units) = (Some("lane/y".to_string()), BTreeMap::new());
        let y = write(&fixture, "y", &other);
        let merged = merge(fixture.root(), LAYOUT, &[q, t, x, y], None);
        no_conclusion(
            &merged,
            &["lane/y is not a part of the checkout".to_string()],
        );
    }

    #[test]
    fn the_hand_written_modules_of_the_lanes_and_the_job_cover_its_list_once() {
        let fixture = checkout("merge-coverage", r#"[{"name": "a"}]"#);
        let job = qualification(&fixture);
        let (q, lane) = (write(&fixture, "q", &job), lane_x(&fixture, &job));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = |job: &Receipt, lane: &Receipt| {
            let (q, x) = (write(&fixture, "q", job), write(&fixture, "x", lane));
            merge(fixture.root(), LAYOUT, &[q, t.clone(), x], None)
        };
        let merged_lane = |lane: &Receipt| merged(&job, lane);
        let ok = merged_lane(&lane);
        verified(&ok);
        assert_eq!(
            ok.checks,
            Checks {
                coverage: true,
                names: true,
                waivers: true,
                extraction: true,
                seeds: None
            }
        );
        let module = |name: &str| name.to_string();
        let of = "the hand-written module";
        // A hand-written module in no lane: the list of the job has it.
        let mut listed = job.clone();
        listed
            .handwritten
            .as_mut()
            .expect("the list")
            .insert(module("Krepi.Proofs.A"), module("shared"));
        let merged_job = merged(&listed, &lane);
        no_conclusion(
            &merged_job,
            &[format!("{of} Krepi.Proofs.A is held by no part")],
        );
        assert!(!merged_job.checks.coverage);
        // A module in two lanes, here in the lane and the job.
        let mut twice = lane.clone();
        twice
            .lane
            .as_mut()
            .expect("the lane")
            .modules
            .push(module("Krepi.Qualification.Arithmetic"));
        let problem =
            format!("{of} Krepi.Qualification.Arithmetic is held by qualification, lane/x");
        no_conclusion(&merged_lane(&twice), &[problem]);
        // A lane that holds a module that the list does not have.
        let mut more = lane.clone();
        more.lane
            .as_mut()
            .expect("the lane")
            .modules
            .push(module("Krepi.Proofs.B"));
        let problem =
            format!("{of} Krepi.Proofs.B of lane/x is not in the list of the qualification job");
        no_conclusion(&merged_lane(&more), &[problem]);
        // A job without its list.
        let mut unlisted = job.clone();
        unlisted.handwritten = None;
        let problem = "the receipt of the qualification job lists no hand-written modules";
        no_conclusion(&merged(&unlisted, &lane), &[problem.to_string()]);
        let _ = q;
    }

    #[test]
    fn no_public_constant_is_declared_by_two_parts() {
        let fixture = checkout("merge-names", r#"[{"name": "a"}]"#);
        let mut job = qualification(&fixture);
        job.lane.as_mut().expect("the lane").constants =
            vec!["Krepi.Qualification.Arithmetic.f".to_string()];
        let mut lane = lane_x(&fixture, &job);
        let names = &mut lane.lane.as_mut().expect("the lane").constants;
        names.extend(["KrepiGen.A.Funs.f", "Krepi.Proofs.A.g"].map(String::from));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = |job: &Receipt, lane: &Receipt| {
            let (q, x) = (write(&fixture, "q", job), write(&fixture, "x", lane));
            merge(fixture.root(), LAYOUT, &[q, t.clone(), x], None)
        };
        verified(&merged(&job, &lane));
        // The same name in the lane and in the job.
        lane.lane
            .as_mut()
            .expect("the lane")
            .constants
            .push("Krepi.Qualification.Arithmetic.f".to_string());
        let conflict = merged(&job, &lane);
        let problem = "the public constant Krepi.Qualification.Arithmetic.f is declared by qualification, lane/x";
        no_conclusion(&conflict, &[problem.to_string()]);
        assert!(!conflict.checks.names && conflict.checks.coverage);
    }

    #[test]
    fn a_theorem_of_the_same_type_and_universe_parameters_in_two_parts_is_no_conflict() {
        // Lean imports a theorem that two modules declare when its type and
        // universe parameters are the same in both, as the equations that it
        // generates where a `match` is used are: the qualification job and
        // the lane of `Fdt` declare this pair on the proofs. It refuses any
        // other constant of one name, and so does the merge.
        let fixture = checkout("merge-same-theorem", r#"[{"name": "a"}, {"name": "b"}]"#);
        let lanes = serde_json::json!({"schema": 1, "lanes": [
            {"name": "x", "components": ["A"]}, {"name": "y", "components": ["B"]}]});
        fixture.write(LAYOUT.lanes, &format!("{lanes:#}\n"));
        fixture.commit_all();
        let job = qualification(&fixture);
        let lanes = base::lanes(fixture.root(), LAYOUT).expect("the lanes");
        let (x, y) = (
            lane_of(&fixture, &job, &lanes[0]),
            lane_of(&fixture, &job, &lanes[1]),
        );
        let held = [&job, &x, &y];
        let targets = ["a", "b"].map(|t| {
            let part = format!("target/{t}/1");
            write(&fixture, t, &receipt(&fixture, &part, &units_of(t)))
        });
        // The merge of the job and the two lanes, each with `constants`.
        let merged = |constants: [Vec<String>; 3]| {
            let names = ["q", "x", "y"];
            let written = std::array::from_fn::<_, 3, _>(|i| {
                let mut receipt = held[i].clone();
                receipt.lane.as_mut().expect("the lane").constants = constants[i].clone();
                write(&fixture, names[i], &receipt)
            });
            let ([q, x, y], [a, b]) = (written, targets.clone());
            merge(fixture.root(), LAYOUT, &[q, a, b, x, y], None)
        };
        let first = "Aeneas.Std.U64.checked_add_bv_spec.match_1.congr_eq_1";
        let second = "Aeneas.Std.U64.checked_add_bv_spec.match_1.congr_eq_2";
        let pair = vec![
            format!("{first} theorem 3405691582[]"),
            format!("{second} theorem 4027431614[]"),
        ];
        let none = Vec::new;
        for both in [
            [pair.clone(), pair.clone(), none()],
            [none(), pair.clone(), pair.clone()],
        ] {
            let ok = merged(both);
            verified(&ok);
            assert!(ok.checks.names);
        }
        // Another type, other universe parameters, or a constant that is not
        // a theorem in one part or in both.
        for (entries, parts) in [
            (
                [Some("theorem 1[]"), Some("theorem 2[]"), None],
                "qualification, lane/x",
            ),
            (
                [Some("theorem 1[u]"), Some("theorem 1[v]"), None],
                "qualification, lane/x",
            ),
            (
                [Some("other 1[]"), Some("theorem 1[]"), None],
                "qualification, lane/x",
            ),
            (
                [Some("theorem 1[]"), Some("theorem 1[]"), Some("other 1[]")],
                "qualification, lane/x, lane/y",
            ),
            (
                [None, Some("other 1[u]"), Some("other 1[u]")],
                "lane/x, lane/y",
            ),
        ] {
            let found = merged(entries.map(|e| Vec::from_iter(e.map(|e| format!("{first} {e}")))));
            let problem = format!("the public constant {first} is declared by {parts}");
            no_conclusion(&found, &[problem]);
            assert!(!found.checks.names && found.checks.coverage);
        }
    }

    #[test]
    fn each_lane_leaves_out_what_the_closure_of_the_job_gives_of_its_modules() {
        let fixture = checkout(
            "merge-closure",
            r#"[{"name": "a", "proof_modules": ["Krepi.Proofs.A"]}]"#,
        );
        waive(&fixture, "a", "9999-12-31");
        let text = fs::read_to_string(fixture.root().join(LAYOUT.lanes)).expect("the lanes");
        let text = text.replace(
            "\"components\": [",
            "\"modules\": [\"Krepi.Proofs.A\"], \"components\": [",
        );
        fixture.write(LAYOUT.lanes, &text);
        fixture.commit_all();
        let mut job = qualification(&fixture);
        let held = job.handwritten.as_mut().expect("the list");
        held.insert("Krepi.Proofs.A".to_string(), "shared".to_string());
        let mut lane = lane_x(&fixture, &job);
        let own = lane.lane.as_mut().expect("the lane");
        own.modules.push("Krepi.Proofs.A".to_string());
        own.left_out
            .insert("Krepi.Proofs.A".to_string(), "a".to_string());
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = |lane: &Receipt| {
            let (q, x) = (write(&fixture, "q", &job), write(&fixture, "x", lane));
            merge(fixture.root(), LAYOUT, &[q, t.clone(), x], None)
        };
        assert_eq!(conclusion(&merged(&lane)).0, Status::Verified);
        // A lane that leaves out less than the closure, or more.
        let mut less = lane.clone();
        less.lane.as_mut().expect("the lane").left_out.clear();
        let problem = "lane/x leaves out [], where the waivers leave out [Krepi.Proofs.A]";
        let found = merged(&less);
        no_conclusion(&found, &[problem.to_string()]);
        assert!(!found.checks.waivers);
        let mut more = lane.clone();
        more.lane
            .as_mut()
            .expect("the lane")
            .left_out
            .insert("Krepi.Proofs.B".to_string(), "a".to_string());
        let problem = "lane/x leaves out [Krepi.Proofs.A, Krepi.Proofs.B], where the waivers leave out [Krepi.Proofs.A]";
        no_conclusion(&merged(&more), &[problem.to_string()]);
    }

    #[test]
    fn a_job_whose_statement_hash_differs_from_the_registry_gives_no_verified_merge() {
        // The qualification job rejects `base` when the recorded statement hash
        // is not the computed one, and the merge with it is not VERIFIED.
        let fixture = checkout("merge-hash", r#"[{"name": "a"}]"#);
        let mut job = qualification(&fixture);
        let unit = job.units.get_mut(base::PHASE).expect("the unit");
        (unit.status, unit.reason) = (
            Status::Rejected,
            Some(
                "verification/statements.json records 0, the statement side of the snapshot is 1"
                    .to_string(),
            ),
        );
        job.status = Status::Rejected;
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[write(&fixture, "q", &job), t]);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, false));
        assert!(!merged.gates.axioms);
    }

    #[test]
    fn receipts_that_agree_but_are_not_of_the_commit_checked_out_give_no_conclusion() {
        let fixture = checkout("merge-elsewhere", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        verified(&merge_in(&fixture, &[q.clone(), t.clone()]));
        let (c0, t0) = (rev(&fixture, "HEAD"), rev(&fixture, "HEAD^{tree}"));
        // The receipts agree with each other, and the checkout moves on.
        fixture.write("README.md", "moved\n");
        fixture.commit_all();
        let (c1, t1) = (rev(&fixture, "HEAD"), rev(&fixture, "HEAD^{tree}"));
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        let (at, head) = ((c0.as_str(), t0.as_str()), (c1.as_str(), t1.as_str()));
        let c = lane_beside(&fixture, "q");
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
        let mut shard = receipt(&fixture, "target/a/1", &units_of("a"));
        shard.commit = Some(before.clone());
        let t = write(&fixture, "t", &shard);
        let merged = merge_in(&fixture, &[q.clone(), t.clone()]);
        no_conclusion(&merged, &[elsewhere(&t, (&before, &tree), checkout)]);
        // A shard of the head with another tree.
        let other = "f".repeat(40);
        let mut shard = receipt(&fixture, "target/a/1", &units_of("a"));
        shard.tree = Some(other.clone());
        let t = write(&fixture, "t", &shard);
        let merged = merge_in(&fixture, &[q, t.clone()]);
        no_conclusion(&merged, &[elsewhere(&t, (&head, &other), checkout)]);
    }

    #[test]
    fn receipts_of_different_images_or_without_an_image_give_no_conclusion() {
        let fixture = checkout("merge-images", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let shard = receipt(&fixture, "target/a/1", &units_of("a"));
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
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t]);
        let (at, head) = ((c0.as_str(), t0.as_str()), (c1.as_str(), t1.as_str()));
        let c = lane_beside(&fixture, "q");
        no_conclusion(&merged, &[elsewhere(&q, at, head), elsewhere(&c, at, head)]);
    }

    #[test]
    fn a_registry_of_two_formal_targets_with_the_receipt_of_one_shard_gives_no_conclusion() {
        let fixture = checkout("merge-missing", r#"[{"name": "a"}, {"name": "b"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q, t]);
        no_conclusion(
            &merged,
            &[
                "the unit target/b has no conclusion".to_string(),
                "0 receipts are of the part target/b/1, where one is expected".to_string(),
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
        let t = write(&fixture, "t", &receipt(&fixture, "target/a/1", &all));
        verified(&merge_in(&fixture, &[q.clone(), t]));
        let t = write(&fixture, "t", &receipt(&fixture, "target/a/1", &all[..1]));
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
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let c = write(
            &fixture,
            "c",
            &receipt(&fixture, "target/c/1", &units_of("c")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t.clone(), c]);
        no_conclusion(
            &merged,
            &[
                "the unit target/c has a conclusion but is not registered".to_string(),
                "target/c/1 is not a part of the checkout".to_string(),
            ],
        );
        // A planned target is no shard.
        let p = write(&fixture, "p", &receipt(&fixture, "target/p/1", &[]));
        let merged = merge_in(&fixture, &[q, t, p]);
        let problem = "target/p/1 is not a part of the checkout";
        no_conclusion(&merged, &[problem.to_string()]);
    }

    #[test]
    fn a_synthetic_wall_clock_above_2880_s_is_flagged_over_80_percent() {
        let fixture = checkout("merge-clock", r#"[{"name": "a"}]"#);
        let mut q = qualification(&fixture);
        q.seconds = 2_700.0;
        let q = write(&fixture, "q", &q);
        let shard = |seconds: f64| {
            let mut shard = receipt(&fixture, "target/a/1", &units_of("a"));
            shard.seconds = seconds;
            write(&fixture, "t", &shard)
        };
        // The slowest part and 60 s of the merge stay below 2,880 s.
        let merged = merge_in(&fixture, &[q.clone(), shard(2_800.0)]);
        verified(&merged);
        assert_eq!(merged.chain_seconds, 2_800.0);
        assert!(merged.wall_clock_seconds < 2_880.0 && !merged.over_80_percent);
        assert_eq!(merged.merge_from, "job");
        assert!(merged.merge_seconds >= 60.0);
        // A shard that takes longer pushes the synthetic wall clock above.
        let merged = merge_in(&fixture, &[q.clone(), shard(2_830.0)]);
        verified(&merged);
        assert_eq!(merged.chain_seconds, 2_830.0);
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
        // The limit is 80% of the wall-clock limit of the gate.
        assert_eq!(FLAG, Duration::from_secs(2_880));
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
        units.push("base/lane/x".to_string());
        units.sort();
        assert_eq!(keys, units);
        assert_eq!(merged.parts.len(), 2);
        let bytes = fs::read(&q).expect("the receipt");
        assert_eq!(merged.parts[0].sha256, Some(sha256(&bytes)));
        // A shard where the registry has no formal target.
        let x = write(&fixture, "x", &receipt(&fixture, "target/x/1", &[]));
        let paths = with_lanes(&fixture, &[q, x]);
        let merged = super::merge(fixture.root(), LAYOUT, &paths, None);
        let problem = "target/x/1 is not a part of the checkout";
        no_conclusion(&merged, &[problem.to_string()]);
    }

    #[test]
    fn of_the_receipts_of_one_part_only_that_of_the_latest_attempt_counts() {
        let fixture = checkout("merge-attempts", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let attempt = |attempt: &str, status: Status| {
            let mut shard = receipt(&fixture, "target/a/1", &units_of("a"));
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
            "2 receipts are of the part target/a/1, where one is expected",
        ];
        no_conclusion(&merged, &problems.map(String::from));
    }

    /// The exit of `cargo xtask formal merge` in `fixture` for `paths`
    /// [`with_lanes`].
    pub(crate) fn exit(fixture: &Fixture, paths: &[&PathBuf]) -> ExitCode {
        let paths = with_lanes(
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
            let mut shard = receipt(&fixture, "target/a/1", &all);
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
            &receipt(&fixture, "target/a/1", &units_of("a")),
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
        // Without it, the lane beside it is missing too.
        let merged = merge_in(&fixture, std::slice::from_ref(&t));
        let mut missing = problems("has no conclusion", 0);
        let lane = [
            "the unit base/lane/x has no conclusion",
            "0 receipts are of the part lane/x, where one is expected",
        ];
        missing.splice(missing.len() - 1..missing.len() - 1, lane.map(String::from));
        no_conclusion(&merged, &missing);
        let x = write(&fixture, "x", &lane_x(&fixture, &qualification(&fixture)));
        let merged = merge(fixture.root(), LAYOUT, &[q.clone(), q, t, x], None);
        let mut twice = problems("has 2 conclusions", 2);
        let held = "the hand-written module Krepi.Qualification.Arithmetic is held by qualification, qualification";
        twice.push(held.to_string());
        no_conclusion(&merged, &twice);
    }

    #[test]
    fn a_receipt_that_cannot_be_read_or_is_not_of_a_shard_of_schema_7_gives_no_conclusion() {
        let fixture = checkout("merge-receipts", r#"[{"name": "a"}]"#);
        let q = write(&fixture, "q", &qualification(&fixture));
        let shard = receipt(&fixture, "target/a/1", &units_of("a"));
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
            no_conclusion(&merged, &[first, unit, none("target/a/1")]);
            assert_eq!(merged.parts[1].sha256, sha256);
        }
        // A receipt of schema 5, which has no shard, still concludes its
        // units, but is no receipt of its part.
        let mut old = serde_json::to_value(qualification(&fixture)).expect("JSON");
        old["schema"] = 5.into();
        old.as_object_mut().expect("an object").remove("shard");
        fixture.write("artifacts/parts/old.json", &old.to_string());
        let old = fixture.root().join("artifacts/parts/old.json");
        let shown = old.display();
        let merged = merge_in(&fixture, &[old.clone(), write(&fixture, "t", &shard)]);
        let schema = format!("{shown}: schema 5 where 7 is expected");
        let lane = "the unit base/lane/x has no conclusion".to_string();
        no_conclusion(
            &merged,
            &[schema, lane, none("lane/x"), none("qualification")],
        );
        // A receipt of schema 7 without a shard.
        let mut unnamed = shard;
        unnamed.shard = None;
        let unnamed = write(&fixture, "unnamed", &unnamed);
        let merged = merge_in(&fixture, &[q, unnamed.clone()]);
        let problem = format!("{} has no shard", unnamed.display());
        no_conclusion(&merged, &[problem, none("target/a/1")]);
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
            &receipt(&fixture, "target/a/1", &units_of("a")),
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
        assert_eq!(WORKERS, 2);
    }

    #[test]
    fn the_calibration_registry_keeps_the_shard_limit() {
        let calibration = targets(include_str!(
            "../../../verification/qualification/calibration/targets.json"
        ));
        assert_eq!(budget_problems(&calibration), Vec::<String>::new());
        // The planned target of the calibration is no shard.
        assert_eq!(
            shards(&calibration),
            BTreeMap::from([("target/calibration/1".to_string(), 3_000)])
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
                ("target/a/1".to_string(), 3_300),
                ("target/b/1".to_string(), registry::BUDGET)
            ])
        );
        assert_eq!(budget_problems(&registry(3_300)), Vec::<String>::new());
        // However many workers a shard has, they do not divide its budget.
        for budget in [3_301, 6_600] {
            assert_eq!(
                budget_problems(&registry(budget)),
                [format!(
                    "part target/a/1: its registered budget of {budget} s is more than the shard limit of 3300 s"
                )]
            );
        }
    }

    /// The receipts of the qualification job and of the shard of `a`, whose
    /// target the proofs reject and which has no mutants, so that it is
    /// complete, as a run of it is.
    pub(crate) fn rejected(fixture: &Fixture) -> [PathBuf; 2] {
        let mut shard = receipt(fixture, "target/a/1", &units_of("a"));
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
        hold(&fixture);
        fixture
    }

    /// The receipts of the qualification job of `fixture` of [`proving`], of
    /// the part of `a`, whose proofs the part rejects after its audit
    /// concluded `audit`, and of the lane `x`, whose base round concluded the
    /// statement `statement` and whose comparator `comparator/a` `compared`.
    fn proved_parts(
        fixture: &Fixture,
        statement: Status,
        audit: Class,
        compared: Status,
    ) -> [PathBuf; 3] {
        let job = qualification(fixture);
        let mut lane = lane_x(fixture, &job);
        lane.units
            .get_mut(&base::unit(PROVED))
            .expect("the unit")
            .status = statement;
        let mut shard = receipt(fixture, "target/a/1", &units_of("a"));
        shard.status = Status::Rejected;
        shard.units.get_mut("target/a").expect("the unit").status = Status::Rejected;
        let argv = "lake env lean Audit.lean";
        shard.commands = vec![tool("target/a", Site::AxiomAudit, argv, audit)];
        lane.units.get_mut("comparator/a").expect("the unit").status = compared;
        [("q", job), ("t", shard), ("x", lane)].map(|(name, part)| write(fixture, name, &part))
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
        let mut shard = receipt(&fixture, "target/a/1", &all);
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
            &receipt(&fixture, "target/a/1", &units_of("a")),
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
        let shard = receipt(&fixture, "target/a/1", &units_of("a"));
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
    fn a_lane_that_did_not_extract_a_formal_target_outside_the_waivers_gives_no_conclusion() {
        let fixture = checkout("merge-left-out", r#"[{"name": "a"}, {"name": "b"}]"#);
        waive(&fixture, "b", "9999-12-31");
        let t = write(
            &fixture,
            "a",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let b = write(
            &fixture,
            "b",
            &receipt(&fixture, "target/b/1", &units_of("b")),
        );
        // The lane of `a` and `b` extracted `a` and left out `b`, or extracted
        // both.
        let job = qualification(&fixture);
        let mut lane = lane_x(&fixture, &job);
        assert_eq!(Vec::from_iter(lane.proof_targets.keys()), ["a"]);
        let q = write(&fixture, "q", &job);
        let merged = |lane: &Receipt| {
            merge_in(
                &fixture,
                &[q.clone(), t.clone(), b.clone(), write(&fixture, "x", lane)],
            )
        };
        verified(&merged(&lane));
        lane.proof_targets
            .insert("b".to_string(), receipt::Target::default());
        verified(&merged(&lane));
        // A lane that left out `a`, as under a waiver that has since expired.
        lane.proof_targets.remove("a");
        let problem = "the formal target a is not extracted by its lane";
        let left = merged(&lane);
        no_conclusion(&left, &[problem.to_string()]);
        assert!(!left.checks.extraction && left.checks.coverage);
        // Nor does a lane extract it without its component.
        let mut moved = lane_x(&fixture, &job);
        moved
            .lane
            .as_mut()
            .expect("the lane")
            .components
            .retain(|c| c != "A");
        no_conclusion(&merged(&moved), &[problem.to_string()]);
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
            receipt(&fixture, "target/a/1", &units_of("a")),
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
        let mut shard = receipt(&fixture, "target/a/1", &units_of("a"));
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
                shard => receipt(&fixture, &format!("target/{shard}/1"), &units_of(shard)),
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
                (Some(13_372_738_764), false, Some(false)),
            ]
        );
        let summary = summary(&merged);
        let flagged = |line: &&str| line.starts_with("- part ") || line.starts_with("- job ");
        let parts = Vec::from_iter(summary.lines().filter(flagged));
        assert_eq!(
            parts,
            [
                "- job formal shard a/1: 2880.001 s, above 2880 s",
                "- part target/a/1: memory peak 13372738765 B, above 13372738764 B",
            ]
        );
        let job = &merged.jobs["formal shard a/1"];
        assert_eq!(
            (job.over_seconds, job.cgroup_memory_peak, job.over_memory),
            (true, Some(MEMORY + 1), Some(true))
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
        hold(&fixture);
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
        hold(&fixture);
        waive(&fixture, "a", "9999-12-31");
        // The base round of the lane leaves the statements of a module that
        // it leaves out unchecked.
        let scoped = |lane: &mut Receipt, theorem: &str| {
            let unit = lane.units.get_mut(&base::unit(theorem)).expect("the unit");
            unit.status = Status::Scoped;
        };
        let job = qualification(&fixture);
        let mut lane = lane_x(&fixture, &job);
        scoped(&mut lane, "Krepi.Proofs.A.s");
        let (q, x) = (write(&fixture, "q", &job), write(&fixture, "x", &lane));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q.clone(), t.clone(), x.clone()]);
        assert_eq!(conclusion(&merged), (Status::Rejected, true, true));
        assert!(merged.waivers[0].used);
        assert_eq!(exit(&fixture, &[&q, &t, &x]), ExitCode::SUCCESS);
        // A statement of a module that only imports what a waiver leaves out
        // is no waived target's.
        scoped(&mut lane, "Krepi.Proofs.Helper.r");
        let x = write(&fixture, "x", &lane);
        let merged = merge_in(&fixture, &[q.clone(), t.clone(), x.clone()]);
        assert_eq!(conclusion(&merged), (Status::Scoped, true, false));
        assert_eq!(exit(&fixture, &[&q, &t, &x]), ExitCode::FAILURE);
        // Without a waiver that holds, the statement is required.
        waive(&fixture, "a", "2000-01-01");
        let job = qualification(&fixture);
        let mut lane = lane_x(&fixture, &job);
        scoped(&mut lane, "Krepi.Proofs.A.s");
        let (q, x) = (write(&fixture, "q", &job), write(&fixture, "x", &lane));
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let merged = merge_in(&fixture, &[q, t, x]);
        assert_eq!(conclusion(&merged), (Status::Scoped, true, false));
    }

    #[test]
    fn each_hard_gate_fails_on_its_own_entries() {
        let fixture = proving("merge-gates");
        let parts = |fixture: &Fixture| {
            let (job, shard) = (
                qualification(fixture),
                receipt(fixture, "target/a/1", &units_of("a")),
            );
            let lane = lane_x(fixture, &job);
            (job, shard, lane)
        };
        let gates_of = |fixture: &Fixture, job: &Receipt, shard: &Receipt, lane: &Receipt| {
            let parts = [("q", job), ("t", shard), ("x", lane)];
            let merged = merge_in(
                fixture,
                &parts.map(|(name, part)| write(fixture, name, part)),
            );
            assert_eq!(merged.problems, Vec::<String>::new());
            gates(&merged)
        };
        let (job, shard, lane) = parts(&fixture);
        let all = |job: &Receipt| gates_of(&fixture, job, &shard, &lane);
        let of_lane = |lane: &Receipt| gates_of(&fixture, &job, &shard, lane);
        assert_eq!(all(&job), [true, true, true]);
        let status = |receipt: &mut Receipt, unit: &str, status: Status| {
            receipt.units.get_mut(unit).expect("the unit").status = status;
        };
        // The axioms: an audit that did not pass, no audit of the
        // qualification job or of a lane, or a unit of a base round or of a
        // target that is not VERIFIED; a run of the heartbeats is no audit.
        let mut other = job.clone();
        other.commands[0].class = Class::ProofFailure;
        assert_eq!(all(&other), [false, true, true]);
        other.commands.remove(0);
        assert_eq!(all(&other), [false, true, true]);
        let mut other = lane.clone();
        other.commands.remove(0);
        assert_eq!(of_lane(&other), [false, true, true]);
        let heartbeats = "lake env lean --json .heartbeats/Krepi/Proofs/A.lean";
        let heartbeats = tool("base", Site::AxiomAudit, heartbeats, Class::ProofFailure);
        let mut other = job.clone();
        other.commands.push(heartbeats);
        assert_eq!(all(&other), [true, true, true]);
        let mut other = job.clone();
        status(&mut other, base::PHASE, Status::Rejected);
        assert_eq!(all(&other), [false, true, true]);
        for unit in ["base/lane/x".to_string(), base::unit(PROVED)] {
            let mut other = lane.clone();
            status(&mut other, &unit, Status::Rejected);
            assert_eq!(of_lane(&other), [false, true, true], "{unit}");
        }
        let mut other = shard.clone();
        let argv = "lake env lean Audit.lean";
        other.commands = vec![tool("target/a", Site::AxiomAudit, argv, Class::ToolFailure)];
        assert_eq!(gates_of(&fixture, &job, &other, &lane), [false, true, true]);
        status(&mut other, "target/a", Status::Rejected);
        other.commands.clear();
        assert_eq!(gates_of(&fixture, &job, &other, &lane), [false, true, true]);
        // `leanchecker`: no replay, two, or one that did not pass, in the
        // qualification job or in a lane, and in a lane one of a module other
        // than its root; the version of Lean is no replay.
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
        let replays = |lane: &mut Receipt, replays: Vec<Command>| {
            lane.commands.retain(|c| c.site != Site::Leanchecker);
            lane.commands.extend(replays);
        };
        let one = |class| replay_of("base/lane/x", class);
        for (replayed, why) in [
            (vec![], "without a replay"),
            (vec![one(Class::Passed), one(Class::Passed)], "with two"),
            (vec![one(Class::ProofFailure)], "with one that failed"),
            (
                vec![tool(
                    "base/lane/x",
                    Site::Leanchecker,
                    "lake env leanchecker --fresh Krepi.Proofs.A",
                    Class::Passed,
                )],
                "of another module",
            ),
        ] {
            let mut other = lane.clone();
            replays(&mut other, replayed);
            assert_eq!(of_lane(&other), [true, false, true], "{why}");
        }
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
            let mut other = lane.clone();
            status(&mut other, "comparator/a", unit_status);
            assert_eq!(of_lane(&other), [true, true, false], "{unit_status:?}");
        }
        // Under a waiver of `a`, its commands and units hold, but neither the
        // unit of a base round nor a replay does.
        waive(&fixture, "a", "9999-12-31");
        let (job, mut shard, mut lane) = parts(&fixture);
        status(&mut lane, &base::unit(PROVED), Status::Rejected);
        shard.commands = vec![tool("target/a", Site::AxiomAudit, argv, Class::ToolFailure)];
        status(&mut shard, "target/a", Status::Rejected);
        status(&mut lane, "comparator/a", Status::NotRun);
        assert_eq!(gates_of(&fixture, &job, &shard, &lane), [true, true, true]);
        lane.commands[1].class = Class::ProofFailure;
        status(&mut lane, "base/lane/x", Status::Rejected);
        assert_eq!(
            gates_of(&fixture, &job, &shard, &lane),
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
        let mut shard = receipt(&fixture, "target/a/1", &all);
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
        hold(&fixture);
        waive(&fixture, "a", "9999-12-31");
        let t = write(
            &fixture,
            "t",
            &receipt(&fixture, "target/a/1", &units_of("a")),
        );
        let job = qualification(&fixture);
        let mut part = lane_x(&fixture, &job);
        let scoped = |receipt: &mut Receipt, unit: &str| {
            receipt.units.get_mut(unit).expect("the unit").status = Status::Scoped;
        };
        let merged = |job: &Receipt, part: &Receipt| {
            let (q, x) = (write(&fixture, "q", job), write(&fixture, "x", part));
            merge_in(&fixture, &[q, t.clone(), x])
        };
        // The statement in the proof module of `a` is left out and covered.
        scoped(&mut part, &base::unit("Krepi.Proofs.A.s"));
        scoped(&mut part, "comparator/a");
        let waived = merged(&job, &part);
        assert_eq!(conclusion(&waived), (Status::Rejected, true, true));
        assert_eq!(gates(&waived), [true, true, true]);
        // That of a module that only imports what the waiver leaves out is not.
        scoped(&mut part, &base::unit("Krepi.Proofs.Helper.r"));
        scoped(&mut part, "comparator/lane/x");
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
            &receipt(&fixture, "target/a/1", &units_of("a")),
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
    fn a_job_of_more_than_2880_s_is_flagged_and_the_slowest_job_gives_the_wall_clock() {
        let fixture = checkout("merge-job", r#"[{"name": "a"}]"#);
        let part = |name: &str, mut receipt: Receipt, seconds: f64| {
            receipt.seconds = seconds;
            write(&fixture, name, &receipt)
        };
        // The receipts of the qualification job, the lane `x` and the part of
        // `a`, of `seconds`, each its own job beside the others.
        let merged = |[q, x, t]: [f64; 3]| {
            let job = qualification(&fixture);
            let lane = lanes::parse(
                &fs::read_to_string(fixture.root().join(LAYOUT.lanes)).expect("lanes"),
            );
            let lane = lane_of(&fixture, &job, &lane.expect("lanes").lanes[0]);
            let (q, x) = (part("q", job, q), part("x", lane, x));
            let t = part("t", receipt(&fixture, "target/a/1", &units_of("a")), t);
            let merged = merge_in(&fixture, &[q, x, t]);
            verified(&merged);
            merged
        };
        let flags = |merged: &Merge| Vec::from_iter(merged.parts.iter().map(|p| p.over_seconds));
        let job = merged([1_500.0, 1_000.0, 2_400.0]);
        assert_eq!(job.chain_seconds, 2_400.0);
        assert_eq!(job.chain, ["formal shard a/1"]);
        assert_eq!(flags(&job), [false, false, false]);
        let jobs = Vec::from_iter(
            job.jobs
                .iter()
                .map(|(name, job)| (name.as_str(), job.seconds)),
        );
        let expected = [
            ("formal lane x", 1_000.0),
            ("formal run", 1_500.0),
            ("formal shard a/1", 2_400.0),
        ];
        assert_eq!(jobs, expected);
        assert_eq!(
            Vec::from_iter(job.parts.iter().map(|p| p.job.clone())),
            [
                Some("formal run".to_string()),
                Some("formal lane x".to_string()),
                Some("formal shard a/1".to_string())
            ]
        );
        // A lane of more than 2,880 s flags its job and its part, and gives
        // the wall clock.
        let over = merged([1_500.0, 2_880.5, 10.0]);
        assert_eq!(
            (over.chain_seconds, over.chain.clone()),
            (2_880.5, vec!["formal lane x".to_string()])
        );
        assert!(over.over_80_percent && over.jobs["formal lane x"].over_seconds);
        assert!(!over.jobs["formal run"].over_seconds);
        assert_eq!(flags(&over), [false, true, false]);
        let summary = summary(&over);
        let line = "- job formal lane x: 2880.5 s, above 2880 s";
        assert!(summary.lines().any(|l| l == line), "{summary}");
    }

    #[test]
    fn jobs_that_needs_chains_count_by_their_sum_in_the_synthetic_wall_clock() {
        let jobs = [
            ("formal run", ("gate", 1_000.0)),
            ("formal lane a", ("lane", 1_500.0)),
            ("formal lane b", ("lane", 1_200.0)),
            ("formal shard t/1", ("shard", 2_000.0)),
        ];
        let jobs = Jobs::from_iter(jobs.map(|(name, job)| (name.to_string(), job)));
        let names = |names: &[&str]| Vec::from_iter(names.iter().map(|name| name.to_string()));
        // Beside each other, as the workflow runs them, the slowest job alone.
        assert_eq!(
            chain(&jobs, &NEEDS),
            (names(&["formal shard t/1"]), 2_000.0)
        );
        // A lane that needs the qualification job follows it, so the chain is
        // the qualification job and its slowest lane.
        let needs: [(&str, &[&str]); 3] = [("gate", &[]), ("lane", &["gate"]), ("shard", &[])];
        let chained = (names(&["formal run", "formal lane a"]), 2_500.0);
        assert_eq!(chain(&jobs, &needs), chained);
        // A part that needs the lanes follows the slowest of them.
        let needs: [(&str, &[&str]); 3] =
            [("gate", &[]), ("lane", &["gate"]), ("shard", &["lane"])];
        let chained = (
            names(&["formal run", "formal lane a", "formal shard t/1"]),
            4_500.0,
        );
        assert_eq!(chain(&jobs, &needs), chained);
    }

    #[test]
    fn the_needs_of_the_jobs_of_the_gate_are_those_of_the_table_after_the_limits() {
        // The workflow `formal` and the table of xtask give each job of the
        // gate the same jobs that it needs, so that the merge computes the
        // synthetic wall clock by the chains that the workflow runs.
        let text = include_str!("../../../.github/workflows/formal.yml");
        let documents = yaml_rust2::YamlLoader::load_from_str(text).expect("the workflow");
        let jobs = &documents[0]["jobs"];
        let needs = |job: &yaml_rust2::Yaml| match job {
            yaml_rust2::Yaml::String(one) => vec![one.clone()],
            yaml_rust2::Yaml::Array(many) => {
                Vec::from_iter(many.iter().filter_map(|n| n.as_str().map(String::from)))
            }
            _ => Vec::new(),
        };
        for (key, after) in NEEDS {
            let expected = Vec::from_iter(["limits"].iter().chain(after).map(|n| n.to_string()));
            assert_eq!(needs(&jobs[key]["needs"]), expected, "{key}");
        }
        let parts = needs(&jobs["parts"]["needs"]);
        assert_eq!(parts, NEEDS.map(|(key, _)| key.to_string()));
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
