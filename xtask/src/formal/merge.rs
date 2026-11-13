//! The shards of the proof gate and their merge, as "Shards and merge" in
//! `docs/formal-verification.md` describes: beside the qualification job,
//! every formal target is a shard of its own, named by its unit, whose
//! registered budget, over its workers, is at most the shard limit, the
//! wall-clock limit of the gate less the time of the merge; and
//! `cargo xtask formal merge` combines the receipts of these parts of one
//! commit into the conclusion of the whole gate.

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
use super::{base, guard, qualify};

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

/// The synthetic wall clock above which a merge flags it: 80% of the limit.
pub const FLAG: Duration = Duration::from_secs(WALL_CLOCK.as_secs() * 4 / 5);

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
/// extraction margin for the qualification job, and the shard margin for
/// the shard of a target, which the budget of its target grows.
pub fn budget(shard: &str) -> Duration {
    let qualification = run::GATE_BUDGET + EXTRACTION_MARGIN;
    [qualification, SHARD_MARGIN][usize::from(target(shard).is_some())]
}

/// The shard that `--shard` names: `qualification` or `target/<name>`.
pub fn shard(name: &str) -> Result<String, String> {
    let valid = name == qualify::PHASE || target(name).is_some_and(|t| !t.is_empty());
    let invalid = format!("`{name}` is neither {} nor target/<name>", qualify::PHASE);
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
/// and its summary into [`DIR`] and prints the summary. It exits with 0 for
/// a complete `VERIFIED` conclusion and 1 otherwise, or with 120, the record
/// on standard error, when it cannot write them.
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
    let passed = merged.status == Status::Verified && merged.complete;
    ExitCode::from(u8::from(!passed))
}

/// The record of the merge of the receipts at `paths` in the checkout `root`
/// in `layout`, with the seconds `job` of its job before the merge. When
/// every precondition holds, its conclusion is that of a whole run from the
/// failures of the receipts and the units, complete when every receipt is;
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
    // The receipts are of the commit checked out, whose gate inputs are clean.
    let (inputs, mut git) = (paths::gate_inputs(layout), guard::Standalone(root));
    let head = paths::snapshot(&mut git, &inputs).and_then(|(commit, tree, _)| {
        let changes = paths::changes(&mut git, &inputs)?.join(", ");
        let dirty = format!("the gate inputs of the checkout are not clean: {changes}");
        problems.extend((!changes.is_empty()).then_some(dirty));
        Ok((Some(commit), Some(tree)))
    });
    let head = head.map_err(|error| problems.push(format!("cannot read the checkout: {error}")));
    let none = |value: &Option<String>| value.clone().unwrap_or("none".to_string());
    let (mut given, mut images) = (BTreeMap::new(), BTreeSet::new());
    for (index, receipt) in &receipts {
        let shown = &merged.parts[*index].receipt;
        let at = (receipt.commit.clone(), receipt.tree.clone());
        if let Some((commit, tree)) = head.as_ref().ok().filter(|head| **head != at) {
            let at = format!("of commit {} and tree {}", none(&at.0), none(&at.1));
            let checkout = format!("of commit {} and tree {}", none(commit), none(tree));
            problems.push(format!("{shown} is {at}, and the checkout {checkout}"));
        }
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
    // Each unit that the checkout registers has exactly one conclusion.
    let read = |path: &str| {
        let text = fs::read_to_string(root.join(path));
        text.map_err(|error| format!("cannot read {path}: {error}"))
    };
    let at = |path: &'static str| move |error: String| format!("{path}: {error}");
    let cases = |text: String| qualify::load_cases(&text, layout).map(drop);
    let statements = |text: String| guard::load_statements(&text, layout).map(drop);
    let statements = |text| statements(text).map_err(at(layout.statements));
    let registry = |text: String| registry::parse(&text).map_err(at(layout.registry));
    problems.extend(read(layout.cases).and_then(cases).err());
    problems.extend(read(layout.statements).and_then(statements).err());
    let targets = read(layout.registry).and_then(registry);
    let targets = targets.map_err(|problem| problems.push(problem));
    let targets = targets.map_or_else(|()| Vec::new(), |registry| registry.targets);
    let [_, finish] = run::target_phases(root, layout, &BTreeSet::new(), None, None);
    let (qualification, base) = (qualify::phase(root, layout), base::phase(root, layout));
    let mut registered = Vec::new();
    for Phase { name, units, .. } in [qualification, base, finish] {
        registered.extend(units.into_iter().map(|unit| (unit, name.clone())));
    }
    let concluded = receipts.iter().flat_map(|(_, receipt)| &receipt.units);
    let concluded = concluded.map(|(unit, u)| (unit.clone(), (u.status, u.reason.clone())));
    let (units, unaccounted) = outcome::account(&registered, concluded.collect(), None);
    problems.extend(unaccounted);
    // One receipt of the qualification job and of the shard of each formal target.
    let mut expected = BTreeSet::from_iter(shards(&targets).into_keys());
    expected.insert(qualify::PHASE.to_string());
    for part in &expected {
        let count = given.remove(part.as_str()).unwrap_or(0);
        let problem = format!("{count} receipts are of the part {part}, where one is expected");
        problems.extend((count != 1).then_some(problem));
    }
    let (registry, other) = (layout.registry, given.keys());
    problems.extend(other.map(|part| format!("{part} is not a part of {registry}")));
    // The conclusion, which only a merge without a problem synthesizes.
    let failures = receipts.iter().flat_map(|(_, receipt)| &receipt.failures);
    let mut statuses = Vec::from_iter(failures.map(|failure| failure.status));
    statuses.extend(units.values().map(|unit| unit.status));
    let complete = receipts.iter().all(|(_, receipt)| receipt.complete);
    merged.complete = problems.is_empty() && complete;
    statuses.extend((!problems.is_empty()).then_some(Status::ToolFailure));
    merged.status = outcome::run_status(&statuses, false);
    merged.image = images.pop_first().filter(|_| images.is_empty()).flatten();
    (merged.commit, merged.tree) = head.unwrap_or_default();
    (merged.schema, merged.units, merged.problems) = (receipt::MERGE_SCHEMA, units, problems);
    // The synthetic wall clock: the slowest part and the merge to its end.
    let kept = merged.parts.iter().filter(|part| !part.superseded);
    merged.slowest_part_seconds = kept.map(|part| part.seconds).fold(0.0, f64::max);
    merged.merge_from = ["command", "job"][usize::from(job.is_some())].to_string();
    merged.merge_seconds = receipt::seconds(job.unwrap_or_default() + start.elapsed());
    let (slowest, seconds) = (merged.slowest_part_seconds, merged.merge_seconds);
    (merged.wall_clock_seconds, merged.over_80_percent) = wall_clock(slowest, seconds);
    merged
}

/// The summary of `merged`: its conclusion and wall clock, whether the
/// clock is above [`FLAG`], and each problem.
fn summary(merged: &Merge) -> String {
    let (status, seconds) = (word(&merged.status), merged.wall_clock_seconds);
    let complete = ["not ", ""][usize::from(merged.complete)];
    let conclusion = format!("formal merge: {status}, {complete}complete");
    let mut lines = vec![format!("{conclusion}; synthetic wall clock {seconds} s")];
    let over = "the synthetic wall clock is above 80% of the wall-clock limit of the gate";
    let over = format!("- {over}, {} s", WALL_CLOCK.as_secs());
    lines.extend(merged.over_80_percent.then_some(over));
    let problems = merged.problems.iter();
    lines.extend(problems.map(|problem| format!("- problem: {problem}")));
    lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formal::fixture::{self, Fixture};
    use crate::formal::receipt::{Failure, Image, Unit};
    use crate::formal::registry;
    use crate::formal::run::tests::register;

    const LAYOUT: &Layout = &Layout::PRODUCTION;

    /// The image that the receipts of the tests name, but where a test
    /// changes it.
    fn image(digit: char) -> String {
        let digest = digit.to_string().repeat(64);
        format!("ghcr.io/casxi-lab/krepi-formal@sha256:{digest}")
    }

    /// A checkout with one qualification case, no proved statement and the
    /// registry of `targets`, a JSON list, committed.
    fn checkout(label: &str, targets: &str) -> Fixture {
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
    /// of 600 s and the image `image('a')`, that concludes each of `units`.
    fn receipt(fixture: &Fixture, shard: &str, units: &[String]) -> Receipt {
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
            units: BTreeMap::from_iter(units.iter().map(unit)),
            ..Receipt::default()
        }
    }

    /// The receipt of the qualification job of `fixture` at its head.
    fn qualification(fixture: &Fixture) -> Receipt {
        receipt(
            fixture,
            qualify::PHASE,
            &qualification_units(fixture.root()),
        )
    }

    /// Writes `receipt` below the ignored `artifacts/parts/` of `fixture`.
    fn write(fixture: &Fixture, name: &str, receipt: &Receipt) -> PathBuf {
        let path = format!("artifacts/parts/{name}.json");
        fixture.write(&path, &receipt::render(receipt));
        fixture.root().join(path)
    }

    /// The merge of the receipts at `paths` in `fixture`, with 60 s of its
    /// job before the command.
    fn merge_in(fixture: &Fixture, paths: &[PathBuf]) -> Merge {
        merge(fixture.root(), LAYOUT, paths, Some(Duration::from_secs(60)))
    }

    /// The units of a target `t` without mutants.
    fn units_of(target: &str) -> Vec<String> {
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
        no_conclusion(&merged, &[elsewhere(&q, at, head), elsewhere(&t, at, head)]);
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
        no_conclusion(&merged, &[elsewhere(&q, at, head)]);
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
        assert_eq!(merged.parts.len(), 1);
        let bytes = fs::read(&q).expect("the receipt");
        assert_eq!(merged.parts[0].sha256, Some(sha256(&bytes)));
        // A shard where the registry has no formal target.
        let x = write(&fixture, "x", &receipt(&fixture, "target/x", &[]));
        let merged = super::merge(fixture.root(), LAYOUT, &[q, x], None);
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
            [false, true, false]
        );
        // Two receipts of one part and of the same attempt.
        let merged = merge_in(&fixture, &[q, first.clone(), first]);
        let problems = [
            "the unit target/a has 2 conclusions",
            "2 receipts are of the part target/a, where one is expected",
        ];
        no_conclusion(&merged, &problems.map(String::from));
    }

    /// The exit of `cargo xtask formal merge` in `fixture` for `paths`.
    fn exit(fixture: &Fixture, paths: &[&PathBuf]) -> ExitCode {
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
        let merged = merge_in(&fixture, std::slice::from_ref(&t));
        no_conclusion(&merged, &problems("has no conclusion", 0));
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
        no_conclusion(&merged, &[schema, none("qualification")]);
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
}
