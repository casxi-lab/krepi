//! The comparator of a lane of the proof gate, as "Comparator" in
//! `docs/formal-verification.md` describes it: in the stage of the base
//! round that the base run of the lane kept, `lake comparator` checks the
//! theorem of each proved statement of the lane against a challenge that
//! declares it, with the axioms that the base audit admitted for its unit;
//! the run then writes the receipt of the lane with the base record.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use serde_json::json;

use super::guard::{self, State, Statement};
use super::lean::{self, STANDARD_AXIOMS};
use super::outcome::{Site, Status, word};
use super::qualify::{conclusion, lake};
use super::receipt::{self, BASE_RECORD, BASE_SCHEMA, BaseRecord, Failure, Receipt};
use super::run::{self, Gate, Phase};
use super::toolchain::sha256;
use super::{Layout, base, merge, registry};

/// The name of the phase, and the first part of its units.
pub const PHASE: &str = "comparator";

/// The budget of the phase.
pub const BUDGET: Duration = Duration::from_secs(1_800);

/// The variable that names the runs directory where the sandbox sees it.
pub const RUNS: &str = "KREPI_FORMAL_RUNS";

/// The Lean library of the challenges in the stage.
const LIBRARY: &str = "KrepiChallenge";

/// The part that concludes each unit, and its proved statements.
pub type Units = BTreeMap<String, (String, Vec<Statement>)>;

/// The units of the checkout `root`, each with its lane: `comparator/<target>`
/// with the proved statements of a lane whose modules that formal target
/// alone lists, as a waiver of it leaves them out, `comparator/lane/<name>`
/// with the other proved statements of the lane, and `comparator`, of no part,
/// with those of a module of no lane.
pub fn units(root: &Path, layout: &Layout) -> Result<Units, String> {
    let read = |path: &str| base::read(&root.join(path)).map_err(|e| format!("cannot read {e}"));
    let statements = guard::load_statements(&read(layout.statements)?, layout);
    let statements = statements.map_err(|e| format!("{}: {e}", layout.statements))?;
    let targets = registry::parse(&read(layout.registry)?);
    let targets = (targets.map_err(|e| format!("{}: {e}", layout.registry))?).targets;
    let formal = Vec::from_iter((targets.iter()).filter(|t| t.state == registry::State::Formal));
    let lanes = base::lanes(root, layout)?;
    let modules = statements.statements.iter().map(|s| s.module.clone());
    let homes = base::homes(layout, modules);
    let mut units = Units::new();
    for statement in (statements.statements.into_iter()).filter(|s| s.state == State::Proved) {
        let part = base::part_of(&lanes, &statement.module, homes.get(&statement.module));
        let part = part.filter(|part| merge::lane(part).is_some());
        let mut listing = (formal.iter()).filter(|t| t.proof_modules.contains(&statement.module));
        let alone = (listing.next()).filter(|_| listing.next().is_none());
        let name = (alone.map(|t| t.name.clone()).or(part.clone())).filter(|_| part.is_some());
        let name = name.map_or(PHASE.to_string(), |name| format!("{PHASE}/{name}"));
        units
            .entry(name)
            .or_insert((part.unwrap_or_default(), Vec::new()))
            .1
            .push(statement);
    }
    Ok(units)
}

/// The comparator of the lane `lane` of the checkout `root`, whose base run
/// left its run below `runs`, if given, else below the runs directory of
/// `root`.
pub fn phase<'a>(root: &Path, layout: &'a Layout, lane: &str, runs: Option<String>) -> Phase<'a> {
    let part = format!("lane/{lane}");
    let units = units(root, layout).map(|units| units.into_iter().filter(|(_, (p, _))| *p == part));
    let units = units.map(Units::from_iter);
    let runs = runs.map_or(root.join(run::RUNS), PathBuf::from);
    Phase {
        name: PHASE.to_string(),
        budget: BUDGET,
        units: Vec::from_iter(units.iter().flat_map(|units| units.keys().cloned())),
        body: Box::new(move |gate| compare(gate, units?, &runs)),
    }
}

/// Runs the comparator on `units` in the stage of the one base record of
/// the lane below `runs` of the commit, tree, image and run of CI, whose
/// deadline it takes; an error stops the phase.
fn compare(gate: &mut Gate, units: Units, runs: &Path) -> Result<(), String> {
    let layout = *gate.layout();
    let of = |r: &Receipt| (r.commit.clone(), r.tree.clone(), r.trigger.run_id.clone());
    let image = |r: &Receipt| r.image.as_ref().and_then(|image| image.reference.clone());
    let run = |r: &Receipt| (of(r), image(r), r.shard.clone());
    let this = run(&gate.receipt);
    let entries = fs::read_dir(runs).into_iter().flatten().flatten();
    let found = entries.filter_map(|entry| record(&entry.path().join(BASE_RECORD)));
    let found = found.filter(|(_, record)| record.schema == BASE_SCHEMA && run(record) == this);
    let found = Vec::from_iter(found);
    let count = format!(
        "{} has {} base records of the lane, not one",
        runs.display(),
        found.len()
    );
    let [(sha256, job)] = <[_; 1]>::try_from(found).map_err(|_| count)?;
    gate.continue_from(job.started, job.budgets.gate_seconds);
    let mut read = BaseRecord::default();
    (read.sha256, read.run) = (sha256, job.run.clone());
    (read.started, read.seconds) = (job.started, job.seconds);
    gate.receipt.base_record = Some(read);
    if units.is_empty() {
        return Ok(());
    }
    let base = (job.base.as_ref()).ok_or(format!("the run {} has no base round", job.run))?;
    // The challenges are the modules of a library of their own in the stage.
    let stage = runs.join(format!("{}/work/{}/stage", job.run, base::PHASE));
    let stage = stage.join(Path::new(layout.project).file_name().unwrap_or_default());
    let lakefile = stage.join("lakefile.toml");
    let library = format!("\n[[lean_lib]]\nname = \"{LIBRARY}\"\n");
    let text = base::read(&lakefile)?.replace(&library, "") + &library;
    base::write(&lakefile, &text)?;
    // The challenges import all but the proofs and the proof modules of targets.
    let listed = BTreeSet::from_iter(job.proof_targets.values().flat_map(|t| &t.proof_modules));
    let below = format!("{}.", layout.proofs);
    let proof = |m: &str| format!("{m}.").starts_with(&below) || listed.iter().any(|l| *l == m);
    let kept = (base.modules.iter()).filter(|module| !proof(module));
    let imports = String::from_iter(kept.map(|module| format!("public import {module}\n")));
    let private = |a: &str| (a.strip_prefix("_private.")?.split_once(".0.")).map(|m| proof(m.0));
    let entry = |s: &Statement| base.theorems.get(&s.theorem);
    for (index, (unit, (_, proved))) in units.into_iter().enumerate() {
        // SCOPED for a statement left out, NOT_RUN for one not verified and audited.
        let state = |s: &&Statement| entry(s).map(|t| (t.status, t.axioms.is_some()));
        let scoped = (proved.iter()).find(|s| state(s).is_some_and(|(s, _)| s == Status::Scoped));
        let other = (proved.iter()).find(|s| state(s) != Some((Status::Verified, true)));
        if let Some(Statement { theorem: t, .. }) = scoped.or(other) {
            let found = (base.theorems.get(t)).map_or("no entry".to_string(), |e| word(&e.status));
            let reason = format!("the base round did not audit and verify {t}: {found}");
            let status = [Status::NotRun, Status::Scoped][usize::from(scoped.is_some())];
            gate.conclude(&unit, (status, Some(reason)));
            continue;
        }
        let audited = (proved.iter()).flat_map(|s| entry(s).and_then(|t| t.axioms.clone()));
        let names = audited.flatten().chain(STANDARD_AXIOMS.map(String::from));
        let names = names.filter(|a| a != "sorryAx" && private(a) != Some(true));
        let allowed = BTreeSet::from_iter(names);
        let pairs = Vec::from_iter((proved.iter()).map(|s| (s.theorem.clone(), s.name.clone())));
        let module = format!("{LIBRARY}.C{index}");
        let problems = judge(gate, &stage, &unit, &module, &pairs, &allowed, &imports)?;
        gate.conclude(&unit, conclusion(&problems));
        // The calibration's challenges of no unit that must be rejected: the first
        // theorem with the second statement, and with one permitted axiom fewer.
        if let ([a, b, ..], 0, true) = (&pairs[..], index, layout.project != layout.root_project) {
            let fewer = &allowed - &BTreeSet::from(["propext".to_string()]);
            let swapped = (a.0.clone(), b.1.clone());
            for (name, pair) in [("Statement", swapped), ("Axiom", a.clone())] {
                let allowed = [&allowed, &fewer][usize::from(name == "Axiom")];
                let unit = format!("{PHASE}-negative/{}", name.to_lowercase());
                let module = format!("{LIBRARY}.{name}");
                judge(gate, &stage, &unit, &module, &[pair], allowed, &imports)?;
            }
        }
    }
    Ok(())
}

/// Makes `receipt`, of the comparator run of a lane, the receipt of the lane
/// with the base record that it read below `runs`, read again: with the
/// phases, units, round, lane, targets, commands and failures of the base run
/// before its own, the larger memory peaks and the least free disk of both,
/// the free disk at the start, the start and budget of the base run and the
/// seconds of both. A record that differs when it is read again is a tool
/// failure.
pub fn combine(runs: &Path, receipt: &mut Receipt) {
    let Some(mut read) = receipt.base_record.clone() else {
        return;
    };
    let again = record(&runs.join(&read.run).join(BASE_RECORD));
    let Some((_, base)) = again.filter(|(sha256, _)| *sha256 == read.sha256) else {
        let status = Status::ToolFailure;
        let message = format!("cannot read the base record of {} again", read.run);
        receipt.failures.push(Failure { status, message });
        return run::conclude(receipt, false);
    };
    let offset = receipt.started.saturating_sub(base.started) as f64;
    let count = u32::try_from(base.commands.len()).unwrap_or(u32::MAX);
    let mut commands = base.commands;
    let logs = (commands.iter_mut()).flat_map(|c| [&mut c.stdout, &mut c.stderr]);
    for log in logs.flatten() {
        log.path = format!("../{}/{}", base.run, log.path);
    }
    for command in &mut receipt.commands {
        command.sequence = command.sequence.saturating_add(count);
        command.started = receipt::seconds(Duration::from_secs_f64(command.started + offset));
    }
    commands.append(&mut receipt.commands);
    (receipt.commands, receipt.base, receipt.lane) = (commands, base.base, base.lane);
    receipt.proof_targets = base.proof_targets;
    receipt.phases.extend(base.phases);
    receipt.units.extend(base.units);
    receipt.failures.splice(0..0, base.failures);
    let (own, theirs) = (&mut receipt.resources, base.resources);
    own.cgroup_memory_peak = own.cgroup_memory_peak.max(theirs.cgroup_memory_peak);
    let rss = own
        .largest_process_max_rss
        .max(theirs.largest_process_max_rss);
    let least = (own.disk_least_available.into_iter()).chain(theirs.disk_least_available);
    (own.largest_process_max_rss, own.disk_least_available) = (rss, least.min());
    own.disk_available_at_start = theirs.disk_available_at_start;
    (read.comparator_started, read.comparator_seconds) = (receipt.started, receipt.seconds);
    receipt.base_record = Some(read);
    (receipt.started, receipt.budgets) = (base.started, base.budgets);
    receipt.seconds = receipt::seconds(Duration::from_secs_f64(base.seconds + receipt.seconds));
    run::conclude(receipt, false);
}

/// The SHA-256 of the receipt or base record at `path`, and what it holds,
/// if it can be read.
fn record(path: &Path) -> Option<(String, Receipt)> {
    let bytes = fs::read(path).ok()?;
    Some((sha256(&bytes), serde_json::from_slice(&bytes).ok()?))
}

/// Runs `lake comparator` in `stage` as a command of `unit` on the challenge
/// `module`, which declares each theorem of `pairs` with its statement after
/// `imports`, with the `allowed` axioms. Its problems are none when it passed,
/// else its `error:` lines or its reason.
fn judge(
    gate: &mut Gate,
    stage: &Path,
    unit: &str,
    module: &str,
    pairs: &[(String, String)],
    allowed: &BTreeSet<String>,
    imports: &str,
) -> Result<Vec<String>, String> {
    let declared = (pairs.iter()).map(|(t, s)| format!("public theorem {t} : {s} := sorry\n"));
    let challenge = format!("module\n\n{imports}\n{}", String::from_iter(declared));
    base::write(&stage.join(lean::module_file(module)), &challenge)?;
    let names = Vec::from_iter(pairs.iter().map(|(theorem, _)| theorem));
    let config = json!({"challenge_module": module, "solution_module": gate.layout().namespace,
        "theorem_names": names, "permitted_axioms": allowed});
    let file = format!("{module}.json");
    base::write(&stage.join(&file), &format!("{config:#}\n"))?;
    let args = ["comparator", "--config", &file].map(str::to_string);
    let (ran, verdict, _) = gate.run(unit, &lake(Site::Comparator, &args, stage), |_| Ok(()));
    let errors = (ran.map(|ran| lean::errors(&ran.output))).filter(|errors| !errors.is_empty());
    let failed = verdict.reason.map(|reason| errors.unwrap_or(vec![reason]));
    Ok(failed.unwrap_or_default())
}

#[cfg(test)]
mod tests {
    //! The comparator of a lane runs after the base run of the lane in the
    //! base fixture of `base.rs`, whose Lake stand-in passes `lake comparator`
    //! unless a test gives it a script: the statement `S`, proved by `T` in
    //! `Krepi.Proofs.Counter`, and the statement `R`, proved by `M` in
    //! `Krepi.Proofs.Main`, with the formal target `t`.

    use std::process::ExitCode;

    use serde_json::Value;

    use super::*;
    use crate::formal::base::tests::{self as fixtures, S, T, axioms, hashed, stage};
    use crate::formal::fixture::{self, Fixture, commands, lake_script, status};
    use crate::formal::outcome::Class;
    use crate::formal::receipt;
    use crate::formal::run::tests::{
        Done, comparator_run, gate_shard, plenty, root_package, shard_phases,
    };
    use crate::formal::{merge, waiver};

    const LAYOUT: Layout = Layout::PRODUCTION;

    /// A layout whose Lake project is not the root project, as that of the
    /// calibration is, with the paths of production.
    const CALIBRATION: Layout = Layout {
        root_project: "verification/qualification",
        ..Layout::PRODUCTION
    };

    const R: &str = "Krepi.Statements.Counter.R";
    const M: &str = "Krepi.Proofs.Main.m";

    /// The proof module of `T`, which `t` lists in [`checkout`].
    const COUNTER: &str = "Krepi.Proofs.Counter";

    /// The checkout `label`: the base fixture with `R`, and the target `t`
    /// with the proof modules `modules` and the fields `extra`, committed
    /// with its statement hash.
    fn checkout(label: &str, modules: &[&str], extra: Value) -> Fixture {
        let mut fixture = fixtures::base(label);
        root_package(&fixture, "krepi-kernel", "");
        fixtures::register(&fixture, &[(S, T, "proved"), (R, M, "proved")]);
        let mut target = json!({"name": "t", "module": "T", "start_from": ["crate::f"],
            "proof_modules": modules, "obligations": [{"id": "s", "theorems": [T]}]});
        let fields = target.as_object_mut().expect("an object");
        fields.extend(extra.as_object().expect("an object").clone());
        fixtures::targets(&fixture, &json!([target]));
        hashed(&mut fixture);
        fixture
    }

    /// The base run of the lane `a` of `fixture`, which passes.
    fn job(fixture: &Fixture) -> Done {
        let job = fixtures::job(fixture);
        assert_eq!(job.code, ExitCode::SUCCESS, "{:?}", job.failures());
        job
    }

    /// The comparator run of the lane `a` of `fixture` in production.
    fn compared(fixture: &Fixture) -> Done {
        comparator_run(fixture, &LAYOUT, "a", None)
    }

    /// The base record that the base run `job` wrote.
    fn record_of(job: &Done) -> PathBuf {
        job.run.path.join(BASE_RECORD)
    }

    /// The challenge `name` of the stage of `job`, and its configuration.
    fn challenge(job: &Done, name: &str) -> (String, Value) {
        let read = |path: String| fs::read_to_string(stage(job).join(path)).expect("a file");
        let text = read(format!("KrepiChallenge/{name}.lean"));
        let config = read(format!("KrepiChallenge.{name}.json"));
        (text, serde_json::from_str(&config).expect("JSON"))
    }

    /// The permitted axioms of the challenge `name` of the stage of `job`.
    fn permitted(job: &Done, name: &str) -> Vec<String> {
        let config = challenge(job, name).1;
        serde_json::from_value(config["permitted_axioms"].clone()).expect("names")
    }

    /// The standard axioms and `more`, sorted.
    fn with_standard(more: &[&str]) -> Vec<String> {
        let names = ["Classical.choice", "Quot.sound", "propext"]
            .iter()
            .chain(more);
        Vec::from_iter(BTreeSet::from_iter(names.map(|name| name.to_string())))
    }

    /// Rewrites the base record of `job` with `edit`.
    fn edit(job: &Done, edit: impl FnOnce(&mut Receipt)) {
        let mut written = job.written();
        edit(&mut written);
        fs::write(record_of(job), receipt::render(&written)).expect("write the record");
    }

    /// An edit of a receipt.
    type Edit = fn(&mut Receipt);

    /// The theorems of the base record of `receipt`.
    fn theorems(receipt: &mut Receipt) -> &mut BTreeMap<String, base::Theorem> {
        &mut receipt.base.as_mut().expect("a base record").theorems
    }

    /// The entry of `T` in the base record of `receipt`.
    fn of_t(receipt: &mut Receipt) -> &mut base::Theorem {
        theorems(receipt).get_mut(T).expect("the theorem")
    }

    /// The units and command lines of the comparator in `done`.
    fn runs(done: &Done) -> Vec<(String, String)> {
        let compared = (done.receipt.commands.iter()).filter(|c| c.site == Site::Comparator);
        let line = |c: &receipt::Command| (c.unit.clone().unwrap_or_default(), c.argv.join(" "));
        Vec::from_iter(compared.map(line))
    }

    /// The unit `unit` with the command line of the challenge `name`.
    fn run_of(unit: &str, name: &str) -> (String, String) {
        let line = format!("lake comparator --config KrepiChallenge.{name}.json");
        (unit.to_string(), line)
    }

    /// The conclusion of `unit` when the base round did not verify and audit
    /// `theorem`, of the status `found`.
    fn unverified(theorem: &str, found: &str) -> String {
        format!("the base round did not audit and verify {theorem}: {found}")
    }

    #[test]
    fn the_units_are_the_formal_targets_with_proved_statements_and_one_for_the_others() {
        // A planned statement has no unit, nor a planned target, and a
        // module that two formal targets list is in the unit of neither, as
        // a waiver of one of them does not leave it out.
        let fixture = fixtures::base("comparator-units");
        let statement = |name: &str, theorem: &str, state: &str| {
            let module = theorem.rsplit_once('.').expect("a module").0;
            json!({"name": name, "theorem": theorem, "module": module, "state": state})
        };
        let statements = json!({"schema": 1, "hash": "0".repeat(40), "statements": [
            statement(S, T, "proved"), statement(R, M, "proved"),
            statement("Krepi.Statements.Counter.Q", "Krepi.Proofs.Other.q", "proved"),
            statement("Krepi.Statements.Counter.P", "Krepi.Proofs.Counter.p", "planned"),
        ]});
        fixture.write(LAYOUT.statements, &statements.to_string());
        let target = |name: &str, state: &str, modules: &[&str]| json!({"name": name, "state": state, "module": "T", "proof_modules": modules});
        let registry = json!([
            target("p", "planned", &["Krepi.Proofs.Other"]),
            target("t", "formal", &[COUNTER, "Krepi.Proofs.Other"]),
            target("u", "formal", &[COUNTER, "Krepi.Proofs.Main"]),
        ]);
        fixtures::targets(&fixture, &registry);
        let modules = [COUNTER, "Krepi.Proofs.Main", "Krepi.Proofs.Other"];
        let lane = json!({"name": "a", "components": [], "modules": modules});
        fixture.write(
            LAYOUT.lanes,
            &json!({"schema": 1, "lanes": [lane]}).to_string(),
        );
        let found = units(fixture.root(), &LAYOUT).expect("the units");
        let theorems =
            |unit: &str| Vec::from_iter(found[unit].1.iter().map(|s| s.theorem.as_str()));
        assert!(found.values().all(|(part, _)| part == "lane/a"));
        assert_eq!(
            Vec::from_iter(found.keys()),
            ["comparator/lane/a", "comparator/t", "comparator/u"]
        );
        assert_eq!(theorems("comparator/lane/a"), [T]);
        assert_eq!(
            (theorems("comparator/t"), theorems("comparator/u")),
            (vec!["Krepi.Proofs.Other.q"], vec![M])
        );
        // The comparator concludes each with one challenge in the stage of
        // the base run, and in production runs no other.
        let fixture = checkout("comparator-part", &[COUNTER], json!({}));
        let job = job(&fixture);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        let units = receipt.units.keys().filter(|unit| unit.starts_with(PHASE));
        assert_eq!(Vec::from_iter(units), ["comparator/lane/a", "comparator/t"]);
        for unit in ["comparator/lane/a", "comparator/t"] {
            assert_eq!(status(&done, unit), (Status::Verified, None));
        }
        assert_eq!(
            runs(&done),
            [
                run_of("comparator/lane/a", "C0"),
                run_of("comparator/t", "C1")
            ]
        );
        let at = stage(&job);
        let at = at.strip_prefix(fixture.root()).expect("below the root");
        assert!(
            (done.receipt.commands.iter())
                .all(|c| c.site != Site::Comparator || Path::new(&c.cwd) == at)
        );
        let (_, config) = challenge(&job, "C1");
        let expected = json!({"challenge_module": "KrepiChallenge.C1", "solution_module": "Krepi",
            "theorem_names": [T], "permitted_axioms": with_standard(&[])});
        assert_eq!(config, expected);
    }

    #[test]
    fn without_a_proved_statement_the_comparator_runs_nothing_and_the_lane_is_verified() {
        let mut fixture = fixtures::base("comparator-none");
        fixtures::register(&fixture, &[(S, T, "planned")]);
        hashed(&mut fixture);
        job(&fixture);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(Vec::from_iter(receipt.units.keys()), [fixtures::A]);
        assert!(runs(&done).is_empty() && receipt.phases[PHASE].ran);
    }

    #[test]
    fn the_challenge_imports_the_stage_outside_the_proofs_and_declares_each_statement() {
        let fixture = checkout("comparator-imports", &[COUNTER], json!({}));
        let job = job(&fixture);
        compared(&fixture);
        let modules = job.written().base.expect("a base record").modules;
        for module in [
            COUNTER,
            "Krepi.Proofs.Main",
            "Krepi.Spec.Counter",
            "KrepiGen.T.Funs",
        ] {
            assert!(modules.iter().any(|m| m == module), "{modules:?}");
        }
        let imports = |left: &[&str]| {
            let kept = (modules.iter())
                .filter(|m| !m.starts_with("Krepi.Proofs.") && !left.contains(&m.as_str()));
            String::from_iter(kept.map(|module| format!("public import {module}\n")))
        };
        let declared = format!("public theorem {M} : {R} := sorry\n");
        let (text, _) = challenge(&job, "C0");
        assert_eq!(text, format!("module\n\n{}\n{declared}", imports(&[])));
        assert!(
            text.contains("public import Krepi.Statements.Counter\n"),
            "{text}"
        );
        // A proof module that a target lists outside the proofs is not
        // imported either.
        edit(&job, |receipt| {
            let target = receipt.proof_targets.get_mut("t").expect("the target");
            target.proof_modules.push("Krepi.Spec.Counter".to_string());
        });
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let (text, _) = challenge(&job, "C0");
        assert_eq!(
            text,
            format!("module\n\n{}\n{declared}", imports(&["Krepi.Spec.Counter"]))
        );
        // The challenges are a library of the stage.
        let lakefile = fs::read_to_string(stage(&job).join("lakefile.toml")).expect("the lakefile");
        assert_eq!(
            lakefile,
            "-- lakefile.toml\n\n[[lean_lib]]\nname = \"KrepiChallenge\"\n"
        );
    }

    #[test]
    fn the_permitted_axioms_are_those_that_the_base_audit_admitted_for_the_theorems_of_the_unit() {
        // `T` uses an axiom that `t` trusts, and `M` one of `axioms.json`;
        // `t` trusts another and `axioms.json` registers another, which no
        // theorem uses.
        let trusted = |name: &str| json!({"name": name, "reason": "Reviewed."});
        let trusts = [trusted("Krepi.Extra.ax"), trusted("Krepi.Extra.unused")];
        let extra = json!({"trusted_axioms": trusts});
        let mut fixture = checkout("comparator-permitted", &[COUNTER], extra);
        let library =
            |name: &str| json!({"name": name, "source": "Krepi.Lib", "reason": "Reviewed."});
        let registry =
            json!({"schema": 1, "axioms": [library("Krepi.Lib.ax"), library("Krepi.Lib.unused")]});
        fixture.write(LAYOUT.axioms, &format!("{registry}\n"));
        hashed(&mut fixture);
        axioms(&fixture, T, "propext, Krepi.Extra.ax");
        axioms(&fixture, M, "Quot.sound, Krepi.Lib.ax");
        let job = job(&fixture);
        // The job also recorded a template declaration of `t`.
        edit(&job, |receipt| {
            let target = receipt.proof_targets.get_mut("t").expect("the target");
            target.declarations.push("KrepiGen.T.decl".to_string());
        });
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(permitted(&job, "C0"), with_standard(&["Krepi.Lib.ax"]));
        assert_eq!(permitted(&job, "C1"), with_standard(&["Krepi.Extra.ax"]));
    }

    #[test]
    fn the_standard_axioms_are_always_permitted() {
        // The audit reports no axiom for `T`, and `propext` alone for `M`.
        let fixture = checkout("comparator-standard", &[COUNTER], json!({}));
        axioms(&fixture, M, "propext");
        let job = job(&fixture);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let audited = |theorem: &str| {
            let record = job.written().base.expect("a base record");
            record.theorems[theorem].axioms.clone().expect("audited")
        };
        assert_eq!(
            (audited(T), audited(M)),
            (vec![], vec!["propext".to_string()])
        );
        for name in ["C0", "C1"] {
            assert_eq!(permitted(&job, name), with_standard(&[]));
        }
    }

    #[test]
    fn sorry_is_never_permitted_even_when_the_audit_admitted_it() {
        let trusted = json!({"name": "sorryAx", "reason": "Reviewed."});
        let extra = json!({"trusted_axioms": [trusted]});
        let fixture = checkout("comparator-sorry", &[COUNTER], extra);
        axioms(&fixture, T, "propext, sorryAx");
        let job = job(&fixture);
        let record = job.written().base.expect("a base record");
        let theorem = &record.theorems[T];
        assert_eq!(theorem.status, Status::Verified);
        assert_eq!(
            theorem.axioms.as_deref(),
            Some(&["propext".to_string(), "sorryAx".to_string()][..])
        );
        compared(&fixture);
        assert_eq!(permitted(&job, "C1"), with_standard(&[]));
    }

    #[test]
    fn a_native_decision_private_to_a_proof_module_is_not_permitted_and_its_theorem_is_rejected() {
        let fixture = checkout("comparator-native", &[COUNTER], json!({}));
        let job = job(&fixture);
        // The audit admitted a native decision of `T` in its proof module,
        // and one of a library module.
        let own = format!("_private.{COUNTER}.0.{T}._native.native_decide.ax_1_1");
        let library = "_private.Aeneas.Std.Core.0.Aeneas.Std.x._native.bv_decide.ax_1_1";
        edit(&job, |receipt| {
            let axioms = ["propext", &own, library].map(String::from);
            theorems(receipt).get_mut(T).expect("the theorem").axioms = Some(axioms.into());
        });
        let illegal = format!("error: Illegal axiom detected: '{own}'");
        let script = format!(
            "if [ \"$3\" = KrepiChallenge.C1.json ]; then echo \"{illegal}\" >&2; exit 1; fi\n"
        );
        lake_script(&fixture, "comparator", &script);
        let done = compared(&fixture);
        assert_eq!(permitted(&job, "C1"), with_standard(&[library]));
        assert_eq!(
            status(&done, "comparator/t"),
            (Status::Rejected, Some(illegal.as_str()))
        );
        let classes = Vec::from_iter(commands(&done, "comparator/t").iter().map(|c| c.class));
        assert_eq!(classes, [Class::ProofFailure]);
        assert_eq!(status(&done, "comparator/lane/a"), (Status::Verified, None));
        assert_eq!(done.receipt.status, Status::Rejected);
    }

    #[test]
    fn a_native_decision_of_a_library_lemma_that_an_item_names_passes_the_audit_and_the_comparator()
    {
        // As a refinement proof: the statement side reaches the Aeneas Lean
        // library through the generated definitions of a planned target
        // alone, and the proof uses a lemma of the library that `bv_tac`
        // proved by a native decision.
        let mut fixture = fixtures::base("comparator-library-native");
        root_package(&fixture, "krepi-kernel", "");
        let planned =
            json!({"name": "p", "state": "planned", "module": "P", "start_from": ["crate::f"]});
        fixtures::targets(&fixture, &json!([planned]));
        let statement = "module\n\npublic import KrepiGen.P.Funs\n\n\
            @[expose] public def Krepi.Statements.P.V : Prop := True\n";
        fixture.write("verification/Krepi/Statements/P.lean", statement);
        let proof = "module\n\npublic import Krepi.Statements.P\n\n\
            public theorem v : Krepi.Statements.P.V := by bv_tac 8\n";
        fixture.write("verification/Krepi/Proofs/P.lean", proof);
        let (v, theorem) = ("Krepi.Statements.P.V", "Krepi.Proofs.P.v");
        fixtures::register(&fixture, &[(S, T, "proved"), (v, theorem, "proved")]);
        hashed(&mut fixture);
        let (source, lemma) = (
            "Aeneas.Tactic.Solver.BvTac.Lemmas",
            "Aeneas.Std.U8.bv_mod_size",
        );
        let axiom = format!("_private.{source}.0.{lemma}._native.bv_decide.ax_1_5");
        axioms(&fixture, theorem, &axiom);
        lake_script(
            &fixture,
            "audit",
            &format!("echo 'krepi-audit native {axiom} {source}'\n"),
        );
        // Without an item, the audit rejects the theorem.
        let rejected = fixtures::job(&fixture).written();
        let record = rejected.base.expect("a base record");
        let depends = format!("{theorem} depends on {axiom}");
        assert_eq!(record.theorems[theorem].problems, [depends]);
        // The item of its lemma admits it, and the comparator permits it.
        let item = json!({"kind": "library-native-decision", "source": source,
            "declaration": lemma, "reason": "Reviewed."});
        let tcb = json!({"schema": 1, "items": [item]});
        fixture.write(LAYOUT.tcb, &format!("{tcb}\n"));
        hashed(&mut fixture);
        let job = job(&fixture);
        let record = job.written().base.expect("a base record");
        assert_eq!(record.theorems[theorem].status, Status::Verified);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(status(&done, "comparator/lane/a"), (Status::Verified, None));
        assert_eq!(permitted(&job, "C0"), with_standard(&[&axiom]));
        let (text, _) = challenge(&job, "C0");
        assert!(text.contains("public import KrepiGen.P.Funs\n"), "{text}");
        assert!(!text.contains("import Krepi.Proofs"), "{text}");
    }

    #[test]
    fn a_theorem_that_the_base_round_did_not_verify_leaves_its_unit_not_run() {
        // The base round rejects `T`, whose axiom no registry admits.
        let fixture = checkout("comparator-rejected", &[COUNTER], json!({}));
        axioms(&fixture, T, "Krepi.Extra.ax");
        let rejected = fixtures::job(&fixture);
        let record = rejected.written().base.expect("a base record");
        assert_eq!(
            record.theorems[T].problems,
            [format!("{T} depends on Krepi.Extra.ax")]
        );
        let done = compared(&fixture);
        let reason = unverified(T, "REJECTED");
        assert_eq!(
            status(&done, "comparator/t"),
            (Status::NotRun, Some(reason.as_str()))
        );
        assert_eq!(runs(&done), [run_of("comparator/lane/a", "C0")]);
        // The receipt of the lane has the rejection of its base round, and
        // NOT_RUN leaves it not complete.
        let receipt = done.written();
        assert_eq!(
            (receipt.status, receipt.complete),
            (Status::Rejected, false)
        );
        // Without an entry, with one of a tool failure, or one verified but
        // without its axioms.
        let fixture = checkout("comparator-unverified", &[COUNTER], json!({}));
        let job = job(&fixture);
        let original = fs::read(record_of(&job)).expect("the record");
        let edits: [(&str, Edit); 3] = [
            ("no entry", |receipt| drop(theorems(receipt).remove(T))),
            ("TOOL_FAILURE", |receipt| {
                of_t(receipt).status = Status::ToolFailure
            }),
            ("VERIFIED", |receipt| of_t(receipt).axioms = None),
        ];
        for (found, change) in edits {
            fs::write(record_of(&job), &original).expect("restore the record");
            edit(&job, change);
            let done = compared(&fixture);
            let reason = unverified(T, found);
            assert_eq!(
                status(&done, "comparator/t"),
                (Status::NotRun, Some(reason.as_str()))
            );
            assert_eq!(status(&done, "comparator/lane/a"), (Status::Verified, None));
            assert_eq!(runs(&done), [run_of("comparator/lane/a", "C0")], "{found}");
        }
    }

    #[test]
    fn when_the_base_build_did_not_pass_the_units_are_not_run() {
        // The base round of a receipt whose base build failed verifies no
        // theorem.
        let fixture = checkout("comparator-unbuilt", &[COUNTER], json!({}));
        let error = "error: Krepi/Proofs/Counter.lean:9:22: unsolved goals";
        lake_script(&fixture, "build", &fixture::failing(COUNTER, &[error], 1));
        let job = fixtures::job(&fixture);
        let base = |done: &Done| status(done, fixtures::A).0;
        assert_eq!(base(&job), Status::Rejected);
        let done = compared(&fixture);
        for (unit, theorem) in [("comparator/lane/a", M), ("comparator/t", T)] {
            let reason = unverified(theorem, "REJECTED");
            assert_eq!(status(&done, unit), (Status::NotRun, Some(reason.as_str())));
        }
        assert!(runs(&done).is_empty());
    }

    #[test]
    fn the_comparator_concludes_by_the_class_of_its_command() {
        let fixture = checkout("comparator-classes", &[COUNTER], json!({}));
        job(&fixture);
        let mismatch = "error: Challenge and solution theorem statement do not match";
        let built = "comparator exited with 1: what it compares was not built";
        for (script, conclusion) in [
            ("", (Status::Verified, None)),
            (
                &format!("echo '{mismatch}' >&2; exit 1\n")[..],
                (Status::Rejected, Some(mismatch)),
            ),
            // A name that the challenge lacks, or a module that did not build.
            (
                "echo 'error: Child exited with 134' >&2; exit 1\n",
                (Status::ToolFailure, Some(built)),
            ),
            (
                "echo 'error: Child exited with 1' >&2; exit 1\n",
                (Status::ToolFailure, Some(built)),
            ),
            // Lake could not start the comparison.
            (
                "echo 'error: nothing to check' >&2; exit 2\n",
                (Status::ToolFailure, Some("comparator exited with 2")),
            ),
        ] {
            lake_script(&fixture, "comparator", script);
            let done = compared(&fixture);
            for unit in ["comparator/lane/a", "comparator/t"] {
                assert_eq!(status(&done, unit), conclusion, "{script}");
            }
        }
    }

    #[test]
    fn a_statement_left_out_by_a_waiver_makes_its_unit_scoped() {
        let fixture = checkout("comparator-waived", &[COUNTER], json!({}));
        waiver::tests::waive(&fixture, "t", "9999-12-31");
        job(&fixture);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let reason = unverified(T, "SCOPED");
        assert_eq!(
            status(&done, "comparator/t"),
            (Status::Scoped, Some(reason.as_str()))
        );
        assert_eq!(status(&done, "comparator/lane/a"), (Status::Verified, None));
        assert_eq!(runs(&done), [run_of("comparator/lane/a", "C0")]);
    }

    #[test]
    fn a_waiver_does_not_cover_the_comparator_on_a_module_that_another_formal_target_lists() {
        // `t` and `u` list the proof module of `T`, so that a waiver of `t`
        // leaves it in the base round and in the unit `comparator`, whose
        // rejection no waiver covers.
        let mut fixture = fixtures::base("comparator-shared");
        root_package(&fixture, "krepi-kernel", "");
        let target = |name: &str, module: &str, theorems: &[&str]| {
            let obligations =
                Vec::from_iter(theorems.iter().map(|t| json!({"id": "s", "theorems": [t]})));
            json!({"name": name, "module": module, "start_from": ["crate::f"],
                "proof_modules": [COUNTER], "obligations": obligations})
        };
        fixtures::targets(
            &fixture,
            &json!([target("t", "T", &[T]), target("u", "U", &[])]),
        );
        waiver::tests::waive(&fixture, "t", "9999-12-31");
        hashed(&mut fixture);
        let job = job(&fixture);
        let mismatch = "error: Challenge and solution theorem statement do not match";
        lake_script(
            &fixture,
            "comparator",
            &format!("echo '{mismatch}' >&2; exit 1\n"),
        );
        let done = compared(&fixture);
        let units = done
            .receipt
            .units
            .keys()
            .filter(|unit| unit.starts_with(PHASE));
        assert_eq!(Vec::from_iter(units), ["comparator/lane/a"]);
        assert_eq!(
            status(&done, "comparator/lane/a"),
            (Status::Rejected, Some(mismatch))
        );
        let root = fixture.root();
        let shard = |name: &str| {
            let shard = format!("target/{name}/1");
            gate_shard(&fixture, &shard, shard_phases(root, &shard), plenty)
        };
        assert!(job.run.path.join(BASE_RECORD).is_file());
        let parts = [
            ("q", fixtures::qualification(&fixture)),
            ("a", done),
            ("t", shard("t")),
            ("u", shard("u")),
        ];
        let parts = parts.map(|(name, done)| fixtures::part(&fixture, name, &done));
        let merged = merge::merge(root, &LAYOUT, &parts, Some(Duration::ZERO));
        assert_eq!(merged.problems, Vec::<String>::new());
        let held = (
            merged.passes,
            merged.gates.comparator,
            merged.waivers[0].used,
        );
        assert_eq!(held, (false, false, false));
        assert_eq!(merged.status, Status::Rejected);
    }

    #[test]
    fn the_comparator_of_a_lane_reads_its_one_base_record_of_the_run_or_is_a_tool_failure() {
        let mut fixture = checkout("comparator-alone", &[COUNTER], json!({}));
        // A second lane, `b`, without a module.
        let path = fixture.root().join(LAYOUT.lanes);
        let mut lanes: Value =
            serde_json::from_str(&fs::read_to_string(&path).expect("lanes")).expect("JSON");
        let b = json!({"name": "b", "components": [], "modules": []});
        lanes["lanes"].as_array_mut().expect("lanes").push(b);
        fixture.write(LAYOUT.lanes, &format!("{lanes:#}\n"));
        hashed(&mut fixture);
        let runs_of = fixture.root().join(run::RUNS);
        let stopped = |done: &Done, problem: &str| {
            let message = format!("the phase comparator stopped: {problem}");
            assert_eq!(done.failures(), [message.as_str()]);
            let receipt = done.written();
            assert_eq!(
                (receipt.status, receipt.complete),
                (Status::ToolFailure, false)
            );
            for unit in ["comparator/lane/a", "comparator/t"] {
                assert_eq!(status(done, unit), (Status::NotRun, Some(message.as_str())));
            }
            assert!(runs(done).is_empty() && receipt.base_record.is_none());
        };
        let found = |count: usize| {
            let runs = runs_of.display();
            format!("{runs} has {count} base records of the lane, not one")
        };
        let none = found(0);
        stopped(&compared(&fixture), &none);
        // The base record of another lane is not read: without one of its
        // own, the lane has none; with one, its axioms are those of its own
        // record, whatever the other gives the theorem.
        let other = run::tests::gate_shard(
            &fixture,
            "lane/b",
            shard_phases(fixture.root(), "lane/b"),
            plenty,
        );
        assert!(record_of(&other).is_file());
        stopped(&compared(&fixture), &none);
        edit(&other, |receipt| {
            let theorem = base::Theorem {
                axioms: Some(vec!["Krepi.Other.ax".to_string()]),
                status: Status::Verified,
                ..base::Theorem::default()
            };
            theorems(receipt).insert(T.to_string(), theorem);
        });
        let job = job(&fixture);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(permitted(&job, "C1"), with_standard(&[]));
        let read = done
            .receipt
            .base_record
            .clone()
            .expect("the record that it read");
        assert_eq!(read.run, job.run.id);
        // A record of another run of CI, tree or image, or of another commit.
        let original = fs::read(record_of(&job)).expect("the record");
        let elsewhere: [Edit; 3] = [
            |receipt| receipt.trigger.run_id = Some("7".to_string()),
            |receipt| receipt.tree = Some("0".repeat(40)),
            |receipt| {
                let reference = Some(merge::tests::image('b'));
                receipt.image = Some(receipt::Image {
                    reference,
                    ..receipt::Image::default()
                });
            },
        ];
        for change in elsewhere {
            fs::write(record_of(&job), &original).expect("restore the record");
            edit(&job, change);
            stopped(&compared(&fixture), &none);
        }
        fs::write(record_of(&job), &original).expect("restore the record");
        fixture.write("README.md", "moved\n");
        fixture.commit_all();
        stopped(&compared(&fixture), &none);
        // One of the commit without a base round.
        let job = self::job(&fixture);
        edit(&job, |receipt| receipt.base = None);
        let message = format!(
            "the phase comparator stopped: the run {} has no base round",
            job.run.id
        );
        let done = compared(&fixture);
        assert_eq!(done.failures(), [message.as_str()]);
        // Two of the commit and run, as one that a build below the runs
        // directory added would make, whichever has a base round.
        self::job(&fixture);
        stopped(&compared(&fixture), &found(2));
    }

    #[test]
    fn the_runs_directory_of_the_variable_holds_the_stage() {
        let fixture = checkout("comparator-runs", &[COUNTER], json!({}));
        let job = job(&fixture);
        let elsewhere = fixture.root().join("artifacts/elsewhere");
        fs::create_dir_all(&elsewhere).expect("create the directory");
        fs::rename(&job.run.path, elsewhere.join(&job.run.id)).expect("move the run");
        let done = comparator_run(&fixture, &LAYOUT, "a", Some(&elsewhere));
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let stage = elsewhere
            .join(&job.run.id)
            .join("work/base/stage/verification");
        assert!(stage.join("KrepiChallenge/C0.lean").is_file());
        let at = Vec::from_iter(
            done.receipt
                .commands
                .iter()
                .filter(|c| c.site == Site::Comparator),
        );
        assert!(
            at.iter().all(|c| fixture.root().join(&c.cwd) == stage),
            "{at:?}"
        );
        // Without it, the runs directory of the checkout has no such record.
        assert_eq!(compared(&fixture).receipt.status, Status::ToolFailure);
    }

    #[test]
    fn a_second_run_on_a_kept_stage_adds_the_library_once() {
        let fixture = checkout("comparator-twice", &[COUNTER], json!({}));
        let job = job(&fixture);
        for _ in 0..2 {
            let done = compared(&fixture);
            assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        }
        let lakefile = fs::read_to_string(stage(&job).join("lakefile.toml")).expect("the lakefile");
        assert_eq!(
            lakefile,
            "-- lakefile.toml\n\n[[lean_lib]]\nname = \"KrepiChallenge\"\n"
        );
    }

    #[test]
    fn the_calibration_runs_two_challenges_that_the_comparator_must_reject() {
        // The first unit has `S` and `R`, in that order.
        let fixture = checkout(
            "comparator-calibration",
            &[COUNTER, "Krepi.Proofs.Main"],
            json!({}),
        );
        let job = job(&fixture);
        let mismatch = "error: Challenge and solution theorem statement do not match";
        let illegal = "error: Illegal axiom detected: 'propext'";
        let script = format!(
            "case \"$3\" in\n  KrepiChallenge.Statement.json) echo '{mismatch}' >&2; exit 1 ;;\n  \
             KrepiChallenge.Axiom.json) echo \"{illegal}\" >&2; exit 1 ;;\nesac\n"
        );
        lake_script(&fixture, "comparator", &script);
        let done = comparator_run(&fixture, &CALIBRATION, "a", None);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        // They conclude no unit.
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        let units = receipt.units.keys().filter(|unit| unit.starts_with(PHASE));
        assert_eq!(Vec::from_iter(units), ["comparator/t"]);
        let negatives = ["comparator-negative/statement", "comparator-negative/axiom"];
        let expected = [
            run_of("comparator/t", "C0"),
            run_of(negatives[0], "Statement"),
            run_of(negatives[1], "Axiom"),
        ];
        assert_eq!(runs(&done), expected);
        for unit in negatives {
            let classes = Vec::from_iter(commands(&done, unit).iter().map(|c| c.class));
            assert_eq!(classes, [Class::ProofFailure], "{unit}");
        }
        // `T` with the statement of `M`, and with the permitted axioms of the
        // unit, and with its own statement and those axioms but `propext`.
        let declared = |theorem: &str, statement: &str| {
            format!("\npublic theorem {theorem} : {statement} := sorry\n")
        };
        let ((statement, swapped), (axiom, fewer)) =
            (challenge(&job, "Statement"), challenge(&job, "Axiom"));
        assert!(statement.ends_with(&declared(T, R)), "{statement}");
        assert!(axiom.ends_with(&declared(T, S)), "{axiom}");
        for config in [&swapped, &fewer] {
            assert_eq!(config["theorem_names"], json!([T]));
        }
        let all = permitted(&job, "C0");
        assert_eq!(swapped["permitted_axioms"], json!(all));
        let without = Vec::from_iter(all.iter().filter(|name| *name != "propext"));
        assert_eq!(fewer["permitted_axioms"], json!(without));
        // A first unit with one statement runs none.
        let fixture = checkout("comparator-calibration-one", &[COUNTER], json!({}));
        self::job(&fixture);
        let done = comparator_run(&fixture, &CALIBRATION, "a", None);
        assert_eq!(
            runs(&done),
            [
                run_of("comparator/lane/a", "C0"),
                run_of("comparator/t", "C1")
            ]
        );
    }

    #[test]
    fn the_receipt_of_a_lane_has_the_larger_memory_and_the_least_disk_of_its_two_runs() {
        // The free disk at the start is that of the base run, which starts
        // the job; each run gives the larger reading of one memory peak and
        // the smaller of the least free disk in turn.
        let fixture = Fixture::new("comparator-resources");
        let runs = fixture.root().join("runs");
        let readings = |start, least, rss, peak| receipt::Resources {
            disk_available_at_start: Some(start),
            disk_least_available: Some(least),
            largest_process_max_rss: Some(rss),
            cgroup_memory_peak: Some(peak),
        };
        let (first, second) = (readings(1_000, 400, 50, 70), readings(900, 500, 60, 65));
        for (base, own, combined) in [
            (&first, &second, readings(1_000, 400, 60, 70)),
            (&second, &first, readings(900, 400, 60, 70)),
        ] {
            let record = Receipt {
                schema: BASE_SCHEMA,
                run: "base".to_string(),
                resources: base.clone(),
                ..Receipt::default()
            };
            let text = receipt::render(&record);
            fixture.write(&format!("runs/base/{BASE_RECORD}"), &text);
            let read = BaseRecord {
                sha256: sha256(text.as_bytes()),
                run: "base".to_string(),
                ..BaseRecord::default()
            };
            let mut lane = Receipt {
                resources: own.clone(),
                base_record: Some(read),
                ..Receipt::default()
            };
            combine(&runs, &mut lane);
            assert!(lane.failures.is_empty(), "{:?}", lane.failures);
            assert_eq!(lane.resources, combined);
        }
    }
}
