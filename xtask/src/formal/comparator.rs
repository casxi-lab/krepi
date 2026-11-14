//! The comparator part of the proof gate, as "Comparator" in
//! `docs/formal-verification.md` describes it: in the stage of the base
//! round that the qualification job kept, `lake comparator` checks the
//! theorem of each proved statement against a challenge that declares it,
//! with the axioms that the base audit admitted for its unit.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use serde_json::json;

use super::guard::{self, State, Statement};
use super::lean::{self, STANDARD_AXIOMS};
use super::outcome::{Site, Status, word};
use super::qualify::{self, conclusion, lake};
use super::receipt::Receipt;
use super::run::{self, Gate, Phase};
use super::{Layout, base, registry};

/// The name of the part and its phase, and the first part of its units.
pub const PHASE: &str = "comparator";

/// The budget of the part.
pub const BUDGET: Duration = Duration::from_secs(1_800);

/// The variable that names the runs directory where the sandbox sees it.
pub const RUNS: &str = "KREPI_FORMAL_RUNS";

/// The Lean library of the challenges in the stage.
const LIBRARY: &str = "KrepiChallenge";

/// The proved statements of each unit.
type Units = BTreeMap<String, Vec<Statement>>;

/// The units of the checkout `root`: `comparator/<target>` with the proved
/// statements of the first formal target that lists their modules, and
/// `comparator` with the others.
fn units(root: &Path, layout: &Layout) -> Result<Units, String> {
    let read = |path: &str| base::read(&root.join(path)).map_err(|e| format!("cannot read {e}"));
    let statements = guard::load_statements(&read(layout.statements)?, layout);
    let statements = statements.map_err(|e| format!("{}: {e}", layout.statements))?;
    let targets = registry::parse(&read(layout.registry)?);
    let targets = (targets.map_err(|e| format!("{}: {e}", layout.registry))?).targets;
    let formal = Vec::from_iter((targets.iter()).filter(|t| t.state == registry::State::Formal));
    let mut units = Units::new();
    for statement in (statements.statements.into_iter()).filter(|s| s.state == State::Proved) {
        let target = (formal.iter()).find(|t| t.proof_modules.contains(&statement.module));
        let name = target.map_or(PHASE.to_string(), |t| format!("{PHASE}/{}", t.name));
        units.entry(name).or_default().push(statement);
    }
    Ok(units)
}

/// The comparator part of the checkout `root`, whose qualification job left
/// its run below `runs`, if given, else below the runs directory of `root`.
pub fn phase<'a>(root: &Path, layout: &'a Layout, runs: Option<String>) -> Phase<'a> {
    let units = units(root, layout);
    let runs = runs.map_or(root.join(run::RUNS), PathBuf::from);
    Phase {
        name: PHASE.to_string(),
        budget: BUDGET,
        units: Vec::from_iter(units.iter().flat_map(|units| units.keys().cloned())),
        body: Box::new(move |gate| compare(gate, units?, &runs)),
    }
}

/// Runs the comparator on `units` in the stage of the latest qualification
/// job below `runs` of the commit and run of CI; an error stops the phase.
fn compare(gate: &mut Gate, units: Units, runs: &Path) -> Result<(), String> {
    if units.is_empty() {
        return Ok(());
    }
    let layout = *gate.layout();
    let run = |receipt: &Receipt| (receipt.commit.clone(), receipt.trigger.run_id.clone());
    let this = run(&gate.receipt);
    let ours = |job: &Receipt| run(job) == this && job.shard.as_deref() == Some(qualify::PHASE);
    let read = |path: PathBuf| serde_json::from_slice::<Receipt>(&fs::read(path).ok()?).ok();
    let entries = fs::read_dir(runs).into_iter().flatten().flatten();
    let jobs = entries.filter_map(|entry| read(entry.path().join("receipt.json")));
    let job = jobs.filter(ours).max_by_key(|job| job.started);
    let job = job.ok_or(format!("{} has no qualification receipt", runs.display()))?;
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
    for (index, (unit, proved)) in units.into_iter().enumerate() {
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
    //! The comparator part runs after the qualification job of the base
    //! fixture of `base.rs`, whose Lake stand-in passes `lake comparator`
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
    use crate::formal::run::tests::{Done, comparator_part, root_package};
    use crate::formal::waiver;

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

    /// The qualification job of `fixture`, which passes.
    fn job(fixture: &Fixture) -> Done {
        let job = fixtures::job(fixture);
        assert_eq!(job.code, ExitCode::SUCCESS, "{:?}", job.failures());
        job
    }

    /// The comparator part of `fixture` in production.
    fn compared(fixture: &Fixture) -> Done {
        comparator_part(fixture, &LAYOUT, None)
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

    /// Rewrites the receipt of `job` with `edit`.
    fn edit(job: &Done, edit: impl FnOnce(&mut Receipt)) {
        let mut written = job.written();
        edit(&mut written);
        fs::write(job.run.receipt(), receipt::render(&written)).expect("write the receipt");
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
        // module that two formal targets list is in the unit of the first.
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
            target("t", "formal", &[COUNTER]),
            target("u", "formal", &[COUNTER, "Krepi.Proofs.Main"]),
        ]);
        fixtures::targets(&fixture, &registry);
        let found = units(fixture.root(), &LAYOUT).expect("the units");
        let theorems = |unit: &str| Vec::from_iter(found[unit].iter().map(|s| s.theorem.as_str()));
        assert_eq!(
            Vec::from_iter(found.keys()),
            ["comparator", "comparator/t", "comparator/u"]
        );
        assert_eq!(theorems("comparator"), ["Krepi.Proofs.Other.q"]);
        assert_eq!(
            (theorems("comparator/t"), theorems("comparator/u")),
            (vec![T], vec![M])
        );
        // The part concludes each with one challenge in the stage of the
        // job, and in production runs no other.
        let fixture = checkout("comparator-part", &[COUNTER], json!({}));
        let job = job(&fixture);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(
            Vec::from_iter(receipt.units.keys()),
            ["comparator", "comparator/t"]
        );
        for unit in ["comparator", "comparator/t"] {
            assert_eq!(status(&done, unit), (Status::Verified, None));
        }
        assert_eq!(
            runs(&done),
            [run_of("comparator", "C0"), run_of("comparator/t", "C1")]
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
    fn without_a_proved_statement_the_part_runs_nothing_and_is_verified() {
        // It reads no receipt of a qualification job, which has not run.
        let mut fixture = fixtures::base("comparator-none");
        fixtures::register(&fixture, &[(S, T, "planned")]);
        hashed(&mut fixture);
        let done = compared(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert!(receipt.units.is_empty() && runs(&done).is_empty());
        assert!(receipt.phases[PHASE].ran);
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
        // and one of a library module, which no registry admits today.
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
        assert_eq!(status(&done, "comparator"), (Status::Verified, None));
        assert_eq!(done.receipt.status, Status::Rejected);
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
        assert_eq!(runs(&done), [run_of("comparator", "C0")]);
        // NOT_RUN alone is a tool failure, which leaves the receipt not complete.
        let receipt = done.written();
        assert_eq!(
            (receipt.status, receipt.complete),
            (Status::ToolFailure, false)
        );
        // Without an entry, with one of a tool failure, or one verified but
        // without its axioms.
        let fixture = checkout("comparator-unverified", &[COUNTER], json!({}));
        let job = job(&fixture);
        let original = fs::read(job.run.receipt()).expect("the receipt");
        let edits: [(&str, Edit); 3] = [
            ("no entry", |receipt| drop(theorems(receipt).remove(T))),
            ("TOOL_FAILURE", |receipt| {
                of_t(receipt).status = Status::ToolFailure
            }),
            ("VERIFIED", |receipt| of_t(receipt).axioms = None),
        ];
        for (found, change) in edits {
            fs::write(job.run.receipt(), &original).expect("restore the receipt");
            edit(&job, change);
            let done = compared(&fixture);
            let reason = unverified(T, found);
            assert_eq!(
                status(&done, "comparator/t"),
                (Status::NotRun, Some(reason.as_str()))
            );
            assert_eq!(status(&done, "comparator"), (Status::Verified, None));
            assert_eq!(runs(&done), [run_of("comparator", "C0")], "{found}");
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
        let base = |done: &Done| status(done, "base").0;
        assert_eq!(base(&job), Status::Rejected);
        let done = compared(&fixture);
        for (unit, theorem) in [("comparator", M), ("comparator/t", T)] {
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
            for unit in ["comparator", "comparator/t"] {
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
        assert_eq!(status(&done, "comparator"), (Status::Verified, None));
        assert_eq!(runs(&done), [run_of("comparator", "C0")]);
    }

    #[test]
    fn without_a_qualification_receipt_of_the_run_the_part_is_a_tool_failure() {
        let fixture = checkout("comparator-alone", &[COUNTER], json!({}));
        let runs_of = fixture.root().join(run::RUNS);
        let stopped = |done: &Done, problem: &str| {
            let message = format!("the phase comparator stopped: {problem}");
            assert_eq!(done.failures(), [message.as_str()]);
            let receipt = done.written();
            assert_eq!(
                (receipt.status, receipt.complete),
                (Status::ToolFailure, false)
            );
            for unit in ["comparator", "comparator/t"] {
                assert_eq!(status(done, unit), (Status::NotRun, Some(message.as_str())));
            }
            assert!(runs(done).is_empty());
        };
        let none = format!("{} has no qualification receipt", runs_of.display());
        stopped(&compared(&fixture), &none);
        // A receipt of the job of another run of CI, or of another commit.
        let job = job(&fixture);
        let original = fs::read(job.run.receipt()).expect("the receipt");
        edit(&job, |receipt| {
            receipt.trigger.run_id = Some("7".to_string())
        });
        stopped(&compared(&fixture), &none);
        fs::write(job.run.receipt(), &original).expect("restore the receipt");
        fixture.write("README.md", "moved\n");
        fixture.commit_all();
        stopped(&compared(&fixture), &none);
        // One of the commit without a base round.
        let job = self::job(&fixture);
        edit(&job, |receipt| receipt.base = None);
        stopped(
            &compared(&fixture),
            &format!("the run {} has no base round", job.run.id),
        );
    }

    #[test]
    fn the_runs_directory_of_the_variable_holds_the_stage() {
        let fixture = checkout("comparator-runs", &[COUNTER], json!({}));
        let job = job(&fixture);
        let elsewhere = fixture.root().join("artifacts/elsewhere");
        fs::create_dir_all(&elsewhere).expect("create the directory");
        fs::rename(&job.run.path, elsewhere.join(&job.run.id)).expect("move the run");
        let done = comparator_part(&fixture, &LAYOUT, Some(&elsewhere));
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
        // Without it, the runs directory of the checkout has no such receipt.
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
        let done = comparator_part(&fixture, &CALIBRATION, None);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        // They conclude no unit.
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(Vec::from_iter(receipt.units.keys()), ["comparator/t"]);
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
        let done = comparator_part(&fixture, &CALIBRATION, None);
        assert_eq!(
            runs(&done),
            [run_of("comparator", "C0"), run_of("comparator/t", "C1")]
        );
    }
}
