//! The base round of `cargo xtask formal run`, as "Base round" in
//! `docs/formal-verification.md` describes it: the hand-written Lean of the
//! snapshot, with the generated modules of the proof cases of the
//! qualification, built in a stage of its own from a generated root module,
//! audited, replayed by `leanchecker` and counted in heartbeats. Its units
//! are `base` and one for each proved statement of `statements.json`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use super::Layout;
use super::guard::{self, State, Statement, Statements};
use super::lean::{self, Kind, Sources};
use super::outcome::{Class, Site, Status};
use super::process::Ran;
use super::qualify::{self, conclusion, lake};
use super::registry::{self, declared_axioms};
use super::run::{self, Gate, Phase, Request};
use super::toolchain::sha256;

/// The name of the phase, and the first part of the name of its units.
pub const PHASE: &str = "base";

/// The record of the base round in the receipt: the registries, the
/// statement hash, the modules that the root imports, those whose messages
/// decide a failed build and those built without `--wfail`, each audited or
/// registered theorem, `leanchecker`, the heartbeats and the problems.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Record {
    pub statements_sha256: String,
    pub axioms_sha256: String,
    pub tcb_sha256: String,
    pub statement_hash: Hash,
    pub modules: Vec<String>,
    pub own: Vec<String>,
    pub planned: Vec<String>,
    pub theorems: BTreeMap<String, Theorem>,
    pub leanchecker: Leanchecker,
    pub heartbeats: Heartbeats,
    pub problems: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hash {
    pub recorded: String,
    pub computed: String,
}

/// A theorem: its axioms when it was audited, and its conclusion.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Theorem {
    pub module: String,
    pub kind: Kind,
    pub state: Option<State>,
    pub axioms: Option<Vec<String>>,
    pub status: Status,
    pub problems: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Leanchecker {
    pub version: Option<String>,
    pub sha256: String,
    pub mode: String,
    pub prefixes: Vec<String>,
}

/// The heartbeats of each theorem, and why a file or a theorem has none.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Heartbeats {
    pub method: String,
    pub counts: BTreeMap<String, u64>,
    pub missing: BTreeMap<String, String>,
}

/// The unit of the statement that `theorem` proves.
pub fn unit(theorem: &str) -> String {
    format!("{PHASE}/{theorem}")
}

/// The base round, with the statements of `statements.json` of the checkout
/// `root`, which is clean at the start of the run, for its units. The phase
/// stops when that file cannot be read, or differs from the export's.
pub fn phase<'a>(root: &Path, layout: &'a Layout) -> Phase<'a> {
    let path = layout.statements;
    let read = read(&root.join(path))
        .and_then(|text| Ok((guard::load_statements(&text, layout)?, text)))
        .map_err(|error| format!("cannot read {path}: {error}"));
    let proved = (read.iter().flat_map(|(file, _)| &file.statements))
        .filter(|statement| statement.state == State::Proved);
    let units = [PHASE.to_string()].into_iter();
    Phase {
        name: PHASE.to_string(),
        budget: Duration::from_secs(3_600),
        units: units.chain(proved.map(|s| unit(&s.theorem))).collect(),
        body: Box::new(move |gate| {
            let (statements, text) = read?;
            round(gate, &statements, &text)
        }),
    }
}

/// The text of `path`, or why it cannot be read.
pub fn read(path: &Path) -> Result<String, String> {
    fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))
}

/// Writes `text` to `path`, with its directories.
fn write(path: &Path, text: &str) -> Result<(), String> {
    let at = |error: std::io::Error| format!("{}: {error}", path.display());
    fs::create_dir_all(path.parent().unwrap_or(path)).map_err(at)?;
    fs::write(path, text).map_err(at)
}

/// Runs `request` as a command of `base` whose files `read` reads, unless
/// `stop` says why it does not start; a command that did not end by itself
/// stops the later ones.
fn step<T>(
    gate: &mut Gate,
    stop: &mut Option<String>,
    request: &Request,
    read: impl FnMut(&Ran) -> Result<T, String>,
) -> (Class, String, Option<T>) {
    if let Some(reason) = stop {
        gate.skip(PHASE, request, reason);
        return (Class::NotRun, String::new(), None);
    }
    let (ran, verdict, value) = gate.run(PHASE, request, read);
    if [Class::ToolFailure, Class::Budget, Class::NotRun].contains(&verdict.class) {
        *stop = Some(format!("{} before it did not finish", request.program));
    }
    let output = ran.map(|ran| ran.output).unwrap_or_default();
    (verdict.class, output, value)
}

/// Runs the base round on `statements`, read from the checkout as `text`.
/// An error is an internal error of the gate, which stops the phase.
fn round(gate: &mut Gate, statements: &Statements, text: &str) -> Result<(), String> {
    let (layout, source, work) = (*gate.layout(), gate.source(), gate.work().join(PHASE));
    let input = |path: &str| read(&source.join(path));
    if input(layout.statements)? != text {
        let path = layout.statements;
        return Err(format!("{path} differs from the one read at the start"));
    }
    let (axioms, tcb) = (input(layout.axioms)?, input(layout.tcb)?);
    let mut sources = Sources {
        registry: lean::load_axioms(&axioms).map_err(|e| format!("{}: {e}", layout.axioms))?,
        tcb: lean::load_tcb(&tcb).map_err(|error| format!("{}: {error}", layout.tcb))?,
        ..Sources::default()
    };
    let installation = gate.installation()?;
    // No command may write the library, with its packages, or Lean.
    let read_only = [installation.backend(), installation.lean_bin().join("..")];
    let listing = lean::listing(&read_only, None)?;
    let checker = installation.lean_bin().join("leanchecker");
    let checker = fs::read(&checker).map_err(|e| format!("{}: {e}", checker.display()))?;
    let mut record = Record {
        statements_sha256: sha256(text.as_bytes()),
        axioms_sha256: sha256(axioms.as_bytes()),
        tcb_sha256: sha256(tcb.as_bytes()),
        ..Record::default()
    };
    // The statement hash, and the file and source rules of the Lean files,
    // of which only module files named as modules reach the stage.
    let commit = gate.receipt.commit.clone().unwrap_or_default();
    fs::create_dir_all(&work).map_err(|error| format!("{}: {error}", work.display()))?;
    let (computed, tracked) = guard::statement_hash(gate, &commit, &layout, &work)?;
    let (recorded, mut problems) = (statements.hash.clone(), Vec::new());
    if computed != recorded {
        let side = format!("the statement side of the snapshot is {computed}");
        problems.push(format!("{} records {recorded}, {side}", layout.statements));
    }
    record.statement_hash = Hash { recorded, computed };
    let (stage, export) = (work.join("stage"), source.join(layout.project));
    let pins = source.join(layout.root_project);
    let project = lean::create_stage(&export, &pins, &stage, &installation.backend())?;
    let (mut files, mine) = (Vec::new(), format!("{}/", layout.namespace));
    for (path, entry) in tracked.iter().filter(|(path, _)| path.ends_with(".lean")) {
        let file = &path[layout.project.len() + 1..];
        if entry.mode == "120000" {
            problems.push(format!("{path} is a symbolic link"));
            continue;
        }
        let text = input(path)?;
        problems.extend(lean::source_problems(path, &text, &sources.tcb, &layout));
        let named = qualify::is_module(&file.trim_end_matches(".lean").replace('/', "."));
        problems.extend((!named).then(|| format!("{path} does not name a Lean module")));
        if named && guard::header_imports(&lean::tokens(&text)).0 && file.starts_with(&mine) {
            lean::copy_into(&export, &project, file)?;
            files.push(file.to_string());
        }
    }
    gate.handwritten.clone_from(&files);
    // The generated modules of each proof case whose generated code built,
    // and the declarations of the case by its proof and external modules,
    // when its proofs are in this project.
    let (mut cases, mut missing) = (BTreeMap::new(), Vec::new());
    let qualification = gate.receipt.qualification.clone().unwrap_or_default();
    let here = layout.project == layout.root_project;
    for case in qualify::load_cases(&input(layout.cases)?, &layout)?
        .into_iter()
        .filter(|_| here)
    {
        let Some(proof) = &case.proof else { continue };
        let unit = qualify::unit(&case.name);
        let mut commands = (gate.receipt.commands.iter()).filter(|c| c.unit == Some(unit.clone()));
        let build = commands.find(|command| command.site == Site::QualificationBuild);
        let built = build.is_some_and(|build| build.class == Class::Passed);
        let Some(case_record) = qualification.cases.get(&case.name).filter(|_| built) else {
            missing.push((unit.clone(), format!("{unit} did not build its code")));
            continue;
        };
        let from = qualify::case_stage(gate, &case.name).join(layout.root_project);
        // The templates were installed under the names of their reviewed files.
        for file in (case_record.generated.keys()).map(|file| file.replace("_Template", "")) {
            lean::copy_into(&from, &project, &file)?;
            (sources.declared).extend(declared_axioms(&read(&project.join(&file))?));
            files.push(file);
        }
        let external = |name| format!("{}.{}.{name}", layout.generated, case.module);
        let externals = (case.models.iter()).flat_map(|_| ["FunsExternal", "TypesExternal"]);
        let modules = externals.map(external).chain([proof.module.clone()]);
        cases.extend(modules.map(|module| (module, case_record.declarations.clone())));
    }
    // The generated modules of each target that the run extracted, whose
    // definitions type-check, as its stage holds them, and what the theorems
    // of its proof modules may use beyond the registry of library axioms:
    // the declarations of its templates and its trusted axioms.
    let mut targets = BTreeMap::new();
    let mut registered = Vec::new();
    if !gate.receipt.proof_targets.is_empty() {
        let text = input(layout.registry)?;
        let read = registry::parse(&text).map_err(|e| format!("{}: {e}", layout.registry))?;
        registered = read.targets;
    }
    for (name, target) in gate.receipt.proof_targets.clone() {
        let lacks = format!("the target {name} has no generated definitions that type-check");
        if !target.typed {
            missing.push((target.unit.unwrap_or(PHASE.to_string()), lacks));
            continue;
        }
        let from = run::target_project(gate, &name);
        for file in (target.generated.keys()).map(|file| file.replace("_Template", "")) {
            lean::copy_into(&from, &project, &file)?;
            (sources.declared).extend(declared_axioms(&read(&project.join(&file))?));
            files.push(file);
        }
        let own = (registered.iter()).filter(|registered| registered.name == name);
        let trusted = own.flat_map(|registered| &registered.trusted_axioms);
        let mut allowed = target.declarations.clone();
        allowed.extend(trusted.map(|axiom| axiom.name.clone()));
        targets.extend((target.proof_modules.into_iter()).map(|m| (m, allowed.clone())));
    }
    // A case whose commands force its conclusion forces the round's.
    let forced = |unit: &&String| {
        let mut commands = (gate.receipt.commands.iter()).filter(|c| c.unit.as_ref() == Some(unit));
        commands.any(|command| matches!(command.class, Class::ToolFailure | Class::Budget))
    };
    let first = missing
        .iter()
        .find(|(unit, _)| forced(&unit))
        .or(missing.first())
        .cloned();
    let missing = first.as_ref().map(|(unit, _)| unit.clone());
    // The modules of the stage, krepi's own and those of planned statements.
    let modules = (files.iter()).map(|file| file.trim_end_matches(".lean").replace('/', "."));
    let modules = BTreeSet::from_iter(modules);
    let mine = format!("{}.", layout.namespace);
    let own = (modules.iter()).filter(|m| m.starts_with(&mine) || cases.contains_key(*m));
    let own: Vec<String> = own.cloned().collect();
    let (proved, planned): (Vec<&Statement>, Vec<&Statement>) =
        (statements.statements.iter()).partition(|statement| statement.state == State::Proved);
    let planned: BTreeSet<&String> = planned.into_iter().map(|planned| &planned.module).collect();
    let absent = planned.iter().filter(|module| !modules.contains(**module));
    problems.extend(absent.map(|module| format!("the planned module {module} has no file")));
    let root = project.join(lean::module_file(layout.namespace));
    write(&root, &lean::root_source(&modules))?;
    // The builds: all but the planned modules with `--wfail`, then the root.
    // A build that failed, or a kernel report of `leanchecker`, stops every
    // theorem from being checked.
    gate.own = own.clone();
    let mut inherited = Vec::from_iter(first.map(|(_, why)| why));
    let mut stop = inherited.first().cloned();
    let root = format!("+{}", layout.namespace);
    let unplanned = (modules.iter()).filter(|module| !planned.contains(module));
    let unplanned = unplanned.map(|module| format!("+{module}")).collect();
    let mut builds = vec![(unplanned, true), (vec![root.clone()], false)];
    if planned.is_empty() {
        builds = vec![(vec![root], true)];
    }
    for (targets, wfail) in builds {
        let args = lean::build_args(&targets, wfail);
        let build = lake(Site::BaseBuild, &args, &project);
        let (class, output, _) = step(gate, &mut stop, &build, |_| Ok(()));
        let at = lean::proof_messages(&output, &own).into_iter();
        let at = at.map(|(m, l, c)| format!("{}:{l}:{c}", lean::module_file(m)));
        let at: Vec<String> = at.collect();
        if class == Class::ProofFailure {
            inherited.push(format!("the base build failed: {}", at.join(", ")));
            stop = Some("the base build did not pass".to_string());
        } else if class == Class::Passed && !wfail {
            let files: Vec<String> = planned.iter().map(|m| lean::module_file(m)).collect();
            let other = lean::planned_problems(&output, &files).into_iter();
            let message = "a planned module has a message other than declaration uses `sorry`";
            problems.extend(other.map(|line| format!("{message}: {line}")));
        }
    }
    // The audit, `leanchecker` with each prefix, and the version of Lean.
    let audit = lean::audit_source(layout.namespace, &statements.statements, &own);
    write(&project.join(lean::AUDIT), &audit)?;
    let args = lean::check_args(lean::AUDIT);
    let request = lake(Site::AxiomAudit, &args, &project);
    let (class, output, _) = step(gate, &mut stop, &request, |_| Ok(()));
    let ended = matches!(class, Class::Passed | Class::ProofFailure);
    let audit = ended.then(|| lean::audit_output(&output));
    let prefixes = [layout.namespace, layout.generated];
    for prefix in prefixes {
        let args = ["env", "leanchecker", prefix].map(str::to_string);
        let request = lake(Site::Leanchecker, &args, &project);
        let (class, output, _) = step(gate, &mut stop, &request, lean::leanchecker_read);
        if class == Class::ProofFailure {
            let lines: Vec<&str> = output.lines().map(str::trim).collect();
            inherited.push(format!("leanchecker {prefix}: {}", lines.join(" ")));
        }
    }
    problems.extend(inherited.iter().cloned());
    let args = ["--version".to_string()];
    let mut version = lake(Site::Leanchecker, &args, &project);
    version.program = "lean";
    let checked = &mut record.leanchecker;
    checked.version = step(gate, &mut stop, &version, lean::lean_version).2;
    (checked.sha256, checked.mode) = (sha256(&checker), "prefix".to_string());
    checked.prefixes = prefixes.map(str::to_string).into();
    // The heartbeats of the theorems of each own file, which decide nothing.
    let counted = &mut record.heartbeats;
    counted.method = "count_heartbeats".to_string();
    let mut ranges: BTreeMap<&String, Vec<(String, usize)>> = BTreeMap::new();
    let audited = audit.iter().flat_map(|audit| &audit.ranges);
    for (name, (module, line)) in audited.filter(|(_, (module, _))| own.contains(module)) {
        (ranges.entry(module).or_default()).push((name.clone(), *line));
    }
    for (module, at) in ranges {
        let file = lean::module_file(module);
        let (copy, inserted) = lean::heartbeat_copy(&read(&project.join(&file))?, &at);
        let left = (at.iter()).filter(|(name, _)| !inserted.values().any(|n| n == name));
        let why = "its declaration range starts inside another command";
        (counted.missing).extend(left.map(|(name, _)| (name.clone(), why.to_string())));
        let copied = format!(".heartbeats/{file}");
        write(&project.join(&copied), &copy)?;
        let args = ["env", "lean", "--json", &copied].map(str::to_string);
        let request = lake(Site::AxiomAudit, &args, &project);
        let (class, output, _) = step(gate, &mut stop, &request, |_| Ok(()));
        if class == Class::Passed {
            counted.counts.extend(lean::heartbeats(&output, &inserted));
        } else if class == Class::ProofFailure {
            let error = output.lines().find(|line| line.contains("error"));
            (counted.missing).insert(file, error.unwrap_or_default().to_string());
        }
    }
    // The audit's judgment: the axioms of each theorem by the kind of its
    // module, the markers, the statements and the modules that define them.
    let mut theorems = BTreeMap::<String, Theorem>::new();
    let proofs = format!("{}.", layout.proofs);
    if let Some(audit) = &audit {
        let unmarked = own.iter().filter(|module| !audit.modules.contains(*module));
        problems.extend(unmarked.map(|module| format!("the audit has no marker of {module}")));
        let examples = lean::FIRST_EXAMPLE..lean::FIRST_EXAMPLE + proved.len();
        let other = (audit.errors.iter()).filter(|(line, _)| !examples.contains(*line));
        problems.extend(other.map(|(_, errors)| errors.join(" ")));
        sources.native.clone_from(&audit.native);
        for (name, (module, axioms)) in &audit.theorems {
            let theorem = theorems.entry(name.clone()).or_default();
            let case = cases.get(module);
            theorem.kind = match case {
                Some(_) => Kind::Qualification,
                None if module.starts_with(&proofs) => Kind::Target,
                None => Kind::Specification,
            };
            let mut sources = sources.clone();
            sources.case = case.cloned().unwrap_or_default();
            sources
                .registry
                .extend(targets.get(module).into_iter().flatten().cloned());
            let rejected = (axioms.iter()).filter(|a| !lean::allows(theorem.kind, a, &sources));
            theorem.problems = Vec::from_iter(rejected.map(|a| format!("{name} depends on {a}")));
            (theorem.module, theorem.axioms) = (module.clone(), Some(axioms.clone()));
        }
    }
    for statement in &statements.statements {
        let (name, module) = (&statement.name, &statement.module);
        let theorem = theorems.entry(statement.theorem.clone()).or_default();
        (theorem.state, theorem.status) = (Some(statement.state), Status::NotRun);
        theorem.module.clone_from(module);
        let at = (proved.iter()).position(|proved| proved.theorem == statement.theorem);
        let (Some(audit), Some(at)) = (&audit, at) else {
            continue;
        };
        let problems = &mut theorem.problems;
        if (audit.theorems.get(&statement.theorem)).is_none_or(|(found, _)| found != module) {
            problems.push(format!("the audit did not report it in {module}"));
        }
        // The type of the theorem must be the statement itself, which an
        // `example` with a coercion or an instance of the proofs would not check.
        let (defined, exact) = audit.statements.get(name).cloned().unwrap_or_default();
        if !exact || audit.errors.contains_key(&(lean::FIRST_EXAMPLE + at)) {
            problems.push(format!("its type is not the statement {name}"));
        }
        if defined.is_none_or(|found| found.starts_with(&proofs) || !own.contains(&found)) {
            let outside = format!("a module of krepi outside {}", layout.proofs);
            problems.push(format!("the statement {name} is not defined in {outside}"));
        }
    }
    // The conclusions: from a case whose generated code did not build, or
    // from the round, whose problems hold those of unregistered theorems.
    let unregistered = (theorems.values()).filter(|theorem| theorem.state.is_none());
    problems.extend(unregistered.flat_map(|theorem| theorem.problems.clone()));
    let of = missing.unwrap_or(PHASE.to_string());
    let base = gate.conclude_from(PHASE, &of, conclusion(&problems));
    let checked = (theorems.iter_mut()).filter(|(_, t)| t.state != Some(State::Planned));
    let forced = matches!(base, Status::ToolFailure | Status::Budget);
    for (name, theorem) in checked {
        theorem.problems.extend(inherited.iter().cloned());
        let status = conclusion(&theorem.problems);
        theorem.status = match theorem.state {
            Some(_) => gate.conclude_from(&unit(name), &of, status),
            None if forced => base,
            None => status.0,
        };
    }
    record.modules = modules.into_iter().collect();
    record.planned = planned.into_iter().cloned().collect();
    (record.own, record.theorems, record.problems) = (own, theorems, problems);
    gate.receipt.base = Some(record);
    lean::listing(&read_only, Some(&listing)).map(|_| ())
}

#[cfg(test)]
mod tests {
    //! The base round runs after the qualification of the case `arithmetic`
    //! in a fixture of `fixture.rs`, whose stand-ins answer for Lake, `lean`
    //! and `leanchecker`, with a statement side, two proof files, the
    //! registries and the statement `S`, proved by `Krepi.Proofs.Counter.t`.
    //! The texts of the measured forms are what the pinned Lean 4.35.0
    //! printed for the same files (`fixtures/base/`), with the modules of
    //! the fixture.

    use std::collections::BTreeSet;
    use std::path::PathBuf;
    use std::process::{Command, ExitCode};

    use serde_json::{Value, json};

    use super::*;
    use crate::formal::fixture::{
        self, Fixture, MUL_MOD, arithmetic, commands, lake_script, status,
    };
    use crate::formal::outcome::{conventions, word};
    use crate::formal::process::LimitBy;
    use crate::formal::run::tests::{Done, gate};

    const LAYOUT: Layout = Layout::PRODUCTION;

    const S: &str = "Krepi.Statements.Counter.S";
    const T: &str = "Krepi.Proofs.Counter.t";

    /// The proof of `S`, whose theorem starts at line 9.
    const COUNTER: &str = "module\n\npublic import Krepi.Statements.Counter\n\n\
        namespace Krepi.Proofs.Counter\n\nopen Krepi.Statements.Counter Krepi.Spec.Counter\n\n\
        public theorem t : S := by\n  intro n\n  unfold step\n  omega\n\n\
        end Krepi.Proofs.Counter\n";

    /// A proof file without a statement, whose theorem starts at line 5.
    const MAIN: &str = "module\n\nnamespace Krepi.Proofs.Main\n\n\
        public theorem m : True := trivial\n\nend Krepi.Proofs.Main\n";

    /// The files of the stage `counter` of the captures.
    const CAPTURED: [(&str, &str); 5] = [
        (
            "Krepi/Spec/Counter.lean",
            include_str!("fixtures/base/counter/Krepi/Spec/Counter.lean"),
        ),
        (
            "Krepi/Statements/Counter.lean",
            include_str!("fixtures/base/counter/Krepi/Statements/Counter.lean"),
        ),
        (
            "Krepi/Proofs/Counter.lean",
            include_str!("fixtures/base/counter/Krepi/Proofs/Counter.lean"),
        ),
        (
            "Krepi/Proofs/Other.lean",
            include_str!("fixtures/base/counter/Krepi/Proofs/Other.lean"),
        ),
        (
            "Krepi/Proofs/Coerced.lean",
            include_str!("fixtures/base/counter/Krepi/Proofs/Coerced.lean"),
        ),
    ];

    /// The file of the captures at `path`, below `verification/`.
    fn captured(path: &str) -> &'static str {
        let found = CAPTURED.iter().find(|(file, _)| *file == path);
        found.expect("a captured file").1
    }

    /// The base fixture: the qualification of `arithmetic`, the captured
    /// specification and statements, [`COUNTER`], [`MAIN`], empty
    /// registries and the statement `S`.
    fn base(label: &str) -> Fixture {
        let fixture = fixture::qualification(label, &json!([arithmetic()]));
        for path in ["Krepi/Spec/Counter.lean", "Krepi/Statements/Counter.lean"] {
            fixture.write(&format!("verification/{path}"), captured(path));
        }
        fixture.write("verification/Krepi/Proofs/Counter.lean", COUNTER);
        fixture.write("verification/Krepi/Proofs/Main.lean", MAIN);
        fixture.write(LAYOUT.axioms, "{\"schema\": 1, \"axioms\": []}\n");
        fixture.write(LAYOUT.tcb, "{\"schema\": 1, \"items\": []}\n");
        register(&fixture, &[(S, T, "proved")]);
        fixture
    }

    /// Writes `statements.json` with `statements`, as name, theorem and
    /// state, each in the module of its theorem; [`run`] records the hash.
    fn register(fixture: &Fixture, statements: &[(&str, &str, &str)]) {
        let statements: Vec<Value> = (statements.iter())
            .map(|(name, theorem, state)| {
                let (module, _) = theorem.rsplit_once('.').expect("a theorem in a module");
                json!({"name": name, "theorem": theorem, "module": module, "state": state})
            })
            .collect();
        let file = json!({"schema": 1, "hash": "0".repeat(40), "statements": statements});
        let text = serde_json::to_string_pretty(&file).expect("JSON");
        fixture.write(LAYOUT.statements, &format!("{text}\n"));
    }

    /// The statement hash of the head of `fixture`.
    fn hash(fixture: &mut Fixture) -> String {
        let work = fixture.root().join("artifacts/guard");
        fs::create_dir_all(&work).expect("create the work directory");
        guard::statement_hash(fixture, "HEAD", &LAYOUT, &work)
            .expect("the statement hash")
            .0
    }

    /// Commits what changed, with the statement hash of the commit in
    /// `statements.json`, and runs both phases.
    fn run(fixture: &mut Fixture) -> Done {
        hashed(fixture);
        gate(fixture, &[], phases(fixture))
    }

    /// Commits what changed, with the statement hash of the commit in
    /// `statements.json`.
    fn hashed(fixture: &mut Fixture) {
        if !Fixture::git(fixture, &["status", "--porcelain"]).is_empty() {
            fixture.commit_all();
        }
        let hash = hash(fixture);
        let path = fixture.root().join(LAYOUT.statements);
        let mut file: Value =
            serde_json::from_str(&fs::read_to_string(path).expect("the statements")).expect("JSON");
        if file["hash"] != hash {
            file["hash"] = json!(hash);
            let text = serde_json::to_string_pretty(&file).expect("JSON");
            fixture.write(LAYOUT.statements, &format!("{text}\n"));
            fixture.commit_all();
        }
    }

    /// The qualification and the base round of `fixture`.
    fn phases(fixture: &Fixture) -> Vec<Phase<'_>> {
        let root = fixture.root();
        vec![qualify::phase(root, &LAYOUT), phase(root, &LAYOUT)]
    }

    /// A script of the Lake stand-in that prints `log` and exits with `code`.
    fn log(log: &str, code: i32) -> String {
        format!("cat <<'EOF'\n{log}EOF\nexit {code}\n")
    }

    /// Makes the audit report `axioms` for `theorem`, or no line for `none`.
    fn axioms(fixture: &Fixture, theorem: &str, axioms: &str) {
        fixture.write(&format!("artifacts/lake/axioms/{theorem}"), axioms);
    }

    /// The record of the base round.
    fn record(done: &Done) -> &Record {
        done.receipt.base.as_ref().expect("a base record")
    }

    /// The command lines of the unit `base`.
    fn argv(done: &Done) -> Vec<String> {
        let commands = commands(done, PHASE).into_iter();
        commands.map(|command| command.argv.join(" ")).collect()
    }

    /// The class of the command of `base` whose command line is `line`.
    fn class(done: &Done, line: &str) -> Class {
        let commands = commands(done, PHASE).into_iter();
        let found = commands
            .into_iter()
            .find(|command| command.argv.join(" ") == line);
        found.unwrap_or_else(|| panic!("no command {line}")).class
    }

    /// The project of the stage of the base round of `done`.
    fn stage(done: &Done) -> PathBuf {
        done.run.path.join("work/base/stage/verification")
    }

    /// Copies the captured shape of `arithmetic` into the fixture with
    /// `files` written into its generated directory, and makes Aeneas
    /// write it.
    fn reshape(fixture: &Fixture, files: &[(&str, &str)]) {
        let copy = fixture.root().join("artifacts/arithmetic");
        let copied = Command::new("cp")
            .arg("-R")
            .arg(fixture::captured("arithmetic"))
            .arg(&copy)
            .status();
        assert!(copied.expect("cp runs").success());
        for (file, text) in files {
            let path = format!("artifacts/arithmetic/KrepiGen/Qual/Arithmetic/{file}");
            fixture.write(&path, text);
        }
        let from = "artifacts/shapes/KrepiGen.Qual.Arithmetic.from";
        fixture.write(from, copy.to_str().expect("a UTF-8 path"));
    }

    const BUILD: &str = "lake build --no-cache --wfail +Krepi";
    const AUDIT: &str = "lake env lean Audit.lean";
    const KREPI: &str = "lake env leanchecker Krepi";
    const KREPI_GEN: &str = "lake env leanchecker KrepiGen";
    const VERSION: &str = "lean --version";

    #[test]
    fn a_passing_base_round_is_verified_and_recorded() {
        let mut fixture = base("passes");
        let done = run(&mut fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Verified);
        assert!(receipt.complete);
        assert_eq!(receipt.phases[PHASE].budget_seconds, 3_600);
        assert_eq!(status(&done, PHASE), (Status::Verified, None));
        assert_eq!(status(&done, &unit(T)), (Status::Verified, None));
        let (record, hash) = (record(&done), hash(&mut fixture));
        let file = |path: &str| fs::read(fixture.root().join(path)).expect("a registry");
        assert_eq!(record.statements_sha256, sha256(&file(LAYOUT.statements)));
        assert_eq!(record.axioms_sha256, sha256(&file(LAYOUT.axioms)));
        assert_eq!(record.tcb_sha256, sha256(&file(LAYOUT.tcb)));
        assert_eq!(
            (
                &record.statement_hash.recorded,
                &record.statement_hash.computed
            ),
            (&hash, &hash)
        );
        let own = [
            "Krepi.Proofs.Counter",
            "Krepi.Proofs.Main",
            "Krepi.Qualification.Arithmetic",
            "Krepi.Spec.Counter",
            "Krepi.Statements.Counter",
        ];
        assert_eq!(record.own, own);
        let generated = [
            "KrepiGen.Qual.Arithmetic.Funs",
            "KrepiGen.Qual.Arithmetic.Types",
        ];
        assert_eq!(record.modules, [&own[..], &generated[..]].concat());
        assert!(record.planned.is_empty() && record.problems.is_empty());
        let theorem = |module: &str, kind, state, status| Theorem {
            module: module.to_string(),
            kind,
            state,
            axioms: Some(Vec::new()),
            status,
            problems: Vec::new(),
        };
        assert_eq!(
            record.theorems,
            BTreeMap::from([
                (
                    "Krepi.Proofs.Main.m".to_string(),
                    theorem("Krepi.Proofs.Main", Kind::Target, None, Status::Verified)
                ),
                (
                    T.to_string(),
                    theorem(
                        "Krepi.Proofs.Counter",
                        Kind::Target,
                        Some(State::Proved),
                        Status::Verified
                    )
                ),
            ])
        );
        let leanchecker = &record.leanchecker;
        let version = include_str!("fixtures/base/lean-version.txt")
            .lines()
            .nth(1);
        assert_eq!(leanchecker.version.as_deref(), version);
        assert_eq!(leanchecker.sha256, sha256(b"leanchecker\n"));
        assert_eq!(leanchecker.mode, "prefix");
        assert_eq!(leanchecker.prefixes, ["Krepi", "KrepiGen"]);
        // The stage holds the hand-written files, the generated modules of
        // the case and the generated root.
        let stage = stage(&done);
        let root = fs::read_to_string(stage.join("Krepi.lean")).expect("the root");
        let modules = BTreeSet::from_iter(record.modules.iter().cloned());
        assert_eq!(root, lean::root_source(&modules));
        for module in &record.modules {
            assert!(stage.join(lean::module_file(module)).is_file(), "{module}");
        }
        let audit = fs::read_to_string(stage.join(lean::AUDIT)).expect("the audit file");
        let statements = guard::load_statements(
            &String::from_utf8(file(LAYOUT.statements)).expect("UTF-8"),
            &LAYOUT,
        );
        let statements = statements.expect("the statements").statements;
        assert_eq!(audit, lean::audit_source("Krepi", &statements, &record.own));
    }

    #[test]
    fn the_base_round_runs_its_commands_in_order() {
        let mut fixture = base("order");
        let done = run(&mut fixture);
        let heartbeats =
            |module: &str| format!("lake env lean --json .heartbeats/Krepi/Proofs/{module}.lean");
        let passing = [
            BUILD.to_string(),
            AUDIT.to_string(),
            KREPI.to_string(),
            KREPI_GEN.to_string(),
            VERSION.to_string(),
            heartbeats("Counter"),
            heartbeats("Main"),
        ];
        assert_eq!(argv(&done), passing);
        let limits: Vec<LimitBy> = (commands(&done, PHASE).into_iter())
            .map(|command| command.limit)
            .collect();
        use LimitBy::{Cap, Phase};
        assert_eq!(limits, [Phase, Cap, Phase, Phase, Phase, Cap, Cap]);
        let sites: Vec<Site> = (commands(&done, PHASE).into_iter())
            .map(|command| command.site)
            .collect();
        use Site::{AxiomAudit, BaseBuild, Leanchecker};
        assert_eq!(
            sites,
            [
                BaseBuild,
                AxiomAudit,
                Leanchecker,
                Leanchecker,
                Leanchecker,
                AxiomAudit,
                AxiomAudit
            ]
        );
        for command in commands(&done, PHASE) {
            assert_eq!(
                fixture.root().join(&command.cwd),
                stage(&done),
                "{command:?}"
            );
        }
        let git: Vec<&str> = (done.receipt.commands.iter())
            .filter(|command| command.phase.as_deref() == Some(PHASE) && command.unit.is_none())
            .map(|command| command.argv[3].as_str())
            .collect();
        // Git lists the files and writes the statement hash, one tree for each
        // directory with statement-side files, from the deepest up.
        assert_eq!(
            git,
            [
                "ls-tree", "mktree", "mktree", "mktree", "mktree", "mktree", "mktree"
            ]
        );
        // With a planned statement, every module but the planned one is
        // built with `--wfail`, then the root without it.
        fixture.write(
            "verification/Krepi/Proofs/Other.lean",
            captured("Krepi/Proofs/Other.lean"),
        );
        register(
            &fixture,
            &[
                (S, T, "proved"),
                (
                    "Krepi.Statements.Counter.W",
                    "Krepi.Proofs.Other.u",
                    "planned",
                ),
            ],
        );
        let done = run(&mut fixture);
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.receipt.units
        );
        let modules = &record(&done).modules;
        let unplanned = modules
            .iter()
            .filter(|module| *module != "Krepi.Proofs.Other");
        let first: Vec<String> = unplanned.map(|module| format!("+{module}")).collect();
        let mut planned = vec![
            lean::build_args(&first, true).join(" "),
            "build --no-cache +Krepi".to_string(),
        ];
        planned
            .iter_mut()
            .for_each(|line| *line = format!("lake {line}"));
        assert_eq!(argv(&done)[..2], planned);
        assert_eq!(record(&done).planned, ["Krepi.Proofs.Other"]);
        assert_eq!(argv(&done).len(), 9);
    }
    #[test]
    fn every_convention_has_its_class_at_the_base_round_sites() {
        // Each row of the conventions at each site of the base round that it
        // applies to, through the call site: the stand-in at that site is the
        // row's tool. The first command at the build site is build 1, at the
        // audit site the audit, which runs before the heartbeat pass, and at
        // the site of `leanchecker` `leanchecker` itself, before the version
        // query.
        let base_sites = [
            (Site::BaseBuild, BUILD),
            (Site::AxiomAudit, AUDIT),
            (Site::Leanchecker, KREPI),
        ];
        let mut fixture = base("conventions");
        assert_eq!(run(&mut fixture).receipt.status, Status::Verified);
        let (mut pairs, mut met) = (0, BTreeSet::new());
        for row in conventions::rows() {
            let program = fixture.root().join("artifacts/rows").join(row.name);
            if let Some(script) = row.script {
                let path = format!("artifacts/rows/{}", row.name);
                fixture.write(&path, &format!("#!/bin/sh\n{script}\n"));
                fixture.chmod(&path, 0o755);
            }
            let program = program.to_str().expect("a UTF-8 path").to_string();
            for (site, first) in base_sites
                .iter()
                .filter(|(site, _)| row.sites.contains(site))
            {
                let (site, context) = (*site, format!("{} at {}", row.name, word(site)));
                pairs += 1;
                met.insert(site);
                let set = (row.limit, program.clone());
                let mut phases = phases(&fixture);
                let base = phases.pop().expect("the base round");
                let body = base.body;
                phases.push(Phase {
                    body: Box::new(move |gate: &mut Gate| {
                        gate.overrides = Some((site, set.0, set.1));
                        body(gate)
                    }),
                    ..base
                });
                let done = gate(&fixture, &[], phases);
                let commands = commands(&done, PHASE);
                let at = (commands.iter()).position(|command| command.site == site);
                let at = at.unwrap_or_else(|| panic!("{context}: no command at the site"));
                // The program is the row's, the arguments the call site's.
                let (_, args) = first.split_once(' ').expect("a program and its arguments");
                assert_eq!(commands[at].argv[1..].join(" "), args, "{context}");
                assert_eq!(
                    commands[at].class, row.class,
                    "{context}: {:?}",
                    commands[at]
                );
                for later in &commands[at + 1..] {
                    assert_eq!(later.class, Class::NotRun, "{context}: {later:?}");
                    assert!(later.limit_seconds > 0.0, "{context}: {later:?}");
                }
                let (status, reason) = match row.class {
                    Class::ProofFailure => (
                        Status::Rejected,
                        Some("the base build failed: Krepi/Proofs/Main.lean:3:8"),
                    ),
                    Class::Budget => (Status::Budget, None),
                    _ => (Status::ToolFailure, None),
                };
                let concluded = super::tests::status(&done, PHASE);
                assert_eq!(concluded.0, status, "{context}");
                if let Some(reason) = reason {
                    assert_eq!(concluded.1, Some(reason), "{context}");
                }
                assert_eq!(super::tests::status(&done, &unit(T)).0, status, "{context}");
                assert_eq!(done.receipt.status, status, "{context}");
            }
        }
        assert_eq!(pairs, 19);
        assert_eq!(met.len(), 3);
    }

    /// The failure of a build with `--wfail` that Lean 4.35.0 printed for a
    /// warning in `module` at `at`.
    fn warned(module: &str, at: &str, message: &str) -> String {
        let file = lean::module_file(module);
        log(
            &format!(
                "\u{26a0} [1806/1806] Building {module} (1.5s)\nwarning: {file}:{at}: {message}\n\
                 Some required targets logged failures:\n- {module}\nerror: build failed\n"
            ),
            1,
        )
    }

    const SORRY: &str = "declaration uses `sorry`";

    #[test]
    fn a_sorry_in_a_proved_proof_file_fails_the_base_build() {
        let mut fixture = base("proved-sorry");
        let other = "Krepi/Proofs/Other.lean";
        fixture.write(&format!("verification/{other}"), captured(other));
        let planned = (
            "Krepi.Statements.Counter.W",
            "Krepi.Proofs.Other.u",
            "planned",
        );
        register(&fixture, &[(S, T, "proved"), planned]);
        lake_script(
            &fixture,
            "build",
            &warned("Krepi.Proofs.Counter", "10:15", SORRY),
        );
        let done = run(&mut fixture);
        let build = &commands(&done, PHASE)[0];
        assert!(build.argv.contains(&"--wfail".to_string()), "{build:?}");
        assert!(build.argv.contains(&"+Krepi.Proofs.Counter".to_string()));
        assert!(!build.argv.contains(&"+Krepi.Proofs.Other".to_string()));
        assert_eq!(build.class, Class::ProofFailure);
        let failed = "the base build failed: Krepi/Proofs/Counter.lean:10:15";
        assert_eq!(status(&done, PHASE), (Status::Rejected, Some(failed)));
        assert_eq!(status(&done, &unit(T)), (Status::Rejected, Some(failed)));
        // Nothing after the failed build starts.
        let classes = commands(&done, PHASE)
            .into_iter()
            .skip(1)
            .map(|command| command.class);
        assert!(classes.into_iter().all(|class| class == Class::NotRun));
    }

    #[test]
    fn a_sorry_on_the_statement_side_fails_the_base_build() {
        let mut fixture = base("statement-sorry");
        let statements = "Krepi.Statements.Counter";
        lake_script(&fixture, "build", &warned(statements, "8:21", SORRY));
        let done = run(&mut fixture);
        assert_eq!(argv(&done)[0], BUILD);
        assert_eq!(class(&done, BUILD), Class::ProofFailure);
        let failed = "the base build failed: Krepi/Statements/Counter.lean:8:21";
        assert_eq!(status(&done, PHASE), (Status::Rejected, Some(failed)));
        // With a planned statement, the statement side is among the targets
        // that build with `--wfail`.
        let other = "Krepi/Proofs/Other.lean";
        fixture.write(&format!("verification/{other}"), captured(other));
        let planned = (
            "Krepi.Statements.Counter.W",
            "Krepi.Proofs.Other.u",
            "planned",
        );
        register(&fixture, &[(S, T, "proved"), planned]);
        let done = run(&mut fixture);
        let build = &commands(&done, PHASE)[0];
        assert!(build.argv.contains(&format!("+{statements}")), "{build:?}");
        assert!(build.argv.contains(&"--wfail".to_string()));
        assert_eq!(build.class, Class::ProofFailure);
        assert_eq!(status(&done, PHASE), (Status::Rejected, Some(failed)));
    }

    #[test]
    fn a_planned_proof_file_with_another_warning_rejects_the_base_round() {
        let mut fixture = base("planned-warning");
        let other = "Krepi/Proofs/Other.lean";
        fixture.write(&format!("verification/{other}"), captured(other));
        let planned = (
            "Krepi.Statements.Counter.W",
            "Krepi.Proofs.Other.u",
            "planned",
        );
        register(&fixture, &[(S, T, "proved"), planned]);
        // The second form that Lean 4.35.0 printed: an unused variable in
        // another declaration of the planned file.
        let unused = "warning: Krepi/Proofs/Other.lean:10:26: Variable name `h` is not explicitly referenced.";
        let sorry = format!("warning: Krepi/Proofs/Other.lean:12:15: {SORRY}\n");
        let hint = "\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). \
            Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h\n\n\
            Note: This linter can be disabled with `set_option linter.unusedVariables false`\n";
        let built = "\u{26a0} [1806/1806] Built Krepi.Proofs.Other (4.4s)\n";
        let done_line = "Build completed successfully (1806 jobs).\n";
        let output = format!("{built}{unused}\n{hint}{sorry}{done_line}");
        lake_script(&fixture, "planned", &log(&output, 0));
        let done = run(&mut fixture);
        assert_eq!(class(&done, "lake build --no-cache +Krepi"), Class::Passed);
        let message = "a planned module has a message other than declaration uses `sorry`";
        let problem = format!("{message}: {unused}");
        assert_eq!(
            status(&done, PHASE),
            (Status::Rejected, Some(problem.as_str()))
        );
        assert_eq!(status(&done, &unit(T)).0, Status::Verified);
        // The `sorry` warning alone is allowed.
        lake_script(
            &fixture,
            "planned",
            &log(&format!("{built}{sorry}{done_line}"), 0),
        );
        let done = run(&mut fixture);
        assert_eq!(status(&done, PHASE), (Status::Verified, None));
    }

    #[test]
    fn a_proved_theorem_that_uses_a_planned_one_fails_the_audit() {
        let mut fixture = base("uses-planned");
        let other = "Krepi/Proofs/Other.lean";
        fixture.write(&format!("verification/{other}"), captured(other));
        let (u, v) = ("Krepi.Proofs.Other.u", "Krepi.Proofs.Other.v");
        register(
            &fixture,
            &[
                (S, u, "planned"),
                ("Krepi.Statements.Counter.W", v, "proved"),
            ],
        );
        axioms(
            &fixture,
            v,
            "propext, sorryAx, Classical.choice, Quot.sound",
        );
        let done = run(&mut fixture);
        let problem = format!("{v} depends on sorryAx");
        assert_eq!(
            status(&done, &unit(v)),
            (Status::Rejected, Some(problem.as_str()))
        );
        let audit = fs::read_to_string(stage(&done).join(lean::AUDIT)).expect("the audit file");
        assert!(
            audit.contains(&format!("let planned : Array Name := #[`{u}]")),
            "{audit}"
        );
        assert!(!done.receipt.units.contains_key(&unit(u)));
        let planned = &record(&done).theorems[u];
        assert_eq!(
            (planned.state, &planned.axioms, planned.status),
            (Some(State::Planned), &None, Status::NotRun)
        );
    }

    #[test]
    fn a_proved_file_that_imports_a_planned_file_fails_the_base_build() {
        let mut fixture = base("imports-planned");
        let other = "Krepi/Proofs/Other.lean";
        fixture.write(&format!("verification/{other}"), captured(other));
        let uses = "module\n\npublic import Krepi.Proofs.Other\n\nnamespace Krepi.Proofs.Uses\n\n\
            public theorem w : Krepi.Statements.Counter.S := Krepi.Proofs.Other.u\n\n\
            end Krepi.Proofs.Uses\n";
        fixture.write("verification/Krepi/Proofs/Uses.lean", uses);
        let planned = (
            "Krepi.Statements.Counter.W",
            "Krepi.Proofs.Other.u",
            "planned",
        );
        register(&fixture, &[(S, T, "proved"), planned]);
        // The replayed `sorry` of the planned file fails `--wfail`.
        let replayed = format!(
            "\u{26a0} [1806/1807] Replaying Krepi.Proofs.Other\n\
             warning: Krepi/Proofs/Other.lean:12:15: {SORRY}\n\
             \u{2714} [1807/1807] Built Krepi.Proofs.Uses (1.7s)\n\
             Some required targets logged failures:\n- Krepi.Proofs.Other\nerror: build failed\n"
        );
        lake_script(&fixture, "build", &log(&replayed, 1));
        let done = run(&mut fixture);
        let failed = "the base build failed: Krepi/Proofs/Other.lean:12:15";
        assert_eq!(status(&done, PHASE), (Status::Rejected, Some(failed)));
    }

    #[test]
    fn a_proof_file_that_nothing_imports_is_built_and_audited() {
        let mut fixture = base("lone");
        let lone = "module\n\nnamespace Krepi.Proofs.Lone\n\npublic theorem lone : True := trivial\n\n\
            end Krepi.Proofs.Lone\n";
        fixture.write("verification/Krepi/Proofs/Lone.lean", lone);
        let done = run(&mut fixture);
        assert_eq!(status(&done, PHASE), (Status::Verified, None));
        let root = fs::read_to_string(stage(&done).join("Krepi.lean")).expect("the root");
        assert!(root.starts_with("module\n\n"), "{root}");
        assert!(
            root.lines()
                .any(|line| line == "public import Krepi.Proofs.Lone"),
            "{root}"
        );
        assert_eq!(argv(&done)[0], BUILD);
        let audit = fs::read_to_string(stage(&done).join(lean::AUDIT)).expect("the audit file");
        assert!(audit.contains("`Krepi.Proofs.Lone,"), "{audit}");
        let theorem = &record(&done).theorems["Krepi.Proofs.Lone.lone"];
        assert_eq!(
            (&theorem.axioms, theorem.status),
            (&Some(Vec::new()), Status::Verified)
        );
    }

    #[test]
    fn a_lean_file_outside_the_namespaces_of_the_project_rejects_the_base_round() {
        let mut fixture = base("outside");
        fixture.write("verification/Other/Foo.lean", "module\n");
        fixture.write(
            "verification/Krepi.lean",
            "module\nimport Krepi.Proofs.Main\n",
        );
        let done = run(&mut fixture);
        let outside = "is a Lean file outside verification/Krepi/ and verification/externals/";
        let problems = [
            format!("verification/Krepi.lean {outside}"),
            format!("verification/Other/Foo.lean {outside}"),
        ];
        assert_eq!(record(&done).problems, problems);
        assert_eq!(status(&done, PHASE).0, Status::Rejected);
        // The builds still run, on the generated root.
        assert_eq!(class(&done, BUILD), Class::Passed);
        assert!(!stage(&done).join("Other/Foo.lean").exists());
        let root = fs::read_to_string(stage(&done).join("Krepi.lean")).expect("the root");
        let modules = BTreeSet::from_iter(record(&done).modules.iter().cloned());
        assert_eq!(root, lean::root_source(&modules));
    }

    /// A proof file whose theorem `t` depends on an axiom of the same file.
    const CHEAT: &str = "module\n\nnamespace Krepi.Proofs.Main\n\npublic axiom cheat : False\n\n\
        public theorem t : 1 = 2 := cheat.elim\n\nend Krepi.Proofs.Main\n";

    #[test]
    fn a_handwritten_axiom_that_proves_false_fails_the_audit() {
        let mut fixture = base("cheat");
        fixture.write("verification/Krepi/Proofs/Main.lean", CHEAT);
        let theorem = "Krepi.Proofs.Main.t";
        let cheat = "Krepi.Proofs.Main.cheat";
        axioms(
            &fixture,
            theorem,
            &format!("propext, Classical.choice, Quot.sound, {cheat}"),
        );
        let done = run(&mut fixture);
        assert_eq!(class(&done, AUDIT), Class::Passed);
        let found = record(&done);
        let problem = format!("{theorem} depends on {cheat}");
        assert_eq!(
            found.theorems[theorem].problems,
            std::slice::from_ref(&problem)
        );
        assert_eq!(found.theorems[theorem].status, Status::Rejected);
        assert!(found.problems.contains(&problem), "{:?}", found.problems);
        assert_eq!(status(&done, PHASE).0, Status::Rejected);
        // The allowlist decides: with the axiom registered, the theorem
        // passes its audit, and only the source rule rejects the round.
        let registered =
            json!({"schema": 1, "axioms": [{"name": cheat, "source": "x", "reason": "y"}]});
        fixture.write(LAYOUT.axioms, &registered.to_string());
        let done = run(&mut fixture);
        assert_eq!(
            record(&done).theorems[theorem].problems,
            Vec::<String>::new()
        );
        let scan = "verification/Krepi/Proofs/Main.lean:5: axiom".to_string();
        assert_eq!(record(&done).problems, [scan]);
    }

    #[test]
    fn an_unregistered_library_axiom_fails_the_audit() {
        let mut fixture = base("library-axiom");
        let library = "Aeneas.Std.core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec";
        let theorem = "Krepi.Proofs.Main.m";
        // As Lean wraps a long list.
        axioms(
            &fixture,
            theorem,
            &format!("propext,\n Classical.choice,\n Quot.sound,\n {library}"),
        );
        let done = run(&mut fixture);
        let found = &record(&done).theorems[theorem];
        assert_eq!(found.problems, [format!("{theorem} depends on {library}")]);
        assert_eq!(found.status, Status::Rejected);
        assert_eq!(status(&done, PHASE).0, Status::Rejected);
        let registered = json!({"schema": 1, "axioms": [{"name": library, "source": "Aeneas.Std.Slice", "reason": "y"}]});
        fixture.write(LAYOUT.axioms, &registered.to_string());
        let done = run(&mut fixture);
        assert_eq!(record(&done).theorems[theorem].status, Status::Verified);
        assert_eq!(status(&done, PHASE), (Status::Verified, None));
    }

    #[test]
    fn a_registered_theorem_that_the_audit_does_not_report_fails() {
        let mut fixture = base("unreported");
        axioms(&fixture, T, "none");
        let done = run(&mut fixture);
        let problem = "the audit did not report it in Krepi.Proofs.Counter";
        assert_eq!(status(&done, &unit(T)), (Status::Rejected, Some(problem)));
        assert_eq!(record(&done).theorems[T].axioms, None);
    }

    #[test]
    fn an_axiom_in_a_private_proof_body_fails_the_audit() {
        let mut fixture = base("private-axiom");
        let hidden = "_private.Krepi.Proofs.Counter.0.Krepi.Proofs.Counter.hidden";
        axioms(
            &fixture,
            T,
            &format!("propext,\n Classical.choice,\n Quot.sound,\n {hidden}"),
        );
        let done = run(&mut fixture);
        let problem = format!("{T} depends on {hidden}");
        assert_eq!(
            status(&done, &unit(T)),
            (Status::Rejected, Some(problem.as_str()))
        );
    }

    #[test]
    fn a_handwritten_axiom_that_matches_a_trusted_pattern_fails_the_audit() {
        let mut fixture = base("pattern");
        let prefix = "KrepiGen.Qual.Arithmetic";
        let item = json!({"kind": "axiom-pattern", "prefix": prefix, "reason": "opaque"});
        fixture.write(
            LAYOUT.tcb,
            &json!({"schema": 1, "items": [item]}).to_string(),
        );
        let forged = CHEAT.replace("axiom cheat", &format!("axiom {prefix}.forged"));
        fixture.write(
            "verification/Krepi/Proofs/Main.lean",
            &forged.replace("cheat.elim", "False.elim (by assumption)"),
        );
        let theorem = "Krepi.Proofs.Main.t";
        axioms(&fixture, theorem, &format!("propext, {prefix}.forged"));
        // The template of the case declares an axiom with the prefix, which
        // the target theorem may use.
        let template = format!("module\nnamespace {prefix}\naxiom opaque_f : Nat\nend {prefix}\n");
        reshape(&fixture, &[("FunsExternal_Template.lean", &template)]);
        axioms(&fixture, T, &format!("propext, {prefix}.opaque_f"));
        let done = run(&mut fixture);
        let found = &record(&done).theorems[theorem];
        assert_eq!(
            found.problems,
            [format!("{theorem} depends on {prefix}.forged")]
        );
        assert_eq!(status(&done, &unit(T)), (Status::Verified, None));
        let installed = stage(&done).join("KrepiGen/Qual/Arithmetic/FunsExternal.lean");
        assert_eq!(
            fs::read_to_string(installed).expect("the template"),
            template
        );
    }

    #[test]
    fn a_native_decision_axiom_of_generated_code_fails_the_audit() {
        let mut fixture = base("generated-native");
        let funs = fs::read_to_string(
            fixture::captured("arithmetic").join("KrepiGen/Qual/Arithmetic/Funs.lean"),
        );
        let funs = funs.expect("the generated file");
        let native = funs.replace(
            "end KrepiGen.Qual.Arithmetic",
            "def f : 2 ^ 10 = 1024 := by native_decide\n\nend KrepiGen.Qual.Arithmetic",
        );
        assert_ne!(native, funs);
        reshape(&fixture, &[("Funs.lean", &native)]);
        let proof = "module\n\nnamespace Krepi.Qualification.Arithmetic\n\n\
            public theorem mul_mod_spec : True := trivial\n\nend Krepi.Qualification.Arithmetic\n";
        fixture.write("verification/Krepi/Qualification/Arithmetic.lean", proof);
        let axiom = "_private.KrepiGen.Qual.Arithmetic.Funs.0.KrepiGen.Qual.Arithmetic.f._native.native_decide.ax_1_1";
        axioms(&fixture, MUL_MOD, &format!("propext,\n {axiom}"));
        let done = run(&mut fixture);
        let found = &record(&done).theorems[MUL_MOD];
        assert_eq!(
            (found.kind, found.status),
            (Kind::Qualification, Status::Rejected)
        );
        assert_eq!(found.problems, [format!("{MUL_MOD} depends on {axiom}")]);
        assert_eq!(status(&done, PHASE).0, Status::Rejected);
        let staged = fs::read_to_string(stage(&done).join("KrepiGen/Qual/Arithmetic/Funs.lean"));
        assert_eq!(staged.expect("the generated file"), native);
        // The scan reads only the checkout, which has no native decision.
        let tree = crate::repo::Tree::load(fixture.root()).expect("the checkout");
        assert_eq!(
            crate::check::lean_problems(&tree, &LAYOUT),
            Vec::<String>::new()
        );
    }

    /// The failure that `leanchecker` printed for a declaration that a
    /// metaprogram added without the kernel in `module`.
    fn kernel_report(module: &str) -> String {
        format!(
            "leanchecker found a problem in {module}\n\
             uncaught exception: while replaying declaration '{module}.bad':\n\
             (kernel) declaration type mismatch, '{module}.bad' has type\n  True\n\
             but it is expected to have type\n  False\n"
        )
    }

    /// The metaprogram that adds the theorem `bad` of `False` without the
    /// kernel, as `leanchecker` caught it.
    fn hack(module: &str, imports: &str) -> String {
        format!(
            "module\n{imports}meta import Lean\nopen Lean Elab Command in\n\
             run_cmd liftCoreM do\n  withOptions (fun o => debug.skipKernelTC.set o true) do\n    \
             addDecl (.thmDecl {{ \u{ab}name\u{bb} := `{module}.bad, levelParams := [],\n    \
             \u{ab}type\u{bb} := mkConst ``False, value := mkConst ``True.intro }})\n"
        )
    }

    #[test]
    fn a_declaration_added_without_the_kernel_in_a_proof_module_fails_leanchecker() {
        let mut fixture = base("hack-proof");
        let module = "Krepi.Proofs.Hack";
        let text = hack(module, "public import Krepi.Statements.Counter\n")
            + "namespace Krepi.Proofs.Hack\nopen Krepi.Statements.Counter in\n\
               public theorem tb : S := Krepi.Proofs.Hack.bad.elim\nend Krepi.Proofs.Hack\n";
        fixture.write("verification/Krepi/Proofs/Hack.lean", &text);
        // The checker fails only when the stage holds the file and the root
        // imports it.
        let check = format!(
            "if [ -f Krepi/Proofs/Hack.lean ] && grep -qx 'public import {module}' Krepi.lean; then\n{}fi\n",
            log(&kernel_report(module), 1)
        );
        lake_script(&fixture, "leanchecker-Krepi", &check);
        let done = run(&mut fixture);
        assert_eq!(class(&done, BUILD), Class::Passed);
        assert_eq!(class(&done, AUDIT), Class::Passed);
        assert_eq!(class(&done, KREPI), Class::ProofFailure);
        assert_eq!(class(&done, KREPI_GEN), Class::Passed);
        // No theorem is checked when the kernel rejects a declaration.
        assert_eq!(status(&done, &unit(T)).0, Status::Rejected);
        let tb = &record(&done).theorems["Krepi.Proofs.Hack.tb"];
        assert_eq!(
            (tb.axioms.as_deref(), tb.status),
            (Some(&[][..]), Status::Rejected)
        );
        let (status, reason) = status(&done, PHASE);
        assert_eq!(status, Status::Rejected);
        let reason = reason.expect("a reason");
        assert!(reason.starts_with(&format!("leanchecker Krepi: leanchecker found a problem in {module} uncaught exception: while replaying declaration '{module}.bad': (kernel) declaration type mismatch")), "{reason}");
    }

    #[test]
    fn a_declaration_added_without_the_kernel_in_an_external_declaration_fails_leanchecker() {
        let mut fixture = base("hack-external");
        let module = "KrepiGen.Qual.Arithmetic.FunsExternal";
        let mut case = arithmetic();
        case["models"] = json!("verification/externals/Qual/Arithmetic");
        fixture.write(LAYOUT.cases, &fixture::cases_text(&json!([case])));
        let reviewed = hack("KrepiGen.Qual.Arithmetic", "public import Aeneas\n");
        fixture.write(
            "verification/externals/Qual/Arithmetic/FunsExternal.lean",
            &reviewed,
        );
        let template = "module\npublic import Aeneas\nnamespace KrepiGen.Qual.Arithmetic\nend KrepiGen.Qual.Arithmetic\n";
        reshape(&fixture, &[("FunsExternal_Template.lean", template)]);
        let file = lean::module_file(module);
        let check = format!(
            "if [ -f {file} ] && grep -qx 'public import {module}' Krepi.lean; then\n{}fi\n",
            log(&kernel_report(module), 1)
        );
        lake_script(&fixture, "leanchecker-KrepiGen", &check);
        let done = run(&mut fixture);
        assert_eq!(
            status(&done, "qualification/arithmetic"),
            (Status::Verified, None)
        );
        assert!(record(&done).own.contains(&module.to_string()));
        let installed =
            fs::read_to_string(stage(&done).join(file)).expect("the external declarations");
        assert_eq!(installed, reviewed);
        assert_eq!(class(&done, KREPI), Class::Passed);
        assert_eq!(class(&done, KREPI_GEN), Class::ProofFailure);
        assert_eq!(status(&done, PHASE).0, Status::Rejected);
        assert_eq!(status(&done, &unit(T)).0, Status::Rejected);
    }

    #[test]
    fn a_recorded_statement_hash_that_was_not_updated_rejects_the_base_round() {
        let mut fixture = base("stale-hash");
        assert_eq!(status(&run(&mut fixture), PHASE), (Status::Verified, None));
        let recorded = hash(&mut fixture);
        // The definition that `S` uses changes; the statement file and
        // `statements.json` do not.
        let spec = captured("Krepi/Spec/Counter.lean").replace("n + 1", "n + 2");
        fixture.write("verification/Krepi/Spec/Counter.lean", &spec);
        fixture.commit_all();
        let computed = hash(&mut fixture);
        assert_ne!(computed, recorded);
        let done = gate(&fixture, &[], phases(&fixture));
        let problem = format!(
            "{} records {recorded}, the statement side of the snapshot is {computed}",
            LAYOUT.statements
        );
        assert_eq!(record(&done).problems, std::slice::from_ref(&problem));
        assert_eq!(
            status(&done, PHASE),
            (Status::Rejected, Some(problem.as_str()))
        );
        assert_eq!(class(&done, BUILD), Class::Passed);
        assert_eq!(class(&done, AUDIT), Class::Passed);
    }

    #[test]
    fn a_theorem_of_a_weaker_proposition_fails_its_statement() {
        // The proofs of the stage `counter` with what its audit printed:
        // `t` proves the weaker `W`, `Missing` is no statement, and `c`
        // proves `T` of the proofs, whose coercion to `W` lets the `example`
        // of `W` check. The registry refuses `P`, defined in a proof module.
        let mut fixture = base("weaker");
        for path in [
            "Krepi/Proofs/Counter.lean",
            "Krepi/Proofs/Other.lean",
            "Krepi/Proofs/Coerced.lean",
        ] {
            fixture.write(&format!("verification/{path}"), captured(path));
        }
        let w = "Krepi.Statements.Counter.W";
        let statements = [
            (S, T, "proved"),
            (
                "Krepi.Statements.Counter.Missing",
                "Krepi.Proofs.Counter.s",
                "proved",
            ),
            (w, "Krepi.Proofs.Coerced.c", "proved"),
        ];
        register(&fixture, &statements);
        let output = include_str!("fixtures/base/audit/counter.txt").split_once('\n');
        lake_script(&fixture, "audit", &log(output.expect("a capture").1, 1));
        let done = run(&mut fixture);
        assert_eq!(class(&done, AUDIT), Class::ProofFailure);
        let problem = "its type is not the statement Krepi.Statements.Counter.S";
        assert_eq!(status(&done, &unit(T)), (Status::Rejected, Some(problem)));
        let problem = format!("its type is not the statement {w}");
        assert_eq!(
            status(&done, &unit("Krepi.Proofs.Coerced.c")),
            (Status::Rejected, Some(problem.as_str()))
        );
        let missing = "Krepi.Statements.Counter.Missing";
        let problems = [
            format!("its type is not the statement {missing}"),
            format!(
                "the statement {missing} is not defined in a module of krepi outside Krepi.Proofs"
            ),
        ];
        let reason = problems.join("; ");
        assert_eq!(
            status(&done, &unit("Krepi.Proofs.Counter.s")),
            (Status::Rejected, Some(reason.as_str()))
        );
        // Leanchecker does not depend on the audit.
        assert_eq!(class(&done, KREPI), Class::Passed);
        // The stage `counter` had no `Krepi.Proofs.Main`, which this one has.
        let problems = &record(&done).problems;
        assert_eq!(problems, &["the audit has no marker of Krepi.Proofs.Main"]);
    }

    #[test]
    fn a_statement_defined_in_a_proof_module_is_rejected() {
        let mut fixture = base("statement-in-proof");
        let other = "module\n\nnamespace Krepi.Proofs.Other\n\n\
            @[expose] public def _root_.Krepi.Statements.Counter.Q : Prop := True\n\n\
            public theorem q : Krepi.Statements.Counter.Q := trivial\n\nend Krepi.Proofs.Other\n";
        fixture.write("verification/Krepi/Proofs/Other.lean", other);
        let q = "Krepi.Statements.Counter.Q";
        register(
            &fixture,
            &[(S, T, "proved"), (q, "Krepi.Proofs.Other.q", "proved")],
        );
        fixture.write(
            &format!("artifacts/lake/statements/{q}"),
            "Krepi.Proofs.Other",
        );
        let done = run(&mut fixture);
        let problem =
            format!("the statement {q} is not defined in a module of krepi outside Krepi.Proofs");
        assert_eq!(
            status(&done, &unit("Krepi.Proofs.Other.q")),
            (Status::Rejected, Some(problem.as_str()))
        );
        assert_eq!(status(&done, &unit(T)), (Status::Verified, None));
        // Nor may a statement lie in a module that krepi did not write.
        let generated = "KrepiGen.Qual.Arithmetic.Funs";
        fixture.write(&format!("artifacts/lake/statements/{S}"), generated);
        let done = run(&mut fixture);
        let problem =
            format!("the statement {S} is not defined in a module of krepi outside Krepi.Proofs");
        assert_eq!(
            status(&done, &unit(T)),
            (Status::Rejected, Some(problem.as_str()))
        );
    }

    #[test]
    fn a_non_module_lean_file_rejects_the_base_round() {
        let mut fixture = base("not-a-module");
        fixture.write(
            "verification/Krepi/Proofs/Plain.lean",
            "theorem p : True := trivial\n",
        );
        fixture.write("verification/Krepi/Proofs/foo-bar.lean", MAIN);
        // What the pinned Lake printed for a root that imports either file,
        // which no module of krepi would explain.
        let build = "if grep -q Plain Krepi.lean; then\n\
            echo 'error: Krepi.lean:1:0: cannot import non-`module` Krepi.Proofs.Plain from `module`'\n\
            echo 'error: build failed'; exit 1\nfi\n\
            if grep -q foo Krepi.lean; then\n\
            echo \"error: Krepi.lean: bad import 'Krepi.Proofs.foo'\"; echo 'error: build failed'; exit 1\nfi\n";
        lake_script(&fixture, "build", build);
        let done = run(&mut fixture);
        let problems = [
            "verification/Krepi/Proofs/Plain.lean is not a module file: its header has no `module`",
            "verification/Krepi/Proofs/foo-bar.lean does not name a Lean module",
        ];
        assert_eq!(record(&done).problems, problems);
        assert_eq!(status(&done, PHASE).0, Status::Rejected);
        // Neither reaches the stage or the root, so the build passes.
        assert_eq!(class(&done, BUILD), Class::Passed);
        for file in ["Plain.lean", "foo-bar.lean"] {
            assert!(!stage(&done).join("Krepi/Proofs").join(file).exists());
        }
    }

    #[test]
    fn a_lean_file_that_is_a_symbolic_link_rejects_the_base_round() {
        let mut fixture = base("linked");
        fixture.symlink("verification/Krepi/Proofs/Link.lean", "Main.lean");
        let done = run(&mut fixture);
        let problem = "verification/Krepi/Proofs/Link.lean is a symbolic link";
        assert_eq!(record(&done).problems, [problem]);
        assert!(!stage(&done).join("Krepi/Proofs/Link.lean").exists());
        assert!(
            !record(&done)
                .modules
                .contains(&"Krepi.Proofs.Link".to_string())
        );
    }

    #[test]
    fn a_qualification_tool_failure_forces_the_base_round() {
        let mut fixture = base("charon-killed");
        fixture.tool("charon", "kill -9 $$");
        let done = run(&mut fixture);
        assert_eq!(
            status(&done, "qualification/arithmetic").0,
            Status::ToolFailure
        );
        assert_eq!(status(&done, PHASE).0, Status::ToolFailure);
        assert_eq!(status(&done, &unit(T)).0, Status::ToolFailure);
        for command in commands(&done, PHASE) {
            let reason = "not started: qualification/arithmetic did not build its code";
            assert_eq!(
                (command.class, command.reason.as_deref()),
                (Class::NotRun, Some(reason))
            );
        }
        assert_eq!(argv(&done)[..2], [BUILD, AUDIT]);
    }

    #[test]
    fn a_proof_case_that_a_tool_failure_forced_decides_before_a_rejected_one() {
        // `arithmetic` does not build its generated code, as a case may;
        // Charon is killed on `second`, which comes after it.
        let mut fixture = base("two-cases");
        let mut second = fixture::case("second", "Qual.Second", "translated");
        let theorem = "Krepi.Qualification.Second.s";
        second["proof"] = json!({"module": "Krepi.Qualification.Second", "theorems": [theorem]});
        fixture.write(
            LAYOUT.cases,
            &fixture::cases_text(&json!([arithmetic(), second])),
        );
        let proof = "module\n\nnamespace Krepi.Qualification.Second\n\npublic theorem s : True := trivial\n\n\
            end Krepi.Qualification.Second\n";
        fixture.write("verification/Krepi/Qualification/Second.lean", proof);
        let module = "KrepiGen.Qual.Arithmetic.Funs";
        let error = "error: KrepiGen/Qual/Arithmetic/Funs.lean:3:8: type mismatch";
        lake_script(&fixture, module, &fixture::failing(module, &[error], 1));
        let charon = "case \"$*\" in *crate::second*) kill -9 $$ ;; esac\n\
            while [ $# -gt 0 ]; do\n  if [ \"$1\" = --dest-file ]; then : > \"$2\"; fi\n  shift\ndone";
        fixture.tool("charon", charon);
        let done = run(&mut fixture);
        assert_eq!(
            status(&done, "qualification/arithmetic").0,
            Status::Rejected
        );
        assert_eq!(status(&done, "qualification/second").0, Status::ToolFailure);
        assert_eq!(status(&done, PHASE).0, Status::ToolFailure);
        assert_eq!(status(&done, &unit(T)).0, Status::ToolFailure);
    }

    #[test]
    fn a_proof_case_whose_generated_code_did_not_build_rejects_the_base_round() {
        let mut fixture = base("case-unbuilt");
        let module = "KrepiGen.Qual.Arithmetic.Funs";
        let error = "error: KrepiGen/Qual/Arithmetic/Funs.lean:3:8: type mismatch";
        lake_script(&fixture, module, &fixture::failing(module, &[error], 1));
        let done = run(&mut fixture);
        assert_eq!(
            status(&done, "qualification/arithmetic").0,
            Status::Rejected
        );
        let reason = "qualification/arithmetic did not build its code";
        assert_eq!(status(&done, PHASE), (Status::Rejected, Some(reason)));
        assert_eq!(status(&done, &unit(T)), (Status::Rejected, Some(reason)));
        assert!(
            commands(&done, PHASE)
                .iter()
                .all(|command| command.class == Class::NotRun)
        );
    }

    #[test]
    fn a_leanchecker_that_reports_no_kernel_problem_is_a_tool_failure() {
        let mut fixture = base("checker-setup");
        for output in [
            "uncaught exception: Could not find any oleans for: Krepi\n",
            "leanchecker found a problem in Krepi.Proofs.Main\n(kernel) deep recursion detected\n",
        ] {
            lake_script(&fixture, "leanchecker-Krepi", &log(output, 1));
            let done = run(&mut fixture);
            assert_eq!(class(&done, KREPI), Class::ToolFailure, "{output}");
            assert_eq!(status(&done, PHASE).0, Status::ToolFailure, "{output}");
            assert_eq!(class(&done, KREPI_GEN), Class::NotRun);
        }
    }

    #[test]
    fn a_failed_version_query_is_a_tool_failure() {
        let mut fixture = base("version");
        for script in ["exit 1", "echo 'Lake version 5.0.0'\nexit 0"] {
            fixture.write("artifacts/lake/lean.sh", script);
            let done = run(&mut fixture);
            assert_eq!(class(&done, VERSION), Class::ToolFailure, "{script}");
            assert_eq!(status(&done, PHASE).0, Status::ToolFailure, "{script}");
            assert_eq!(record(&done).leanchecker.version, None);
        }
    }

    #[test]
    fn the_receipt_holds_the_heartbeats_of_each_declaration() {
        let mut fixture = base("heartbeats");
        let done = run(&mut fixture);
        let heartbeats = &record(&done).heartbeats;
        assert_eq!(heartbeats.method, "count_heartbeats");
        // The stand-in counts ten per line of the inserted command, which
        // comes before the line of each declaration.
        let counts = [(T.to_string(), 90), ("Krepi.Proofs.Main.m".to_string(), 50)];
        assert_eq!(heartbeats.counts, BTreeMap::from(counts));
        assert!(heartbeats.missing.is_empty());
        let copy = fs::read_to_string(stage(&done).join(".heartbeats/Krepi/Proofs/Counter.lean"));
        let copy = copy.expect("the heartbeat copy");
        assert_eq!(copy.lines().nth(8), Some("#count_heartbeats in"));
        assert_eq!(copy.replacen("#count_heartbeats in\n", "", 1), COUNTER);
    }

    #[test]
    fn a_failed_heartbeat_pass_does_not_decide_the_base_round() {
        let mut fixture = base("heartbeats-fail");
        let error = "{\"severity\":\"error\",\"data\":\"unknown constant\"}";
        lake_script(&fixture, "heartbeats", &log(&format!("{error}\n"), 1));
        let done = run(&mut fixture);
        assert_eq!(status(&done, PHASE), (Status::Verified, None));
        let missing = &record(&done).heartbeats.missing;
        let files = ["Krepi/Proofs/Counter.lean", "Krepi/Proofs/Main.lean"];
        assert_eq!(
            *missing,
            BTreeMap::from(files.map(|file| (file.to_string(), error.to_string())))
        );
        // A heartbeat command that is killed forces the round.
        lake_script(&fixture, "heartbeats", "kill -9 $$");
        let done = run(&mut fixture);
        assert_eq!(status(&done, PHASE).0, Status::ToolFailure);
        assert_eq!(argv(&done).len(), 7);
        assert_eq!(commands(&done, PHASE)[6].class, Class::NotRun);
    }

    #[test]
    fn a_tool_that_writes_the_backend_is_a_tool_failure() {
        let mut fixture = base("backend-write");
        let library = "artifacts/formal/tools/backend/.lake/build/lib/lean/Aeneas.olean";
        fixture.write(library, "olean");
        lake_script(
            &fixture,
            "build",
            "printf x >> ../artifacts/formal/lake/aeneas/.lake/build/lib/lean/Aeneas.olean",
        );
        let done = run(&mut fixture);
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        let changed = [fs::canonicalize(fixture.root().join(library)).expect("the library")];
        assert_eq!(
            done.failures(),
            [format!(
                "the phase base stopped: \
                 the tool installation changed during the phase; changed paths (1): {changed:?}"
            )]
        );
        assert!(receipt.base.is_some());
    }

    #[test]
    fn the_statements_of_the_snapshot_must_be_those_read_at_the_start() {
        let mut fixture = base("statements-changed");
        run(&mut fixture);
        // Git takes the file for unchanged, so the checkout is clean while
        // the run reads other statements than the snapshot's.
        fixture.git(&["update-index", "--skip-worktree", LAYOUT.statements]);
        let text = fs::read_to_string(fixture.root().join(LAYOUT.statements)).expect("the file");
        fixture.write(
            LAYOUT.statements,
            &text.replace("\"proved\"", "\"planned\""),
        );
        let done = gate(&fixture, &[], phases(&fixture));
        assert_eq!(done.receipt.status, Status::ToolFailure);
        let stopped = format!(
            "the phase base stopped: {} differs from the one read at the start",
            LAYOUT.statements
        );
        assert_eq!(done.failures(), [stopped]);
        assert_eq!(status(&done, PHASE).0, Status::NotRun);
    }

    /// Writes the target registry `targets`, a JSON list, and an empty
    /// registry of models.
    fn targets(fixture: &Fixture, targets: &Value) {
        let file = json!({"schema": 2, "specifications": [], "targets": targets});
        fixture.write(LAYOUT.registry, &format!("{file}\n"));
        fixture.write(LAYOUT.models, "{\"schema\": 1, \"models\": []}\n");
    }

    #[test]
    fn a_whole_run_builds_no_planned_target_and_a_run_that_names_it_does() {
        // The generated definitions of the planned target do not type-check,
        // and its kernel workspace is still virtual.
        let mut fixture = base("planned-target");
        let planned =
            json!({"name": "p", "state": "planned", "module": "P", "start_from": ["crate::f"]});
        targets(&fixture, &json!([planned]));
        let error = "error: KrepiGen/P/Funs.lean:3:8: type mismatch";
        let script = fixture::failing("KrepiGen.P.Funs", &[error], 1);
        lake_script(&fixture, "KrepiGen.P.Funs", &script);
        hashed(&mut fixture);
        let done = gate(&fixture, &[], run::tests::every_phase(fixture.root(), &[]));
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        assert!(done.receipt.complete && done.receipt.proof_targets.is_empty());
        assert_eq!(status(&done, PHASE), (Status::Verified, None));
        assert!(
            (done.receipt.commands.iter())
                .all(|c| c.site != Site::Charon || c.unit != Some(PHASE.to_string()))
        );
        // A run that names it, from a root package, builds nothing of `base`.
        run::tests::root_package(&fixture, "krepi-kernel", "");
        hashed(&mut fixture);
        let done = gate(
            &fixture,
            &["p"],
            run::tests::every_phase(fixture.root(), &["p"]),
        );
        let lacks = "the target p has no generated definitions that type-check";
        assert_eq!(status(&done, PHASE), (Status::Rejected, Some(lacks)));
        let reason =
            format!("its generated definitions do not type-check: {error} | error: build failed");
        assert_eq!(
            status(&done, "target/p"),
            (Status::Rejected, Some(reason.as_str()))
        );
    }

    #[test]
    fn the_base_round_admits_the_trusted_axioms_of_a_target_for_its_theorems() {
        // The theorem of the target depends on an axiom that only the target
        // trusts, in the audit of the base round and in that of the target.
        let mut fixture = base("trusted");
        run::tests::root_package(&fixture, "krepi-kernel", "");
        let theorem = "Krepi.Proofs.Main.m";
        axioms(&fixture, theorem, "Krepi.Extra.ax");
        let mut target = json!({
            "name": "t", "module": "T", "start_from": ["crate::f"],
            "proof_modules": ["Krepi.Proofs.Main"],
            "obligations": [{"id": "m", "theorems": [theorem]}],
        });
        targets(&fixture, &json!([target]));
        hashed(&mut fixture);
        let done = gate(&fixture, &[], run::tests::every_phase(fixture.root(), &[]));
        let depends = format!("{theorem} depends on Krepi.Extra.ax");
        assert_eq!(record(&done).theorems[theorem].problems, [depends.as_str()]);
        assert_eq!(
            status(&done, "target/t"),
            (Status::Rejected, Some(depends.as_str()))
        );
        target["trusted_axioms"] = json!([{"name": "Krepi.Extra.ax", "reason": "Reviewed."}]);
        targets(&fixture, &json!([target]));
        hashed(&mut fixture);
        let done = gate(&fixture, &[], run::tests::every_phase(fixture.root(), &[]));
        assert_eq!(done.receipt.status, Status::Verified, "{:?}", done.receipt);
        let audited = &record(&done).theorems[theorem];
        assert_eq!(
            (audited.kind, audited.status),
            (Kind::Target, Status::Verified)
        );
        assert_eq!(status(&done, "target/t"), (Status::Verified, None));
    }
}
