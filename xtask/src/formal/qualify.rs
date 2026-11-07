//! The qualification phase of `cargo xtask formal run`, the tool
//! qualification regression that "Qualification" in
//! `docs/formal-verification.md` describes.
//!
//! Each case of `verification/qualification/cases.json` is a unit: it is
//! extracted in a work directory of its own, compared with its expectation
//! and, unless it expects a rejection, built alone in a stage of its own.
//! Each theorem of a case is a unit too, built and audited in its case's
//! stage by commands of the case's unit, and may depend only on the
//! standard axioms and the generated declarations of its own case.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::{Deserialize, Serialize};

use super::Layout;
use super::extract::{self, Extraction};
use super::lean::{self, STANDARD_AXIOMS};
use super::outcome::{Class, Site, Status, Verdict};
use super::process::Ran;
use super::receipt::{self, Observed, QualificationCase, QualificationTheorem};
use super::registry::declared_axioms;
use super::run::{self, Gate, Phase};
use super::toolchain::environment::Tool;
use super::toolchain::sha256;

/// The name of the phase, and the first part of the name of its units.
pub const PHASE: &str = "qualification";

/// The schema of `cases.json` that this module reads.
pub const SCHEMA: u32 = 1;

/// The audit file of a case, in the project of its stage.
const AUDIT: &str = "Audit.lean";

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Cases {
    schema: u32,
    cases: Vec<Case>,
}

/// The outcome that the tools are expected to give a case.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Expect {
    /// Aeneas translates the shape and the generated Lean type-checks.
    Translated,
    /// Aeneas translates the shape and the generated Lean does not
    /// type-check.
    IllTyped,
    /// Aeneas rejects the shape, or leaves it partial.
    Rejected,
}

/// A case of `cases.json`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Case {
    pub name: String,
    /// The module path of the translation below the generated namespace.
    pub module: String,
    /// The items that the extraction starts from; empty for a case with
    /// parts.
    pub start_from: Vec<String>,
    /// The parts of a case whose modules are extracted one by one and
    /// imported together.
    #[serde(default)]
    pub parts: Vec<Part>,
    #[serde(default)]
    pub opaque: Vec<String>,
    pub expect: Expect,
    /// The generated file, such as `Funs.lean` or `Types.lean`, in which
    /// every type error of an ill-typed case lies.
    pub type_errors_in: Option<String>,
    /// A directory of reviewed external declarations (`TypesExternal.lean`,
    /// `FunsExternal.lean`) installed in place of the generated templates.
    pub models: Option<String>,
    pub diagnostics: Vec<String>,
    pub external_functions: Vec<String>,
    pub external_types: Vec<String>,
    /// The translated loops with their source files, when the case records
    /// them (see [`Extraction::loop_sources`]).
    pub loop_sources: Option<Vec<String>>,
    pub proof: Option<Proof>,
}

/// A part of a case: a module below the case's, with its roots.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Part {
    pub module: String,
    pub start_from: Vec<String>,
}

/// The theorems that a case proves about its translation, and their module.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Proof {
    pub module: String,
    pub theorems: Vec<String>,
}

/// The unit of the case `case`.
pub fn unit(case: &str) -> String {
    format!("{PHASE}/{case}")
}

/// The unit of the theorem `theorem` of the case `case`.
pub fn theorem_unit(case: &str, theorem: &str) -> String {
    format!("{PHASE}/{case}/{theorem}")
}

/// The units of `cases`, in their order: each case, then its theorems.
fn units(cases: &[Case]) -> Vec<String> {
    let mut units = Vec::new();
    for case in cases {
        units.push(unit(&case.name));
        for theorem in case.proof.iter().flat_map(|proof| &proof.theorems) {
            units.push(theorem_unit(&case.name, theorem));
        }
    }
    units
}

/// Whether `module` is a Lean module path of components that start with an
/// ASCII letter and hold ASCII letters, digits and `_`.
fn is_module(module: &str) -> bool {
    module.split('.').all(|component| {
        component
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic())
            && (component.chars()).all(|c| c.is_ascii_alphanumeric() || c == '_')
    })
}

/// The cases of the text `text` of `cases.json`, which must follow its
/// schema: each case has a name of its own, a module, and roots or parts;
/// an ill-typed case, and only it, records the generated file of its type
/// errors; `models` names a directory below `verification/externals`; and
/// a proof, of a translated case alone, lies below `Krepi.Qualification`
/// and names its theorems, below its module, once each.
pub fn load_cases(text: &str, layout: &Layout) -> Result<Vec<Case>, String> {
    let path = layout.cases;
    let document: Cases = serde_json::from_str(text).map_err(|error| format!("{path}: {error}"))?;
    if document.schema != SCHEMA {
        return Err(format!(
            "{path}: schema {} where {SCHEMA} is expected",
            document.schema
        ));
    }
    let mut names = BTreeSet::new();
    for case in &document.cases {
        let context = format!("{path} case {}", case.name);
        if !names.insert(case.name.as_str()) {
            return Err(format!("{context}: duplicate name"));
        }
        if let Some(problem) = case_problem(case, layout) {
            return Err(format!("{context}: {problem}"));
        }
    }
    Ok(document.cases)
}

/// Why `case` does not follow the schema of `cases.json`, if it does not.
fn case_problem(case: &Case, layout: &Layout) -> Option<String> {
    let below = |module: &str, parent: &str| module.starts_with(&format!("{parent}."));
    let word = |c: char| c.is_ascii_alphanumeric() || c == '-' || c == '_';
    let problem = if case.name.is_empty() || !case.name.chars().all(word) {
        "a case name holds only ASCII letters, digits, `-` and `_`"
    } else if !is_module(&case.module) {
        "`module` is not a Lean module path"
    } else if case.parts.is_empty() && case.start_from.is_empty() {
        "a case needs at least one root in `start_from`"
    } else if !case.parts.is_empty() && !case.start_from.is_empty() {
        "a case with `parts` has its roots in its parts"
    } else if (case.parts.iter())
        .any(|part| !is_module(&part.module) || !below(&part.module, &case.module))
    {
        "the module of a part lies below the module of its case"
    } else if case.parts.iter().any(|part| part.start_from.is_empty()) {
        "a part needs at least one root in `start_from`"
    } else if case.type_errors_in.is_none() && case.expect == Expect::IllTyped {
        "an ill-typed case records the generated file of its type errors (`type_errors_in`)"
    } else if case.type_errors_in.is_some() && case.expect != Expect::IllTyped {
        "only an ill-typed case records `type_errors_in`"
    } else if (case.type_errors_in.as_ref())
        .is_some_and(|file| file.contains('/') || !file.ends_with(".lean"))
    {
        "`type_errors_in` names a generated Lean file of the case"
    } else if (case.models.as_ref())
        .is_some_and(|models| !is_directory_below(models, layout.externals))
    {
        "`models` names a directory below the reviewed external declarations"
    } else if case.models.is_some() && !case.parts.is_empty() {
        "a case with `parts` has no `models`"
    } else if let Some(proof) = &case.proof {
        let qualification = format!("{}.Qualification", layout.namespace);
        let theorems: BTreeSet<&String> = proof.theorems.iter().collect();
        if !is_module(&proof.module) || !below(&proof.module, &qualification) {
            "the module of a proof lies below the namespace of the qualification proofs"
        } else if case.expect != Expect::Translated {
            "only a translated case has a proof"
        } else if proof.theorems.is_empty() || theorems.len() != proof.theorems.len() {
            "a proof names its theorems, each once"
        } else if (proof.theorems.iter()).any(|theorem| !below(theorem, &proof.module)) {
            "the theorems of a proof lie below its module"
        } else {
            return None;
        }
    } else {
        return None;
    };
    Some(problem.to_string())
}

/// Whether `path` names a directory below `parent`, with no empty, `.` or
/// `..` component.
fn is_directory_below(path: &str, parent: &str) -> bool {
    let plain = |rest: &str| rest.split('/').all(|part| !matches!(part, "" | "." | ".."));
    (path.strip_prefix(parent))
        .and_then(|rest| rest.strip_prefix('/'))
        .is_some_and(plain)
}

/// The distinct `items`, sorted.
fn sorted(items: &[String]) -> Vec<String> {
    let distinct: BTreeSet<&String> = items.iter().collect();
    distinct.into_iter().cloned().collect()
}

/// The Lean errors in `output` that lie in a generated file directly in the
/// directory `directory` (`KrepiGen/<case module path>/`) of a case, not in
/// that of another case below it: the definitions themselves or the type
/// definitions they import, where the kernel rejects, for example, a
/// recursive type that occurs inside an external type.
fn case_errors(output: &str, directory: &str) -> Vec<String> {
    let file = |rest: &str| rest.split(':').next().unwrap_or_default().to_string();
    let own = |line: &String| {
        line.split_once(directory)
            .is_some_and(|(_, rest)| !file(rest).contains('/'))
    };
    lean::errors(output).into_iter().filter(own).collect()
}

/// How many of `errors` lie in the generated file `file` of `directory`.
fn errors_in(errors: &[String], directory: &str, file: &str) -> usize {
    let path = format!("{directory}{file}:");
    errors.iter().filter(|line| line.contains(&path)).count()
}

/// The text installed for the generated template `kind`: the template itself,
/// or the reviewed declarations of that name from the case's `models`
/// directory below `root`, which may declare as axioms only declarations that
/// the template declares and does not use `sorry`.
fn installed_external(
    root: &Path,
    case: &Case,
    kind: &str,
    template: &str,
) -> Result<String, String> {
    let Some(directory) = &case.models else {
        return Ok(template.to_string());
    };
    let path = format!("{directory}/{kind}.lean");
    let text = fs::read_to_string(root.join(&path)).map_err(|error| format!("{path}: {error}"))?;
    let generated: BTreeSet<String> = declared_axioms(template).into_iter().collect();
    if let Some(axiom) = declared_axioms(&text)
        .into_iter()
        .find(|axiom| !generated.contains(axiom))
    {
        return Err(format!(
            "{}: {kind}.lean declares {axiom}, which is not a generated declaration",
            case.name
        ));
    }
    if text.contains("sorry") {
        return Err(format!("{}: {kind}.lean uses sorry", case.name));
    }
    Ok(text)
}

/// What `extractions`, those of a case or of each of its parts, show
/// together: complete when each is, with the diagnostics of each in order
/// and the union of their items.
fn observed(extractions: &[Extraction]) -> Observed {
    let union = |items: &dyn Fn(&Extraction) -> Vec<String>| {
        sorted(&extractions.iter().flat_map(items).collect::<Vec<_>>())
    };
    Observed {
        complete: extractions.iter().all(|extraction| extraction.complete),
        diagnostics: (extractions.iter())
            .flat_map(|extraction| extraction.diagnostics.clone())
            .collect(),
        external_functions: union(&Extraction::external_functions),
        external_types: union(&Extraction::external_types),
        loop_sources: union(&Extraction::loop_sources),
    }
}

/// The differences between what an extraction shows and its expectation.
fn differences(case: &Case, extraction: &Observed) -> Vec<String> {
    let mut problems = Vec::new();
    let translated = case.expect != Expect::Rejected;
    let outcome = |complete| match complete {
        true => "a complete translation",
        false => "a rejection",
    };
    if extraction.complete != translated {
        let (expected, got) = (outcome(translated), outcome(extraction.complete));
        problems.push(format!("expected {expected}, got {got}"));
    }
    let mut recorded = vec![
        ("diagnostics", &case.diagnostics, &extraction.diagnostics),
        (
            "external functions",
            &case.external_functions,
            &extraction.external_functions,
        ),
        (
            "external types",
            &case.external_types,
            &extraction.external_types,
        ),
    ];
    if let Some(loop_sources) = &case.loop_sources {
        recorded.push(("loop sources", loop_sources, &extraction.loop_sources));
    }
    for (what, expected, actual) in recorded {
        let (expected, actual) = (sorted(expected), sorted(actual));
        for missing in expected.iter().filter(|item| !actual.contains(item)) {
            problems.push(format!("{what}: expected but absent: {missing}"));
        }
        for extra in actual.iter().filter(|item| !expected.contains(item)) {
            problems.push(format!("{what}: present but not expected: {extra}"));
        }
    }
    problems
}

/// Installs the Lean files that `extractions` generated for `case` in the
/// project `project` of its stage, with the reviewed declarations of its
/// `models` directory below `root` in place of the templates. The
/// declarations of the templates of a case with a proof are added to
/// `declarations`. Returns, inside, the reason for which a reviewed file is
/// not installed; an error is an internal error of the gate.
fn install(
    root: &Path,
    case: &Case,
    extractions: &[Extraction],
    project: &Path,
    declarations: &mut Vec<String>,
) -> Result<Result<(), String>, String> {
    let at = |path: &Path, error: std::io::Error| format!("{}: {error}", path.display());
    for extraction in extractions {
        for file in extraction.files.keys() {
            let source = extraction.generated.join(file);
            let target = project.join(file.replace("_Template", ""));
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent).map_err(|error| at(parent, error))?;
            }
            let Some(stem) = file.strip_suffix("_Template.lean") else {
                fs::copy(&source, &target).map_err(|error| at(&source, error))?;
                continue;
            };
            let kind = stem.rsplit('/').next().unwrap_or(stem);
            let template = fs::read_to_string(&source).map_err(|error| at(&source, error))?;
            if case.proof.is_some() {
                declarations.extend(declared_axioms(&template));
            }
            match installed_external(root, case, kind, &template) {
                Ok(text) => fs::write(&target, text).map_err(|error| at(&target, error))?,
                Err(refused) => return Ok(Err(refused)),
            }
        }
    }
    Ok(Ok(()))
}

/// The complete source that audits `theorems` of the proof module `module`
/// in one Lean environment, a file that is not a module.
fn audit_source(module: &str, theorems: &[String]) -> String {
    let lines = theorems
        .iter()
        .map(|theorem| format!("#print axioms {theorem}\n"));
    format!("import {module}\n{}", lines.collect::<String>())
}

/// Why each of the `theorems` of a case whose templates declare
/// `declarations` does not pass its audit, which reported `axioms` and
/// exited with `code`. Each theorem must be reported and may depend only on
/// the standard axioms and those declarations; a theorem that was not
/// requested and a failed command fail every theorem of the case.
fn judge_case_audit(
    axioms: &BTreeMap<String, Vec<String>>,
    code: Option<i32>,
    theorems: &[String],
    declarations: &[String],
) -> BTreeMap<String, Vec<String>> {
    let unrequested = axioms.keys().filter(|theorem| !theorems.contains(theorem));
    let mut every: Vec<String> = unrequested
        .map(|theorem| format!("the case audit reported {theorem}, which was not requested"))
        .collect();
    if code != Some(0) {
        let code = code.map_or_else(|| "no status".to_string(), |code| code.to_string());
        every.push(format!("the case audit exited with {code}"));
    }
    let allowed =
        |axiom: &String| STANDARD_AXIOMS.contains(&axiom.as_str()) || declarations.contains(axiom);
    let judge = |theorem: &String| {
        let mut own: Vec<String> = match axioms.get(theorem) {
            None => vec![format!("the case audit did not report {theorem}")],
            Some(list) => (list.iter().filter(|axiom| !allowed(axiom)))
                .map(|axiom| format!("{theorem} depends on {axiom}"))
                .collect(),
        };
        own.extend(every.iter().cloned());
        (theorem.clone(), own)
    };
    theorems.iter().map(judge).collect()
}

/// Judges the build of the generated code of `case`, whose directory of
/// generated modules is `directory` (`KrepiGen/<case module path>/`):
/// a translated case must build, and an ill-typed one must exit with 1
/// with type errors only in the file that it records, every message of the
/// log naming that file but Lake's closing lines. A build that did not
/// finish by itself shows nothing about the case, whose conclusion its
/// class forces. Adds the differences and the type errors to `record`.
fn judge_build(
    case: &Case,
    directory: &str,
    verdict: &Verdict,
    ran: Option<&Ran>,
    record: &mut QualificationCase,
) {
    let output = ran.map_or("", |ran| ran.output.as_str());
    let finished = matches!(verdict.class, Class::Passed | Class::ProofFailure);
    let Some(file) = &case.type_errors_in else {
        if verdict.class == Class::ProofFailure {
            let errors = lean::errors(output).join(" | ");
            (record.differences).push(format!("the generated code does not type-check: {errors}"));
        }
        return;
    };
    let errors = case_errors(output, directory);
    let in_file = errors_in(&errors, directory, file);
    record.type_errors = ran.map(|_| receipt::TypeErrors {
        file: file.clone(),
        errors: errors.len() as u64,
        in_file: in_file as u64,
    });
    if !finished {
        return;
    }
    let differences = &mut record.differences;
    let code = ran.and_then(Ran::code);
    if verdict.class == Class::Passed {
        differences.push("the generated code was expected not to type-check".to_string());
    } else if errors.is_empty() {
        differences.push("the build reports no type error in the files of the case".to_string());
    } else if code != Some(1) {
        let code = code.map_or_else(|| "no status".to_string(), |code| code.to_string());
        differences.push(format!("the ill-typed build exited with {code}, not 1"));
    }
    if in_file != errors.len() {
        differences.push(format!(
            "expected every type error in {file}, found {in_file} of {}",
            errors.len()
        ));
    }
    // The lines with which Lake closes a failed build name no file.
    let closing = ["error: build failed", "error: Lean exited with code 1"];
    let path = format!("{directory}{file}:");
    for line in output.lines() {
        let message = line.starts_with("error:") || line.starts_with("warning:");
        if message && !closing.contains(&line.trim_end()) && !line.contains(&path) {
            differences.push(format!("a message outside {file}: {line}"));
        }
    }
}

/// The qualification phase, with the cases of `cases.json` of the checkout
/// `root`, which is clean at the start of the run, as its units. The phase
/// stops when that file cannot be read, or differs from the export's.
pub fn phase<'a>(root: &Path, layout: &'a Layout) -> Phase<'a> {
    let path = layout.cases;
    let read = fs::read_to_string(root.join(path))
        .map_err(|error| format!("cannot read {path}: {error}"))
        .and_then(|text| Ok((load_cases(&text, layout)?, text)));
    let units = read
        .as_ref()
        .map_or_else(|_| Vec::new(), |(cases, _)| units(cases));
    Phase {
        name: PHASE.to_string(),
        budget: Duration::from_secs(3_600),
        units,
        body: Box::new(move |gate| {
            let (cases, text) = read?;
            qualify(gate, &cases, &text)
        }),
    }
}

/// Qualifies `cases`, read from the checkout as `text`, in their order. An
/// error is an internal error of the gate, which stops the phase.
fn qualify(gate: &mut Gate, cases: &[Case], text: &str) -> Result<(), String> {
    let layout = *gate.layout();
    let source = gate.source();
    let read = |path: &str| {
        fs::read(source.join(path))
            .map_err(|error| format!("cannot read {path} of the export: {error}"))
    };
    if read(layout.cases)? != text.as_bytes() {
        return Err(format!(
            "{} of the snapshot is not the file that the run read at its start",
            layout.cases
        ));
    }
    let configuration = read(layout.extraction)?;
    extract::configuration(&String::from_utf8_lossy(&configuration), &layout)
        .map_err(|error| format!("{}: {error}", layout.extraction))?;
    let manifest = format!("{}/Cargo.toml", layout.qualification);
    let mut problems = extract::package_problems(&String::from_utf8_lossy(&read(&manifest)?))
        .map_err(|error| format!("{manifest}: {error}"))?;
    // Cargo runs a build script of the package without a `build` key too.
    let script = source.join(layout.qualification).join("build.rs");
    if fs::symlink_metadata(script).is_ok() {
        problems.push("its package has a build script, build.rs".to_string());
    }
    if !problems.is_empty() {
        return Err(format!("{manifest}: {}", problems.join("; ")));
    }
    let backend = gate.backend()?;
    if !backend.is_dir() {
        return Err(format!(
            "the Aeneas Lean library of the installation, {}, is not a directory",
            backend.display()
        ));
    }
    let record = gate.qualification();
    record.cases_sha256 = sha256(text.as_bytes());
    record.extraction_sha256 = sha256(&configuration);
    for case in cases {
        qualify_case(gate, &backend, case)?;
    }
    Ok(())
}

/// Extracts, compares and builds one case, and concludes it and its
/// theorems.
fn qualify_case(gate: &mut Gate, backend: &Path, case: &Case) -> Result<(), String> {
    let (layout, source) = (*gate.layout(), gate.source());
    let unit = unit(&case.name);
    let work = gate.work().join("cases").join(&case.name);
    let package = source.join(layout.qualification);
    let roots: Vec<(&str, &[String], PathBuf)> = if case.parts.is_empty() {
        vec![(&case.module, &case.start_from, work.clone())]
    } else {
        (case.parts.iter().enumerate())
            .map(|(index, part)| {
                let directory = work.join("parts").join(index.to_string());
                (part.module.as_str(), part.start_from.as_slice(), directory)
            })
            .collect()
    };
    let mut extractions = Vec::new();
    for (module, start_from, directory) in &roots {
        let request = extract::Request {
            unit: &unit,
            module,
            package: &package,
            start_from,
            opaque: &case.opaque,
            work: directory,
        };
        extractions.push(extract::extract(gate, &request)?);
    }
    let mut record = QualificationCase {
        unit: unit.clone(),
        module: case.module.clone(),
        parts: case.parts.iter().map(|part| part.module.clone()).collect(),
        expect: case.expect,
        models: case.models.clone(),
        observed: observed(&extractions),
        type_errors: None,
        differences: Vec::new(),
        generated: (extractions.iter())
            .flat_map(|extraction| extraction.files.clone())
            .collect(),
        declarations: Vec::new(),
    };
    record.differences = differences(case, &record.observed);
    let records = |gate: &mut Gate, record: &QualificationCase| {
        let cases = &mut gate.qualification().cases;
        cases.insert(case.name.clone(), record.clone());
    };
    records(gate, &record);
    let generated = format!("{}.{}", layout.generated, case.module);
    // A case with parts builds the module that imports them together.
    let leaf = if case.parts.is_empty() {
        "Funs"
    } else {
        "Check"
    };
    let target = format!("{generated}.{leaf}");
    let site = match case.expect {
        Expect::IllTyped => Site::IllTypedBuild,
        _ => Site::QualificationBuild,
    };
    let stage = work.join("stage");
    let project = stage.join(layout.project);
    let arguments = lean::build_args(&target);
    let build = lake(site, &arguments, &project);
    // Whether the generated code built, as the proofs of the case need.
    let mut built = false;
    if case.expect == Expect::Rejected {
        // Nothing of a case that is expected to be rejected is built.
    } else if !record.observed.complete {
        gate.skip(&unit, &build, "the extraction is not complete");
    } else {
        let export = source.join(layout.project);
        lean::create_stage(&export, &stage, backend)?;
        let declarations = &mut record.declarations;
        let installed = install(&source, case, &extractions, &project, declarations)?;
        if case.models.is_some() {
            copy_lean_files(
                &export,
                &project,
                &format!("{}/Qualification/Models", layout.namespace),
            )?;
        }
        if !case.parts.is_empty() {
            write_check(&project, layout.generated, case, &target)?;
        }
        if let Err(refused) = installed {
            let difference = format!("cannot install the generated files: {refused}");
            record.differences.push(difference);
            gate.skip(&unit, &build, "the generated files are not installed");
        } else {
            let (ran, verdict, _) = gate.run(&unit, &build, |_| Ok(()));
            let directory = format!("{}/", generated.replace('.', "/"));
            judge_build(case, &directory, &verdict, ran.as_ref(), &mut record);
            built = verdict.class == Class::Passed;
        }
    }
    records(gate, &record);
    if let Some(proof) = &case.proof {
        prove(gate, case, proof, &record, built, &project)?;
    }
    let (status, reason) = conclusion(&record.differences);
    gate.conclude(&unit, status, reason);
    Ok(())
}

/// The Lake command with `args` at `site`, in the project `project` of a
/// stage.
fn lake<'a>(site: Site, args: &'a [String], project: &'a Path) -> run::Request<'a> {
    let tool = match site {
        Site::CaseAudit => Tool::LakeEnvLean,
        _ => Tool::LakeBuild,
    };
    run::Request {
        site,
        tool,
        program: "lake",
        args,
        cwd: project,
        stdin: None,
    }
}

/// `VERIFIED` without `problems`, and otherwise `REJECTED` for them.
fn conclusion(problems: &[String]) -> (Status, Option<String>) {
    if problems.is_empty() {
        (Status::Verified, None)
    } else {
        (Status::Rejected, Some(problems.join("; ")))
    }
}

/// Copies the Lean files of the directory `directory` of the project
/// `export`, if it has one, into the project `project` of a stage.
fn copy_lean_files(export: &Path, project: &Path, directory: &str) -> Result<(), String> {
    let path = export.join(directory);
    let at = |error: std::io::Error| format!("{}: {error}", path.display());
    let entries = match fs::read_dir(&path) {
        Err(error) if error.kind() == ErrorKind::NotFound => return Ok(()),
        entries => entries.map_err(at)?,
    };
    for entry in entries {
        let name = entry.map_err(at)?.file_name();
        let name = name.to_string_lossy();
        if name.ends_with(".lean") {
            lean::copy_into(export, project, &format!("{directory}/{name}"))?;
        }
    }
    Ok(())
}

/// Writes the module that imports the definitions of each part of `case`
/// together, in the case's directory of the generated namespace
/// `generated`.
fn write_check(project: &Path, generated: &str, case: &Case, module: &str) -> Result<(), String> {
    let mut text = "module\n".to_string();
    for part in &case.parts {
        text.push_str(&format!("public import {generated}.{}.Funs\n", part.module));
    }
    let path = project.join(lean::module_file(module));
    fs::write(&path, text).map_err(|error| format!("{}: {error}", path.display()))
}

/// Builds and audits the theorems of `proof` of `case` in the project
/// `project` of its stage when the generated code of the case `built`, and
/// concludes each theorem from those commands of the case's unit. A
/// theorem of a case that is not as expected, whose recorded state is
/// `record`, is rejected.
fn prove(
    gate: &mut Gate,
    case: &Case,
    proof: &Proof,
    record: &QualificationCase,
    built: bool,
    project: &Path,
) -> Result<(), String> {
    let unit = unit(&case.name);
    let build_arguments = lean::build_args(&proof.module);
    let build = lake(Site::QualificationBuild, &build_arguments, project);
    let audit_arguments = lean::check_args(AUDIT);
    let audit = lake(Site::CaseAudit, &audit_arguments, project);
    let mut every = Vec::new();
    let (mut axioms, mut judged) = (BTreeMap::new(), BTreeMap::new());
    if !built {
        let reason = "the generated code of the case did not build";
        for request in [&build, &audit] {
            gate.skip(&unit, request, reason);
        }
        every.push("its case did not build its generated code".to_string());
    } else {
        let export = gate.source().join(gate.layout().project);
        let file = lean::module_file(&proof.module);
        if export.join(&file).is_file() {
            lean::copy_into(&export, project, &file)?;
        }
        let (ran, verdict, _) = gate.run(&unit, &build, |_| Ok(()));
        if verdict.class == Class::Passed {
            let path = project.join(AUDIT);
            fs::write(&path, audit_source(&proof.module, &proof.theorems))
                .map_err(|error| format!("{}: {error}", path.display()))?;
            let (ran, verdict, _) = gate.run(&unit, &audit, |_| Ok(()));
            let finished = matches!(verdict.class, Class::Passed | Class::ProofFailure);
            if let Some(ran) = ran.filter(|_| finished) {
                axioms = lean::parse_axioms(&ran.output);
                let declarations = &record.declarations;
                judged = judge_case_audit(&axioms, ran.code(), &proof.theorems, declarations);
            }
        } else {
            gate.skip(&unit, &audit, "the proof did not build");
            let errors = ran.map_or_else(Vec::new, |ran| lean::errors(&ran.output));
            every.push(format!("the proof does not build: {}", errors.join(" | ")));
        }
    }
    if !record.differences.is_empty() {
        every.push("its case is not as expected".to_string());
    }
    for theorem in &proof.theorems {
        let mut problems = judged.get(theorem).cloned().unwrap_or_default();
        problems.extend(every.iter().cloned());
        let (status, reason) = conclusion(&problems);
        let theorem_unit = theorem_unit(&case.name, theorem);
        gate.conclude_from(&theorem_unit, &unit, status, reason);
        let entry = QualificationTheorem {
            case: case.name.clone(),
            unit: theorem_unit,
            axioms: axioms.get(theorem).cloned(),
        };
        gate.qualification().theorems.insert(theorem.clone(), entry);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    //! The stand-ins for the tools are shell scripts in the installation of
    //! a fixture. Charon writes the LLBC file that it is asked for. Aeneas
    //! writes, for the module path of its `-subdir`, what the pinned Aeneas
    //! wrote for a captured shape of the qualification crate (the fixtures
    //! of `extract.rs`) when the test names one, and otherwise a translation
    //! without items in an empty `Types.lean` and `Funs.lean`; it prints the
    //! log and exits with the status that the test gives the module. Lake
    //! records each call, runs the script that the test gives the module it
    //! builds, or `Audit` for `lake env lean`, and otherwise builds, or
    //! prints for each theorem of `Audit.lean` that it depends on `propext`
    //! and `Quot.sound`.

    use std::collections::BTreeMap;
    use std::process::ExitCode;

    use serde_json::{Value, json};

    use super::*;
    use crate::formal::extract;
    use crate::formal::fixture::Fixture;
    use crate::formal::outcome::{conventions, word};
    use crate::formal::receipt::Command;
    use crate::formal::run::tests::{Done, gate};

    /// The theorem of the case `arithmetic`.
    const MUL_MOD: &str = "Krepi.Qualification.Arithmetic.mul_mod_spec";

    /// The manifest of a qualification crate that the gate accepts.
    const MANIFEST: &str = "[package]\nname = \"formal-qualification\"\nversion = \"0.0.0\"\n\
        edition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[workspace]\n";

    /// A Charon stand-in that writes the LLBC file it is asked for.
    const CHARON: &str = "while [ $# -gt 0 ]; do\n  \
        if [ \"$1\" = --dest-file ]; then : > \"$2\"; fi\n  shift\ndone";

    /// The Aeneas stand-in of the fixture at `root`.
    fn aeneas(root: &str) -> String {
        format!(
            "while [ $# -gt 0 ]; do\n  \
               case \"$1\" in -subdir) subdir=$2 ;; -dest) dest=$2 ;; esac\n  \
               shift\n\
             done\n\
             shape='{root}/artifacts/shapes/'$(echo \"$subdir\" | tr / .)\n\
             mkdir -p \"$dest/$subdir\"\n\
             if [ -f \"$shape.from\" ]; then\n  \
               cp -R \"$(cat \"$shape.from\")/.\" \"$dest\"\n\
             else\n  \
               : > \"$dest/$subdir/Types.lean\"\n  \
               : > \"$dest/$subdir/Funs.lean\"\n  \
               echo '{{\"functions\": [], \"types\": []}}' > \"$dest/translation.json\"\n\
             fi\n\
             if [ -f \"$shape.log\" ]; then cat \"$shape.log\"; fi\n\
             if [ -f \"$shape.status\" ]; then exit \"$(cat \"$shape.status\")\"; fi"
        )
    }

    /// The Lake stand-in of the fixture at `root`.
    fn lake(root: &str) -> String {
        format!(
            "lake='{root}/artifacts/lake'\n\
             mkdir -p \"$lake\"\n\
             echo \"$PWD $*\" >> \"$lake/calls\"\n\
             case \"$1\" in\n  \
               build) for argument; do target=$argument; done ;;\n  \
               env) target=Audit ;;\n\
             esac\n\
             if [ -f \"$lake/$target.sh\" ]; then . \"$lake/$target.sh\"; fi\n\
             if [ \"$target\" = Audit ]; then\n  \
               while read -r first rest; do\n    \
                 if [ \"$first\" = '#print' ]; then\n      \
                   echo \"'${{rest#axioms }}' depends on axioms: [propext, Quot.sound]\"\n    \
                 fi\n  \
               done < Audit.lean\n\
             else\n  \
               echo 'Build completed successfully (2 jobs).'\n\
             fi"
        )
    }

    /// The directory of the captured shape `shape`.
    fn captured(shape: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/formal/fixtures/extraction")
            .join(shape)
    }

    /// The text of `cases.json` with `cases`.
    fn cases_text(cases: &Value) -> String {
        let document = json!({"schema": 1, "cases": cases});
        let mut text = serde_json::to_string_pretty(&document).expect("JSON");
        text.push('\n');
        text
    }

    /// A case `name` of `module` that expects `expect`, with no items.
    fn case(name: &str, module: &str, expect: &str) -> Value {
        json!({
            "name": name,
            "module": module,
            "start_from": [format!("crate::{}", name.replace('-', "_"))],
            "expect": expect,
            "diagnostics": [],
            "external_functions": [],
            "external_types": [],
        })
    }

    /// The case of the captured shape `arithmetic`, with its loop and its
    /// theorem.
    fn arithmetic() -> Value {
        let mut case = case("arithmetic", "Qual.Arithmetic", "translated");
        case["loop_sources"] = json!(["arithmetic.pow_mod_loop src/lib.rs"]);
        case["proof"] = json!({"module": "Krepi.Qualification.Arithmetic", "theorems": [MUL_MOD]});
        case
    }

    /// The case of the captured shape `shared-pointers`.
    fn shared_pointers() -> Value {
        let mut case = case("shared-pointers", "Qual.SharedPointers", "translated");
        case["external_functions"] = json!([
            "alloc::sync::{alloc::sync::Arc<T>}::ptr_eq",
            "alloc::sync::{impl core::ops::deref::Deref<T> for alloc::sync::Arc<T>}::deref",
        ]);
        case["external_types"] = json!(["alloc::sync::Arc"]);
        case
    }

    /// The case of the captured shape `nested-loop`, which Aeneas rejects.
    fn nested_loop() -> Value {
        let mut case = case("nested-loop", "Qual.NestedLoop", "rejected");
        case["diagnostics"] = json!([
            "[Error] Ignoring the body of 'formal_qualification::nested_loop::charge_grid' because of previous error",
            "[Error] Returns inside of nested loops are not supported yet",
        ]);
        case["external_functions"] = json!(["formal_qualification::nested_loop::charge_grid"]);
        case
    }

    /// An ill-typed case, whose type error the Lake stand-in prints.
    fn ill() -> Value {
        let mut case = case("ill", "Qual.Ill", "ill-typed");
        case["type_errors_in"] = json!("Funs.lean");
        case
    }

    /// A build log of Lake that reports `lines` of the module `module` and
    /// fails, with the status `status`.
    fn failing(module: &str, lines: &[&str], status: i32) -> String {
        let mut script = format!("echo '\u{2716} [2/2] Building {module} (1.6s)'\n");
        for line in lines {
            script.push_str(&format!("echo '{line}'\n"));
        }
        script.push_str(&format!(
            "echo 'Some required targets logged failures:'\necho '- {module}'\n\
             echo 'error: build failed'\nexit {status}\n"
        ));
        script
    }

    /// A fixture with the qualification `cases`, not committed: the
    /// qualification crate, the Lake project files, the extraction
    /// configuration, the proof module of `arithmetic`, the Aeneas Lean
    /// library of the installation, the stand-ins, and the shapes and Lake
    /// scripts of the cases above.
    fn qualification(label: &str, cases: &Value) -> Fixture {
        let fixture = Fixture::new(label);
        let root = fixture.root().to_str().expect("a UTF-8 path").to_string();
        assert!(!root.contains('\''), "{root}");
        fixture.write(".gitignore", "/artifacts/\n/verification/.lake/\n");
        fixture.write("verification/qualification/Cargo.toml", MANIFEST);
        fixture.write("verification/qualification/src/lib.rs", "");
        fixture.write("verification/qualification/cases.json", &cases_text(cases));
        fixture.write(
            "verification/extraction.toml",
            include_str!("../../../verification/extraction.toml"),
        );
        for file in lean::PROJECT_FILES {
            fixture.write(&format!("verification/{file}"), &format!("-- {file}\n"));
        }
        fixture.write(
            "verification/Krepi/Qualification/Arithmetic.lean",
            "module\n",
        );
        fixture.write("artifacts/formal/tools/backend/.lake/packages/README", "");
        fixture.tool("charon", CHARON);
        fixture.tool("aeneas", &aeneas(&root));
        fixture.tool("lake", &lake(&root));
        for name in ["arithmetic", "shared-pointers", "nested-loop"] {
            let module = match name {
                "arithmetic" => "Qual.Arithmetic",
                "shared-pointers" => "Qual.SharedPointers",
                _ => "Qual.NestedLoop",
            };
            let key = format!("artifacts/shapes/KrepiGen.{module}");
            let directory = captured(name);
            fixture.write(&format!("{key}.from"), directory.to_str().expect("UTF-8"));
            if name == "nested-loop" {
                let log = fs::read_to_string(directory.join("aeneas.log")).expect("the log");
                fixture.write(&format!("{key}.log"), &log);
                fixture.write(&format!("{key}.status"), "1\n");
            }
        }
        let type_error = "error: KrepiGen/Qual/Ill/Funs.lean:3:8: type mismatch";
        lake_script(
            &fixture,
            "KrepiGen.Qual.Ill.Funs",
            &failing("KrepiGen.Qual.Ill.Funs", &[type_error], 1),
        );
        fixture
    }

    /// Makes Lake run `script` for `target`.
    fn lake_script(fixture: &Fixture, target: &str, script: &str) {
        fixture.write(&format!("artifacts/lake/{target}.sh"), script);
    }

    /// Commits what changed in `fixture` and runs its qualification.
    fn run(fixture: &Fixture) -> Done {
        if !fixture.git(&["status", "--porcelain"]).is_empty() {
            fixture.commit_all();
        }
        gate(
            fixture,
            &[],
            vec![phase(fixture.root(), &Layout::PRODUCTION)],
        )
    }

    /// The conclusion of `unit`.
    fn status<'a>(done: &'a Done, unit: &str) -> (Status, Option<&'a str>) {
        let entry = &done.receipt.units[unit];
        (entry.status, entry.reason.as_deref())
    }

    /// The commands of `unit`.
    fn commands<'a>(done: &'a Done, unit: &str) -> Vec<&'a Command> {
        (done.receipt.commands.iter())
            .filter(|command| command.unit.as_deref() == Some(unit))
            .collect()
    }

    /// The sites of the commands of `unit`, with their classes.
    fn sites(done: &Done, unit: &str) -> Vec<(Site, Class)> {
        (commands(done, unit).into_iter())
            .map(|command| (command.site, command.class))
            .collect()
    }

    /// The record of the qualification.
    fn record(done: &Done) -> &receipt::Qualification {
        done.receipt
            .qualification
            .as_ref()
            .expect("a qualification record")
    }

    /// The paths of the files below `directory`, relative to it.
    fn files_below(directory: &Path) -> Vec<String> {
        let mut found = Vec::new();
        let mut pending = vec![directory.to_path_buf()];
        while let Some(next) = pending.pop() {
            for entry in fs::read_dir(&next).expect("a directory") {
                let path = entry.expect("an entry").path();
                if path.is_symlink() || path.is_file() {
                    let relative = path.strip_prefix(directory).expect("below");
                    found.push(relative.to_string_lossy().into_owned());
                } else if path.is_dir() {
                    pending.push(path);
                }
            }
        }
        found.sort();
        found
    }

    #[test]
    fn a_qualification_of_every_kind_of_case_is_verified() {
        let mut models = shared_pointers();
        models["models"] = json!("verification/externals/Qual/SharedPointers");
        let fixture = qualification(
            "every-kind",
            &json!([arithmetic(), models, nested_loop(), ill()]),
        );
        // The reviewed declarations keep the generated axioms of the
        // template, and the definitions that they use are installed too.
        let templates = captured("shared-pointers").join("KrepiGen/Qual/SharedPointers");
        let template =
            fs::read_to_string(templates.join("FunsExternal_Template.lean")).expect("the template");
        let reviewed = "verification/externals/Qual/SharedPointers";
        fixture.write(&format!("{reviewed}/FunsExternal.lean"), &template);
        let types = "module\npublic import Aeneas\n-- reviewed types\n";
        fixture.write(&format!("{reviewed}/TypesExternal.lean"), types);
        fixture.write(
            "verification/Krepi/Qualification/Models/Arc.lean",
            "module\n",
        );
        let done = run(&fixture);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Verified);
        assert!(receipt.complete);
        let units: Vec<&str> = receipt.units.keys().map(String::as_str).collect();
        assert_eq!(
            units,
            [
                "qualification/arithmetic",
                "qualification/arithmetic/Krepi.Qualification.Arithmetic.mul_mod_spec",
                "qualification/ill",
                "qualification/nested-loop",
                "qualification/shared-pointers",
            ]
        );
        for unit in receipt.units.values() {
            assert_eq!(
                (unit.status, unit.phase.as_str()),
                (Status::Verified, PHASE)
            );
        }
        assert_eq!(receipt.phases[PHASE].budget_seconds, 3_600);
        use Class::{Passed, ProofFailure};
        let build = Site::QualificationBuild;
        assert_eq!(
            sites(&done, "qualification/arithmetic"),
            [
                (Site::Charon, Passed),
                (Site::Aeneas, Passed),
                (build, Passed),
                (build, Passed),
                (Site::CaseAudit, Passed),
            ]
        );
        // Nothing of a case that is expected to be rejected is built.
        assert_eq!(
            sites(&done, "qualification/nested-loop"),
            [(Site::Charon, Passed), (Site::Aeneas, ProofFailure)]
        );
        assert_eq!(
            sites(&done, "qualification/ill"),
            [
                (Site::Charon, Passed),
                (Site::Aeneas, Passed),
                (Site::IllTypedBuild, ProofFailure),
            ]
        );
        let argv: Vec<Vec<String>> = (commands(&done, "qualification/arithmetic").into_iter())
            .skip(2)
            .map(|command| command.argv.clone())
            .collect();
        assert_eq!(
            argv,
            [
                lean::build_args("KrepiGen.Qual.Arithmetic.Funs"),
                lean::build_args("Krepi.Qualification.Arithmetic"),
                lean::check_args("Audit.lean"),
            ]
            .map(|args| [vec!["lake".to_string()], args].concat())
        );
        let work = done.run.path.join("work/cases");
        let stage = |case: &str| work.join(case).join("stage");
        for command in commands(&done, "qualification/arithmetic")
            .into_iter()
            .skip(2)
        {
            let cwd = fixture.root().join(&command.cwd);
            assert_eq!(cwd, stage("arithmetic").join("verification"));
        }
        // The record of each case.
        let record = record(&done);
        let cases = fs::read(fixture.root().join(Layout::PRODUCTION.cases)).expect("the cases");
        assert_eq!(record.cases_sha256, sha256(&cases));
        let configuration = include_bytes!("../../../verification/extraction.toml");
        assert_eq!(record.extraction_sha256, sha256(configuration));
        let arithmetic = &record.cases["arithmetic"];
        assert_eq!(arithmetic.unit, "qualification/arithmetic");
        assert_eq!(arithmetic.expect, Expect::Translated);
        assert!(arithmetic.observed.complete);
        assert_eq!(
            arithmetic.observed.loop_sources,
            ["arithmetic.pow_mod_loop src/lib.rs"]
        );
        let generated: Vec<&str> = arithmetic.generated.keys().map(String::as_str).collect();
        assert_eq!(
            generated,
            [
                "KrepiGen/Qual/Arithmetic/Funs.lean",
                "KrepiGen/Qual/Arithmetic/Types.lean"
            ]
        );
        assert_eq!(arithmetic.differences, Vec::<String>::new());
        assert_eq!(arithmetic.declarations, Vec::<String>::new());
        let nested = &record.cases["nested-loop"];
        assert!(!nested.observed.complete);
        assert_eq!(nested.observed.diagnostics.len(), 2);
        assert_eq!(nested.type_errors, None);
        assert_eq!(
            record.cases["ill"].type_errors,
            Some(receipt::TypeErrors {
                file: "Funs.lean".to_string(),
                errors: 1,
                in_file: 1,
            })
        );
        assert_eq!(
            record.cases["shared-pointers"].models.as_deref(),
            Some(reviewed)
        );
        assert_eq!(
            record.theorems[MUL_MOD],
            QualificationTheorem {
                case: "arithmetic".to_string(),
                unit: theorem_unit("arithmetic", MUL_MOD),
                axioms: Some(vec!["propext".to_string(), "Quot.sound".to_string()]),
            }
        );
        // What each stage holds.
        assert_eq!(
            files_below(&stage("arithmetic")),
            [
                "artifacts/formal/lake/aeneas",
                "artifacts/formal/lake/packages",
                "verification/Audit.lean",
                "verification/Krepi/Qualification/Arithmetic.lean",
                "verification/KrepiGen/Qual/Arithmetic/Funs.lean",
                "verification/KrepiGen/Qual/Arithmetic/Types.lean",
                "verification/lake-manifest.json",
                "verification/lakefile.toml",
                "verification/lean-toolchain",
            ]
        );
        let backend = fixture.root().join("artifacts/formal/tools/backend");
        let link = stage("arithmetic").join("artifacts/formal/lake/aeneas");
        assert_eq!(fs::read_link(link).expect("a link"), backend);
        assert_eq!(
            fs::read_to_string(stage("arithmetic").join("verification/Audit.lean"))
                .expect("the audit"),
            format!("import Krepi.Qualification.Arithmetic\n#print axioms {MUL_MOD}\n")
        );
        let project = stage("shared-pointers").join("verification");
        let installed = |file: &str| {
            fs::read_to_string(project.join("KrepiGen/Qual/SharedPointers").join(file))
                .expect("an installed file")
        };
        assert_eq!(installed("FunsExternal.lean"), template);
        assert_eq!(installed("TypesExternal.lean"), types);
        assert!(
            project
                .join("Krepi/Qualification/Models/Arc.lean")
                .is_file()
        );
        assert!(!stage("nested-loop").exists());
        // Each extraction's Cargo target directory is removed after it, and
        // what the tools wrote stays.
        for case in ["arithmetic", "ill", "nested-loop", "shared-pointers"] {
            assert!(!work.join(case).join("target").exists(), "{case}");
            assert!(work.join(case).join("extract.llbc").is_file(), "{case}");
            assert!(
                work.join(case).join("aeneas/translation.json").is_file(),
                "{case}"
            );
        }
    }

    #[test]
    fn the_committed_case_list_is_frozen() {
        // The 103 cases kept from the CAS project, in its order, then the
        // new ones.
        const KEPT: [&str; 103] = [
            "str_from",
            "arithmetic",
            "checked",
            "integer-conversions",
            "option-combinators",
            "single-loop",
            "nested-loop",
            "split-loop",
            "loop-break-tail",
            "loop-break-branch",
            "iterator-adapters",
            "index-loop",
            "option-reference-eq",
            "trim-by-index",
            "vector-operations",
            "closure-parameter",
            "generic-trait",
            "ordered-maps",
            "shared-pointers",
            "recursion",
            "formatting",
            "floats",
            "binary64-bits",
            "binary64-values",
            "clock",
            "atomics",
            "observations",
            "slices",
            "field-interface",
            "polynomial-interface",
            "default-method",
            "default-self-call",
            "default-direct-call",
            "checks-before-loop",
            "return-before-loop",
            "flag-before-loop",
            "loop-in-branch",
            "placement-before-loop",
            "returns-then-helper",
            "owned-before-loop",
            "owned-then-helper",
            "coefficient-map",
            "registry-records",
            "registry-static-reference",
            "registry-str-names",
            "const-str-names",
            "static-str-table",
            "string-match",
            "string-literal-return",
            "enum-index-cast",
            "function-pointers",
            "series-summer",
            "error-conversion",
            "map-iteration",
            "map-reverse-iteration",
            "map-next-back",
            "map-entry",
            "map-last",
            "map-loop-charge",
            "map-next-back-charge",
            "term-walk",
            "map-term-walk",
            "carried-term-walk",
            "view-map-loop",
            "view-map-range",
            "view-index-loop",
            "view-value-join",
            "view-borrowed-helper",
            "view-map-helper",
            "monomial-order",
            "range-loop",
            "literal-variant-match",
            "registry-items",
            "subtrait-loop",
            "elimination-skeleton",
            "shared-term",
            "match-machine",
            "match-machine-arc",
            "term-layout-cut",
            "match-search",
            "strategy-data",
            "strategy-recursive",
            "strategy-loop",
            "indexed-field-sum",
            "collection-tree-copy",
            "collection-tree-map",
            "collection-tree-walk",
            "collection-tree-frame-enum",
            "string-bytes",
            "string-chars",
            "collection-tree-kinds",
            "collection-hand-traits",
            "collection-tree-keyed-frames",
            "collection-value-instance",
            "iterator-arena",
            "iterator-owned-stack",
            "generic-into-iterator-loop",
            "generic-into-iterator-step",
            "moving-if-join",
            "moving-if-helper",
            "unwrap-in-loop",
            "unwrap-in-helper",
            "division-walk",
        ];
        const NEW: [&str; 9] = [
            "cfg-shape",
            "const-generic",
            "r1-function-item-value",
            "r2-iterator-any",
            "r3-iterator-flatten",
            "r4-closure-callback",
            "r5-stop-path-borrow-join",
            "r6-same-enum-name",
            "r7-private-enum",
        ];
        let text = include_str!("../../../verification/qualification/cases.json");
        let cases = load_cases(text, &Layout::PRODUCTION).expect("the committed cases are valid");
        let names: Vec<&str> = cases.iter().map(|case| case.name.as_str()).collect();
        let frozen: Vec<&str> = KEPT.iter().chain(&NEW).copied().collect();
        assert_eq!(names, frozen);
        assert_eq!(names.len(), 112);
        let unique: BTreeSet<&str> = frozen.iter().copied().collect();
        assert_eq!(unique.len(), 112);
        assert_eq!(units(&cases).len(), 115);
    }

    /// The extraction of the captured `shape`, of the case `module`, with
    /// the diagnostics of the log of its Aeneas, complete unless they report
    /// an error.
    fn extraction(shape: &str, module: &str) -> Extraction {
        let directory = captured(shape);
        let text = fs::read_to_string(directory.join("translation.json")).expect("a translation");
        let log = fs::read_to_string(directory.join("aeneas.log")).unwrap_or_default();
        let diagnostics = extract::diagnostics(&log);
        let complete = !diagnostics.iter().any(|line| line.starts_with("[Error]"));
        Extraction {
            complete,
            diagnostics,
            namespace: format!("{}.{module}", Layout::PRODUCTION.generated),
            generated: directory,
            files: BTreeMap::new(),
            translation: serde_json::from_str(&text).expect("a captured translation"),
        }
    }

    /// The differences of the case `name`, one of those of a captured
    /// shape, from its captured extraction once `edit` has changed it in
    /// `cases.json`.
    fn differences_after(name: &str, edit: impl FnOnce(&mut Value)) -> Vec<String> {
        let mut cases = json!([arithmetic(), shared_pointers(), nested_loop()]);
        let entry = (cases.as_array_mut().expect("a list").iter_mut())
            .find(|case| case["name"] == name)
            .expect("a case of a captured shape");
        edit(entry);
        let loaded = load_cases(&cases_text(&cases), &Layout::PRODUCTION).expect("valid cases");
        let case = loaded
            .iter()
            .find(|case| case.name == name)
            .expect("the case");
        differences(case, &observed(&[extraction(name, &case.module)]))
    }

    /// Adds `item` to the list `field` of a case.
    fn add(field: &'static str, item: &'static str) -> impl FnOnce(&mut Value) {
        move |case| {
            case[field]
                .as_array_mut()
                .expect("a list")
                .push(json!(item))
        }
    }

    /// Removes the first item of the list `field` of a case.
    fn remove(field: &'static str) -> impl FnOnce(&mut Value) {
        move |case| {
            case[field].as_array_mut().expect("a list").remove(0);
        }
    }

    #[test]
    fn the_captured_extractions_are_as_their_cases_expect() {
        for name in ["arithmetic", "shared-pointers", "nested-loop"] {
            assert_eq!(
                differences_after(name, |_| {}),
                Vec::<String>::new(),
                "{name}"
            );
        }
    }

    #[test]
    fn a_rejection_where_a_translation_is_expected_is_a_difference() {
        let found = differences_after("nested-loop", |case| case["expect"] = json!("translated"));
        assert_eq!(found, ["expected a complete translation, got a rejection"]);
    }

    #[test]
    fn a_translation_where_a_rejection_is_expected_is_a_difference() {
        // The shape starts to translate.
        let found = differences_after("arithmetic", |case| {
            case["expect"] = json!("rejected");
            case.as_object_mut().expect("a case").remove("proof");
        });
        assert_eq!(found, ["expected a rejection, got a complete translation"]);
    }

    #[test]
    fn a_missing_diagnostic_is_a_difference() {
        let found = differences_after("nested-loop", add("diagnostics", "[Warn ] Unused"));
        assert_eq!(found, ["diagnostics: expected but absent: [Warn ] Unused"]);
    }

    #[test]
    fn an_extra_diagnostic_is_a_difference() {
        let found = differences_after("nested-loop", remove("diagnostics"));
        assert_eq!(
            found,
            [
                "diagnostics: present but not expected: [Error] Ignoring the body of \
                 'formal_qualification::nested_loop::charge_grid' because of previous error"
            ]
        );
    }

    #[test]
    fn a_missing_external_function_is_a_difference() {
        let found = differences_after(
            "shared-pointers",
            add(
                "external_functions",
                "alloc::sync::{alloc::sync::Arc<T>}::new",
            ),
        );
        assert_eq!(
            found,
            ["external functions: expected but absent: alloc::sync::{alloc::sync::Arc<T>}::new"]
        );
    }

    #[test]
    fn an_extra_external_function_is_a_difference() {
        let found = differences_after("shared-pointers", remove("external_functions"));
        assert_eq!(
            found,
            [
                "external functions: present but not expected: alloc::sync::{alloc::sync::Arc<T>}::ptr_eq"
            ]
        );
    }

    #[test]
    fn a_missing_external_type_is_a_difference() {
        let found = differences_after("arithmetic", add("external_types", "alloc::sync::Arc"));
        assert_eq!(
            found,
            ["external types: expected but absent: alloc::sync::Arc"]
        );
    }

    #[test]
    fn an_extra_external_type_is_a_difference() {
        let found = differences_after("shared-pointers", remove("external_types"));
        assert_eq!(
            found,
            ["external types: present but not expected: alloc::sync::Arc"]
        );
    }

    #[test]
    fn a_missing_loop_source_is_a_difference() {
        let found = differences_after(
            "arithmetic",
            add("loop_sources", "arithmetic.sub_mod_loop src/lib.rs"),
        );
        assert_eq!(
            found,
            ["loop sources: expected but absent: arithmetic.sub_mod_loop src/lib.rs"]
        );
        // A case that records no loops is not compared on them.
        let found = differences_after("arithmetic", |case| {
            case.as_object_mut().expect("a case").remove("loop_sources");
        });
        assert_eq!(found, Vec::<String>::new());
    }

    #[test]
    fn an_extra_loop_source_is_a_difference() {
        let found = differences_after("arithmetic", remove("loop_sources"));
        assert_eq!(
            found,
            ["loop sources: present but not expected: arithmetic.pow_mod_loop src/lib.rs"]
        );
    }

    #[test]
    fn a_case_that_differs_from_its_expectation_rejects_the_run() {
        let mut differs = arithmetic();
        differs["diagnostics"] = json!(["[Warn ] Unused"]);
        let broken = case("broken", "Qual.Broken", "translated");
        // A shape that starts to translate, which is not built.
        let translates = case("translates", "Qual.Translates", "rejected");
        let fixture = qualification("differs", &json!([differs, broken, translates]));
        let error = "error: KrepiGen/Qual/Broken/Funs.lean:7:2: unknown identifier";
        lake_script(
            &fixture,
            "KrepiGen.Qual.Broken.Funs",
            &failing("KrepiGen.Qual.Broken.Funs", &[error], 1),
        );
        let done = run(&fixture);
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.receipt.status, Status::Rejected);
        assert!(done.receipt.complete);
        assert_eq!(done.failures(), Vec::<&str>::new());
        assert_eq!(
            status(&done, "qualification/arithmetic"),
            (
                Status::Rejected,
                Some("diagnostics: expected but absent: [Warn ] Unused")
            )
        );
        // The proof is still built and audited, and its theorem is rejected
        // with its case.
        assert_eq!(
            status(&done, &theorem_unit("arithmetic", MUL_MOD)),
            (Status::Rejected, Some("its case is not as expected"))
        );
        assert_eq!(commands(&done, "qualification/arithmetic").len(), 5);
        assert_eq!(
            status(&done, "qualification/broken"),
            (
                Status::Rejected,
                Some(
                    "the generated code does not type-check: error: KrepiGen/Qual/Broken/Funs.lean:7:2: \
                     unknown identifier | error: build failed"
                )
            )
        );
        assert_eq!(
            status(&done, "qualification/translates"),
            (
                Status::Rejected,
                Some("expected a rejection, got a complete translation")
            )
        );
        assert_eq!(
            sites(&done, "qualification/translates"),
            [(Site::Charon, Class::Passed), (Site::Aeneas, Class::Passed)]
        );
        assert!(!done.run.path.join("work/cases/translates/stage").exists());
        assert_eq!(
            record(&done).cases["broken"].differences,
            [
                "the generated code does not type-check: error: KrepiGen/Qual/Broken/Funs.lean:7:2: \
                 unknown identifier | error: build failed"
            ]
        );
    }

    #[test]
    fn a_killed_ill_typed_build_is_a_tool_failure_and_not_as_expected() {
        let fixture = qualification("ill-killed", &json!([ill()]));
        // The type error lies in the recorded file, but Lake reports a Lean
        // process that signal 9 ended.
        let lines = [
            "error: KrepiGen/Qual/Ill/Funs.lean:3:8: type mismatch",
            "error: Lean exited with code 137",
        ];
        lake_script(
            &fixture,
            "KrepiGen.Qual.Ill.Funs",
            &failing("KrepiGen.Qual.Ill.Funs", &lines, 1),
        );
        let done = run(&fixture);
        let reason = "ill-typed-build: Lean was ended by signal 9";
        assert_eq!(
            sites(&done, "qualification/ill")[2],
            (Site::IllTypedBuild, Class::ToolFailure)
        );
        assert_eq!(
            status(&done, "qualification/ill"),
            (Status::ToolFailure, Some(reason))
        );
        assert_eq!(done.receipt.status, Status::ToolFailure);
        assert_eq!(done.code, ExitCode::FAILURE);
    }

    #[test]
    fn an_ill_typed_build_with_an_error_in_another_file_is_not_as_expected() {
        let fixture = qualification("ill-elsewhere", &json!([ill()]));
        let lines = [
            "error: KrepiGen/Qual/Ill/Funs.lean:3:8: type mismatch",
            "error: KrepiGen/Qual/Ill/Types.lean:5:0: unknown identifier",
        ];
        lake_script(
            &fixture,
            "KrepiGen.Qual.Ill.Funs",
            &failing("KrepiGen.Qual.Ill.Funs", &lines, 1),
        );
        let done = run(&fixture);
        assert_eq!(
            status(&done, "qualification/ill"),
            (
                Status::Rejected,
                Some(
                    "expected every type error in Funs.lean, found 1 of 2; a message outside \
                     Funs.lean: error: KrepiGen/Qual/Ill/Types.lean:5:0: unknown identifier"
                )
            )
        );
        assert_eq!(
            record(&done).cases["ill"].type_errors,
            Some(receipt::TypeErrors {
                file: "Funs.lean".to_string(),
                errors: 2,
                in_file: 1,
            })
        );
        assert_eq!(done.receipt.status, Status::Rejected);
    }

    #[test]
    fn an_ill_typed_build_that_passes_is_not_as_expected() {
        let fixture = qualification("ill-passes", &json!([ill()]));
        lake_script(
            &fixture,
            "KrepiGen.Qual.Ill.Funs",
            "echo 'Build completed successfully (2 jobs).'\nexit 0",
        );
        let done = run(&fixture);
        assert_eq!(
            sites(&done, "qualification/ill")[2],
            (Site::IllTypedBuild, Class::Passed)
        );
        assert_eq!(
            status(&done, "qualification/ill"),
            (
                Status::Rejected,
                Some("the generated code was expected not to type-check")
            )
        );
        assert_eq!(done.receipt.status, Status::Rejected);
    }

    #[test]
    fn ill_typed_cases_count_errors_in_their_own_generated_files() {
        let output = "error: KrepiGen/Qual/SharedTerm/Types.lean:58:0: (kernel) arg #1\n\
            error: KrepiGen/Qual/SharedTerm/Funs.lean:7:2: unknown\n\
            error: KrepiGen/Qual/SharedTerm/Types.lean:85:35: unknown\n\
            error: KrepiGen/Qual/Shared/Funs.lean:1:1: other case\n\
            error: KrepiGen/Qual/SharedTerm/Inner/Funs.lean:2:1: case below\n\
            error: Lean exited with code 1\n";
        let directory = "KrepiGen/Qual/SharedTerm/";
        let errors = case_errors(output, directory);
        assert_eq!(errors.len(), 3);
        assert_eq!(errors_in(&errors, directory, "Types.lean"), 2);
        assert_eq!(errors_in(&errors, directory, "Funs.lean"), 1);
        assert_eq!(errors_in(&errors, directory, "TypesExternal.lean"), 0);
        let other = case_errors(output, "KrepiGen/Qual/Shared/");
        assert_eq!(other.len(), 1);
        assert_eq!(errors_in(&other, "KrepiGen/Qual/Shared/", "Funs.lean"), 1);
        // The files of a case whose module lies below another case's are its
        // own alone.
        assert_eq!(
            case_errors(output, "KrepiGen/Qual/SharedTerm/Inner/").len(),
            1
        );
        assert!(case_errors(output, "KrepiGen/Qual/Rationals/").is_empty());
    }

    #[test]
    fn a_theorem_that_uses_a_declaration_of_another_case_fails_its_audit() {
        let fixture = qualification("borrowed", &json!([arithmetic(), shared_pointers()]));
        // The audit reports an axiom that only the template of the other
        // case declares.
        let report = format!("'{MUL_MOD}' depends on axioms: [propext, alloc.sync.Arc.ptr_eq]");
        lake_script(&fixture, "Audit", &format!("echo \"{report}\"\nexit 0"));
        let done = run(&fixture);
        let theorem = theorem_unit("arithmetic", MUL_MOD);
        let reason = format!("{MUL_MOD} depends on alloc.sync.Arc.ptr_eq");
        assert_eq!(
            status(&done, &theorem),
            (Status::Rejected, Some(reason.as_str()))
        );
        assert_eq!(
            status(&done, "qualification/arithmetic"),
            (Status::Verified, None)
        );
        assert_eq!(done.receipt.status, Status::Rejected);
        assert!(done.receipt.complete);
        assert_eq!(
            record(&done).theorems[MUL_MOD].axioms,
            Some(vec![
                "propext".to_string(),
                "alloc.sync.Arc.ptr_eq".to_string()
            ])
        );
        // The axiom is a declaration of the other case's template, which a
        // theorem of that case could use.
        let template = captured("shared-pointers")
            .join("KrepiGen/Qual/SharedPointers/FunsExternal_Template.lean");
        let template = fs::read_to_string(template).expect("the template");
        let declarations = declared_axioms(&template);
        assert!(declarations.contains(&"alloc.sync.Arc.ptr_eq".to_string()));
        let (axioms, theorems) = (lean::parse_axioms(&report), [MUL_MOD.to_string()]);
        let own = judge_case_audit(&axioms, Some(0), &theorems, &declarations);
        assert_eq!(own[MUL_MOD], Vec::<String>::new());
        let other = judge_case_audit(&axioms, Some(0), &theorems, &[]);
        assert_eq!(other[MUL_MOD], [reason]);
    }

    #[test]
    fn an_audit_that_does_not_report_a_theorem_fails() {
        let fixture = qualification("unreported", &json!([arithmetic()]));
        lake_script(&fixture, "Audit", "echo 'no theorem'\nexit 0");
        let done = run(&fixture);
        let theorem = theorem_unit("arithmetic", MUL_MOD);
        let reason = format!("the case audit did not report {MUL_MOD}");
        assert_eq!(
            status(&done, &theorem),
            (Status::Rejected, Some(reason.as_str()))
        );
        assert_eq!(record(&done).theorems[MUL_MOD].axioms, None);
        assert_eq!(done.receipt.status, Status::Rejected);
        // Nor may it report a theorem that was not requested.
        let other = "Krepi.Qualification.Arithmetic.other";
        let script = format!(
            "echo \"'{MUL_MOD}' depends on axioms: [propext]\"\n\
             echo \"'{other}' depends on axioms: [propext]\"\nexit 0"
        );
        lake_script(&fixture, "Audit", &script);
        let done = run(&fixture);
        let reason = format!("the case audit reported {other}, which was not requested");
        assert_eq!(
            status(&done, &theorem),
            (Status::Rejected, Some(reason.as_str()))
        );
        assert_eq!(
            record(&done).theorems[MUL_MOD].axioms,
            Some(vec!["propext".to_string()])
        );
        // An audit that fails by itself fails the theorem as well.
        lake_script(
            &fixture,
            "Audit",
            &format!("echo \"'{MUL_MOD}' depends on axioms: [propext]\"\nexit 1"),
        );
        let done = run(&fixture);
        assert_eq!(
            status(&done, &theorem),
            (Status::Rejected, Some("the case audit exited with 1"))
        );
    }

    #[test]
    fn a_killed_audit_concludes_its_theorems_as_tool_failures() {
        let fixture = qualification("audit-killed", &json!([arithmetic()]));
        lake_script(&fixture, "Audit", "kill -9 $$");
        let done = run(&fixture);
        let reason = "case-audit was ended by signal 9";
        let theorem = theorem_unit("arithmetic", MUL_MOD);
        assert_eq!(status(&done, &theorem), (Status::ToolFailure, Some(reason)));
        // The audit is a command of the case, which it forces as well.
        assert_eq!(
            status(&done, "qualification/arithmetic"),
            (Status::ToolFailure, Some(reason))
        );
        assert_eq!(record(&done).theorems[MUL_MOD].axioms, None);
        assert_eq!(done.receipt.status, Status::ToolFailure);
    }

    #[test]
    fn a_proof_that_does_not_build_rejects_its_theorems() {
        let fixture = qualification("proof-fails", &json!([arithmetic()]));
        let error = "error: Krepi/Qualification/Arithmetic.lean:20:2: unsolved goals";
        let module = "Krepi.Qualification.Arithmetic";
        lake_script(&fixture, module, &failing(module, &[error], 1));
        let done = run(&fixture);
        let theorem = theorem_unit("arithmetic", MUL_MOD);
        assert_eq!(
            status(&done, &theorem),
            (
                Status::Rejected,
                Some(
                    "the proof does not build: error: Krepi/Qualification/Arithmetic.lean:20:2: \
                      unsolved goals | error: build failed"
                )
            )
        );
        // The case itself is as expected.
        assert_eq!(
            status(&done, "qualification/arithmetic"),
            (Status::Verified, None)
        );
        let audit = commands(&done, "qualification/arithmetic")[4];
        assert_eq!(
            (audit.site, audit.class, audit.reason.as_deref()),
            (
                Site::CaseAudit,
                Class::NotRun,
                Some("not started: the proof did not build")
            )
        );
        assert_eq!(done.receipt.status, Status::Rejected);
        assert!(done.receipt.complete);
        // A case that does not build its generated code runs no proof.
        lake_script(
            &fixture,
            "KrepiGen.Qual.Arithmetic.Funs",
            &failing("KrepiGen.Qual.Arithmetic.Funs", &["error: x"], 1),
        );
        let done = run(&fixture);
        let skipped: Vec<(Site, Option<&str>)> = (commands(&done, "qualification/arithmetic")
            .into_iter())
        .skip(3)
        .map(|command| (command.site, command.reason.as_deref()))
        .collect();
        let reason = Some("not started: the generated code of the case did not build");
        assert_eq!(
            skipped,
            [
                (Site::QualificationBuild, reason),
                (Site::CaseAudit, reason)
            ]
        );
        let (status, reason) = status(&done, &theorem);
        assert_eq!(status, Status::Rejected);
        assert_eq!(
            reason,
            Some("its case did not build its generated code; its case is not as expected")
        );
    }

    #[test]
    fn reviewed_externals_may_declare_only_generated_axioms() {
        let template = fs::read_to_string(
            captured("shared-pointers")
                .join("KrepiGen/Qual/SharedPointers/FunsExternal_Template.lean"),
        )
        .expect("the template");
        let scratch = crate::scratch::Scratch::new("reviewed");
        let directory = "verification/externals/Qual/SharedPointers";
        let cases = json!([{
            "name": "shared-pointers", "module": "Qual.SharedPointers",
            "start_from": ["crate::shared_pointers"], "expect": "translated",
            "models": directory, "diagnostics": [], "external_functions": [],
            "external_types": [],
        }]);
        let cases = load_cases(&cases_text(&cases), &Layout::PRODUCTION).expect("valid cases");
        let installed = |text: &str| {
            scratch.write(&format!("{directory}/FunsExternal.lean"), text);
            installed_external(&scratch.0, &cases[0], "FunsExternal", &template)
        };
        // A reviewed file may define what the template declares.
        let defined = "def alloc.sync.Arc.ptr_eq := 0\n";
        assert_eq!(installed(defined), Ok(defined.to_string()));
        assert_eq!(installed(&template), Ok(template.clone()));
        assert_eq!(
            installed(&format!("{template}axiom extra.cheat : False\n")),
            Err(
                "shared-pointers: FunsExternal.lean declares extra.cheat, which is not a \
                 generated declaration"
                    .to_string()
            )
        );
        // So does one declared with a modifier or after an attribute.
        let refused = |axiom: &str| {
            Err(format!(
                "shared-pointers: FunsExternal.lean declares {axiom}, which is not a generated \
                 declaration"
            ))
        };
        let public = format!("{template}public axiom extra.cheat : False\n");
        assert_eq!(installed(&public), refused("extra.cheat"));
        let private = format!("{template}@[simp] private axiom hidden : True\n");
        assert_eq!(installed(&private), refused("hidden"));
        assert_eq!(
            installed("theorem t : False := sorry\n"),
            Err("shared-pointers: FunsExternal.lean uses sorry".to_string())
        );
        // A reviewed file that is not there is named as the case names it.
        assert_eq!(
            installed_external(&scratch.0, &cases[0], "TypesExternal", ""),
            Err(format!(
                "{directory}/TypesExternal.lean: No such file or directory (os error 2)"
            ))
        );
        // Without a reviewed file, the template is installed.
        let mut plain = cases[0].clone();
        plain.models = None;
        assert_eq!(
            installed_external(&scratch.0, &plain, "FunsExternal", &template),
            Ok(template.clone())
        );
        // The run rejects the case and does not build it.
        let mut models = shared_pointers();
        models["models"] = json!(directory);
        let fixture = qualification("reviewed-extra", &json!([models]));
        let extra = format!("{template}axiom extra.cheat : False\n");
        fixture.write(&format!("{directory}/FunsExternal.lean"), &extra);
        fixture.write(&format!("{directory}/TypesExternal.lean"), "module\n");
        let done = run(&fixture);
        assert_eq!(
            status(&done, "qualification/shared-pointers"),
            (
                Status::Rejected,
                Some(
                    "cannot install the generated files: shared-pointers: FunsExternal.lean \
                     declares extra.cheat, which is not a generated declaration"
                )
            )
        );
        let build = commands(&done, "qualification/shared-pointers")[2];
        assert_eq!(
            (build.class, build.reason.as_deref()),
            (
                Class::NotRun,
                Some("not started: the generated files are not installed")
            )
        );
    }

    #[test]
    fn a_case_without_a_root_fails_the_run() {
        let refused = |edit: &dyn Fn(&mut Value)| {
            let mut cases = json!([arithmetic()]);
            edit(&mut cases[0]);
            load_cases(&cases_text(&cases), &Layout::PRODUCTION).expect_err("invalid cases")
        };
        let context = "verification/qualification/cases.json case arithmetic: ";
        let expect = |edit: &dyn Fn(&mut Value), problem: &str| {
            assert_eq!(refused(edit), format!("{context}{problem}"));
        };
        expect(
            &|case| case["start_from"] = json!([]),
            "a case needs at least one root in `start_from`",
        );
        expect(
            &|case| case["type_errors_in"] = json!("Funs.lean"),
            "only an ill-typed case records `type_errors_in`",
        );
        expect(
            &|case| case["models"] = json!("verification/Krepi/Qualification"),
            "`models` names a directory below the reviewed external declarations",
        );
        expect(
            &|case| case["models"] = json!("verification/externals/../Krepi"),
            "`models` names a directory below the reviewed external declarations",
        );
        expect(
            &|case| case["proof"]["module"] = json!("Krepi.Proofs.Arithmetic"),
            "the module of a proof lies below the namespace of the qualification proofs",
        );
        expect(
            &|case| case["proof"]["theorems"] = json!([MUL_MOD, MUL_MOD]),
            "a proof names its theorems, each once",
        );
        expect(
            &|case| case["proof"]["theorems"] = json!(["Nat.le_refl"]),
            "the theorems of a proof lie below its module",
        );
        assert_eq!(
            refused(&|case| case["name"] = json!("../arithmetic")),
            "verification/qualification/cases.json case ../arithmetic: a case name holds only \
             ASCII letters, digits, `-` and `_`"
        );
        let unknown = refused(&|case| case["loop_source"] = json!([]));
        assert!(unknown.contains("unknown field `loop_source`"), "{unknown}");
        let mut ill_typed = ill();
        ill_typed
            .as_object_mut()
            .expect("a case")
            .remove("type_errors_in");
        assert_eq!(
            load_cases(&cases_text(&json!([ill_typed])), &Layout::PRODUCTION),
            Err(
                "verification/qualification/cases.json case ill: an ill-typed case records the \
                 generated file of its type errors (`type_errors_in`)"
                    .to_string()
            )
        );
        let twice = cases_text(&json!([ill(), ill()]));
        assert!(
            load_cases(&twice, &Layout::PRODUCTION)
                .expect_err("twice")
                .ends_with("duplicate name")
        );
        // The phase has no units then, and stops.
        let mut rootless = arithmetic();
        rootless["start_from"] = json!([]);
        let fixture = qualification("rootless", &json!([rootless]));
        let done = run(&fixture);
        assert_eq!(done.receipt.status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        assert_eq!(
            done.failures(),
            [format!(
                "the phase qualification stopped: {context}a case needs at least one root in \
                 `start_from`"
            )]
        );
        assert!(done.receipt.units.is_empty());
        assert!(
            done.receipt
                .commands
                .iter()
                .all(|command| command.unit.is_none())
        );
    }

    #[test]
    fn a_crate_that_cargo_would_build_otherwise_stops_the_phase() {
        let stopped = |label: &str, edit: &dyn Fn(&Fixture)| {
            let fixture = qualification(label, &json!([arithmetic()]));
            edit(&fixture);
            let done = run(&fixture);
            assert_eq!(done.receipt.status, Status::ToolFailure, "{label}");
            assert!(!done.receipt.complete, "{label}");
            assert!(
                done.receipt
                    .commands
                    .iter()
                    .all(|command| command.unit.is_none())
            );
            let failures = done.failures();
            let [failure] = failures.as_slice() else {
                panic!("{failures:?}");
            };
            failure.to_string()
        };
        let manifest = "verification/qualification/Cargo.toml";
        let context = format!("the phase qualification stopped: {manifest}: ");
        assert_eq!(
            stopped("build-script", &|fixture| {
                fixture.write("verification/qualification/build.rs", "fn main() {}\n");
            }),
            format!("{context}its package has a build script, build.rs")
        );
        assert_eq!(
            stopped("features", &|fixture| {
                let features = format!("{MANIFEST}\n[features]\ndefault = [\"pi5\"]\npi5 = []\n");
                fixture.write(manifest, &features);
            }),
            format!("{context}it has [features], which the gate does not allow")
        );
    }

    #[test]
    fn the_cases_file_of_the_snapshot_must_be_the_one_read_at_the_start() {
        let fixture = qualification("cases-changed", &json!([arithmetic()]));
        fixture.commit_all();
        // Git takes the file for unchanged, so the checkout is clean while
        // the run reads other cases than the snapshot's.
        let path = Layout::PRODUCTION.cases;
        fixture.git(&["update-index", "--skip-worktree", path]);
        fixture.write(path, &cases_text(&json!([arithmetic(), ill()])));
        let done = gate(
            &fixture,
            &[],
            vec![phase(fixture.root(), &Layout::PRODUCTION)],
        );
        assert_eq!(done.receipt.status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        assert_eq!(
            done.failures(),
            [format!(
                "the phase qualification stopped: {path} of the snapshot is not the file that the \
                 run read at its start"
            )]
        );
        assert_eq!(status(&done, "qualification/ill").0, Status::NotRun);
        assert_eq!(done.receipt.inputs.clean_after, Some(true));
    }

    #[test]
    fn the_parts_of_a_case_are_imported_together() {
        let parts = json!({
            "name": "parts", "module": "Qual.Parts", "start_from": [],
            "parts": [
                {"module": "Qual.Parts.A", "start_from": ["crate::parts::a"]},
                {"module": "Qual.Parts.B", "start_from": ["crate::parts::b"]},
            ],
            "expect": "ill-typed", "type_errors_in": "Check.lean",
            "diagnostics": [], "external_functions": [], "external_types": [],
        });
        let fixture = qualification("parts", &json!([parts]));
        let error = "error: KrepiGen/Qual/Parts/Check.lean:1:0: import KrepiGen.Qual.Parts.B.Types \
            failed, environment already contains 'instDiscriminantErrorIsize' from \
            KrepiGen.Qual.Parts.A.Types";
        lake_script(
            &fixture,
            "KrepiGen.Qual.Parts.Check",
            &failing("KrepiGen.Qual.Parts.Check", &[error], 1),
        );
        let done = run(&fixture);
        assert_eq!(
            status(&done, "qualification/parts"),
            (Status::Verified, None)
        );
        use Class::{Passed, ProofFailure};
        assert_eq!(
            sites(&done, "qualification/parts"),
            [
                (Site::Charon, Passed),
                (Site::Aeneas, Passed),
                (Site::Charon, Passed),
                (Site::Aeneas, Passed),
                (Site::IllTypedBuild, ProofFailure),
            ]
        );
        let build = commands(&done, "qualification/parts")[4];
        assert_eq!(
            build.argv.last().map(String::as_str),
            Some("KrepiGen.Qual.Parts.Check")
        );
        let work = done.run.path.join("work/cases/parts");
        for part in ["0", "1"] {
            assert!(
                work.join("parts").join(part).join("extract.llbc").is_file(),
                "{part}"
            );
            assert!(
                !work.join("parts").join(part).join("target").exists(),
                "{part}"
            );
        }
        let project = work.join("stage/verification");
        assert_eq!(
            fs::read_to_string(project.join("KrepiGen/Qual/Parts/Check.lean")).expect("the check"),
            "module\npublic import KrepiGen.Qual.Parts.A.Funs\npublic import KrepiGen.Qual.Parts.B.Funs\n"
        );
        for part in ["A", "B"] {
            assert!(
                project
                    .join(format!("KrepiGen/Qual/Parts/{part}/Funs.lean"))
                    .is_file()
            );
        }
        let record = &record(&done).cases["parts"];
        assert_eq!(record.parts, ["Qual.Parts.A", "Qual.Parts.B"]);
        assert_eq!(
            record.type_errors,
            Some(receipt::TypeErrors {
                file: "Check.lean".to_string(),
                errors: 1,
                in_file: 1,
            })
        );
    }

    #[test]
    fn an_ignored_lean_file_does_not_reach_a_case_stage() {
        let fixture = qualification("ignored", &json!([arithmetic()]));
        // A file that Git ignores, and one below the ignored Lake directory,
        // leave the checkout clean.
        fixture.write(
            ".git/info/exclude",
            "/verification/Krepi/Qualification/Stray.lean\n",
        );
        fixture.write("verification/Krepi/Qualification/Stray.lean", "module\n");
        fixture.write("verification/.lake/Stray.lean", "module\n");
        let done = run(&fixture);
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        let stray: Vec<String> = (files_below(&done.run.path).into_iter())
            .filter(|path| path.ends_with("Stray.lean"))
            .collect();
        assert_eq!(stray, Vec::<String>::new());
        let stage = done
            .run
            .path
            .join("work/cases/arithmetic/stage/verification");
        assert!(stage.join("Krepi/Qualification/Arithmetic.lean").is_file());
    }

    #[test]
    fn a_failed_copy_into_a_case_stage_gives_an_incomplete_tool_failure_receipt() {
        let checked = case("checked", "Qual.Checked", "translated");
        let fixture = qualification("stage-copy", &json!([arithmetic(), checked]));
        // A project file that each stage copies is a link to nothing, in
        // the snapshot and in its export.
        let manifest = "verification/lake-manifest.json";
        fs::remove_file(fixture.root().join(manifest)).expect("remove the file");
        fixture.symlink(manifest, "missing.json");
        let done = run(&fixture);
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        let failures = done.failures();
        let [failure] = failures.as_slice() else {
            panic!("{failures:?}");
        };
        let start = format!(
            "the phase qualification stopped: cannot copy {}: ",
            done.run.source().join(manifest).display()
        );
        assert!(failure.starts_with(&start), "{failure}");
        for unit in [
            "qualification/arithmetic".to_string(),
            theorem_unit("arithmetic", MUL_MOD),
            "qualification/checked".to_string(),
        ] {
            assert_eq!(
                status(&done, &unit),
                (Status::NotRun, Some(*failure)),
                "{unit}"
            );
        }
        assert_eq!(
            sites(&done, "qualification/arithmetic"),
            [(Site::Charon, Class::Passed), (Site::Aeneas, Class::Passed)]
        );
        assert!(commands(&done, "qualification/checked").is_empty());
        let cases: Vec<&String> = record(&done).cases.keys().collect();
        assert_eq!(cases, ["arithmetic"]);
        // The copies before it were made.
        let stage = done.run.path.join("work/cases/arithmetic/stage");
        assert_eq!(
            files_below(&stage),
            ["verification/lakefile.toml", "verification/lean-toolchain"]
        );
        // The end snapshot is taken all the same.
        assert!(receipt.inputs.after.is_some());
        assert_eq!(receipt.inputs.after, receipt.inputs.before);
        assert_eq!(receipt.inputs.clean_after, Some(true));
    }

    #[test]
    fn every_convention_has_its_class_at_the_qualification_sites() {
        // Each row of the conventions, at each qualification site that it
        // applies to, through the call site of the phase: the stand-in at
        // that site is the row's tool. The case that expects a rejection
        // meets the row at Charon and Aeneas, and the ill-typed case at its
        // build, and neither may conclude as expected.
        let qualification_sites = [
            Site::Charon,
            Site::Aeneas,
            Site::QualificationBuild,
            Site::IllTypedBuild,
            Site::CaseAudit,
        ];
        let fixture = qualification("conventions", &json!([arithmetic(), nested_loop(), ill()]));
        fixture.commit_all();
        let mut pairs = 0;
        for row in conventions::rows() {
            let program = fixture.root().join("artifacts/rows").join(row.name);
            if let Some(script) = row.script {
                let path = format!("artifacts/rows/{}", row.name);
                fixture.write(&path, &format!("#!/bin/sh\n{script}\n"));
                fixture.chmod(&path, 0o755);
            }
            let program = program.to_str().expect("a UTF-8 path").to_string();
            for &site in row
                .sites
                .iter()
                .filter(|site| qualification_sites.contains(site))
            {
                pairs += 1;
                let context = format!("{} at {}", row.name, word(&site));
                let set = (row.limit, program.clone());
                let mut phase = phase(fixture.root(), &Layout::PRODUCTION);
                let body = phase.body;
                phase.body = Box::new(move |gate: &mut Gate| {
                    gate.overrides = Some((site, set.0, set.1));
                    body(gate)
                });
                let done = gate(&fixture, &[], vec![phase]);
                let forced = match row.class {
                    Class::Budget => Status::Budget,
                    _ => Status::ToolFailure,
                };
                let mut met = Vec::new();
                for case in ["arithmetic", "nested-loop", "ill"] {
                    let unit = unit(case);
                    let skipped = |command: &&Command| {
                        command.class == Class::NotRun && command.limit_seconds > 0.0
                    };
                    let Some(first) = (commands(&done, &unit).into_iter())
                        .find(|command| command.site == site && !skipped(command))
                    else {
                        continue;
                    };
                    met.push(case);
                    assert_eq!(first.class, row.class, "{context}: {case}: {first:?}");
                    assert_eq!(status(&done, &unit).0, forced, "{context}: {case}");
                    if case == "arithmetic" {
                        let theorem = theorem_unit(case, MUL_MOD);
                        assert_eq!(status(&done, &theorem).0, forced, "{context}");
                    }
                }
                let expected: &[&str] = match site {
                    Site::Charon | Site::Aeneas => &["arithmetic", "nested-loop", "ill"],
                    Site::IllTypedBuild => &["ill"],
                    _ => &["arithmetic"],
                };
                assert_eq!(met, expected, "{context}");
                assert_eq!(done.receipt.status, forced, "{context}");
            }
        }
        assert_eq!(pairs, 29);
    }

    #[test]
    fn the_qualification_crate_is_a_workspace_of_one_package() {
        let root = crate::repo::root();
        let layout = Layout::PRODUCTION;
        let output = std::process::Command::new(crate::check::cargo())
            .args(["metadata", "--offline", "--locked", "--format-version", "1"])
            .arg("--manifest-path")
            .arg(root.join(layout.qualification).join("Cargo.toml"))
            .output()
            .expect("run cargo metadata");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stderr}");
        let metadata: Value = serde_json::from_slice(&output.stdout).expect("JSON");
        let packages: Vec<&str> = (metadata["packages"]
            .as_array()
            .expect("the packages")
            .iter())
        .map(|package| package["name"].as_str().expect("a name"))
        .collect();
        assert_eq!(packages, ["formal-qualification"]);
        let lock = include_str!("../../../verification/qualification/Cargo.lock");
        assert_eq!(lock.matches("[[package]]").count(), 1, "{lock}");
        let manifest = include_str!("../../../verification/qualification/Cargo.toml");
        assert_eq!(extract::package_problems(manifest), Ok(Vec::new()));
        let workspace = metadata["workspace_root"]
            .as_str()
            .expect("a workspace root");
        let expected = fs::canonicalize(root.join(layout.qualification)).expect("the crate");
        assert_eq!(fs::canonicalize(workspace).expect("the root"), expected);
    }
}
