//! The mutants of a target, as "Mutants" in `docs/formal-verification.md`
//! describes: the registered ones, which a run builds after their target is
//! verified and judges by where the errors of each build fall; and the
//! source mutants that `cargo xtask formal mutants` generates with a set of
//! operators, judged the same way, with the list of those that survive.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::process::ExitCode;
use std::time::Duration;

use proc_macro2::{LineColumn, Span};
use serde::{Deserialize, Serialize};
use syn::visit::{self, Visit};
use syn::{BinOp, Expr, Lit, UnOp};
use walkdir::WalkDir;

use super::Layout;
use super::lean::{self, Ranges};
use super::outcome::{self, Class, Site, Status};
use super::process::Ran;
use super::receipt::{self, Receipt};
use super::registry::{self, Target};
use super::run::{self, Gate, Request, RunDir};
use super::toolchain::{environment::Tool, sha256};
use super::{externals, extract, inventory, paths, qualify};
use crate::repo::Tree;

/// The budget of a run of `cargo xtask formal mutants`, in place of that of
/// the gate and its targets.
pub const RUN_BUDGET: Duration = Duration::from_secs(14_400);

/// The operators of the source mutants, by the names that `--operator`
/// takes.
pub const OPERATORS: &str =
    "ordering equality arithmetic bitwise logical negation literal condition method";

/// What each operator replaces, `<operator> <text> <replacement>`, where
/// `_` is no text.
const CHANGES: &str = "ordering < <=,ordering <= <,ordering > >=,ordering >= >,\
    equality == !=,equality != ==,arithmetic + -,arithmetic - +,arithmetic * +,\
    arithmetic / *,arithmetic % /,arithmetic += -=,arithmetic -= +=,arithmetic *= +=,\
    arithmetic /= *=,arithmetic %= /=,bitwise & |,bitwise | &,bitwise ^ |,bitwise << >>,\
    bitwise >> <<,bitwise &= |=,bitwise |= &=,bitwise ^= |=,bitwise <<= >>=,bitwise >>= <<=,\
    logical && ||,logical || &&,negation ! _,method checked_add checked_sub,\
    method checked_sub checked_add,method wrapping_add wrapping_sub,\
    method wrapping_sub wrapping_add,method saturating_add saturating_sub,\
    method saturating_sub saturating_add,method min max,method max min";

/// The schema of a list of survivors.
pub const SCHEMA: u32 = 1;

/// What separates a target's unit from the name of a registered mutant in
/// the unit of the mutant.
const MUTANT: &str = "/mutant/";

/// The file of the list of survivors that a run of `formal mutants` writes
/// in its work directory, before the receipt is written.
const DRAFT: &str = "mutants.json";

/// The unit of the registered mutant `mutant` of the target `target`.
pub fn unit(target: &str, mutant: &str) -> String {
    format!("{}{MUTANT}{mutant}", run::target_unit(target))
}

/// The unit of the source mutants of `target` in a run of `formal mutants`.
pub fn generated_unit(target: &str) -> String {
    format!("mutants/{target}")
}

/// The unit whose budget the commands of `unit` share: that of its target
/// for a registered mutant, and its own otherwise.
pub fn owner(unit: &str) -> &str {
    unit.split_once(MUTANT).map_or(unit, |(target, _)| target)
}

/// The units of the mutants of the selected formal target `target`: that
/// of its source mutants when the run generates them, and otherwise one for
/// each registered mutant, unless it registers more than it may.
pub fn units(target: &Target, generate: bool) -> Vec<String> {
    match generate {
        true => vec![generated_unit(&target.name)],
        false if target.mutants.len() > registry::MUTANTS => Vec::new(),
        false => Vec::from_iter(target.mutants.iter().map(|m| unit(&target.name, &m.name))),
    }
}

/// The path of the list of survivors of `target` in `layout`.
pub fn list_path(layout: &Layout, target: &str) -> String {
    format!("{}/{target}.json", layout.mutants)
}

/// Fills in the seconds of each target of `receipt` that has a unit, those
/// of the commands of its unit and of its mutants, and those of each mutant.
pub fn seconds(receipt: &mut Receipt) {
    let mut by_unit: BTreeMap<&str, f64> = BTreeMap::new();
    for command in &receipt.commands {
        *by_unit
            .entry(command.unit.as_deref().unwrap_or(""))
            .or_default() += command.seconds;
    }
    let round = |sum: f64| receipt::seconds(Duration::from_secs_f64(sum));
    for target in receipt.proof_targets.values_mut() {
        let Some(own) = target.unit.as_deref() else {
            continue;
        };
        let mine = by_unit.iter().filter(|(unit, _)| owner(unit) == own);
        target.seconds = round(mine.map(|(_, seconds)| seconds).sum());
        let mutants = by_unit.iter().filter_map(|(unit, seconds)| {
            let name = unit.strip_prefix(own)?.strip_prefix(MUTANT)?;
            Some((name.to_string(), round(*seconds)))
        });
        target.mutants = mutants.collect();
    }
}

/// How the build of a mutant ended: the declarations that failed, and the
/// positions of errors outside every declaration, or what else may explain
/// the failure.
#[derive(Debug, PartialEq)]
pub enum Verdict {
    /// The build failed in the proof modules alone, in a named theorem.
    Rejected {
        failed: BTreeSet<String>,
        outside: Vec<String>,
    },
    /// The build passed, or failed in the proof modules alone but in no named
    /// theorem.
    Accepted {
        failed: BTreeSet<String>,
        outside: Vec<String>,
    },
    /// Something besides errors in the proof modules may explain the failure.
    Inconclusive(Vec<String>),
    /// Lake or a Lean process it ran was killed or ran out of time, so the
    /// build tells nothing about the mutant.
    Killed(String),
}

/// Classifies the build of a mutant, given the proof modules with their
/// declaration ranges in the target's build and the theorems of which one
/// must fail. An error counts against the top-level declaration whose range
/// contains its position; an error outside every range counts against none
/// and is listed by its position.
pub fn verdict(build: &Ran, modules: &[String], ranges: &Ranges, fails: &[String]) -> Verdict {
    if let Some(reason) = outcome::killed(build) {
        return Verdict::Killed(reason);
    }
    let (mut failed, mut outside) = (BTreeSet::new(), Vec::new());
    let status = build.code().unwrap_or_default();
    if status == 0 {
        return Verdict::Accepted { failed, outside };
    }
    let errors = match lean::confined_errors(status, &build.output, modules) {
        Ok(errors) => errors,
        Err(problems) => return Verdict::Inconclusive(problems),
    };
    for (module, line, column) in errors {
        match ranges.at(module, line, column) {
            Some(declared) => failed.extend(declared.names.keys().cloned()),
            None => {
                let position = position(module, line, column);
                if !outside.contains(&position) {
                    outside.push(position);
                }
            }
        }
    }
    if fails.iter().any(|name| failed.contains(name)) {
        Verdict::Rejected { failed, outside }
    } else {
        Verdict::Accepted { failed, outside }
    }
}

/// The problem with a mutant when a theorem of `fails`, of which one must
/// fail, is not a top-level theorem of the target's proof modules, against
/// which no error could count.
pub fn unknown_failures(fails: &[String], ranges: &Ranges) -> Option<String> {
    let unknown = Vec::from_iter(fails.iter().filter(|name| !ranges.theorem(name)));
    let unknown = Vec::from_iter(unknown.into_iter().map(String::as_str)).join(", ");
    (!unknown.is_empty()).then(|| format!("not a theorem of the target's proof modules: {unknown}"))
}

/// A position in a proof module, as Lean prints it in a message.
fn position(module: &str, line: usize, column: usize) -> String {
    format!("{}:{line}:{column}", lean::module_file(module))
}

/// Classifies a failed build of the proofs of a target, `build`: a proof
/// failure, the problem, when Lean reports an error or a warning, which
/// fails the build as well, in one of its proof `modules`, wherever in the
/// file, and otherwise a tool failure, the error, as when Lake or a Lean
/// process it ran was killed.
pub fn build_failure(modules: &[String], build: &Ran) -> Result<String, String> {
    if let Some(reason) = outcome::killed(build) {
        return Err(reason);
    }
    let found = lean::proof_messages(&build.output, modules);
    let messages = messages(&build.output);
    if found.is_empty() {
        return Err(format!("generated or model code did not build: {messages}"));
    }
    let at = found
        .into_iter()
        .map(|(module, line, column)| position(module, line, column));
    Ok(format!(
        "the proofs failed at {}: {messages}",
        Vec::from_iter(at).join(", ")
    ))
}

/// The errors and the warnings that Lean and Lake printed in `output`, as
/// one line: a Lake build fails on a warning as well.
fn messages(output: &str) -> String {
    let lines = output.lines().map(str::trim);
    let kept = lines.filter(|line| line.contains("error:") || line.starts_with("warning:"));
    kept.collect::<Vec<_>>().join(" | ")
}

/// Builds the proofs of `modules` in the stage project `project`, with the
/// hand-written Lean of the export and the root module that imports them,
/// with warnings as errors, as a command of `unit`.
pub fn prove(
    gate: &mut Gate,
    unit: &str,
    project: &Path,
    modules: &[String],
) -> Result<(Option<Ran>, outcome::Verdict), String> {
    let layout = *gate.layout();
    for file in gate.handwritten.clone() {
        lean::copy_into(&gate.source().join(layout.project), project, &file)?;
    }
    let root = lean::root_source(&BTreeSet::from_iter(modules.iter().cloned()));
    let path = project.join(lean::module_file(layout.namespace));
    fs::write(&path, root).map_err(at(&path))?;
    let args = lean::build_args(&[format!("+{}", layout.namespace)], true);
    let build = qualify::lake(Site::TargetBuild, &args, project);
    let (ran, verdict, _) = gate.run(unit, &build, |_| Ok(()));
    Ok((ran, verdict))
}

/// The text of an error of a file operation on `path`.
fn at(path: &Path) -> impl Fn(std::io::Error) -> String + '_ {
    move |error| format!("{}: {error}", path.display())
}

/// A mutant: an edit of a file of the package of its target, and the
/// theorems of which one must fail.
struct Mutation<'a> {
    file: &'a str,
    find: &'a str,
    replace: &'a str,
    fails: &'a [String],
}

/// What a mutant tells.
enum Judged {
    /// The proofs reject it.
    Rejected,
    /// It survives: it was built and judged accepted, for the reason.
    Survived(String),
    /// `cargo check` does not build it.
    Unbuildable,
    /// It tells nothing, for the reason, with the status of its unit.
    Failed(Status, String),
}

/// Copies the package of `target` from the export into `work`, with the
/// Cargo configuration of the export, edits it, and, when `check`, checks
/// that Cargo builds it; then extracts it, installs what the tools generated
/// in a stage and builds the proofs there, all as commands of `unit`, and
/// judges the build with `ranges`. A pattern that does not occur once, an
/// extraction that fails and generated files that cannot be installed are
/// rejections.
fn build(
    gate: &mut Gate,
    target: &Target,
    unit: &str,
    mutation: &Mutation,
    ranges: &Ranges,
    work: &Path,
    check: bool,
) -> Result<Judged, String> {
    let (layout, source) = (*gate.layout(), gate.source());
    let (from, root) = (source.join(layout.kernel), work.join("source"));
    let package = root.join(layout.kernel);
    let rejected = |why: String| Ok(Judged::Failed(Status::Rejected, why));
    let text = fs::read_to_string(from.join(mutation.file)).map_err(at(&from))?;
    if text.matches(mutation.find).count() != 1 {
        return rejected(format!(
            "the pattern must occur exactly once in {}",
            mutation.file
        ));
    }
    copy_tree(&from, &package)?;
    if source.join(paths::CARGO_CONFIG).is_file() {
        let config = root.join(paths::CARGO_CONFIG);
        fs::create_dir_all(root.join(".cargo")).map_err(at(&root))?;
        fs::copy(source.join(paths::CARGO_CONFIG), &config).map_err(at(&config))?;
    }
    let path = package.join(mutation.file);
    fs::write(&path, text.replacen(mutation.find, mutation.replace, 1)).map_err(at(&path))?;
    if check {
        let (target_dir, args) = (
            work.join("check"),
            ["check", "--lib", "--locked", "--quiet"],
        );
        let args = Vec::from_iter(
            args.iter()
                .chain(&["--target", layout.triple])
                .map(|a| a.to_string()),
        );
        let tool = Tool::Charon {
            target_dir: &target_dir,
        };
        let (program, cwd, stdin) = ("cargo", &package, None);
        let request = Request {
            site: Site::CargoCheck,
            tool,
            program,
            args: &args,
            cwd,
            stdin,
        };
        let (_, verdict, _) = gate.run(unit, &request, |_| Ok(()));
        let _ = fs::remove_dir_all(&target_dir);
        match verdict.class {
            Class::Passed => {}
            Class::ProofFailure => return Ok(Judged::Unbuildable),
            _ => {
                return Ok(Judged::Failed(
                    Status::ToolFailure,
                    verdict.reason.unwrap_or_default(),
                ));
            }
        }
    }
    let opaque = Vec::from_iter(target.opaque.iter().map(|opaque| opaque.pattern.clone()));
    let request = extract::Request {
        unit,
        module: target.module.as_deref().unwrap_or_default(),
        package: &package,
        start_from: &target.start_from,
        opaque: &opaque,
        work: &work.join("extract"),
        triple: Some(layout.triple),
    };
    let extraction = extract::extract(gate, &request)?;
    if !extraction.complete {
        return rejected(format!(
            "inconclusive, its extraction failed: {}",
            extraction.diagnostics.join("; ")
        ));
    }
    let stage = work.join("stage");
    if let Err(why) = externals::stage(gate, target, &extraction, &stage)? {
        return rejected(format!(
            "inconclusive, its generated files cannot be installed: {why}"
        ));
    }
    let project = stage.join(Path::new(layout.project).file_name().unwrap_or_default());
    let (ran, verdict) = prove(gate, unit, &project, &target.proof_modules)?;
    let modules = &target.proof_modules;
    let judged = ran.map(|ran| self::verdict(&ran, modules, ranges, mutation.fails));
    Ok(
        match judged.unwrap_or_else(|| Verdict::Killed(verdict.reason.unwrap_or_default())) {
            Verdict::Rejected { .. } => Judged::Rejected,
            Verdict::Accepted { outside, .. } => {
                let mut why = format!(
                    "the mutant was not rejected by {}",
                    mutation.fails.join(", ")
                );
                if !outside.is_empty() {
                    why += &format!(
                        "; errors outside every declaration at {}",
                        outside.join(", ")
                    );
                }
                Judged::Survived(why)
            }
            Verdict::Inconclusive(problems) => {
                let mut shown = Vec::from_iter(problems.iter().take(3).map(String::as_str));
                shown.extend((problems.len() > 3).then_some("…"));
                let shown = shown.join("; ");
                let why =
                    format!("inconclusive, the build did not fail in the proofs alone: {shown}");
                Judged::Failed(Status::Rejected, why)
            }
            Verdict::Killed(why) => {
                Judged::Failed(Status::ToolFailure, format!("inconclusive, {why}"))
            }
        },
    )
}

/// Copies the files below `from` to the same paths below `to`.
fn copy_tree(from: &Path, to: &Path) -> Result<(), String> {
    for entry in WalkDir::new(from) {
        let entry = entry.map_err(|error| format!("cannot copy the package: {error}"))?;
        let path = to.join(entry.path().strip_prefix(from).unwrap_or(entry.path()));
        let copied = match entry.file_type().is_dir() {
            true => fs::create_dir_all(&path),
            false => fs::copy(entry.path(), &path).map(|_| ()),
        };
        copied.map_err(at(&path))?;
    }
    Ok(())
}

/// Runs the mutants of the selected formal target `target` after its unit:
/// with `project`, the stage project where its proofs built and passed the
/// audit, its registered mutants, or the source mutants of `operators` when
/// the run generates them; without it, concludes their units as not run.
/// The declaration ranges of that build, printed as a command of the
/// target's unit, attribute the errors of every mutant's build; when they
/// make no table, every mutant is inconclusive, and the tool failure of the
/// target is returned.
pub fn after(
    gate: &mut Gate,
    target: &Target,
    project: Option<&Path>,
    operators: Option<&[String]>,
) -> Result<Option<String>, String> {
    let units = units(target, operators.is_some());
    let conclude = |gate: &mut Gate, status, why: &str| {
        let why = Some(why.to_string());
        units
            .iter()
            .for_each(|unit| _ = gate.conclude(unit, (status, why.clone())));
    };
    let Some(project) = project else {
        conclude(gate, Status::NotRun, "the target is not verified");
        return Ok(None);
    };
    let own = run::target_unit(&target.name);
    let ranges = match lean::declaration_ranges(gate, &own, project, &target.proof_modules)? {
        Ok(ranges) => ranges,
        Err(problems) => {
            let why = "the declaration ranges of its proofs make no table: ".to_string();
            let why = why + &problems.join("; ");
            conclude(gate, Status::Rejected, &format!("inconclusive, {why}"));
            return Ok(Some(why));
        }
    };
    if let Some(operators) = operators {
        return generated(gate, target, &ranges, operators).map(|()| None);
    }
    let work = gate
        .work()
        .join("targets")
        .join(&target.name)
        .join("mutants");
    for mutant in &target.mutants {
        let (unit, fails) = (unit(&target.name, &mutant.name), &mutant.fails);
        let conclusion = match unknown_failures(fails, &ranges) {
            Some(problem) => (Status::Rejected, Some(problem)),
            None => {
                let (file, find, replace) = (&mutant.file, &mutant.find, &mutant.replace);
                let mutation = Mutation {
                    file,
                    find,
                    replace,
                    fails,
                };
                let work = work.join(&mutant.name);
                match build(gate, target, &unit, &mutation, &ranges, &work, false)? {
                    Judged::Rejected => (Status::Verified, None),
                    Judged::Survived(why) => (Status::Rejected, Some(why)),
                    Judged::Unbuildable => (Status::Rejected, Some("it does not build".into())),
                    Judged::Failed(status, why) => (status, Some(why)),
                }
            }
        };
        gate.conclude(&unit, conclusion);
    }
    Ok(None)
}

/// A source mutant: the point of its edit, `<file>:<line>:<column>` with
/// the file of the repository, its operator, the edit, the inventory key of
/// the function that it edits, and, in a list of survivors, the class and
/// the reason that a reviewer gives it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Survivor {
    pub point: String,
    pub operator: String,
    pub find: String,
    pub replace: String,
    pub function: String,
    pub class: Option<Category>,
    pub reason: Option<String>,
}

/// Why a survivor survives: a lemma that the proofs lack, no theorem about
/// the function that it edits, or a mutant with the meaning of the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Category {
    MissingLemma,
    NoTheorem,
    Equivalent,
}

/// The list of survivors of a target, `<mutants>/<target>.json`, with the
/// commit and the operators of its run, the name of its run directory, the
/// ID of the CI run, if any, and the SHA-256 of its receipt, and its counts.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct List {
    pub schema: u32,
    pub target: String,
    pub commit: String,
    pub operators: Vec<String>,
    pub run: String,
    pub run_id: Option<String>,
    pub receipt_sha256: String,
    pub generated: usize,
    pub killed: usize,
    pub unbuildable: usize,
    pub not_unique: usize,
    pub survivors: Vec<Survivor>,
}

/// The points of the body of a function: the start and the end of the
/// text to replace, the operator and the replacement.
#[derive(Default)]
struct Points(Vec<(LineColumn, LineColumn, &'static str, String)>);

impl Points {
    /// The points of the token `text` at `span`, one for each change.
    fn token(&mut self, span: Span, text: &str) {
        let (start, mut end) = (span.start(), span.start());
        end.column += text.chars().count();
        for change in CHANGES
            .split(',')
            .map(|c| Vec::from_iter(c.split_whitespace()))
        {
            if let [operator, from, to] = change[..]
                && from == text
            {
                self.0.push((
                    start,
                    end,
                    operator,
                    [to, ""][usize::from(to == "_")].to_string(),
                ));
            }
        }
    }
}

/// The span of the first token of a binary operator, and its text.
fn binary(op: &BinOp) -> Option<(Span, &'static str)> {
    macro_rules! table {
        ($($variant:ident $text:literal)*) => {
            match op { $(BinOp::$variant(t) => Some((t.spans[0], $text)),)* _ => None }
        };
    }
    table!(Add "+" Sub "-" Mul "*" Div "/" Rem "%" And "&&" Or "||" BitXor "^" BitAnd "&"
        BitOr "|" Shl "<<" Shr ">>" Eq "==" Lt "<" Le "<=" Ne "!=" Ge ">=" Gt ">"
        AddAssign "+=" SubAssign "-=" MulAssign "*=" DivAssign "/=" RemAssign "%="
        BitXorAssign "^=" BitAndAssign "&=" BitOrAssign "|=" ShlAssign "<<=" ShrAssign ">>=")
}

/// The points of a function body: operators, integer literals, `if`
/// conditions and integer methods, but not in patterns, types, attributes,
/// macro calls, nested items, array lengths or generic arguments.
impl<'ast> Visit<'ast> for Points {
    fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
        if let Some((span, text)) = binary(&node.op) {
            self.token(span, text);
        }
        visit::visit_expr_binary(self, node);
    }
    fn visit_expr_unary(&mut self, node: &'ast syn::ExprUnary) {
        if let UnOp::Not(not) = &node.op {
            self.token(not.spans[0], "!");
        }
        visit::visit_expr_unary(self, node);
    }
    fn visit_expr_lit(&mut self, node: &'ast syn::ExprLit) {
        let Lit::Int(lit) = &node.lit else {
            return;
        };
        let (Ok(value), text) = (lit.base10_parse::<u128>(), lit.to_string()) else {
            return;
        };
        let next = match value {
            0 => 1,
            1 => 0,
            n => n.saturating_add(1),
        };
        let digits = match text.get(..2) {
            Some("0x") => format!("{next:#x}"),
            Some("0o") => format!("{next:#o}"),
            Some("0b") => format!("{next:#b}"),
            _ => next.to_string(),
        };
        let (start, mut end) = (lit.span().start(), lit.span().start());
        end.column += text.chars().count();
        self.0.push((start, end, "literal", digits + lit.suffix()));
    }
    fn visit_expr_if(&mut self, node: &'ast syn::ExprIf) {
        if !matches!(*node.cond, Expr::Let(_)) {
            let start = node.if_token.span.end();
            let end = node.then_branch.brace_token.span.open().start();
            for to in [" true ", " false "] {
                self.0.push((start, end, "condition", to.to_string()));
            }
        }
        visit::visit_expr_if(self, node);
    }
    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        self.token(node.method.span(), &node.method.to_string());
        visit::visit_expr_method_call(self, node);
    }
    fn visit_expr_repeat(&mut self, node: &'ast syn::ExprRepeat) {
        self.visit_expr(&node.expr);
    }
    fn visit_pat(&mut self, _: &'ast syn::Pat) {}
    fn visit_type(&mut self, _: &'ast syn::Type) {}
    fn visit_attribute(&mut self, _: &'ast syn::Attribute) {}
    fn visit_macro(&mut self, _: &'ast syn::Macro) {}
    fn visit_item(&mut self, _: &'ast syn::Item) {}
    fn visit_generic_argument(&mut self, _: &'ast syn::GenericArgument) {}
}

/// The functions of a file outside test code, with their bodies, by the
/// part of their inventory key after `#`.
#[derive(Default)]
struct Bodies<'ast> {
    inline: Vec<String>,
    owner: Option<String>,
    found: Vec<(String, &'ast syn::Block)>,
}

impl<'ast> Bodies<'ast> {
    fn function(&mut self, attrs: &[syn::Attribute], ident: &syn::Ident, body: &'ast syn::Block) {
        if !inventory::is_test(attrs) {
            let prefix = self
                .inline
                .iter()
                .chain(&self.owner)
                .map(|part| part.clone() + "::");
            self.found
                .push((prefix.collect::<String>() + &ident.to_string(), body));
        }
    }
}

impl<'ast> Visit<'ast> for Bodies<'ast> {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        let attrs = match item {
            syn::Item::Fn(item) => return self.function(&item.attrs, &item.sig.ident, &item.block),
            syn::Item::Mod(item) => &item.attrs,
            syn::Item::Impl(item) => &item.attrs,
            syn::Item::Trait(item) => &item.attrs,
            _ => return,
        };
        if !inventory::is_test(attrs) {
            visit::visit_item(self, item);
        }
    }
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        self.inline.push(item.ident.to_string());
        visit::visit_item_mod(self, item);
        self.inline.pop();
    }
    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let outer = std::mem::replace(&mut self.owner, inventory::owner(&item.self_ty));
        visit::visit_item_impl(self, item);
        self.owner = outer;
    }
    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        let outer = self.owner.replace(item.ident.to_string());
        visit::visit_item_trait(self, item);
        self.owner = outer;
    }
    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.function(&item.attrs, &item.sig.ident, &item.block);
    }
    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        if let Some(body) = &item.default {
            self.function(&item.attrs, &item.sig.ident, body);
        }
    }
}

/// The byte offset of `at` in `text`, whose lines start at `starts`.
fn offset(text: &str, starts: &[usize], at: LineColumn) -> Option<usize> {
    let line = &text[*starts.get(at.line.checked_sub(1)?)?..];
    let columns = line.char_indices().map(|(at, _)| at).chain([line.len()]);
    Some(text.len() - line.len() + columns.into_iter().nth(at.column)?)
}

/// The shortest text of `text` that holds the bytes from `start` to `end`,
/// lies within their lines, does not cut a word and occurs once, by its
/// start and end.
fn unique(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    let first = text[..start].rfind('\n').map_or(0, |at| at + 1);
    let last = text[end..].find('\n').map_or(text.len(), |at| end + at);
    let word = |c: char| c.is_alphanumeric() || c == '_';
    let cuts = |at: usize| {
        let (before, after) = (text[..at].chars().next_back(), text[at..].chars().next());
        !(before.is_some_and(word) && after.is_some_and(word))
    };
    for length in (end - start)..=(last - first) {
        for from in first.max(end.saturating_sub(length))..=start.min(last - length) {
            let (to, ok) = (
                from + length,
                text.is_char_boundary(from) && text.is_char_boundary(from + length),
            );
            let once = |window: &str| text.find(window) == text.rfind(window);
            if ok && cuts(from) && cuts(to) && once(&text[from..to]) {
                return Some((from, to));
            }
        }
    }
    None
}

/// The source mutants of `target` with `operators` in the files that `read`
/// gives by their paths, of class `no-theorem` in a function of `unclosed`
/// and without a class otherwise, and the number of points without a text
/// that occurs once in their file.
pub fn generate(
    read: &dyn Fn(&str) -> Option<String>,
    target: &Target,
    operators: &[String],
) -> Result<(Vec<Survivor>, usize), String> {
    let mut files: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for key in target.proves.iter().chain(&target.unclosed) {
        let (file, name) = key
            .split_once('#')
            .ok_or(format!("{key}: not an inventory key"))?;
        files.entry(file).or_default().insert(name);
    }
    let (mut mutants, mut not_unique, mut seen) = (Vec::new(), 0, BTreeSet::new());
    for (file, names) in files {
        let text = read(file).ok_or(format!("{file} cannot be read"))?;
        let text = text.as_str();
        let parsed = syn::parse_file(text).map_err(|error| format!("{file}: {error}"))?;
        let mut bodies = Bodies::default();
        bodies.visit_file(&parsed);
        let starts = Vec::from_iter(
            [0].into_iter()
                .chain(text.match_indices('\n').map(|(at, _)| at + 1)),
        );
        for (name, body) in bodies
            .found
            .iter()
            .filter(|(name, _)| names.contains(name.as_str()))
        {
            let mut points = Points::default();
            points.visit_block(body);
            for (start, end, operator, to) in points.0 {
                let bytes = offset(text, &starts, start).zip(offset(text, &starts, end));
                let Some((from, until)) =
                    bytes.filter(|_| operators.iter().any(|op| op == operator))
                else {
                    continue;
                };
                let Some((left, right)) = unique(text, from, until) else {
                    not_unique += 1;
                    continue;
                };
                let (find, replace) = (
                    &text[left..right],
                    [&text[left..from], &to, &text[until..right]].concat(),
                );
                let function = format!("{file}#{name}");
                let class = target.unclosed.contains(&function);
                if seen.insert((file, find.to_string(), replace.clone())) {
                    mutants.push(Survivor {
                        point: format!("{file}:{}:{}", start.line, start.column + 1),
                        operator: operator.to_string(),
                        find: find.to_string(),
                        replace,
                        function,
                        class: class.then_some(Category::NoTheorem),
                        reason: None,
                    });
                }
            }
        }
    }
    Ok((mutants, not_unique))
}

/// Generates the source mutants of `target` with `operators` from the
/// export and runs each in a stage of its own, with the theorems of all its
/// obligations to fail, as commands of its unit; concludes the unit, and
/// writes the draft of its list of survivors when every mutant was decided.
/// A theorem of the obligations outside the top-level theorems of the
/// proofs rejects the unit before any mutant runs.
fn generated(
    gate: &mut Gate,
    target: &Target,
    ranges: &Ranges,
    operators: &[String],
) -> Result<(), String> {
    let (layout, unit) = (*gate.layout(), generated_unit(&target.name));
    let fails = Vec::from_iter(target.obligations.iter().flat_map(|o| o.theorems.clone()));
    if let Some(problem) = unknown_failures(&fails, ranges) {
        gate.conclude(&unit, (Status::Rejected, Some(problem)));
        return Ok(());
    }
    let source = gate.source();
    let read = |file: &str| fs::read_to_string(source.join(file)).ok();
    let (points, not_unique) = generate(&read, target, operators)?;
    let (operators, generated) = (operators.to_vec(), points.len());
    let (target_name, schema) = (target.name.clone(), SCHEMA);
    let mut list = List {
        schema,
        target: target_name,
        operators,
        generated,
        not_unique,
        ..List::default()
    };
    let (mut failed, work) = (Vec::new(), gate.work().join("mutants").join(&target.name));
    for (index, point) in points.into_iter().enumerate() {
        let file = point.point.split(':').next().unwrap_or_default();
        let file = file
            .strip_prefix(&format!("{}/", layout.kernel))
            .unwrap_or(file);
        let (find, replace, fails) = (&point.find, &point.replace, &fails[..]);
        let work = work.join(index.to_string());
        let judged = build(
            gate,
            target,
            &unit,
            &Mutation {
                file,
                find,
                replace,
                fails,
            },
            ranges,
            &work,
            true,
        )?;
        let _ = fs::remove_dir_all(&work);
        match judged {
            Judged::Rejected => list.killed += 1,
            Judged::Survived(_) => list.survivors.push(point),
            Judged::Unbuildable => list.unbuildable += 1,
            Judged::Failed(_, why) => failed.push(format!("{}: {why}", point.point)),
        }
    }
    let count = failed.len();
    let why = (count > 0).then(|| format!("{count} mutants tell nothing: {}", failed.join("; ")));
    if gate.conclude(
        &unit,
        (
            [Status::Verified, Status::Rejected][usize::from(count > 0)],
            why,
        ),
    ) == Status::Verified
    {
        let path = gate.work().join(DRAFT);
        fs::write(&path, serde_json::to_string_pretty(&list).expect("a list"))
            .map_err(at(&path))?;
    }
    Ok(())
}

/// After a run of `formal mutants` of `target` that ended with `code`,
/// writes its list of survivors from the draft of the run `run`, with the
/// commit and the receipt summary, as `<mutants>/<target>.json` of `root`,
/// and prints its counts; a run that is not `SCOPED` or left no draft
/// writes no list.
pub fn write_list(
    root: &Path,
    layout: &Layout,
    target: &str,
    run: &RunDir,
    receipt: &Receipt,
    code: ExitCode,
) -> ExitCode {
    let draft = fs::read_to_string(run.path.join("work").join(DRAFT));
    let (true, Ok(Ok(mut list)), Ok(bytes)) = (
        receipt.status == Status::Scoped,
        draft.map(|t| serde_json::from_str::<List>(&t)),
        fs::read(run.receipt()),
    ) else {
        println!("formal mutants: no list of survivors");
        return ExitCode::FAILURE;
    };
    (list.commit, list.run) = (
        receipt.commit.clone().unwrap_or_default(),
        receipt.run.clone(),
    );
    (list.run_id, list.receipt_sha256) = (receipt.trigger.run_id.clone(), sha256(&bytes));
    let path = root.join(list_path(layout, target));
    let text = serde_json::to_string_pretty(&list).expect("a list") + "\n";
    if let Err(error) =
        fs::create_dir_all(root.join(layout.mutants)).and_then(|()| fs::write(&path, text))
    {
        eprintln!("cannot write {}: {error}", path.display());
        return ExitCode::FAILURE;
    }
    let (generated, killed, survived) = (list.generated, list.killed, list.survivors.len());
    let (unbuildable, not_unique, path) = (list.unbuildable, list.not_unique, path.display());
    println!(
        "formal mutants: {generated} generated, {killed} killed, {survived} survived, {unbuildable} do not build, {not_unique} points without a text that occurs once; {path}"
    );
    code
}

/// The problems of the lists of survivors in `tree` of `layout`, whose
/// registry has `targets`: a list that does not parse, of another schema,
/// of a target that the registry does not have or not at its path, a
/// survivor without a class or a reason, and one in a function of
/// `unclosed` of another class than `no-theorem`; and the inventory keys of
/// the functions of the survivors that no theorem covers.
pub fn list_problems(
    tree: &Tree,
    layout: &Layout,
    targets: &[Target],
) -> (Vec<String>, BTreeSet<String>) {
    let (mut problems, mut uncovered) = (Vec::new(), BTreeSet::new());
    let below = |path: &&str| {
        path.strip_prefix(layout.mutants)
            .is_some_and(|r| r.starts_with('/'))
    };
    for (path, text) in tree.texts().filter(|(path, _)| below(path)) {
        let list = match serde_json::from_str::<List>(text) {
            Ok(list) if list.schema == SCHEMA => list,
            Ok(list) => {
                problems.push(format!(
                    "{path}: schema {} where {SCHEMA} is expected",
                    list.schema
                ));
                continue;
            }
            Err(error) => {
                problems.push(format!("{path}: not a list of survivors: {error}"));
                continue;
            }
        };
        let registered = targets.iter().find(|target| target.name == list.target);
        if registered.is_none() || path != list_path(layout, &list.target) {
            problems.push(format!("{path}: not the list of a registered target"));
        }
        for survivor in &list.survivors {
            let point = &survivor.point;
            let blank = survivor
                .reason
                .as_deref()
                .is_none_or(|reason| reason.trim().is_empty());
            let unclosed = registered.is_some_and(|t| t.unclosed.contains(&survivor.function));
            match survivor.class {
                None => problems.push(format!("{path}: the survivor at {point} has no class")),
                Some(_) if blank => {
                    problems.push(format!("{path}: the survivor at {point} has no reason"))
                }
                Some(Category::NoTheorem) => _ = uncovered.insert(survivor.function.clone()),
                Some(_) if unclosed => problems.push(format!(
                    "{path}: the survivor at {point} is in an unclosed function, not no-theorem"
                )),
                Some(_) => {}
            }
        }
    }
    (problems, uncovered)
}

/// The command line of `cargo xtask formal mutants`, with the text `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let target = clap::Arg::new("target").value_name("TARGET").required(true);
    let operator = clap::Arg::new("operator")
        .long("operator")
        .value_name("NAME");
    let parser = clap::builder::PossibleValuesParser::new(OPERATORS.split(' '));
    let operator = operator
        .action(clap::ArgAction::Append)
        .value_parser(parser);
    let operator = operator.help("Generate the mutants of this operator only; may be repeated");
    let calibration = clap::arg!(--calibration "Run in the layout of the calibration target");
    clap::Command::new("mutants")
        .about(about)
        .args([target, operator, calibration])
}

/// The operators that `cargo xtask formal mutants` was given, or all of
/// them, in the order of [`OPERATORS`].
pub fn operators(matches: &clap::ArgMatches) -> Vec<String> {
    let given = BTreeSet::from_iter(matches.get_many::<String>("operator").into_iter().flatten());
    let kept = OPERATORS
        .split(' ')
        .filter(|op| given.is_empty() || given.contains(&op.to_string()));
    kept.map(str::to_string).collect()
}

#[cfg(test)]
mod tests {
    //! The logs and range tables are those of `fixtures/mutants/`, which the
    //! tests of `lean.rs` describe; the runs are those of the fixture of the
    //! targets of `run.rs`.

    use std::time::Duration;

    use super::*;
    use crate::formal::fixture::{self, Fixture};
    use crate::formal::process::{Ended, Limit, LimitBy};
    use crate::formal::run::tests::{
        Done, gate, generating_run, register, target_run, two_targets, with_targets,
    };

    const FAILED: &str = include_str!("fixtures/mutants/failed.txt");
    const MUTANT: &str = include_str!("fixtures/mutants/calibration-mutant.txt");
    const RANGES: &str = include_str!("fixtures/mutants/ranges.txt");
    const CALIBRATION_RANGES: &str = include_str!("fixtures/mutants/calibration-ranges.txt");

    /// A captured text without its first line, which names the command.
    fn captured(text: &str) -> &str {
        text.split_once('\n').expect("a header line").1
    }

    fn names(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| name.to_string()).collect()
    }

    /// A build that ended as `ended` and printed `output`.
    fn lake(ended: Ended, output: &str) -> Ran {
        let limit = Limit {
            duration: Duration::from_secs(60),
            by: LimitBy::Cap,
        };
        let (name, group, output) = ("target-build".to_string(), None, output.to_string());
        let (seconds, stdout, stderr, survivors) = (Duration::ZERO, None, None, false);
        Ran {
            name,
            group,
            ended,
            limit,
            seconds,
            stdout,
            stderr,
            output,
            survivors,
        }
    }

    /// The table of the fixture module and that of the calibration proofs.
    fn tables() -> (Ranges, Ranges) {
        let fixture = captured(RANGES).replace("krepi-ranges-missing Krepi.Proofs.Missing\n", "");
        let fixture = Ranges::parse(&fixture, &names(&["Krepi.Proofs.Fixture"]));
        let calibration = Ranges::parse(
            captured(CALIBRATION_RANGES),
            &names(&["Krepi.Proofs.Calibration"]),
        );
        (fixture.expect("a table"), calibration.expect("a table"))
    }

    #[test]
    fn a_mutant_is_rejected_only_by_errors_in_the_proofs() {
        let (fixture, calibration) = tables();
        let theorem = |name: &str| format!("Krepi.Proofs.Calibration.{name}");
        let modules = names(&["Krepi.Proofs.Calibration"]);
        let mutant = lake(Ended::Exited(1), captured(MUTANT));
        let failed = BTreeSet::from([theorem("alloc_spec")]);
        let rejected = Verdict::Rejected {
            failed: failed.clone(),
            outside: vec![],
        };
        assert_eq!(
            verdict(&mutant, &modules, &calibration, &[theorem("alloc_spec")]),
            rejected
        );
        let accepted = Verdict::Accepted {
            failed,
            outside: vec![],
        };
        assert_eq!(
            verdict(&mutant, &modules, &calibration, &[theorem("charge_spec")]),
            accepted
        );
        let passed = lake(
            Ended::Exited(0),
            "Build completed successfully (1806 jobs).\n",
        );
        let empty = Verdict::Accepted {
            failed: BTreeSet::new(),
            outside: vec![],
        };
        assert_eq!(
            verdict(&passed, &modules, &calibration, &[theorem("alloc_spec")]),
            empty
        );
        // The private theorem `hidden` of the fixture is a named theorem; the
        // errors in a definition, a `where` function and the attribute of
        // another theorem count against those, and those outside every
        // declaration are listed.
        let fixture_modules = names(&["Krepi.Proofs.Fixture"]);
        let build = lake(Ended::Exited(1), captured(FAILED));
        let of = |name: &str| format!("Krepi.Proofs.Fixture.{name}");
        let failed = BTreeSet::from_iter(["documented", "double", "hidden", "withHelper"].map(of));
        let outside = vec![
            "Krepi/Proofs/Fixture.lean:45:0".to_string(),
            "Krepi/Proofs/Fixture.lean:48:26".into(),
        ];
        let rejected = Verdict::Rejected {
            failed: failed.clone(),
            outside: outside.clone(),
        };
        assert_eq!(
            verdict(&build, &fixture_modules, &fixture, &[of("hidden")]),
            rejected
        );
        assert_eq!(
            verdict(&build, &fixture_modules, &fixture, &[of("plain")]),
            Verdict::Accepted { failed, outside }
        );
        // A log that does not keep its rules tells nothing.
        let other = lake(Ended::Exited(2), captured(MUTANT));
        let found = verdict(&other, &modules, &calibration, &[theorem("alloc_spec")]);
        assert_eq!(
            found,
            Verdict::Inconclusive(vec!["Lake ended with status 2".to_string()])
        );
    }

    #[test]
    fn a_killed_build_of_a_mutant_tells_nothing_about_it() {
        let (_, calibration) = tables();
        let modules = names(&["Krepi.Proofs.Calibration"]);
        let fails = names(&["Krepi.Proofs.Calibration.alloc_spec"]);
        for ended in [Ended::Signaled(9), Ended::TimedOut, Ended::Exited(137)] {
            let build = lake(ended, captured(MUTANT));
            let found = verdict(&build, &modules, &calibration, &fails);
            assert!(matches!(found, Verdict::Killed(_)), "{found:?}");
        }
        let killed = captured(MUTANT).replace(
            "Some required",
            "error: Lean exited with code 137\nSome required",
        );
        let found = verdict(
            &lake(Ended::Exited(1), &killed),
            &modules,
            &calibration,
            &fails,
        );
        assert!(matches!(found, Verdict::Killed(_)), "{found:?}");
    }

    #[test]
    fn a_mutant_names_theorems_of_the_proofs() {
        let (fixture, _) = tables();
        let of = |name: &str| format!("Krepi.Proofs.Fixture.{name}");
        assert_eq!(
            unknown_failures(&[of("plain"), of("hidden")], &fixture),
            None
        );
        let unknown = unknown_failures(&[of("plain"), of("double"), of("absent")], &fixture);
        let expected = "not a theorem of the target's proof modules: Krepi.Proofs.Fixture.double, Krepi.Proofs.Fixture.absent";
        assert_eq!(unknown.as_deref(), Some(expected));
    }

    #[test]
    fn a_failed_target_build_is_a_proof_failure_only_with_a_message_in_the_proofs() {
        let modules = names(&["Krepi.Proofs.Calibration"]);
        let build = lake(Ended::Exited(1), captured(MUTANT));
        let failure = build_failure(&modules, &build).expect("a proof failure");
        assert!(
            failure
                .starts_with("the proofs failed at Krepi/Proofs/Calibration.lean:120:2: error: "),
            "{failure}"
        );
        let other = captured(MUTANT).replace(
            "Krepi/Proofs/Calibration.lean",
            "KrepiGen/Calibration/Funs.lean",
        );
        let failure =
            build_failure(&modules, &lake(Ended::Exited(1), &other)).expect_err("a tool failure");
        assert!(
            failure.starts_with("generated or model code did not build: "),
            "{failure}"
        );
        let killed = build_failure(&modules, &lake(Ended::Signaled(9), captured(MUTANT)));
        assert_eq!(
            killed,
            Err("target-build was ended by signal 9".to_string())
        );
    }

    /// The registry of the target `t` and `p` of the fixture with the mutant
    /// of `t` given `entries`.
    fn with_mutant(entries: serde_json::Value) -> String {
        let mut registry: serde_json::Value =
            serde_json::from_str(&two_targets(1_800, 1)).expect("JSON");
        let mutant = registry[0]["mutants"][0]
            .as_object_mut()
            .expect("the mutant");
        mutant.extend(entries.as_object().expect("entries").clone());
        registry.to_string()
    }

    #[test]
    fn a_mutant_is_rejected_unless_it_is_judged_rejected_by_its_proofs() {
        let (absent, theorem) = ("Krepi.Proofs.T.absent", "Krepi.Proofs.T.f_spec");
        let once = "the pattern must occur exactly once in src/lib.rs";
        let cases = [
            // The pattern occurs neither once nor twice.
            (
                serde_json::json!({"find": "no_alloc"}),
                None,
                once.to_string(),
            ),
            (
                serde_json::json!({}),
                Some("#![no_std]\n// no_std\n"),
                once.to_string(),
            ),
            // It names a theorem outside the proofs.
            (
                serde_json::json!({"fails": [theorem, absent]}),
                None,
                format!("not a theorem of the target's proof modules: {absent}"),
            ),
        ];
        for (index, (entries, source, reason)) in cases.into_iter().enumerate() {
            let fixture = with_targets(&format!("mutant-{index}"), &with_mutant(entries));
            if let Some(source) = source {
                fixture.write("kernel/src/lib.rs", source);
                fixture.commit_all();
            }
            let done = gate(&fixture, &[], target_run(&fixture, &[]));
            assert_eq!(
                fixture::status(&done, "target/t"),
                (Status::Verified, None),
                "case {index}"
            );
            let rejected = (Status::Rejected, Some(reason.as_str()));
            assert_eq!(
                fixture::status(&done, "target/t/mutant/m0"),
                rejected,
                "case {index}"
            );
            assert!(fixture::commands(&done, "target/t/mutant/m0").is_empty());
            assert_eq!(done.receipt.status, Status::Rejected);
        }
    }

    #[test]
    fn a_mutant_whose_extraction_fails_or_that_survives_fails_the_run() {
        // Charon fails in the package of the mutant.
        let fixture = with_targets("mutant-extraction", &two_targets(1_800, 1));
        let failing = format!(
            "case $PWD in */mutants/*) echo 'error: no crate' >&2; exit 1 ;; esac\n{}",
            fixture::CHARON
        );
        fixture.tool("charon", &failing);
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        let (status, reason) = fixture::status(&done, "target/t/mutant/m0");
        assert_eq!(status, Status::Rejected);
        assert_eq!(
            reason,
            Some("inconclusive, its extraction failed: error: no crate")
        );
        assert_eq!(done.receipt.status, Status::Rejected);
        // The proofs build in the stage of the mutant: it survives.
        let fixture = with_targets("mutant-survives", &two_targets(1_800, 1));
        fixture::lake_script(&fixture, "+Krepi", "");
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        let survived = (
            Status::Rejected,
            Some("the mutant was not rejected by Krepi.Proofs.T.f_spec"),
        );
        assert_eq!(fixture::status(&done, "target/t/mutant/m0"), survived);
        // The seconds of the mutant are those of its commands, and count in
        // those of its target.
        let target = &done.receipt.proof_targets["t"];
        let own: f64 = fixture::commands(&done, "target/t/mutant/m0")
            .iter()
            .map(|c| c.seconds)
            .sum();
        assert_eq!(Vec::from_iter(target.mutants.keys()), ["m0"]);
        assert!((target.mutants["m0"] - own).abs() < 0.01 && target.seconds >= own);
    }

    #[test]
    fn a_run_of_source_mutants_writes_the_list_of_its_target() {
        let fixture = with_targets("generated", &two_targets(1_800, 1));
        let operators = Vec::from_iter(OPERATORS.split(' ').map(str::to_string));
        let done = gate(
            &fixture,
            &["t"],
            generating_run(&fixture, &["t"], Some(operators.clone())),
        );
        assert_eq!(done.receipt.status, Status::Scoped, "{:?}", done.failures());
        assert_eq!(
            fixture::status(&done, "mutants/t"),
            (Status::Verified, None)
        );
        assert!(!done.receipt.units.contains_key("target/t/mutant/m0"));
        let code = write_list(
            fixture.root(),
            &Layout::PRODUCTION,
            "t",
            &done.run,
            &done.receipt,
            done.code,
        );
        assert_eq!(code, ExitCode::SUCCESS);
        let path = fixture.root().join("verification/mutants/t.json");
        assert_eq!(
            list_path(&Layout::PRODUCTION, "t"),
            "verification/mutants/t.json"
        );
        let list: List =
            serde_json::from_str(&fs::read_to_string(path).expect("the list")).expect("a list");
        let receipt = fs::read(done.run.receipt()).expect("the receipt");
        assert_eq!(
            (list.schema, list.target.as_str(), list.operators),
            (SCHEMA, "t", operators)
        );
        assert_eq!(
            (list.run, list.receipt_sha256),
            (done.receipt.run.clone(), sha256(&receipt))
        );
        assert_eq!(Some(list.commit), done.receipt.commit);
        // Without a verified target, no list is written.
        fixture::lake_script(&fixture, "+Krepi", "exit 1\n");
        let done = gate(
            &fixture,
            &["t"],
            generating_run(&fixture, &["t"], Some(vec!["literal".into()])),
        );
        assert_eq!(fixture::status(&done, "mutants/t").0, Status::NotRun);
        let code = write_list(
            fixture.root(),
            &Layout::PRODUCTION,
            "t",
            &done.run,
            &done.receipt,
            done.code,
        );
        assert_eq!(code, ExitCode::FAILURE);
    }

    #[test]
    fn a_run_of_source_mutants_that_is_not_scoped_writes_no_list() {
        let fixture = with_targets("generated-failed", &two_targets(1_800, 1));
        let operators = Some(vec!["literal".to_string()]);
        let done = gate(
            &fixture,
            &["t"],
            generating_run(&fixture, &["t"], operators.clone()),
        );
        assert_eq!(done.receipt.status, Status::Scoped, "{:?}", done.failures());
        let path = fixture.root().join(list_path(&Layout::PRODUCTION, "t"));
        let write = |done: &Done, receipt: &Receipt| {
            let (root, layout) = (fixture.root(), &Layout::PRODUCTION);
            write_list(root, layout, "t", &done.run, receipt, ExitCode::FAILURE)
        };
        // The draft of a verified unit of mutants, in a run that another
        // unit failed.
        let mut receipt = done.receipt.clone();
        receipt.status = Status::Rejected;
        assert_eq!(write(&done, &receipt), ExitCode::FAILURE);
        assert!(!path.exists());
        // A theorem of the obligations that the ranges do not hold as a
        // theorem rejects the unit before a mutant runs.
        let ranges = "echo 'krepi-ranges-module Krepi.Proofs.T 0'; exit 0\n";
        fixture::lake_script(&fixture, "ranges", ranges);
        let done = gate(
            &fixture,
            &["t"],
            generating_run(&fixture, &["t"], operators),
        );
        let reason = "not a theorem of the target's proof modules: Krepi.Proofs.T.f_spec";
        assert_eq!(
            fixture::status(&done, "mutants/t"),
            (Status::Rejected, Some(reason))
        );
        assert!(fixture::commands(&done, "mutants/t").is_empty());
        assert_eq!(write(&done, &done.receipt), ExitCode::FAILURE);
        assert!(!path.exists());
    }

    /// The source of the tests of the generation, in the file `FILE`.
    const SOURCE: &str = r#"pub struct Table { used: u32 }

impl Table {
    pub fn charge(&mut self, cost: u32) -> Option<u32> {
        if self.used + cost > LIMIT && !self.full() {
            return None;
        }
        let [a, b] = [0u8; 2];
        while self.used < 0x10 {
            self.used += 1;
        }
        match cost { 3 => Some(1), _ => self.used.checked_sub(cost).map(|c| c.min(9)) }
    }
}

const LIMIT: u32 = 7;

pub fn plain(x: u32) -> bool { x == 4 || x >> 2 != 0 }

pub fn other(x: u32) -> bool { x == 4 }

pub fn twice(x: u32) -> u32 {
    let y = x + 1;
    let y = x + 1;
    y
}

#[cfg(test)]
mod tests { fn t() { let _ = 1 + 1; } }
"#;

    const FILE: &str = "kernel/src/lib.rs";

    /// The source mutants of the functions `keys` of [`SOURCE`] with
    /// `operators`, which the target proves.
    fn generated_from(keys: &[&str], operators: &[&str]) -> (Vec<Survivor>, usize) {
        generated_in("proves", keys, operators)
    }

    /// The source mutants of the functions `keys` of [`SOURCE`], in the
    /// list `list` of the target, with `operators`.
    fn generated_in(list: &str, keys: &[&str], operators: &[&str]) -> (Vec<Survivor>, usize) {
        let tree = Tree::from_files(&[(FILE, SOURCE)]);
        let registry = serde_json::json!({"schema": 2, "specifications": [], "targets": [{"name": "t", list: keys}]});
        let target = registry::parse(&registry.to_string())
            .expect("a registry")
            .targets
            .remove(0);
        let read = |file: &str| tree.text(file).map(str::to_string);
        generate(&read, &target, &names(operators)).expect("mutants")
    }

    /// The source that `mutant` gives.
    fn applied(mutant: &Survivor) -> String {
        assert_eq!(SOURCE.matches(&mutant.find).count(), 1, "{mutant:?}");
        SOURCE.replacen(&mutant.find, &mutant.replace, 1)
    }

    #[test]
    fn the_operators_change_the_bodies_of_the_functions_of_the_target() {
        let all = Vec::from_iter(OPERATORS.split(' '));
        let (mutants, missing) = generated_from(&["kernel/src/lib.rs#Table::charge"], &all);
        let sources = Vec::from_iter(mutants.iter().map(|m| (m.operator.as_str(), applied(m))));
        let expected = [
            (
                "condition",
                "if self.used + cost > LIMIT && !self.full() {",
                "if true {",
            ),
            (
                "condition",
                "if self.used + cost > LIMIT && !self.full() {",
                "if false {",
            ),
            ("logical", "LIMIT && !", "LIMIT || !"),
            ("ordering", "cost > LIMIT", "cost >= LIMIT"),
            ("arithmetic", "used + cost", "used - cost"),
            ("negation", "!self", "self"),
            ("literal", "[0u8; 2]", "[1u8; 2]"),
            ("ordering", "used < 0x10", "used <= 0x10"),
            ("literal", "0x10", "0x11"),
            ("arithmetic", "used += 1", "used -= 1"),
            ("literal", "+= 1", "+= 0"),
            ("literal", "Some(1)", "Some(0)"),
            ("method", "checked_sub", "checked_add"),
            ("method", "c.min(9)", "c.max(9)"),
            ("literal", "min(9)", "min(10)"),
        ];
        for (operator, from, to) in expected {
            let source = SOURCE.replacen(from, to, 1);
            assert!(
                sources.contains(&(operator, source)),
                "{operator}: {from} -> {to}"
            );
        }
        // Not the pattern of a `match` arm, the length of an array, a `let`
        // pattern, a `while` condition, a constant or the test module.
        assert_eq!(
            (mutants.len(), missing),
            (expected.len(), 0),
            "{sources:#?}"
        );
        assert!(
            mutants
                .iter()
                .all(|m| m.function == "kernel/src/lib.rs#Table::charge")
        );
        assert!(
            mutants
                .iter()
                .all(|m| m.point.starts_with("kernel/src/lib.rs:"))
        );
        let (some, _) = generated_from(&["kernel/src/lib.rs#Table::charge"], &["method"]);
        assert_eq!(some.len(), 2);
        // The mutants of a proved function have no class, and those of an
        // unclosed one no theorem.
        assert!(mutants.iter().all(|m| m.class.is_none()));
        let (unclosed, _) = generated_in("unclosed", &["kernel/src/lib.rs#other"], &["equality"]);
        assert_eq!(
            Vec::from_iter(unclosed.iter().map(|m| m.class)),
            [Some(Category::NoTheorem)]
        );
    }

    #[test]
    fn a_point_takes_the_shortest_text_that_occurs_once_or_none() {
        let keys = [
            "kernel/src/lib.rs#plain",
            "kernel/src/lib.rs#other",
            "kernel/src/lib.rs#twice",
        ];
        let (mutants, missing) = generated_from(&keys, &["equality", "bitwise", "arithmetic"]);
        let edits = Vec::from_iter(
            mutants
                .iter()
                .map(|m| (m.find.as_str(), m.replace.as_str())),
        );
        // `x == 4` occurs twice, and the two lines of `twice` are the same.
        let expected = [
            ("== 4 |", "!= 4 |"),
            ("!=", "=="),
            (">>", "<<"),
            ("== 4 }", "!= 4 }"),
        ];
        assert_eq!(edits, expected);
        assert_eq!(missing, 2);
        assert_eq!(unique("ab ab abc", 6, 7), Some((6, 9)));
        assert_eq!(unique("ab\nab", 3, 4), None);
    }

    /// A list of `target` with one survivor of class `class` and `reason`.
    fn list(target: &str, class: Option<Category>, reason: Option<&str>) -> String {
        let survivor = Survivor {
            point: "kernel/src/lib.rs:5:22".into(),
            operator: "arithmetic".into(),
            find: "used + cost".into(),
            replace: "used - cost".into(),
            function: "kernel/src/lib.rs#Table::charge".into(),
            class,
            reason: reason.map(str::to_string),
        };
        let list = List {
            schema: SCHEMA,
            target: target.into(),
            survivors: vec![survivor],
            ..List::default()
        };
        serde_json::to_string_pretty(&list).expect("JSON")
    }

    #[test]
    fn a_survivor_without_a_class_fails_the_check() {
        let registry = r#"{"schema": 2, "specifications": [], "targets": [{"name": "t"}]}"#;
        let targets = registry::parse(registry).expect("a registry").targets;
        let path = "verification/mutants/t.json";
        let check = |text: &str| {
            list_problems(
                &Tree::from_files(&[(path, text)]),
                &Layout::PRODUCTION,
                &targets,
            )
        };
        let (problems, _) = check(&list("t", None, None));
        assert_eq!(
            problems,
            [format!(
                "{path}: the survivor at kernel/src/lib.rs:5:22 has no class"
            )]
        );
        let (problems, _) = check(&list("t", Some(Category::MissingLemma), Some(" ")));
        assert_eq!(
            problems,
            [format!(
                "{path}: the survivor at kernel/src/lib.rs:5:22 has no reason"
            )]
        );
        let (problems, uncovered) = check(&list(
            "t",
            Some(Category::NoTheorem),
            Some("No theorem covers it."),
        ));
        assert!(problems.is_empty());
        assert_eq!(
            Vec::from_iter(uncovered),
            ["kernel/src/lib.rs#Table::charge"]
        );
        let lemma = list(
            "t",
            Some(Category::MissingLemma),
            Some("No lemma bounds it."),
        );
        assert_eq!(check(&lemma), (Vec::new(), BTreeSet::new()));
        // A survivor in an unclosed function has no theorem.
        let registry = r#"{"schema": 2, "specifications": [],
            "targets": [{"name": "t", "unclosed": ["kernel/src/lib.rs#Table::charge"]}]}"#;
        let unclosed = registry::parse(registry).expect("a registry").targets;
        let tree = Tree::from_files(&[(path, &lemma)]);
        assert_eq!(
            list_problems(&tree, &Layout::PRODUCTION, &unclosed).0,
            [format!(
                "{path}: the survivor at kernel/src/lib.rs:5:22 is in an unclosed function, not no-theorem"
            )]
        );
        let (problems, _) = check(&list(
            "u",
            Some(Category::Equivalent),
            Some("Same meaning."),
        ));
        assert_eq!(
            problems,
            [format!("{path}: not the list of a registered target")]
        );
        let (problems, _) = check("{}");
        assert!(
            problems[0].starts_with(&format!("{path}: not a list of survivors: ")),
            "{problems:?}"
        );
    }

    #[test]
    fn the_units_of_the_mutants_share_the_budget_of_their_target() {
        assert_eq!(unit("t", "m"), "target/t/mutant/m");
        assert_eq!(owner(&unit("t", "m")), "target/t");
        assert_eq!(owner("target/t"), "target/t");
        assert_eq!(owner(&generated_unit("t")), "mutants/t");
        let fixture = Fixture::new("units");
        register(&fixture, &two_targets(1_800, 31));
        let target = registry::parse(
            &fs::read_to_string(fixture.root().join("verification/targets.json"))
                .expect("the registry"),
        )
        .expect("a registry");
        assert!(units(&target.targets[0], false).is_empty());
        assert_eq!(units(&target.targets[0], true), ["mutants/t"]);
    }

    #[test]
    fn the_limits_of_the_workflows_cover_the_deadlines_of_their_gates_and_receipts() {
        use crate::formal::run::{GATE_BUDGET, RECEIPT_MARGIN};
        use yaml_rust2::YamlLoader;
        let minutes = |seconds: u64| seconds.div_ceil(60);
        let (gate, margin) = (GATE_BUDGET.as_secs(), RECEIPT_MARGIN.as_secs());
        // `formal.yml` computes them from these two numbers.
        let formal = include_str!("../../../.github/workflows/formal.yml");
        assert!(
            formal.contains(&format!("gate_budget={gate}\n"))
                && formal.contains(&format!("receipt_margin={margin}\n"))
        );
        // With these lines, which give 126 and 195 minutes without a formal
        // target, and room for 9,900 s of formal budgets in a job of 360.
        for line in [
            r#"jq -e 'all(.targets[]; .name | test("^[a-z0-9][a-z0-9-]*$"))' "$registry" > /dev/null"#,
            "minutes() { echo $(( (gate_budget + $1 + receipt_margin + 59) / 60 )); }",
            r#"echo "gate=$((gate + 1))""#,
            r#"echo "job=$((15 + 55 + gate))""#,
            r#"echo "planned-gate=$((planned + 2))""#,
            r#"echo "planned-job=$((15 + planned + 2 + 3))""#,
            "if [ $((15 + 55 + gate)) -gt 360 ] || [ $((15 + planned + 2 + 3)) -gt 360 ]; then",
        ] {
            assert!(formal.contains(&format!("{line}\n")), "{line}");
        }
        let job = |budgets: u64| 15 + 55 + minutes(gate + budgets + margin);
        assert_eq!((minutes(gate + margin) + 1, job(0)), (126, 195));
        assert!(job(9_900) <= 360 && job(9_901) > 360);
        // `formal-calibration.yml` writes them for the registry of the
        // calibration.
        let text = include_str!("../../../.github/workflows/formal-calibration.yml");
        let document = YamlLoader::load_from_str(text).expect("YAML").remove(0);
        let registry = include_str!("../../../verification/qualification/calibration/targets.json");
        let registry = registry::parse(registry).expect("a registry");
        let budget = |state| {
            registry
                .targets
                .iter()
                .filter(|t| t.state == state)
                .map(|t| t.budget)
                .sum::<u64>()
        };
        let rows = document["jobs"]["calibration"]["strategy"]["matrix"]["include"]
            .as_vec()
            .expect("the matrix")
            .clone();
        for (row, budget) in rows.iter().zip([
            budget(registry::State::Formal),
            budget(registry::State::Planned),
        ]) {
            let deadline = minutes(gate + budget + margin);
            assert_eq!(
                row["deadline"].as_str(),
                Some(format!("{deadline}m").as_str())
            );
            assert_eq!(row["step"].as_i64(), Some(deadline as i64 + 2));
            assert!(
                row["job"]
                    .as_i64()
                    .is_some_and(|job| job >= deadline as i64 + 2 + 20)
            );
        }
        let deadline = minutes(RUN_BUDGET.as_secs() + margin);
        assert!(text.contains(&format!("deadline.sh --stop-commands {deadline}m 1m")));
        let job = &document["jobs"]["mutants"];
        let step = job["steps"]
            .as_vec()
            .expect("steps")
            .iter()
            .find(|s| s["id"].as_str() == Some("mutants"));
        assert_eq!(
            step.expect("the step")["timeout-minutes"].as_i64(),
            Some(deadline as i64 + 2)
        );
        assert!(
            job["timeout-minutes"]
                .as_i64()
                .is_some_and(|job| (deadline as i64 + 20..=270).contains(&job))
        );
    }
}
