//! The statement side of the Lake project and `cargo xtask formal guard`,
//! as "Statements and proofs" and "Guard" in `docs/formal-verification.md`
//! describe them: the statement registry, the statement hash and the import
//! rule of the statement side, and the rules for pull requests that change
//! the statement side, the proofs, the sources or the registries.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::Duration;

use clap::{Arg, ArgMatches, value_parser};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::Layout;
use super::base::read;
use super::lean::{self, Item, PROJECT_FILES, Token};
use super::paths::{self, Files, Git, tree_records};
use super::qualify::is_module;
use super::registry::{self, Mutant, Target};
use super::run::Phase;
use super::toolchain::is_hex;
use crate::manifests::USER;

/// `verification/statements.json`: the statement hash and the statements.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Statements {
    pub schema: u32,
    pub hash: String,
    pub statements: Vec<Statement>,
}

/// The proposition `name` of the statement side, which the theorem
/// `theorem` of the proof module `module` proves, or is to prove.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Statement {
    pub name: String,
    pub theorem: String,
    pub module: String,
    pub state: State,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum State {
    Planned,
    Proved,
}

/// What the guard read of a pull request: its commits and labels, the
/// statement hash of its head, the statement-side, proof and source paths
/// changed since the merge base, the statements proved there and not at the
/// head, the statements registered at only one of the merge base and the
/// head, that is, added, removed or renamed, the files with a new raised
/// heartbeat limit, what each registry rule found, which the receipt does not
/// hold, and why each rule fails, or `None`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Record {
    pub base: String,
    pub head: String,
    pub merge_base: String,
    pub labels: BTreeSet<String>,
    pub ai_proof: bool,
    pub statement_hash: String,
    pub statement_side: Vec<String>,
    pub proofs: Vec<String>,
    pub sources: Vec<String>,
    pub demoted: Vec<String>,
    pub restated: Vec<String>,
    pub raised: Vec<String>,
    #[serde(skip)]
    pub registry: BTreeMap<String, Vec<String>>,
    pub rules: BTreeMap<String, Option<String>>,
}

/// A rule: why it fails on a record with the description's fields, or `None`.
type Rule = fn(&Record, &BTreeMap<&str, Option<&str>>) -> Option<String>;

/// The phases of the proof work that `Phase` names.
const PHASES: [&str; 3] = ["statement", "proof", "rewrite"];

/// The rules of the guard, by name; later checks add rows. The last rows are
/// the classes of registry changes, in the order of [`CLASSES`].
const RULES: [(&str, Rule); 24] = [
    ("statement-change-needs-spec", |record, _| {
        let side = named("it changes", &record.statement_side);
        let changes = [side, named("it no longer proves", &record.demoted)];
        let changes = Vec::from_iter(changes.into_iter().flatten()).join(" and ");
        let unlabelled = !changes.is_empty() && !record.labels.contains("spec");
        unlabelled.then(|| format!("{changes} without the label spec"))
    }),
    ("spec-approval", |record, fields| {
        let given = |name: &str| fields.get(name).copied().flatten();
        let names = ["Review", "Approval", "Approved-Statement-Hash"];
        let missing = Vec::from_iter(names.into_iter().filter(|name| given(name).is_none()));
        let missing = named("the description lacks a well-formed", &missing);
        let hash = &record.statement_hash;
        let other = given(names[2]).filter(|approved| approved != hash);
        let other = other.map(|approved| format!("the approved hash {approved} is not {hash}"));
        missing.or(other).filter(|_| record.labels.contains("spec"))
    }),
    ("no-sources-with-proofs-or-statements", |record, _| {
        let label = (record.labels.contains("proof")).then(|| "the label proof".to_string());
        let side = named("statement-side files", &record.statement_side);
        let with = [label, named("proof files", &record.proofs), side];
        let with = Vec::from_iter(with.into_iter().flatten()).join(" and ");
        let sources = named("it changes the sources", &record.sources);
        let sources = sources.filter(|_| !with.is_empty());
        sources.map(|sources| format!("{sources} with {with}"))
    }),
    ("heartbeats-need-review", |record, fields| {
        let reviewed = fields.get("Heartbeats-Review").copied().flatten().is_some();
        let raised = named("it raises a heartbeat limit in", &record.raised);
        let raised = raised.filter(|_| !reviewed);
        raised.map(|raised| format!("{raised} without a well-formed Heartbeats-Review"))
    }),
    ("phase-and-author", |record, fields| {
        let given = |name: &str| fields.get(name).copied().flatten();
        let phase = given("Phase").filter(|phase| PHASES.contains(phase));
        let names = [("Phase", phase), ("Author", given("Author"))];
        let missing = (names.into_iter()).filter(|(_, value)| value.is_none());
        let missing = Vec::from_iter(missing.map(|(name, _)| name));
        let labelled = ["spec", "proof"].map(|label| record.labels.contains(label));
        let missing = named("the description lacks a well-formed", &missing);
        missing.filter(|_| labelled.contains(&true))
    }),
    ("proof-of-registered-statements", |record, _| {
        let restated = named(
            "it adds, removes or renames the statements",
            &record.restated,
        );
        let restated = restated.filter(|_| !record.labels.contains("spec"));
        restated.map(|it| format!("{it} without the label spec"))
    }),
    ("registry-target-removed", class::<0>),
    ("registry-theorem-removed", class::<1>),
    ("registry-mutant-removed", class::<2>),
    ("registry-proves-narrowed", class::<3>),
    ("registry-formal-made-planned", class::<4>),
    ("registry-unconstrained-added", class::<5>),
    ("registry-opaque-added", class::<6>),
    ("registry-trusted-axiom-added", class::<7>),
    ("registry-model-added", class::<8>),
    ("registry-obligation-changed", class::<9>),
    ("registry-start-from-changed", class::<10>),
    ("registry-mutant-file-changed", class::<11>),
    ("registry-mutant-find-changed", class::<12>),
    ("registry-mutant-replace-changed", class::<13>),
    ("registry-mutant-renamed", class::<14>),
    ("registry-mutant-fails-grown", class::<15>),
    ("registry-trusted-reason-changed", class::<16>),
    ("registry-unreadable", class::<17>),
];

/// The registries that the guard compares at one commit: the targets by
/// name, the names of the models and the items of the trusted base; at the
/// head, also why a changed registry cannot be read on either side.
#[derive(Debug, Clone, Default)]
struct Registries {
    targets: BTreeMap<String, Target>,
    models: Vec<String>,
    tcb: Vec<Item>,
    unreadable: Vec<String>,
}

impl Registries {
    /// Reads `text`, the registry `path` of `layout`; an empty text, of the
    /// side that lacks the file, is an empty registry.
    fn read(&mut self, path: &str, text: &str, layout: &Layout) -> Result<(), String> {
        if text.is_empty() {
            return Ok(());
        } else if path == layout.registry {
            self.targets = paths::targets(text)?;
        } else if path == layout.models {
            let json: Value = serde_json::from_str(text).map_err(|error| error.to_string())?;
            let models = json["models"].as_array().filter(|_| json["schema"] == 1);
            let models = models.ok_or("not a model registry of schema 1")?;
            self.models = Vec::from_iter(models.iter().map(|model| model["name"].to_string()));
        } else {
            self.tcb = lean::load_tcb(text)?;
        }
        Ok(())
    }
}

/// The registries at the merge base and at the head.
type Sides = [Registries; 2];

/// Values by key, each key with the set of its values.
type Multimap = BTreeMap<String, BTreeSet<String>>;

/// The values of `kind` at the merge base and at the head that a class of
/// registry changes compares: those of each target by its name, of each
/// mutant by `<target>/<mutant>`, and the reason of each trusted item.
fn of(sides: &Sides, kind: &str) -> [Multimap; 2] {
    sides.each_ref().map(|side| {
        let mut found = Multimap::new();
        for (_, key, values) in facts(side).into_iter().filter(|(of, ..)| *of == kind) {
            found.entry(key).or_default().extend(values);
        }
        found
    })
}

/// `field` of each of `items`.
fn each<T>(items: &[T], field: fn(&T) -> &String) -> Vec<String> {
    items.iter().map(|item| field(item).clone()).collect()
}

/// The values of each kind that the registries `side` give, by key; a
/// planned target has the empty value of the kind `planned`.
fn facts(side: &Registries) -> Vec<(&'static str, String, Vec<String>)> {
    let targets = Vec::from_iter(side.targets.keys().cloned());
    let models = ("models", "models.json".to_string(), side.models.clone());
    let mut facts = vec![("targets", "targets.json".to_string(), targets), models];
    for item in &side.tcb {
        let (key, reason) = match item.clone() {
            Item::NativeDecision {
                file,
                declaration,
                reason,
            } => (format!("native-decision {file} {declaration}"), reason),
            Item::AxiomPattern { prefix, reason } => (format!("axiom-pattern {prefix}"), reason),
        };
        facts.push(("trusted", "tcb.json".to_string(), vec![key.clone()]));
        facts.push(("reasons", format!("{key} in tcb.json"), vec![reason]));
    }
    for (name, t) in &side.targets {
        let planned = (t.state == registry::State::Planned).then(String::new);
        let theorems = t.obligations.iter().flat_map(|o| o.theorems.clone());
        let obligations = t.obligations.iter().map(|o| {
            let mut o = o.clone();
            o.theorems.sort();
            format!("{o:?}")
        });
        let values = [
            ("planned", Vec::from_iter(planned)),
            ("theorems", theorems.collect()),
            ("mutants", each(&t.mutants, |m| &m.name)),
            ("proves", t.proves.clone()),
            ("unconstrained", t.unconstrained.clone()),
            ("opaque", each(&t.opaque, |o| &o.pattern)),
            ("trusted", each(&t.trusted_axioms, |a| &a.name)),
            ("models", Vec::from_iter(t.models.clone())),
            ("obligations", obligations.collect()),
            ("start_from", t.start_from.clone()),
        ];
        facts.extend(values.map(|(kind, values)| (kind, name.clone(), values)));
        for m in &t.mutants {
            let (key, edit) = (format!("{name}/{}", m.name), [&m.file, &m.find, &m.replace]);
            let edit = ["file", "find", "replace"].into_iter().zip(edit);
            facts.extend(edit.map(|(kind, value)| (kind, key.clone(), vec![value.clone()])));
            facts.push(("fails", key, m.fails.clone()));
        }
        let axioms = t.trusted_axioms.iter().map(|a| (&a.name, Some(&a.reason)));
        for (key, why) in axioms.chain(t.opaque.iter().map(|o| (&o.pattern, o.reason.as_ref()))) {
            let key = format!("{key} in {name}");
            facts.push(("reasons", key, Vec::from_iter(why.cloned())));
        }
    }
    facts
}

/// Each value of a key of `before` that `after` lacks, as `<value> in <key>`,
/// or the key alone for the empty value.
fn missing(before: &Multimap, after: &Multimap) -> Vec<String> {
    let mut missing = Vec::new();
    for (key, values) in before {
        let kept = |value: &&String| after.get(key).is_some_and(|kept| kept.contains(*value));
        let at = |v: &String| String::from(format!("{v} in {key}").trim_start_matches(" in "));
        missing.extend(values.iter().filter(|value| !kept(value)).map(at));
    }
    missing
}

/// The values of `kind` that the head lacks.
fn lost(sides: &Sides, kind: &str) -> Vec<String> {
    let [before, after] = of(sides, kind);
    missing(&before, &after)
}

/// The values of `kind` that the merge base lacks.
fn gained(sides: &Sides, kind: &str) -> Vec<String> {
    let [before, after] = of(sides, kind);
    missing(&after, &before)
}

/// The values of `kind` that the head adds to a key of the merge base.
fn grown(sides: &Sides, kind: &str) -> Vec<String> {
    let [before, mut after] = of(sides, kind);
    after.retain(|key, _| before.contains_key(key));
    missing(&after, &before)
}

/// The keys of `kind` of both sides with other values.
fn changed(sides: &Sides, kind: &str) -> Vec<String> {
    let [before, after] = of(sides, kind);
    let other = |(key, values): &(&String, &BTreeSet<String>)| {
        after.get(*key).is_some_and(|after| after != *values)
    };
    Vec::from_iter(before.iter().filter(other).map(|(key, _)| key.clone()))
}

/// The mutants of a target of both sides that the head renames: a name of
/// the merge base that the head lacks, while the head has a new name with
/// the same file, pattern and replacement.
fn renamed([base, head]: &Sides) -> Vec<String> {
    let mut found = Vec::new();
    for (name, before) in &base.targets {
        let Some(after) = head.targets.get(name) else {
            continue;
        };
        let named = |target: &Target, m: &Mutant| target.mutants.iter().any(|o| o.name == m.name);
        for old in before.mutants.iter().filter(|m| !named(after, m)) {
            let edit = |m: &&Mutant| {
                !named(before, m)
                    && (&m.file, &m.find, &m.replace) == (&old.file, &old.find, &old.replace)
            };
            let new = after.mutants.iter().filter(edit);
            found.extend(new.map(|new| format!("{name}/{} to {}", old.name, new.name)));
        }
    }
    found
}

/// What a class of registry changes finds from the registries at the merge
/// base and at the head.
type Class = fn(&Sides) -> Vec<String>;

/// The classes of registry changes, each with the start of its reason; each
/// fails, as a statement change does, without the label `spec`.
const CLASSES: [(&str, Class); 18] = [
    ("it removes the targets", |s| lost(s, "targets")),
    ("it removes the theorems", |s| lost(s, "theorems")),
    ("it removes the mutants", |s| lost(s, "mutants")),
    ("it removes from proves", |s| lost(s, "proves")),
    ("it makes planned the targets", |s| grown(s, "planned")),
    ("it adds the unconstrained", |s| gained(s, "unconstrained")),
    ("it adds the cut points", |s| gained(s, "opaque")),
    ("it adds the trusted axioms", |s| gained(s, "trusted")),
    ("it adds the models", |s| gained(s, "models")),
    ("it changes obligations of", |s| changed(s, "obligations")),
    ("it changes start_from of", |s| changed(s, "start_from")),
    ("it changes the file of", |s| changed(s, "file")),
    ("it changes the pattern of", |s| changed(s, "find")),
    ("it changes the replacement of", |s| changed(s, "replace")),
    ("it renames the mutants", renamed),
    ("it adds to fails", |s| grown(s, "fails")),
    ("it changes the reasons of", |s| changed(s, "reasons")),
    ("it cannot read", |s| s[1].unreadable.clone()),
];

/// The rule of the class `C` of [`CLASSES`]: it fails on what the class
/// found unless the pull request has the label `spec`.
fn class<const C: usize>(record: &Record, _: &BTreeMap<&str, Option<&str>>) -> Option<String> {
    let rule = RULES[RULES.len() - CLASSES.len() + C].0;
    let found = named(CLASSES[C].0, record.registry.get(rule)?);
    let found = found.filter(|_| !record.labels.contains("spec"));
    found.map(|found| format!("{found} without the label spec"))
}

/// `what` and the items of `list`, when it has any.
fn named<T: std::borrow::Borrow<str>>(what: &str, list: &[T]) -> Option<String> {
    (!list.is_empty()).then(|| format!("{what} {}", list.join(", ")))
}

/// Reads `verification/statements.json`, `text`: the hash names a Git tree,
/// names are Lean names of ASCII components, each statement and theorem
/// appears once, and statements lie outside the proofs, their modules below.
pub fn load_statements(text: &str, layout: &Layout) -> Result<Statements, String> {
    let file: Statements = lean::registry(text, |file: &Statements| file.schema)?;
    let below = |name: &str| name.starts_with(&format!("{}.", layout.proofs));
    let hash = format!("the hash {} does not name a Git tree", file.hash);
    let mut problems = Vec::from_iter((!is_hex(&file.hash, 40)).then_some(hash));
    let mut seen = BTreeSet::new();
    for s in &file.statements {
        let names = [&s.name, &s.theorem, &s.module];
        let invalid = (names.into_iter()).filter(|name| !is_module(name));
        let invalid = invalid.map(|name| format!("{name} is not a Lean name of ASCII components"));
        problems.extend(invalid);
        let twice = (names[..2].iter()).filter(|name| !seen.insert(**name));
        problems.extend(twice.map(|name| format!("{name} is registered twice")));
        if below(&s.name) || !below(&s.module) {
            let (name, module, proofs) = (&s.name, &s.module, layout.proofs);
            let problem = format!("{name} must lie outside {proofs} and {module} below it");
            problems.push(problem);
        }
    }
    let file = problems.is_empty().then_some(file);
    file.ok_or(problems.join("; "))
}

/// Whether the repository path `path` lies in the calibration project inside
/// the Lake project of `layout`: it is part of neither the statement side nor
/// the Lean files of that project, but of those of its own layout.
pub fn in_calibration(path: &str, layout: &Layout) -> bool {
    let calibration = Layout::CALIBRATION.project;
    layout.project != calibration && crate::repo::is_within(path, calibration)
}

/// Whether the repository path `path` lies on the statement side: a Lean
/// file of the Lake project outside the proofs, the registry of library
/// axioms, or a Lake project file.
pub fn statement_side(path: &str, layout: &Layout) -> bool {
    let file = path.strip_prefix(&format!("{}/", layout.project));
    let Some(file) = file.filter(|_| !in_calibration(path, layout)) else {
        return false;
    };
    let proofs = format!("{}/", layout.proofs.replace('.', "/"));
    let project = file.starts_with("lakefile.") || PROJECT_FILES.contains(&file);
    let lean = file.ends_with(".lean") && !file.starts_with(&proofs);
    lean || path == layout.axioms || (project && !file.contains('/'))
}

/// The statement hash of `commit`, with the files of its Lake project: the
/// Git tree of exactly its paths on the statement side, as `git write-tree`
/// writes it from an index of those alone. Each tree is written with
/// `git mktree`, from the deepest up, through a file in `work`; like
/// `git write-tree`, this writes tree objects and nothing else.
pub fn statement_hash(
    git: &mut dyn Git,
    commit: &str,
    layout: &Layout,
    work: &Path,
) -> Result<(String, Files), String> {
    let listing = git.git(&["ls-tree", "-r", "-z", commit, "--", layout.project], None)?;
    let mut files = tree_records(&listing)?;
    files.retain(|path, _| !in_calibration(path, layout));
    let mut trees = BTreeMap::from([(String::new(), String::new())]);
    for (path, entry) in &files {
        let (tree, name) = path.rsplit_once('/').unwrap_or_default();
        if statement_side(path, layout) {
            let paths::Entry { mode, kind, oid } = entry;
            let entries = trees.entry(tree.to_string()).or_default();
            entries.push_str(&format!("{mode} {kind} {oid}\t{name}\0"));
        }
    }
    let input = work.join("mktree");
    while let Some((tree, entries)) = trees.pop_last() {
        fs::write(&input, entries).map_err(|error| format!("{}: {error}", input.display()))?;
        let oid = git.git(&["mktree", "-z"], Some(&input))?;
        let oid = String::from_utf8_lossy(&oid).trim().to_string();
        if tree.is_empty() {
            return Ok((oid, files));
        }
        let (parent, name) = tree.rsplit_once('/').unwrap_or(("", &tree));
        let entries = trees.entry(parent.to_string()).or_default();
        entries.push_str(&format!("040000 tree {oid}\t{name}\0"));
    }
    unreachable!("the root is written last")
}

/// Reads the header of a Lean file from its `tokens`, as Lean 4.35.0 does:
/// an optional `module`, an optional `prelude`, then imports of the form
/// `[public] [meta] import [all] <name>`, each of one name. Any other token,
/// a doc comment included, ends it. Returns whether it starts with `module`
/// and the imported modules, with any `«»` removed.
pub fn header_imports(tokens: &[(usize, Token)]) -> (bool, Vec<String>) {
    let mut words = (tokens.iter())
        .map(|(_, token)| match token {
            Token::Name(name) => name.as_str(),
            _ => "",
        })
        .peekable();
    let module = words.next_if_eq(&"module").is_some();
    words.next_if_eq(&"prelude");
    let mut imports = Vec::new();
    loop {
        words.next_if_eq(&"public");
        words.next_if_eq(&"meta");
        if words.next_if_eq(&"import").is_none() {
            break;
        }
        words.next_if_eq(&"all");
        match words.next() {
            Some(name) if !name.is_empty() => imports.push(name.replace(['«', '»'], "")),
            _ => break,
        }
    }
    (module, imports)
}

/// The modules among `imports` that the statement side must not import:
/// the root module and the proofs.
pub fn forbidden_imports<'a>(imports: &'a [String], layout: &Layout) -> Vec<&'a String> {
    let below = format!("{}.", layout.proofs);
    let named = |name: &str| [layout.namespace, layout.proofs].contains(&name);
    let forbidden = |name: &&String| named(name) || name.starts_with(&below);
    imports.iter().filter(forbidden).collect()
}

/// The heartbeat limits that the Lean or Lake `text` raises: at each
/// `maxHeartbeats`, the value after white space, quotes, `»` and `=`, unless
/// it is a number, with `_` between digits, from 1 to Lean's default of
/// 200000, or of 20000 for an option of a namespace such as
/// `synthInstance`. Each is keyed by its lines, with white space collapsed,
/// and the next line that is not blank, trimmed.
fn raises(text: &str) -> BTreeSet<(String, String)> {
    let mut raises = BTreeSet::new();
    for (at, name) in text.match_indices("maxHeartbeats") {
        let after = &text[at + name.len()..];
        let value = after.trim_start_matches(|c: char| c.is_whitespace() || "\"'»=".contains(c));
        let rest = value.trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');
        let digits = value[..value.len() - rest.len()].replace('_', "");
        let dotted = text[..at].trim_end_matches('«').ends_with('.');
        let default = [200_000, 20_000][usize::from(dotted)];
        if (digits.parse()).is_ok_and(|value: u64| (1..=default).contains(&value)) {
            continue;
        }
        let start = text[..at].rfind('\n').map_or(0, |line| line + 1);
        let (line, next) = rest.split_once('\n').unwrap_or((rest, ""));
        let lines = &text[start..text.len() - rest.len() + line.len()];
        let next = next.lines().map(str::trim).find(|line| !line.is_empty());
        let setting = Vec::from_iter(lines.split_whitespace()).join(" ");
        raises.insert((setting, next.unwrap_or_default().to_string()));
    }
    raises
}

/// Checks the pull request of the `pull_request` event `text` with the
/// rules of the guard, through `git` in a repository that holds both of its
/// commits; `work` takes the input of `git mktree`. An error is an input
/// that cannot be read.
fn check(git: &mut dyn Git, text: &str, layout: &Layout, work: &Path) -> Result<Record, String> {
    let event: Value = serde_json::from_str(text).map_err(|error| format!("the event: {error}"))?;
    let pull = &event["pull_request"];
    let sha = |side: &str| pull[side]["sha"].as_str().filter(|sha| is_hex(sha, 40));
    let name = |label: &Value| label["name"].as_str().map(String::from);
    let labels = pull["labels"]
        .as_array()
        .map(|labels| labels.iter().map(name));
    let labels: Option<BTreeSet<String>> = labels.and_then(Iterator::collect);
    let (Some(base), Some(head), Some(labels)) = (sha("base"), sha("head"), labels) else {
        return Err("the event has no pull request with commits and labels".to_string());
    };
    let change = paths::since_merge_base(git, base, head)?;
    let mut record = Record {
        base: base.to_string(),
        head: head.to_string(),
        merge_base: change.merge_base.clone(),
        ai_proof: labels.contains("ai-proof"),
        labels,
        ..Record::default()
    };
    let proofs = format!("{}/{}/", layout.project, layout.proofs.replace('.', "/"));
    let workspaces = [layout.kernel, USER].map(|workspace| format!("{workspace}/"));
    let registries = [layout.registry, layout.models, layout.tcb];
    let mut sides = Sides::default();
    for path in change.paths.iter().map(|(_, path)| path.as_str()) {
        let proof = path.starts_with(&proofs) && path.ends_with(".lean");
        let (side, statements) = (statement_side(path, layout), path == layout.statements);
        let source = workspaces.iter().any(|dir| path.starts_with(dir)) && path.ends_with(".rs");
        record.statement_side.extend(side.then(|| path.to_string()));
        record.proofs.extend(proof.then(|| path.to_string()));
        record.sources.extend(source.then(|| path.to_string()));
        let registry = registries.contains(&path);
        if !(side || proof || statements || registry) {
            continue;
        }
        // The file at the merge base and at the head, where it exists.
        let [before, after] = change.texts(git, path)?;
        if registry {
            // A registry that cannot be read on one side is compared on
            // neither, and fails its own rule.
            let read = |at: usize| {
                let (mut read, text) = (sides[at].clone(), [&before, &after][at]);
                let at = ["the merge base", "the head"][at];
                let read = read.read(path, text, layout).map(|()| read);
                read.map_err(|error| format!("{path} at {at}: {error}"))
            };
            match [0, 1].map(read) {
                [Ok(base), Ok(head)] => sides = [base, head],
                read => sides[1]
                    .unreadable
                    .extend(read.into_iter().filter_map(Result::err)),
            }
        } else if statements {
            let entries = |text: &str| {
                let file = (!text.is_empty()).then(|| load_statements(text, layout));
                let file = file.transpose();
                let file = file.map_err(|error| format!("{path}: {error}"))?;
                let entries = file.into_iter().flat_map(|file| file.statements);
                Ok::<_, String>(BTreeMap::from_iter(entries.map(|s| (s.name.clone(), s))))
            };
            let (before, after) = (entries(&before)?, entries(&after)?);
            let names = BTreeSet::from_iter(before.keys().chain(after.keys()).cloned());
            let proved = |s: Option<&Statement>| s.is_some_and(|s| s.state == State::Proved);
            let demoted = |n: &&String| proved(before.get(*n)) && !proved(after.get(*n));
            record.demoted = Vec::from_iter(names.iter().filter(demoted).cloned());
            // The statements added, removed or renamed; a registered one may
            // change its theorem, its module or its state.
            let restated = |n: &&String| before.contains_key(*n) != after.contains_key(*n);
            record.restated = Vec::from_iter(names.iter().filter(restated).cloned());
        } else if !raises(&after).is_subset(&raises(&before)) {
            record.raised.push(path.to_string());
        }
    }
    let rules = RULES[RULES.len() - CLASSES.len()..].iter().zip(CLASSES);
    let found = rules.map(|((rule, _), (_, class))| (rule.to_string(), class(&sides)));
    record.registry = found.filter(|(_, found)| !found.is_empty()).collect();
    (record.statement_hash, _) = statement_hash(git, head, layout, work)?;
    let fields = fields(pull["body"].as_str().unwrap_or_default());
    let rules = (RULES.iter()).map(|(name, rule)| (name.to_string(), rule(&record, &fields)));
    record.rules = rules.collect();
    Ok(record)
}

/// The fields of the description `body`, each a line `Name: value`: the
/// value of each given once and well formed, a Git object name for
/// `Approved-Statement-Hash` and otherwise an id of 1 to 64 ASCII letters
/// and digits, and `None` for any other.
fn fields(body: &str) -> BTreeMap<&str, Option<&str>> {
    let mut fields = BTreeMap::new();
    for (name, value) in body.lines().filter_map(|line| line.split_once(':')) {
        let value = value.trim();
        let id = matches!(value.len(), 1..=64) && value.chars().all(|c| c.is_ascii_alphanumeric());
        let valid = (name == "Approved-Statement-Hash").then(|| is_hex(value, 40));
        let valid = valid.unwrap_or(id);
        let first = !fields.contains_key(name);
        fields.insert(name, (valid && first).then_some(value));
    }
    fields
}

/// The guard phase of `cargo xtask formal run` on a pull request, when
/// `var` gives `GITHUB_EVENT_NAME` as `pull_request` and the event's file in
/// `GITHUB_EVENT_PATH`: it records the guard in the receipt, through the
/// gate's Git, and has no unit, so its rules decide nothing about the run.
pub fn phase<'a>(var: &dyn Fn(&str) -> Option<String>) -> Option<Phase<'a>> {
    let pull_request = var("GITHUB_EVENT_NAME").is_some_and(|name| name == "pull_request");
    let event = PathBuf::from(var("GITHUB_EVENT_PATH").filter(|_| pull_request)?);
    Some(Phase {
        name: "guard".to_string(),
        budget: Duration::from_secs(300),
        units: Vec::new(),
        body: Box::new(move |gate| {
            let (layout, work) = (*gate.layout(), gate.work());
            gate.receipt.guard = Some(check(gate, &read(&event)?, &layout, &work)?);
            Ok(())
        }),
    })
}

/// Git as `cargo xtask formal guard` runs it in the repository root: with
/// the caller's `PATH` alone, no system or global configuration, literal
/// pathspecs and no optional locks.
pub(super) struct Standalone<'a>(pub(super) &'a Path);

impl Git for Standalone<'_> {
    fn git(&mut self, args: &[&str], stdin: Option<&Path>) -> Result<Vec<u8>, String> {
        let mut command = Command::new("git");
        let path = std::env::var_os("PATH").map(|path| ("PATH", path));
        command.env_clear().envs(path).current_dir(self.0);
        command.env("GIT_CONFIG_NOSYSTEM", "1");
        command.env("GIT_CONFIG_GLOBAL", "/dev/null");
        command.args(["--literal-pathspecs", "--no-optional-locks"]);
        let input = (stdin.map(fs::File::open).transpose()).map_err(|e| e.to_string())?;
        let input = input.map_or_else(Stdio::null, Stdio::from);
        let output = (command.args(args).stdin(input).output()).map_err(|e| format!("git: {e}"))?;
        let error = String::from_utf8_lossy(&output.stderr);
        let error = format!("git {} failed: {}", args.join(" "), error.trim());
        let stdout = (output.status.success()).then_some(output.stdout);
        stdout.ok_or(error)
    }
}

/// The command line of `cargo xtask formal guard`, with `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let event = Arg::new("event").long("event").value_name("PATH");
    let event = event.required(true).value_parser(value_parser!(PathBuf));
    clap::Command::new("guard").about(about).arg(event)
}

/// Entry point of `cargo xtask formal guard` in the repository `root`: it
/// prints `PASSED <rule>` or `FAILED <rule>: <why>` for each rule, the
/// labels and the head's statement hash, and exits with 1 when a rule fails
/// or an input cannot be read. `git mktree` gets its input through a
/// directory below `artifacts/formal/guard/`, which it removes.
pub fn command(root: &Path, layout: &Layout, matches: &ArgMatches) -> ExitCode {
    let event = (matches.get_one::<PathBuf>("event")).expect("a required option");
    let work = root.join(format!("artifacts/formal/guard/{}", std::process::id()));
    let made = fs::create_dir_all(&work).map_err(|error| format!("{}: {error}", work.display()));
    let checked = made.and_then(|()| check(&mut Standalone(root), &read(event)?, layout, &work));
    let _ = fs::remove_dir_all(&work);
    let Ok(record) = checked.map_err(|error| eprintln!("formal guard: {error}")) else {
        return ExitCode::FAILURE;
    };
    for (rule, why) in &record.rules {
        match why {
            None => println!("PASSED {rule}"),
            Some(why) => println!("FAILED {rule}: {why}"),
        }
    }
    let labels = Vec::from_iter(record.labels.iter().map(String::as_str)).join(", ");
    let hash = &record.statement_hash;
    println!("labels: {labels}\nstatement hash: {hash}");
    ExitCode::from(u8::from(record.rules.values().any(Option::is_some)))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::process::Command;

    use serde_json::json;

    use super::*;
    use crate::formal::fixture::Fixture;
    use crate::formal::outcome::{Site, Status};
    use crate::formal::run;
    use crate::formal::toolchain::environment::SYSTEM_PATH;

    const LAYOUT: Layout = Layout::PRODUCTION;

    /// A `pull_request` event as GitHub writes it, shortened, with the
    /// label `proof`.
    const PULL_REQUEST: &str = include_str!("fixtures/guard/pull_request.json");

    /// A `push` event as GitHub writes it, shortened.
    const PUSH: &str = include_str!("fixtures/guard/push.json");

    /// The variable that makes the process of a test the caller of the
    /// standalone guard, with the fixture that it names.
    const STANDALONE: &str = "KREPI_XTASK_STANDALONE_GUARD";

    const SPEC: &str = "verification/Krepi/Spec/Counter.lean";
    const PROOF: &str = "verification/Krepi/Proofs/Counter.lean";

    /// The header fixtures of the layout experiment: a plain import; the
    /// forms of the header with comments, modifiers and quoted names; a
    /// file that is not a module; `prelude` with `import all`; and an
    /// import of the root.
    const IMPORTS_OF_PROOFS: [&str; 5] = [
        "module\nimport Krepi.Proofs.Counter\n",
        "/- Copyright header, /- nested -/ block comment -/\n\
         module -- trailing line comment\n\
         \n\
         public import Krepi.Spec.Counter\n\
         public meta import KrepiGen.Counter\n\
         meta import all Krepi.Statements.Counter\n\
         public /- comment between tokens -/ import\n  \
           all «Krepi».Proofs.«Counter»\n",
        "import Krepi.Statements.Counter\nimport Krepi.Proofs.Counter\n",
        "module\nprelude\npublic import all Krepi.Proofs.Counter\n",
        "module\npublic import Krepi\n",
    ];

    /// A fixture with a file of each kind in its Lake project.
    fn project(label: &str) -> Fixture {
        let fixture = Fixture::new(label);
        for path in [
            "verification/Krepi/Spec/Counter.lean",
            "verification/Krepi/Statements/Counter.lean",
            "verification/Krepi/Proofs/Counter.lean",
            "verification/Krepi/Qualification/Arithmetic.lean",
            "verification/externals/Qual/X/FunsExternal.lean",
            "verification/axioms.json",
            "verification/statements.json",
            "verification/tcb.json",
            "verification/lakefile.toml",
            "verification/lean-toolchain",
            "verification/lake-manifest.json",
            "verification/qualification/cases.json",
        ] {
            fixture.write(path, "-- a file\n");
        }
        fixture.write("verification/statements.json", &registry(&[]));
        fixture.commit_all();
        fixture
    }

    /// `statements.json` with `entries`: the name of a proposition below
    /// `Krepi.Statements.Counter`, the theorem below `Krepi.Proofs.Counter`
    /// that proves it, and its state.
    fn registry(entries: &[(&str, &str, &str)]) -> String {
        let entry = |(name, theorem, state): &(&str, &str, &str)| {
            let names = format!(
                "\"name\": \"Krepi.Statements.Counter.{name}\", \
                 \"theorem\": \"Krepi.Proofs.Counter.{theorem}\""
            );
            format!("{{{names}, \"module\": \"Krepi.Proofs.Counter\", \"state\": \"{state}\"}}")
        };
        let entries = Vec::from_iter(entries.iter().map(entry)).join(", ");
        let hash = "0".repeat(40);
        format!("{{\"schema\": 1, \"hash\": \"{hash}\", \"statements\": [{entries}]}}\n")
    }

    /// The commit at the head of `fixture`.
    fn head_of(fixture: &Fixture) -> String {
        fixture.git(&["rev-parse", "HEAD"]).trim().to_string()
    }

    /// Writes each of `changes`, a path and its text, commits them and
    /// returns the commit.
    fn commit(fixture: &Fixture, changes: &[(&str, &str)]) -> String {
        for (path, text) in changes {
            fixture.write(path, text);
        }
        fixture.commit_all();
        head_of(fixture)
    }

    /// The event of a pull request from `base` to `head` with `labels` and
    /// the description `body`, made from [`PULL_REQUEST`].
    fn event(base: &str, head: &str, labels: &[&str], body: Option<&str>) -> String {
        let mut event: Value = serde_json::from_str(PULL_REQUEST).expect("the fixture parses");
        let pull = &mut event["pull_request"];
        let label = |name: &&str| {
            let mut label = pull["labels"][0].clone();
            label["name"] = (*name).into();
            label
        };
        let labels: Value = labels.iter().map(label).collect();
        (pull["labels"], pull["body"]) = (labels, body.into());
        (pull["base"]["sha"], pull["head"]["sha"]) = (base.into(), head.into());
        event.to_string()
    }

    /// The guard of the pull request from `base` to the head of `fixture`,
    /// with `labels` and the description `body`.
    fn guard(fixture: &mut Fixture, base: &str, labels: &[&str], body: Option<&str>) -> Record {
        let event = event(base, &head_of(fixture), labels, body);
        let work = fixture.root().join("artifacts/guard");
        fs::create_dir_all(&work).expect("create the work directory");
        check(fixture, &event, &LAYOUT, &work).expect("the guard reads its inputs")
    }

    /// The rules that fail in `record`, with why.
    fn failed(record: &Record) -> Vec<(&str, &str)> {
        let failed =
            (record.rules.iter()).filter_map(|(rule, why)| Some((rule.as_str(), why.as_deref()?)));
        failed.collect()
    }

    /// The description of a pull request with the label `spec` that was
    /// reviewed and approved for the statement hash `hash`, with its phase
    /// and author and with Windows line ends.
    fn approval(hash: &str) -> String {
        format!(
            "Changes a statement.\r\n\r\nPhase: statement\r\nAuthor: au1\r\n\
             Review: rev42\r\nApproval: app7\r\nApproved-Statement-Hash: {hash}\r\n"
        )
    }

    /// The description of a pull request with the label `proof`: its phase
    /// and its author.
    const PROVING: Option<&str> = Some("Proves a statement.\n\nPhase: proof\nAuthor: au1\n");

    /// Changes `path` without a label and returns the record, after it
    /// checks that the rule for statement changes fails, and only it.
    fn unlabelled_change(label: &str, path: &str) -> Record {
        let mut fixture = project(label);
        let base = head_of(&fixture);
        commit(&fixture, &[(path, "-- a change of meaning\n")]);
        let record = guard(&mut fixture, &base, &[], None);
        let why = format!("it changes {path} without the label spec");
        assert_eq!(
            failed(&record),
            [("statement-change-needs-spec", why.as_str())]
        );
        assert_eq!(record.statement_side, [path]);
        record
    }

    /// The registries of [`registered`], at their paths: the valid target
    /// registry of the tests of the registry, with a trusted axiom and an
    /// unconstrained function in its formal target `table`, no model and an
    /// item of the trusted base.
    fn registries() -> [(&'static str, Value); 3] {
        let mut targets = registry::tests::valid();
        let table = &mut targets["targets"][0];
        let axiom = json!({"name": "Krepi.Axioms.clock", "reason": "Time is not modelled."});
        table["trusted_axioms"] = json!([axiom]);
        table["unconstrained"] = json!(["krepi_kernel::table::raw"]);
        let models = json!({"schema": 1, "models": []});
        let item =
            json!({"kind": "axiom-pattern", "prefix": "KrepiGen.Table.", "reason": "Generated."});
        let tcb = json!({"schema": 1, "items": [item]});
        [
            (LAYOUT.registry, targets),
            (LAYOUT.models, models),
            (LAYOUT.tcb, tcb),
        ]
    }

    /// Writes `registries` in their form of [`registered`] and commits them;
    /// returns the commit.
    fn commit_registries(fixture: &Fixture, registries: &[(&str, Value)]) -> String {
        for (path, value) in registries {
            fixture.write(path, &format!("{value:#}\n"));
        }
        fixture.commit_all();
        head_of(fixture)
    }

    /// A fixture whose base commit, which it returns, holds [`registries`].
    fn registered(label: &str) -> (Fixture, String) {
        let fixture = project(label);
        let base = commit_registries(&fixture, &registries());
        (fixture, base)
    }

    /// Commits `edit` of [`registries`] on the base of [`registered`] and
    /// checks that exactly the rules `expected` fail, with their reasons,
    /// without the label `spec`, and that none fails with it and its
    /// approval.
    fn registry_change(label: &str, edit: impl FnOnce(&mut [Value; 3]), expected: &[(&str, &str)]) {
        let (mut fixture, base) = registered(label);
        let mut values = registries().map(|(_, value)| value);
        edit(&mut values);
        let paths = registries().map(|(path, _)| path);
        commit_registries(&fixture, &Vec::from_iter(paths.into_iter().zip(values)));
        let record = guard(&mut fixture, &base, &[], None);
        assert_eq!(failed(&record), expected, "{label}");
        let hash = hash(&mut fixture, &LAYOUT);
        let labelled = guard(&mut fixture, &base, &["spec"], Some(&approval(&hash)));
        assert_eq!(failed(&labelled), [], "{label}");
    }

    /// The formal target `table` of the target registry of `registries`.
    fn table(registries: &mut [Value; 3]) -> &mut Value {
        &mut registries[0]["targets"][0]
    }

    /// The list `field` of `value`.
    fn list<'a>(value: &'a mut Value, field: &str) -> &'a mut Vec<Value> {
        value[field].as_array_mut().expect("a list")
    }

    /// The statement hash of the head of `fixture` in `layout`.
    fn hash(fixture: &mut Fixture, layout: &Layout) -> String {
        let work = fixture.root().join("artifacts/guard");
        fs::create_dir_all(&work).expect("create the work directory");
        statement_hash(fixture, "HEAD", layout, &work)
            .expect("the statement hash")
            .0
    }

    /// Commits a change of each of `paths` and returns the statement hash
    /// after each.
    fn hashes_after(fixture: &mut Fixture, paths: &[&str]) -> Vec<(String, String)> {
        let mut hashes = Vec::new();
        for path in paths {
            let text = fs::read_to_string(fixture.root().join(path)).unwrap_or_default();
            fixture.write(path, &format!("{text}-- changed\n"));
            fixture.commit_all();
            hashes.push((path.to_string(), hash(fixture, &LAYOUT)));
        }
        hashes
    }

    #[test]
    fn a_change_of_the_statement_side_changes_the_statement_hash() {
        let mut fixture = project("statement-change");
        let mut before = hash(&mut fixture, &LAYOUT);
        let paths = [
            "verification/Krepi/Spec/Counter.lean",
            "verification/Krepi/Qualification/Arithmetic.lean",
            "verification/externals/Qual/X/FunsExternal.lean",
            "verification/axioms.json",
            "verification/lakefile.toml",
            "verification/lean-toolchain",
            "verification/lake-manifest.json",
            "verification/Krepi/Statements/New.lean",
        ];
        for (path, after) in hashes_after(&mut fixture, &paths) {
            assert_ne!(after, before, "{path}");
            before = after;
        }
    }

    #[test]
    fn a_change_of_a_proof_alone_keeps_the_statement_hash() {
        let mut fixture = project("proof-change");
        let before = hash(&mut fixture, &LAYOUT);
        let paths = [
            "verification/Krepi/Proofs/Counter.lean",
            "verification/Krepi/Proofs/New/Deep.lean",
            "verification/statements.json",
            "verification/targets.json",
            "verification/shards.json",
            "verification/tcb.json",
            "verification/qualification/cases.json",
            "kernel/abi/src/lib.rs",
        ];
        for (path, after) in hashes_after(&mut fixture, &paths) {
            assert_eq!(after, before, "{path}");
        }
    }

    #[test]
    fn the_calibration_project_is_outside_the_statement_side_of_production() {
        // Its Lean files and its Lake configuration are on the statement side
        // of the calibration layout alone, so changing them keeps the
        // statement hash of production and changes that of the calibration.
        let mut fixture = project("calibration");
        let calibration = Layout::CALIBRATION;
        let paths = [
            "verification/qualification/calibration/Krepi/Calibration/Statements.lean",
            "verification/qualification/calibration/lakefile.toml",
            "verification/qualification/calibration/axioms.json",
        ];
        let proof = "verification/qualification/calibration/Krepi/Proofs/Calibration.lean";
        for path in paths.iter().chain([&proof]) {
            assert!(!statement_side(path, &LAYOUT), "{path}");
            assert!(in_calibration(path, &LAYOUT) && !in_calibration(path, &calibration));
            assert_eq!(statement_side(path, &calibration), *path != proof, "{path}");
        }
        let production = hash(&mut fixture, &LAYOUT);
        let mut before = hash(&mut fixture, &calibration);
        for path in paths {
            let (_, after) = hashes_after(&mut fixture, &[path]).remove(0);
            let own = hash(&mut fixture, &calibration);
            assert_eq!((after, own != before), (production.clone(), true), "{path}");
            before = own;
        }
        let work = fixture.root().join("artifacts/guard");
        let (_, listed) = statement_hash(&mut fixture, "HEAD", &LAYOUT, &work).expect("the files");
        assert!(!listed.is_empty() && listed.keys().all(|path| !in_calibration(path, &LAYOUT)));
    }

    #[test]
    fn the_statement_hash_is_the_tree_of_the_documented_recipe() {
        let mut fixture = project("recipe");
        // Files that make more directories mixed.
        fixture.write("verification/Krepi/README.md", "Not Lean.\n");
        fixture.write("verification/Krepi.lean", "module\n");
        fixture.write("verification/qualification/Stray.lean", "module\n");
        fixture.write("verification/Krepi/Proofs/Deep/A.lean", "module\n");
        fixture.write("verification/lakefile.lean", "-- another\n");
        fixture.commit_all();
        // The recipe: an index of the commit without the other paths.
        let root = fixture.root().to_path_buf();
        let index = root.join("artifacts/index");
        let recipe = |args: &[&str]| {
            let output = Command::new("git")
                .args(args)
                .current_dir(&root)
                .env_clear()
                .env("PATH", SYSTEM_PATH)
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .env("GIT_INDEX_FILE", &index)
                .output()
                .expect("Git runs");
            assert!(output.status.success(), "{args:?}: {output:?}");
            String::from_utf8(output.stdout)
                .expect("UTF-8")
                .trim()
                .to_string()
        };
        recipe(&["read-tree", "HEAD"]);
        recipe(&[
            "rm",
            "-r",
            "--cached",
            "--quiet",
            "--",
            ".",
            ":(exclude,glob)verification/**/*.lean",
            ":(exclude)verification/axioms.json",
            ":(exclude,glob)verification/lakefile.*",
            ":(exclude)verification/lean-toolchain",
            ":(exclude)verification/lake-manifest.json",
        ]);
        recipe(&[
            "rm",
            "-r",
            "--cached",
            "--quiet",
            "--ignore-unmatch",
            "--",
            "verification/Krepi/Proofs",
        ]);
        let files = recipe(&["ls-files"]);
        assert_eq!(files.lines().count(), 11, "{files}");
        assert_eq!(hash(&mut fixture, &LAYOUT), recipe(&["write-tree"]));
        // A commit without a statement side has the empty tree.
        let none = Layout {
            project: "absent",
            ..LAYOUT
        };
        assert_eq!(
            hash(&mut fixture, &none),
            "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
        );
    }

    #[test]
    fn a_statement_side_file_that_imports_a_proof_fails() {
        for directory in ["Statements", "Proofs"] {
            let path = format!("verification/Krepi/{directory}/H.lean");
            for (index, text) in IMPORTS_OF_PROOFS.iter().enumerate() {
                let problems = lean::source_problems(&path, text, &[], &LAYOUT);
                let import = if index == 4 {
                    "Krepi"
                } else {
                    "Krepi.Proofs.Counter"
                };
                let mut expected = Vec::new();
                if index == 2 {
                    expected.push(format!(
                        "{path} is not a module file: its header has no `module`"
                    ));
                }
                if directory == "Statements" {
                    expected.push(format!("{path} imports {import}"));
                }
                assert_eq!(problems, expected, "{directory} {index}");
            }
        }
        let (module, imports) = header_imports(&lean::tokens(IMPORTS_OF_PROOFS[1]));
        assert!(module);
        assert_eq!(
            imports,
            [
                "Krepi.Spec.Counter",
                "KrepiGen.Counter",
                "Krepi.Statements.Counter",
                "Krepi.Proofs.Counter"
            ]
        );
        // The rule compares whole components.
        let neighbours =
            "module\nimport Krepi.ProofsHelper\nimport KrepiGen.Proofs\nimport Krepi.Spec\n";
        assert!(
            lean::source_problems("verification/Krepi/Spec/A.lean", neighbours, &[], &LAYOUT)
                .is_empty()
        );
    }

    #[test]
    fn an_import_in_a_comment_is_not_an_import() {
        // A header with imports in comments and a doc comment after it; a
        // module doc before `module`, after which Lean reads no import; and
        // two names after one `import`, of which Lean reads the first.
        let comments = "module\n\
            -- import Krepi.Proofs.Counter\n\
            /- import Krepi.Proofs.Counter -/\n\
            public import Krepi.Spec.Counter\n\
            \n\
            -- not a header any more:\n\
            /-- doc: import Krepi.Proofs.Counter -/\n\
            def x := 1\n";
        let module_doc =
            "/-! module doc before the header -/\nmodule\nimport Krepi.Proofs.Counter\n";
        let two_names = "module\nimport Krepi.Spec.Counter Krepi.Proofs.Counter\n";
        let read = |text: &str| header_imports(&lean::tokens(text));
        let spec = vec!["Krepi.Spec.Counter".to_string()];
        assert_eq!(read(comments), (true, spec.clone()));
        assert_eq!(read(module_doc), (false, Vec::new()));
        assert_eq!(read(two_names), (true, spec));
        let path = "verification/Krepi/Statements/H.lean";
        for text in [comments, two_names] {
            assert!(
                lean::source_problems(path, text, &[], &LAYOUT).is_empty(),
                "{text}"
            );
        }
    }

    #[test]
    fn the_committed_registries_parse() {
        let statements = include_str!("../../../verification/statements.json");
        let statements = load_statements(statements, &LAYOUT).expect("the statements parse");
        assert!(statements.statements.is_empty());
        assert_eq!(statements.hash.len(), 40);
        let axioms = lean::load_axioms(include_str!("../../../verification/axioms.json"));
        assert_eq!(axioms, Ok(BTreeSet::new()));
        let tcb = lean::load_tcb(include_str!("../../../verification/tcb.json"));
        assert_eq!(tcb, Ok(Vec::new()));
    }

    #[test]
    fn a_statement_registry_with_a_bad_entry_is_refused() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let file = |hash: &str, entries: &[String]| {
            let entries = entries.join(", ");
            format!("{{\"schema\": 1, \"hash\": \"{hash}\", \"statements\": [{entries}]}}")
        };
        // The statement `name`, proved by `theorem` of `module`, below
        // `Krepi`.
        let entry = |name: &str, theorem: &str, module: &str| {
            let fields = [("name", name), ("theorem", theorem), ("module", module)];
            let fields = fields.map(|(key, value)| format!("\"{key}\": \"Krepi.{value}\""));
            format!("{{{}, \"state\": \"proved\"}}", fields.join(", "))
        };
        let good = entry("Statements.Counter.S", "Proofs.Counter.t", "Proofs.Counter");
        let read = load_statements(&file(hash, std::slice::from_ref(&good)), &LAYOUT);
        assert_eq!(
            read.expect("a valid registry").statements[0].state,
            State::Proved
        );
        let other = entry("Statements.Counter.W", "Proofs.Counter.t", "Proofs.Counter");
        let upper = hash.to_uppercase();
        for (hash, entries, problem) in [
            (
                "0123",
                vec![good.clone()],
                "the hash 0123 does not name a Git tree",
            ),
            (
                &upper,
                vec![good.clone()],
                &format!("the hash {upper} does not name a Git tree"),
            ),
            (
                hash,
                vec![good.clone(), other],
                "Krepi.Proofs.Counter.t is registered twice",
            ),
            (
                hash,
                vec![entry(
                    "Proofs.Counter.S",
                    "Proofs.Counter.t",
                    "Proofs.Counter",
                )],
                "Krepi.Proofs.Counter.S must lie outside Krepi.Proofs and Krepi.Proofs.Counter below it",
            ),
            (
                hash,
                vec![entry("Statements.S", "Spec.t", "Spec")],
                "Krepi.Statements.S must lie outside Krepi.Proofs and Krepi.Spec below it",
            ),
            (
                hash,
                vec![entry("Statements.Ś", "Proofs.C.t", "Proofs.C")],
                "Krepi.Statements.Ś is not a Lean name of ASCII components",
            ),
        ] {
            let text = file(hash, &entries);
            assert_eq!(
                load_statements(&text, &LAYOUT),
                Err(problem.to_string()),
                "{text}"
            );
        }
        for text in [
            file(hash, &[good.replace("proved", "done")]),
            file(
                hash,
                &[good.replace("\"state\"", "\"extra\": 1, \"state\"")],
            ),
            format!("{{\"schema\": 2, \"hash\": \"{hash}\", \"statements\": []}}"),
        ] {
            assert!(load_statements(&text, &LAYOUT).is_err(), "{text}");
        }
    }

    #[test]
    fn a_specification_change_without_the_spec_label_fails() {
        unlabelled_change("spec-change", SPEC);
    }

    #[test]
    fn an_external_declaration_change_without_the_spec_label_fails() {
        unlabelled_change(
            "external-change",
            "verification/externals/Qual/X/FunsExternal.lean",
        );
    }

    #[test]
    fn an_axiom_registry_change_without_the_spec_label_fails() {
        unlabelled_change("axioms-change", "verification/axioms.json");
    }

    #[test]
    fn a_lake_project_change_without_the_spec_label_fails() {
        for file in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"] {
            unlabelled_change("lake-change", &format!("verification/{file}"));
        }
    }

    #[test]
    fn a_proved_statement_made_planned_without_the_spec_label_fails() {
        let mut fixture = project("demoted");
        let path = "verification/statements.json";
        let proved = registry(&[("S", "s", "proved"), ("T", "t", "proved")]);
        let base = commit(&fixture, &[(path, &proved)]);
        let why = "it no longer proves Krepi.Statements.Counter.S without the label spec";
        let restated = |names: &str| {
            format!("it adds, removes or renames the statements {names} without the label spec")
        };
        let (removed, renamed) = (
            restated("Krepi.Statements.Counter.S"),
            restated("Krepi.Statements.Counter.S, Krepi.Statements.Counter.W"),
        );
        for (case, after, also) in [
            (
                "planned",
                [("S", "s", "planned"), ("T", "t", "proved")].as_slice(),
                None,
            ),
            ("removed", &[("T", "t", "proved")], Some(removed.as_str())),
            (
                "renamed",
                &[("W", "s", "proved"), ("T", "t", "proved")],
                Some(renamed.as_str()),
            ),
        ] {
            commit(&fixture, &[(path, &registry(after))]);
            let record = guard(&mut fixture, &base, &[], None);
            assert_eq!(record.demoted, ["Krepi.Statements.Counter.S"], "{case}");
            // A removed or renamed statement is restated as well.
            let mut expected =
                Vec::from_iter(also.map(|also| ("proof-of-registered-statements", also)));
            expected.push(("statement-change-needs-spec", why));
            assert_eq!(failed(&record), expected, "{case}");
            let hash = hash(&mut fixture, &LAYOUT);
            let labelled = guard(&mut fixture, &base, &["spec"], Some(&approval(&hash)));
            assert_eq!(failed(&labelled), [], "{case}");
        }
        // A proof of a planned statement changes no statement.
        let planned = commit(&fixture, &[(path, &registry(&[("S", "s", "planned")]))]);
        commit(&fixture, &[(path, &registry(&[("S", "s", "proved")]))]);
        let record = guard(&mut fixture, &planned, &["proof"], PROVING);
        assert_eq!(
            (&record.demoted, failed(&record)),
            (&Vec::new(), Vec::new())
        );
    }

    #[test]
    fn a_proof_change_with_a_source_change_fails() {
        let mut fixture = project("proof-and-source");
        let base = head_of(&fixture);
        let source = "kernel/abi/src/lib.rs";
        commit(
            &fixture,
            &[(PROOF, "-- another proof\n"), (source, "// changed\n")],
        );
        let record = guard(&mut fixture, &base, &[], None);
        let why = format!("it changes the sources {source} with proof files {PROOF}");
        let rule = "no-sources-with-proofs-or-statements";
        assert_eq!(failed(&record), [(rule, why.as_str())]);
        assert_eq!(
            (record.proofs, record.sources),
            (vec![PROOF.to_string()], vec![source.to_string()])
        );
        // The label `proof` with a change of the sources alone.
        let base = head_of(&fixture);
        commit(&fixture, &[(source, "// changed again\n")]);
        let record = guard(&mut fixture, &base, &["proof"], PROVING);
        let why = format!("it changes the sources {source} with the label proof");
        assert_eq!(failed(&record), [(rule, why.as_str())]);
        assert_eq!(failed(&guard(&mut fixture, &base, &[], None)), []);
        // Other files of the workspaces, and Rust outside them, are no
        // sources, and a file below the proofs that is not Lean is no proof.
        let base = head_of(&fixture);
        let others = [
            ("kernel/abi/Cargo.toml", "# changed\n"),
            ("xtask/src/x.rs", ""),
            ("verification/Krepi/Proofs/README.md", "Notes.\n"),
        ];
        commit(
            &fixture,
            &[
                others[0],
                others[1],
                others[2],
                (PROOF, "-- a third proof\n"),
            ],
        );
        let record = guard(&mut fixture, &base, &["proof"], PROVING);
        assert_eq!(
            (&record.sources, failed(&record)),
            (&Vec::new(), Vec::new())
        );
        assert_eq!(record.proofs, [PROOF]);
    }

    #[test]
    fn a_statement_change_with_a_source_change_fails() {
        let mut fixture = project("statement-and-source");
        let base = head_of(&fixture);
        let build = "user/sdk/build.rs";
        commit(
            &fixture,
            &[
                (SPEC, "-- a changed definition\n"),
                (build, "fn main() {}\n"),
            ],
        );
        let hash = hash(&mut fixture, &LAYOUT);
        let record = guard(&mut fixture, &base, &["spec"], Some(&approval(&hash)));
        let why = format!("it changes the sources {build} with statement-side files {SPEC}");
        assert_eq!(
            failed(&record),
            [("no-sources-with-proofs-or-statements", why.as_str())]
        );
    }

    #[test]
    fn an_approved_hash_other_than_the_head_statement_hash_fails() {
        let mut fixture = project("approved-hash");
        let (base, old) = (head_of(&fixture), hash(&mut fixture, &LAYOUT));
        commit(&fixture, &[(SPEC, "-- a changed definition\n")]);
        let new = hash(&mut fixture, &LAYOUT);
        let record = guard(&mut fixture, &base, &["spec"], Some(&approval(&old)));
        let why = format!("the approved hash {old} is not {new}");
        assert_eq!(failed(&record), [("spec-approval", why.as_str())]);
        assert_eq!(record.statement_hash, new);
        let record = guard(&mut fixture, &base, &["spec"], Some(&approval(&new)));
        assert_eq!(failed(&record), []);
    }

    #[test]
    fn a_raised_heartbeat_limit_without_review_fails() {
        let mut fixture = project("heartbeats");
        let proof = |before_t: &str, before_u: &str| {
            format!(
                "module\n\npublic import Krepi.Statements.Counter\n\n\
                 {before_t}public theorem t : Krepi.Statements.Counter.S := by\n  decide\n\n\
                 {before_u}public theorem u : Krepi.Statements.Counter.S := by\n  decide\n"
            )
        };
        let raise = "set_option maxHeartbeats 400000 in\n";
        let base = commit(&fixture, &[(PROOF, &proof("", ""))]);
        let raised = commit(&fixture, &[(PROOF, &proof(raise, ""))]);
        let rule = "heartbeats-need-review";
        let why = |path: &str| {
            format!("it raises a heartbeat limit in {path} without a well-formed Heartbeats-Review")
        };
        let unreviewed = [(rule.to_string(), why(PROOF))];
        let failed = |record: &Record| {
            let failed = failed(record).into_iter();
            Vec::from_iter(failed.map(|(rule, why)| (rule.to_string(), why.to_string())))
        };
        assert_eq!(failed(&guard(&mut fixture, &base, &[], None)), unreviewed);
        let review = Some("Heartbeats-Review: rev42\n");
        let reviewed = guard(&mut fixture, &base, &[], review);
        assert_eq!(
            (failed(&reviewed), reviewed.raised),
            (Vec::new(), vec![PROOF.to_string()])
        );
        let malformed = Some("Heartbeats-Review: rev-42\n");
        let record = guard(&mut fixture, &base, &[], malformed);
        assert_eq!(failed(&record), unreviewed);
        // So is a value after a line break and a comment, which Lean reads.
        let split = proof("set_option maxHeartbeats -- reviewed?\n  400000 in\n", "");
        commit(&fixture, &[(PROOF, &split)]);
        assert_eq!(failed(&guard(&mut fixture, &base, &[], None)), unreviewed);
        // Lowering the limit needs no review.
        let lowered = proof("set_option maxHeartbeats 100000 in\n", "");
        commit(&fixture, &[(PROOF, &lowered)]);
        assert_eq!(failed(&guard(&mut fixture, &raised, &[], None)), []);
        // The same line before another theorem is a new raise.
        commit(&fixture, &[(PROOF, &proof("", raise))]);
        assert_eq!(failed(&guard(&mut fixture, &raised, &[], None)), unreviewed);
        // So is the line of the Aeneas template in a new file of reviewed
        // external declarations.
        let base = head_of(&fixture);
        let external = "verification/externals/Qual/Y/FunsExternal.lean";
        let template = "module\n\n/- You can set the `maxHeartbeats` value with the \
            `-max-heartbeats` CLI option -/\nset_option maxHeartbeats 1000000\n\n\
            namespace KrepiGen.Qual.Y\n";
        commit(&fixture, &[(external, template)]);
        let record = guard(&mut fixture, &base, &["spec"], None);
        assert_eq!(record.rules[rule], Some(why(external)));
    }

    #[test]
    fn the_raised_heartbeat_limits_of_a_file_are_read() {
        // Lean reads the value across white space and comments, and takes
        // the option's name in `«»`; a value that cannot be read counts.
        let text = "\
            set_option maxHeartbeats 400000 in\n\n  \
            theorem a : True := trivial\n\
            set_option maxHeartbeats 200000 in\n\
            set_option maxHeartbeats 0\n\
            set_option maxHeartbeats 400_000 in\n\
            set_option maxHeartbeats 0x100 in\n\
            set_option synthInstance.maxHeartbeats 40000 in\n\
            set_option synthInstance.maxHeartbeats 20000 in\n\
            set_option «synthInstance».«maxHeartbeats» 30000 in\n\
            set_option maxHeartbeats\n  400000 in\n\
            set_option «maxHeartbeats» 400000 in\n\
            set_option maxHeartbeats /- c -/ 100000 in\n\
            set_option maxHeartbeats 99999999999999999999 in\n\
            /- You can set the `maxHeartbeats` value -/\n\
            leanOptions = { maxHeartbeats = 999999 }\n\
            \"maxHeartbeats\" = 999999\n\
            moreLeanArgs = [\"-DmaxHeartbeats=300000\"]\n";
        let lines = Vec::from_iter(text.lines().map(str::trim).filter(|l| !l.is_empty()));
        let key = |line: &str, next: usize| (line.to_string(), lines[next].to_string());
        let mut raised = BTreeSet::from([
            key(lines[0], 1),
            key("set_option maxHeartbeats 400000 in", 11),
            (
                "moreLeanArgs = [\"-DmaxHeartbeats=300000\"]".to_string(),
                String::new(),
            ),
        ]);
        raised.extend([3, 4, 5, 6, 8, 11, 12, 13, 14, 15, 16].map(|at| key(lines[at], at + 1)));
        assert_eq!(raises(text), raised);
        assert_eq!(raised.len(), 14);
        assert_eq!(lines[1], "theorem a : True := trivial");
        assert_eq!(raises("set_option maxHeartbeats 1 in"), BTreeSet::new());
    }

    #[test]
    fn a_spec_change_with_review_approval_and_the_head_hash_passes() {
        let mut fixture = project("spec-approved");
        let base = head_of(&fixture);
        let head = commit(&fixture, &[(SPEC, "-- a changed definition\n")]);
        let hash = hash(&mut fixture, &LAYOUT);
        let record = guard(&mut fixture, &base, &["spec"], Some(&approval(&hash)));
        let rules = RULES.map(|(rule, _)| (rule.to_string(), None));
        let expected = Record {
            base: base.clone(),
            head,
            merge_base: base,
            labels: BTreeSet::from(["spec".to_string()]),
            ai_proof: false,
            statement_hash: hash,
            statement_side: vec![SPEC.to_string()],
            rules: BTreeMap::from(rules),
            ..Record::default()
        };
        assert_eq!(record, expected);
    }

    #[test]
    fn a_spec_label_without_its_fields_fails() {
        let mut fixture = project("spec-fields");
        let base = head_of(&fixture);
        commit(&fixture, &[(SPEC, "-- a changed definition\n")]);
        let hash = hash(&mut fixture, &LAYOUT);
        let lacks = |fields: &str| format!("the description lacks a well-formed {fields}");
        let approved = approval(&hash);
        for (body, why) in [
            (None, lacks("Review, Approval, Approved-Statement-Hash")),
            (
                Some("Phase: statement\nAuthor: au1\nReview: rev42\n".to_string()),
                lacks("Approval, Approved-Statement-Hash"),
            ),
            (Some(approved.replace("rev42", "rev-42")), lacks("Review")),
            (Some(approved.replace("app7", "")), lacks("Approval")),
            (
                Some(approved.replace("rev42", &"r".repeat(65))),
                lacks("Review"),
            ),
            (Some(format!("{approved}Review: rev43\n")), lacks("Review")),
            (
                Some(approved.replace("Review:", "- Review:")),
                lacks("Review"),
            ),
            (
                Some(approval(&hash.to_uppercase())),
                lacks("Approved-Statement-Hash"),
            ),
            (Some(approval(&hash[1..])), lacks("Approved-Statement-Hash")),
        ] {
            let record = guard(&mut fixture, &base, &["spec"], body.as_deref());
            // Without a description, the phase and the author are missing too.
            let both = lacks("Phase, Author");
            let phase = body
                .is_none()
                .then_some(("phase-and-author", both.as_str()));
            let expected =
                Vec::from_iter(phase.into_iter().chain([("spec-approval", why.as_str())]));
            assert_eq!(failed(&record), expected, "{body:?}");
        }
        // Spaces around a value, and an id of 64 characters, are allowed.
        let spaced = approved.replace("rev42", &format!("  {}  ", "r".repeat(64)));
        let record = guard(&mut fixture, &base, &["spec"], Some(&spaced));
        assert_eq!(failed(&record), []);
    }

    #[test]
    fn a_spec_or_proof_label_without_phase_and_author_fails() {
        let mut fixture = project("phase-and-author");
        let rule = "phase-and-author";
        let lacks = |fields: &str| format!("the description lacks a well-formed {fields}");
        // A statement change with the label `spec` and its approval.
        let base = head_of(&fixture);
        commit(&fixture, &[(SPEC, "-- a changed definition\n")]);
        let approved = approval(&hash(&mut fixture, &LAYOUT));
        let bare = approved.replace("Phase: statement\r\nAuthor: au1\r\n", "");
        let record = guard(&mut fixture, &base, &["spec"], Some(&bare));
        assert_eq!(failed(&record), [(rule, lacks("Phase, Author").as_str())]);
        assert_eq!(
            failed(&guard(&mut fixture, &base, &["spec"], Some(&approved))),
            []
        );
        // A proof change with the label `proof`.
        let base = head_of(&fixture);
        commit(&fixture, &[(PROOF, "-- a proof\n")]);
        let mut proof = |body| guard(&mut fixture, &base, &["proof"], body);
        for body in [Some("Proves a statement.\n"), None] {
            let record = proof(body);
            assert_eq!(failed(&record), [(rule, lacks("Phase, Author").as_str())]);
        }
        // A phase that is not one of the three, or one of them in another
        // case, a field after white space, an author of another form, and a
        // field given twice.
        for (body, fields) in [
            ("Phase: review\nAuthor: au1\n", "Phase"),
            ("Phase: Proof\nAuthor: au1\n", "Phase"),
            (" Phase: proof\nAuthor: au1\n", "Phase"),
            ("Phase: proof\nAuthor: a-1\n", "Author"),
            ("Phase: proof\nAuthor: au1\nPhase: proof\n", "Phase"),
            ("Phase: proof\nAuthor: au1\nAuthor: au2\n", "Author"),
            ("Phase:\nAuthor:\n", "Phase, Author"),
        ] {
            let record = proof(Some(body));
            assert_eq!(failed(&record), [(rule, lacks(fields).as_str())], "{body}");
        }
        for body in [
            "Phase: rewrite\nAuthor: a1\n",
            "Phase:  statement \r\nAuthor: au1\r\n",
        ] {
            assert_eq!(failed(&proof(Some(body))), [], "{body}");
        }
        // Without either label, the fields are not needed.
        let record = guard(&mut fixture, &base, &[], None);
        assert_eq!(record.rules[rule], None);
    }

    #[test]
    fn a_proof_of_an_unregistered_statement_fails() {
        let mut fixture = project("registered");
        let path = "verification/statements.json";
        let base = commit(&fixture, &[(path, &registry(&[("S", "s", "planned")]))]);
        let rule = "proof-of-registered-statements";
        let why = |name: &str| {
            format!(
                "it adds, removes or renames the statements Krepi.Statements.Counter.{name} \
                 without the label spec"
            )
        };
        let proved = [("S", "s", "proved"), ("T", "t", "proved")];
        commit(&fixture, &[(path, &registry(&proved))]);
        let record = guard(&mut fixture, &base, &["proof"], PROVING);
        assert_eq!(record.restated, ["Krepi.Statements.Counter.T"]);
        assert_eq!(failed(&record), [(rule, why("T").as_str())]);
        // Without the label `proof` the rule fails all the same.
        let record = guard(&mut fixture, &base, &[], None);
        assert_eq!(record.restated, ["Krepi.Statements.Counter.T"]);
        assert_eq!(record.rules[rule].as_deref(), Some(why("T").as_str()));
        // A registered statement from planned to proved, with another theorem
        // or another module, and one that stays planned but changes.
        let elsewhere = |text: String| {
            text.replace(
                "\"module\": \"Krepi.Proofs.Counter\"",
                "\"module\": \"Krepi.Proofs.Other\"",
            )
        };
        for after in [
            registry(&[("S", "s", "proved")]),
            registry(&[("S", "u", "proved")]),
            elsewhere(registry(&[("S", "s", "proved")])),
            registry(&[("S", "u", "planned")]),
        ] {
            commit(&fixture, &[(path, &after)]);
            let record = guard(&mut fixture, &base, &["proof"], PROVING);
            assert_eq!(
                (&record.restated, failed(&record)),
                (&Vec::new(), vec![]),
                "{after}"
            );
        }
        // A removed statement.
        commit(&fixture, &[(path, &registry(&[]))]);
        let record = guard(&mut fixture, &base, &["proof"], PROVING);
        assert_eq!(record.restated, ["Krepi.Statements.Counter.S"]);
        assert_eq!(failed(&record), [(rule, why("S").as_str())]);
        // A proved statement whose proof moves to another theorem or another
        // module, as a rewrite may move it.
        let base = commit(&fixture, &[(path, &registry(&[("S", "s", "proved")]))]);
        let rewrite = Some("Moves a proof.\n\nPhase: rewrite\nAuthor: au1\n");
        for after in [
            registry(&[("S", "u", "proved")]),
            elsewhere(registry(&[("S", "s", "proved")])),
        ] {
            commit(&fixture, &[(path, &after)]);
            let record = guard(&mut fixture, &base, &["proof"], rewrite);
            assert_eq!(
                (&record.restated, failed(&record)),
                (&Vec::new(), vec![]),
                "{after}"
            );
        }
    }

    #[test]
    fn removing_a_target_without_the_spec_label_fails() {
        // The planned target has no theorem, mutant or proved key to lose.
        let why = "it removes the targets slots in targets.json without the label spec";
        registry_change(
            "target-removed",
            |r| list(&mut r[0], "targets").truncate(1),
            &[("registry-target-removed", why)],
        );
    }

    #[test]
    fn removing_an_obligation_theorem_without_the_spec_label_fails() {
        let theorem = "Krepi.Proofs.Table.lookup_refines";
        let why = format!("it removes the theorems {theorem} in table without the label spec");
        registry_change(
            "theorem-removed",
            |r| list(&mut table(r)["obligations"][0], "theorems").retain(|t| t != theorem),
            &[
                (
                    "registry-obligation-changed",
                    "it changes obligations of table without the label spec",
                ),
                ("registry-theorem-removed", &why),
            ],
        );
    }

    #[test]
    fn removing_a_mutant_without_the_spec_label_fails() {
        registry_change(
            "mutant-removed",
            |r| table(r)["mutants"] = json!([]),
            &[(
                "registry-mutant-removed",
                "it removes the mutants bound in table without the label spec",
            )],
        );
    }

    #[test]
    fn narrowing_proves_without_the_spec_label_fails() {
        registry_change(
            "proves-narrowed",
            |r| table(r)["proves"] = json!([]),
            &[(
                "registry-proves-narrowed",
                "it removes from proves kernel/src/table.rs#lookup in table without the label spec",
            )],
        );
    }

    #[test]
    fn making_a_formal_target_planned_without_the_spec_label_fails() {
        registry_change(
            "made-planned",
            |r| table(r)["state"] = json!("planned"),
            &[(
                "registry-formal-made-planned",
                "it makes planned the targets table without the label spec",
            )],
        );
    }

    #[test]
    fn adding_an_unconstrained_function_without_the_spec_label_fails() {
        registry_change(
            "unconstrained-added",
            |r| list(table(r), "unconstrained").push(json!("krepi_kernel::table::other")),
            &[(
                "registry-unconstrained-added",
                "it adds the unconstrained krepi_kernel::table::other in table without the label spec",
            )],
        );
    }

    #[test]
    fn adding_an_opaque_cut_point_without_the_spec_label_fails() {
        let cut = json!({"pattern": "krepi_kernel::table::write", "source": "s", "reason": "r"});
        registry_change(
            "opaque-added",
            |r| list(table(r), "opaque").push(cut),
            &[(
                "registry-opaque-added",
                "it adds the cut points krepi_kernel::table::write in table without the label spec",
            )],
        );
    }

    #[test]
    fn adding_a_trusted_axiom_without_the_spec_label_fails() {
        // `sorryAx` among the trusted axioms of a target, and a new item of
        // the trusted base.
        let axiom = json!({"name": "sorryAx", "reason": "Not proved yet."});
        registry_change(
            "trusted-axiom-added",
            |r| list(table(r), "trusted_axioms").push(axiom),
            &[(
                "registry-trusted-axiom-added",
                "it adds the trusted axioms sorryAx in table without the label spec",
            )],
        );
        let item = json!({
            "kind": "native-decision",
            "file": "verification/Krepi/Proofs/Table.lean",
            "declaration": "Krepi.Proofs.Table.lookup_bound",
            "reason": "Decided by evaluation."
        });
        let why = "it adds the trusted axioms native-decision verification/Krepi/Proofs/Table.lean \
                   Krepi.Proofs.Table.lookup_bound in tcb.json without the label spec";
        registry_change(
            "trusted-item-added",
            |r| list(&mut r[2], "items").push(item),
            &[("registry-trusted-axiom-added", why)],
        );
    }

    #[test]
    fn adding_a_model_without_the_spec_label_fails() {
        // A model of the model registry, and the models of a target.
        registry_change(
            "model-added",
            |r| list(&mut r[1], "models").push(json!({"name": "clock"})),
            &[(
                "registry-model-added",
                "it adds the models \"clock\" in models.json without the label spec",
            )],
        );
        registry_change(
            "target-models-added",
            |r| table(r)["models"] = json!("verification/models/table"),
            &[(
                "registry-model-added",
                "it adds the models verification/models/table in table without the label spec",
            )],
        );
    }

    #[test]
    fn changing_an_obligation_without_the_spec_label_fails() {
        registry_change(
            "obligation-changed",
            |r| table(r)["obligations"][0]["statement"] = json!("Krepi.Statements.Table.other"),
            &[(
                "registry-obligation-changed",
                "it changes obligations of table without the label spec",
            )],
        );
    }

    #[test]
    fn changing_start_from_without_the_spec_label_fails() {
        registry_change(
            "start-from-changed",
            |r| list(table(r), "start_from").push(json!("krepi_kernel::table::insert")),
            &[(
                "registry-start-from-changed",
                "it changes start_from of table without the label spec",
            )],
        );
    }

    #[test]
    fn changing_the_file_of_a_mutant_without_the_spec_label_fails() {
        registry_change(
            "mutant-file-changed",
            |r| table(r)["mutants"][0]["file"] = json!("kernel/src/other.rs"),
            &[(
                "registry-mutant-file-changed",
                "it changes the file of table/bound without the label spec",
            )],
        );
    }

    #[test]
    fn changing_the_pattern_of_a_mutant_without_the_spec_label_fails() {
        registry_change(
            "mutant-find-changed",
            |r| table(r)["mutants"][0]["find"] = json!("index < 5"),
            &[(
                "registry-mutant-find-changed",
                "it changes the pattern of table/bound without the label spec",
            )],
        );
    }

    #[test]
    fn changing_the_replacement_of_a_mutant_without_the_spec_label_fails() {
        registry_change(
            "mutant-replace-changed",
            |r| table(r)["mutants"][0]["replace"] = json!("index < 3"),
            &[(
                "registry-mutant-replace-changed",
                "it changes the replacement of table/bound without the label spec",
            )],
        );
    }

    #[test]
    fn renaming_a_mutant_without_the_spec_label_fails() {
        // The old name is removed as well.
        registry_change(
            "mutant-renamed",
            |r| table(r)["mutants"][0]["name"] = json!("bound2"),
            &[
                (
                    "registry-mutant-removed",
                    "it removes the mutants bound in table without the label spec",
                ),
                (
                    "registry-mutant-renamed",
                    "it renames the mutants table/bound to bound2 without the label spec",
                ),
            ],
        );
    }

    #[test]
    fn adding_a_theorem_to_the_fails_of_a_mutant_without_the_spec_label_fails() {
        let theorem = json!("Krepi.Proofs.Table.lookup_refines");
        registry_change(
            "fails-grown",
            |r| list(&mut table(r)["mutants"][0], "fails").push(theorem),
            &[(
                "registry-mutant-fails-grown",
                "it adds to fails Krepi.Proofs.Table.lookup_refines in table/bound \
                 without the label spec",
            )],
        );
    }

    #[test]
    fn changing_the_reason_of_a_trusted_item_without_the_spec_label_fails() {
        // Of a trusted axiom, of a cut point and of an item of the trusted
        // base.
        let rule = "registry-trusted-reason-changed";
        let why = |item: &str| format!("it changes the reasons of {item} without the label spec");
        let axiom = why("Krepi.Axioms.clock in table");
        registry_change(
            "axiom-reason",
            |r| table(r)["trusted_axioms"][0]["reason"] = json!("Another."),
            &[(rule, &axiom)],
        );
        let cut = why("krepi_kernel::table::hardware::read in table");
        registry_change(
            "opaque-reason",
            |r| table(r)["opaque"][0]["reason"] = json!("Another."),
            &[(rule, &cut)],
        );
        let item = why("axiom-pattern KrepiGen.Table. in tcb.json");
        registry_change(
            "item-reason",
            |r| r[2]["items"][0]["reason"] = json!("Another."),
            &[(rule, &item)],
        );
    }

    #[test]
    fn a_reformatted_registry_needs_no_spec() {
        // Another order of the targets, of the theorems of an obligation and
        // of the fields, and a default written out.
        let (mut fixture, base) = registered("reformatted");
        let [(path, mut targets), ..] = registries();
        list(&mut targets, "targets").reverse();
        let table = &mut targets["targets"][1];
        list(&mut table["obligations"][0], "theorems").reverse();
        table["state"] = json!("formal");
        fixture.write(path, &targets.to_string());
        fixture.commit_all();
        let record = guard(&mut fixture, &base, &[], None);
        assert_eq!(
            (failed(&record), &record.registry),
            (vec![], &BTreeMap::new())
        );
    }

    #[test]
    fn tightening_the_registry_needs_no_spec() {
        // A planned target made formal, fewer trusted axioms, unconstrained
        // functions, cut points and items of the trusted base, and a key more
        // in proves.
        let (mut fixture, base) = registered("tightened");
        let mut values = registries();
        let targets = &mut values[0].1;
        targets["targets"][1]["state"] = json!("formal");
        let table = &mut targets["targets"][0];
        for field in ["trusted_axioms", "unconstrained", "opaque"] {
            table[field] = json!([]);
        }
        list(table, "proves").push(json!("kernel/src/table.rs#insert"));
        values[2].1["items"] = json!([]);
        commit_registries(&fixture, &values);
        let record = guard(&mut fixture, &base, &[], None);
        assert_eq!(
            (failed(&record), &record.registry),
            (vec![], &BTreeMap::new())
        );
    }

    #[test]
    fn an_unreadable_registry_needs_the_spec_label() {
        // A head that is not JSON, and a merge base of another schema.
        let rule = "registry-unreadable";
        let why = |side: &str, error: &str| {
            format!(
                "it cannot read verification/targets.json at {side}: {error} without the label spec"
            )
        };
        let (mut fixture, base) = registered("unreadable");
        commit(&fixture, &[(LAYOUT.registry, "{")]);
        let error = registry::parse("{").expect_err("not JSON");
        let record = guard(&mut fixture, &base, &[], None);
        assert_eq!(failed(&record), [(rule, why("the head", &error).as_str())]);
        let hash = hash(&mut fixture, &LAYOUT);
        let labelled = guard(&mut fixture, &base, &["spec"], Some(&approval(&hash)));
        assert_eq!(failed(&labelled), []);
        let other = r#"{"schema": 3, "targets": []}"#;
        let base = commit(&fixture, &[(LAYOUT.registry, other)]);
        commit_registries(&fixture, &registries()[..1]);
        let record = guard(&mut fixture, &base, &[], None);
        let error = "schema 3 where 2 is expected";
        assert_eq!(
            failed(&record),
            [(rule, why("the merge base", error).as_str())]
        );
        let labelled = guard(&mut fixture, &base, &["spec"], Some(&approval(&hash)));
        assert_eq!(failed(&labelled), []);
    }

    #[test]
    fn the_pull_request_template_holds_the_guard_fields() {
        let template = include_str!("../../../.github/pull_request_template.md");
        let given = fields(template);
        for name in [
            "Phase",
            "Author",
            "Review",
            "Approval",
            "Approved-Statement-Hash",
            "Heartbeats-Review",
        ] {
            let named = |line: &&str| line.split_once(':').is_some_and(|(field, _)| field == name);
            assert_eq!(template.lines().filter(named).count(), 1, "{name}");
            assert_eq!(given.get(name), Some(&None), "{name}");
        }
        assert!(template.contains("`ai-proof`"));
        for phase in PHASES {
            assert!(template.contains(&format!("`{phase}`")), "{phase}");
        }
    }

    #[test]
    fn both_sides_of_a_rename_count() {
        let mut fixture = project("rename");
        let base = head_of(&fixture);
        let moved = "verification/Krepi/Proofs/Moved.lean";
        fixture.git(&["mv", SPEC, moved]);
        fixture.commit_all();
        let record = guard(&mut fixture, &base, &[], None);
        let changed = (&record.statement_side, &record.proofs, &record.sources);
        assert_eq!(
            changed,
            (&vec![SPEC.to_string()], &vec![moved.to_string()], &vec![])
        );
        let why = format!("it changes {SPEC} without the label spec");
        assert_eq!(
            failed(&record),
            [("statement-change-needs-spec", why.as_str())]
        );
    }

    #[test]
    fn only_the_changes_since_the_merge_base_count() {
        let mut fixture = project("merge-base");
        let fork = head_of(&fixture);
        let main = commit(&fixture, &[(SPEC, "-- changed on main\n")]);
        fixture.git(&["checkout", "--quiet", "-b", "topic", &fork]);
        commit(&fixture, &[(PROOF, "-- a proof\n")]);
        let record = guard(&mut fixture, &main, &[], None);
        assert_eq!((&record.base, &record.merge_base), (&main, &fork));
        assert_eq!(record.proofs, [PROOF]);
        assert!(record.statement_side.is_empty());
        assert_eq!(failed(&record), []);
    }

    #[test]
    fn the_labels_are_recorded() {
        let mut fixture = project("labels");
        let base = head_of(&fixture);
        commit(&fixture, &[(PROOF, "-- a proof\n")]);
        let labels = ["proof", "ai-proof", "documentation"];
        let record = guard(&mut fixture, &base, &labels, PROVING);
        assert_eq!(record.labels, BTreeSet::from(labels.map(String::from)));
        assert!(record.ai_proof);
        assert_eq!(failed(&record), []);
        let record = guard(&mut fixture, &base, &["proof"], None);
        assert!(!record.ai_proof);
    }

    #[test]
    fn an_event_that_is_not_a_pull_request_fails() {
        let mut fixture = project("not-a-pull-request");
        let work = fixture.root().join("artifacts/guard");
        fs::create_dir_all(&work).expect("create the work directory");
        let head = head_of(&fixture);
        let unread = "the event has no pull request with commits and labels";
        let label = |name: &str| PULL_REQUEST.replace("\"name\": \"proof\"", name);
        for (text, error) in [
            (PUSH.to_string(), unread),
            (event("HEAD", &head, &[], None), unread),
            (event(&head, &head.to_uppercase(), &[], None), unread),
            (
                event(&head, &head, &[], None).replace("\"labels\"", "\"tags\""),
                unread,
            ),
            (label("\"name\": 7"), unread),
            (label("\"title\": \"proof\""), unread),
        ] {
            assert_eq!(
                check(&mut fixture, &text, &LAYOUT, &work),
                Err(error.to_string())
            );
        }
        let missing = event(&"0".repeat(40), &head, &[], None);
        let error = check(&mut fixture, &missing, &LAYOUT, &work).expect_err("no such commit");
        assert!(error.contains(&"0".repeat(40)), "{error}");
        let error = check(&mut fixture, "{", &LAYOUT, &work).expect_err("not JSON");
        assert!(error.starts_with("the event: "), "{error}");
        assert!(
            check(
                &mut fixture,
                &event(&head, &head, &[], None),
                &LAYOUT,
                &work
            )
            .is_ok()
        );
    }

    #[test]
    fn a_run_on_a_pull_request_records_the_guard() {
        let mut fixture = project("guard-phase");
        let base = head_of(&fixture);
        commit(
            &fixture,
            &[
                (SPEC, "-- a changed definition\n"),
                ("docs/notes.md", "Notes.\n"),
            ],
        );
        let text = event(&base, &head_of(&fixture), &["ai-proof"], None);
        fixture.write("artifacts/event.json", &text);
        let path = fixture.root().join("artifacts/event.json");
        let path = path.to_str().expect("a UTF-8 path").to_string();
        let var = |name: &str| match name {
            "GITHUB_EVENT_NAME" => Some("pull_request".to_string()),
            "GITHUB_EVENT_PATH" => Some(path.clone()),
            _ => None,
        };
        let phases = Vec::from_iter(phase(&var));
        let done = run::tests::gate(&fixture, &[], phases);
        let work = fixture.root().join("artifacts/guard");
        fs::create_dir_all(&work).expect("create the work directory");
        let expected = check(&mut fixture, &text, &LAYOUT, &work).expect("the guard");
        assert_eq!(done.receipt.guard.as_ref(), Some(&expected));
        assert!(expected.ai_proof);
        assert!(expected.rules["statement-change-needs-spec"].is_some());
        // A failing rule decides nothing about the run.
        assert_eq!(
            (done.receipt.status, done.receipt.complete),
            (Status::Verified, true)
        );
        assert!(done.receipt.units.is_empty());
        let phase = &done.receipt.phases["guard"];
        assert_eq!((phase.budget_seconds, phase.ran), (300, true));
        let guarded =
            (done.receipt.commands.iter()).filter(|c| c.phase.as_deref() == Some("guard"));
        let guarded = Vec::from_iter(guarded);
        assert!(
            guarded
                .iter()
                .any(|command| command.argv[3] == "merge-base")
        );
        // Only the changed file of the statement side is read, at both commits.
        let read = guarded
            .iter()
            .filter(|command| command.argv[3] == "cat-file");
        assert_eq!(read.count(), 2);
        assert!(
            guarded
                .iter()
                .all(|command| command.site == Site::Git && command.unit.is_none())
        );
        // Without a pull request event there is no guard phase.
        let push = |name: &str| (name == "GITHUB_EVENT_NAME").then(|| "push".to_string());
        assert!(
            super::phase(&|name| push(name).or(var(name).filter(|_| name != "GITHUB_EVENT_NAME")))
                .is_none()
        );
        let unnamed = |name: &str| var(name).filter(|_| name != "GITHUB_EVENT_NAME");
        assert!(super::phase(&unnamed).is_none());
        let pathless = |name: &str| var(name).filter(|_| name != "GITHUB_EVENT_PATH");
        assert!(super::phase(&pathless).is_none());
        // An event that cannot be read stops the run.
        fs::remove_file(&path).expect("remove the event");
        let done = run::tests::gate(&fixture, &[], Vec::from_iter(super::phase(&var)));
        assert_eq!(
            (done.receipt.status, &done.receipt.guard),
            (Status::ToolFailure, &None)
        );
        assert!(
            done.failures()[0].starts_with("the phase guard stopped: "),
            "{:?}",
            done.failures()
        );
        // A registry that cannot be read fails its rule and stops nothing.
        let base = commit(&fixture, &[(LAYOUT.registry, r#"{"schema": 3}"#)]);
        let head = commit(
            &fixture,
            &[(LAYOUT.registry, r#"{"schema": 2, "targets": []}"#)],
        );
        fixture.write("artifacts/event.json", &event(&base, &head, &[], None));
        let done = run::tests::gate(&fixture, &[], Vec::from_iter(super::phase(&var)));
        assert_eq!(done.receipt.status, Status::Verified);
        let guarded = done.receipt.guard.expect("the guard is recorded");
        assert!(guarded.rules["registry-unreadable"].is_some());
    }

    #[test]
    fn the_standalone_guard_runs_git_without_the_caller_s_git_variables() {
        if let Some(root) = std::env::var_os(STANDALONE) {
            // The caller of the guard, whose Git variables name another
            // repository.
            let root = PathBuf::from(root);
            let guard = |event: &str| {
                let event = root.join("artifacts").join(event);
                let args = ["guard", "--event", event.to_str().expect("a UTF-8 path")];
                let matches = cli("").try_get_matches_from(args).expect("a command line");
                command(&root, &LAYOUT, &matches)
            };
            assert_eq!(guard("passing.json"), ExitCode::SUCCESS);
            assert_eq!(guard("failing.json"), ExitCode::FAILURE);
            assert_eq!(guard("absent.json"), ExitCode::FAILURE);
            // The input of `git mktree` is gone.
            let work = fs::read_dir(root.join("artifacts/formal/guard")).expect("the directory");
            assert_eq!(work.count(), 0);
            return;
        }
        let fixture = project("standalone");
        let base = head_of(&fixture);
        let head = commit(&fixture, &[(PROOF, "-- a proof\n")]);
        fixture.write("artifacts/passing.json", &event(&base, &head, &[], None));
        fixture.write(
            "artifacts/failing.json",
            &event(&base, &head, &["proof"], None),
        );
        commit(&fixture, &[("kernel/abi/src/lib.rs", "// changed\n")]);
        let head = head_of(&fixture);
        fixture.write(
            "artifacts/failing.json",
            &event(&base, &head, &["proof"], None),
        );
        let elsewhere = Fixture::new("elsewhere");
        let git_dir = elsewhere.root().join(".git");
        let (_, tests) = module_path!()
            .split_once("::")
            .expect("a module path below the crate");
        let name =
            format!("{tests}::the_standalone_guard_runs_git_without_the_caller_s_git_variables");
        let output = Command::new(std::env::current_exe().expect("the test executable"))
            .args([name.as_str(), "--exact", "--test-threads=1", "--nocapture"])
            .env(STANDALONE, fixture.root())
            .env("GIT_DIR", &git_dir)
            .env("GIT_WORK_TREE", elsewhere.root())
            .env("GIT_INDEX_FILE", git_dir.join("index"))
            .env("GIT_OBJECT_DIRECTORY", git_dir.join("objects"))
            .output()
            .expect("run the test executable");
        let said = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "{said}{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(said.contains("test result: ok. 1 passed"), "{said}");
        assert!(said.contains("PASSED heartbeats-need-review"), "{said}");
        assert!(
            said.contains("FAILED no-sources-with-proofs-or-statements: "),
            "{said}"
        );
    }
}
