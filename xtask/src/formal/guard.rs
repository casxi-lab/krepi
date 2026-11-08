//! The statement side of the Lake project and `cargo xtask formal guard`,
//! as "Statements and proofs" and "Guard" in `docs/formal-verification.md`
//! describe them: the statement registry, the statement hash and the import
//! rule of the statement side, and the rules for pull requests that change
//! the statement side, the proofs or the sources.

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
use super::lean::{self, PROJECT_FILES, Token};
use super::paths::{self, Files, Git, tree_records};
use super::qualify::is_module;
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
/// heartbeat limit, and why each rule fails, or `None`.
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
    pub rules: BTreeMap<String, Option<String>>,
}

/// A rule: why it fails on a record with the description's fields, or `None`.
type Rule = fn(&Record, &BTreeMap<&str, Option<&str>>) -> Option<String>;

/// The phases of the proof work that `Phase` names.
const PHASES: [&str; 3] = ["statement", "proof", "rewrite"];

/// The rules of the guard, by name; later checks add rows.
const RULES: [(&str, Rule); 6] = [
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
];

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

/// Whether the repository path `path` lies on the statement side: a Lean
/// file of the Lake project outside the proofs, the registry of library
/// axioms, or a Lake project file.
pub fn statement_side(path: &str, layout: &Layout) -> bool {
    let Some(file) = path.strip_prefix(&format!("{}/", layout.project)) else {
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
    let files = tree_records(&listing)?;
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
    let mut output = |args: &[&str]| -> Result<String, String> {
        Ok(String::from_utf8_lossy(&git.git(args, None)?).into_owned())
    };
    let merge_base = output(&["merge-base", base, head])?.trim().to_string();
    let diff = ["diff", "--name-status", "--no-renames", "-z"];
    let changed = output(&[&diff[..], &[merge_base.as_str(), head]].concat())?;
    let mut record = Record {
        base: base.to_string(),
        head: head.to_string(),
        merge_base: merge_base.clone(),
        ai_proof: labels.contains("ai-proof"),
        labels,
        ..Record::default()
    };
    let proofs = format!("{}/{}/", layout.project, layout.proofs.replace('.', "/"));
    let workspaces = [layout.kernel, USER].map(|workspace| format!("{workspace}/"));
    let mut changes = changed.split_terminator('\0');
    while let (Some(status), Some(path)) = (changes.next(), changes.next()) {
        let proof = path.starts_with(&proofs) && path.ends_with(".lean");
        let (side, registry) = (statement_side(path, layout), path == layout.statements);
        let source = workspaces.iter().any(|dir| path.starts_with(dir)) && path.ends_with(".rs");
        record.statement_side.extend(side.then(|| path.to_string()));
        record.proofs.extend(proof.then(|| path.to_string()));
        record.sources.extend(source.then(|| path.to_string()));
        if !(side || proof || registry) {
            continue;
        }
        // The file at the merge base and at the head, where it exists.
        let mut text = |commit: &str, absent: &str| match status == absent {
            true => Ok(String::new()),
            false => output(&["cat-file", "blob", &format!("{commit}:{path}")]),
        };
        let (before, after) = (text(&merge_base, "A")?, text(head, "D")?);
        if registry {
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
struct Standalone<'a>(&'a Path);

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
            "verification/tcb.json",
            "verification/qualification/cases.json",
            "kernel/abi/src/lib.rs",
        ];
        for (path, after) in hashes_after(&mut fixture, &paths) {
            assert_eq!(after, before, "{path}");
        }
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
