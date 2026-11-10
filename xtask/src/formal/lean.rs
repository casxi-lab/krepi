//! The Lake project `verification/` as the gate builds it: the stage of a
//! unit, laid out as the repository with links below `artifacts/formal/lake`
//! to the installation, which is read in place, and no artifact cache, so no
//! build reuses an output from outside the run; the arguments of its Lake
//! commands and the reading of their output; the source rules of the
//! hand-written Lean; the registries; and the allowlist of the audits.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use serde::de::DeserializeOwned;
use walkdir::WalkDir;

use super::Layout;
use super::guard::{self, State, Statement};
use super::process::Ran;

/// The axioms that every Lean development may use. Anything else that
/// `#print axioms` reports for a theorem must be allowed for it by name.
pub const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

/// The directory of the links to the installation, relative to the root of
/// a stage, as `lakefile.toml` names it.
const LINKS: &str = "artifacts/formal/lake";

/// The project files that a stage copies from the export.
pub const PROJECT_FILES: [&str; 3] = ["lakefile.toml", "lean-toolchain", "lake-manifest.json"];

/// The audit file of a stage, in its project.
pub const AUDIT: &str = "Audit.lean";

/// Creates the stage `stage`, which must not exist, from the Lake project
/// `project` of the export, whose directory name it keeps, with the Lean
/// toolchain and the Lake lock of the project `pins` of the export, the root
/// package of the lock renamed to that of `project` when it is another, and
/// with the links to `backend`, the Aeneas Lean library of the installation,
/// and its packages. Returns the directory of the project in the stage.
pub fn create_stage(
    project: &Path,
    pins: &Path,
    stage: &Path,
    backend: &Path,
) -> Result<PathBuf, String> {
    let at = |path: &Path, error: std::io::Error| format!("{}: {error}", path.display());
    (fs::create_dir(stage))
        .map_err(|error| format!("cannot create the stage {}", at(stage, error)))?;
    let name = (project.file_name()).ok_or(format!("{} names no directory", project.display()))?;
    let staged = stage.join(name);
    fs::create_dir(&staged).map_err(|error| at(&staged, error))?;
    for (index, file) in PROJECT_FILES.into_iter().enumerate() {
        let (from, to) = (
            [project, pins][usize::from(index > 0)].join(file),
            staged.join(file),
        );
        fs::copy(&from, &to).map_err(|error| format!("cannot copy {}", at(&from, error)))?;
    }
    if project != pins {
        let read = |file: &str| fs::read_to_string(staged.join(file)).map_err(|e| at(&staged, e));
        let lakefile: toml::Table =
            (read(PROJECT_FILES[0])?.parse()).map_err(|e| format!("{e}"))?;
        let mut lock: serde_json::Value = (serde_json::from_str(&read(PROJECT_FILES[2])?))
            .map_err(|error| format!("the Lake lock: {error}"))?;
        lock["name"] = lakefile
            .get("name")
            .and_then(toml::Value::as_str)
            .unwrap_or("")
            .into();
        let path = staged.join(PROJECT_FILES[2]);
        let text = serde_json::to_string_pretty(&lock).map_err(|error| error.to_string())?;
        fs::write(&path, text + "\n").map_err(|error| at(&path, error))?;
    }
    let (links, packages) = (stage.join(LINKS), backend.join(".lake/packages"));
    fs::create_dir_all(&links).map_err(|error| at(&links, error))?;
    for (name, target) in [("aeneas", backend), ("packages", &packages)] {
        let link = links.join(name);
        std::os::unix::fs::symlink(target, &link).map_err(|error| at(&link, error))?;
    }
    Ok(staged)
}

/// Copies `file`, relative to `from`, to the same path below `to`, with its
/// directories.
pub fn copy_into(from: &Path, to: &Path, file: &str) -> Result<(), String> {
    let (source, destination) = (from.join(file), to.join(file));
    let parent = destination.parent().unwrap_or(to);
    fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    let copied = fs::copy(&source, &destination).map(|_| ());
    copied.map_err(|error| format!("cannot copy {}: {error}", source.display()))
}

/// The arguments of `lake` that build `targets` without Lake's cache, with
/// warnings as errors when `wfail`, so that `sorry` fails the build too.
pub fn build_args<T: ToString>(targets: &[T], wfail: bool) -> Vec<String> {
    let options = ["build", "--no-cache", "--wfail"][..2 + usize::from(wfail)].iter();
    let options = options.map(|option| option.to_string());
    options.chain(targets.iter().map(T::to_string)).collect()
}

/// The arguments of `lake` that check the Lean file `file`, relative to the
/// project, in the environment of the project.
pub fn check_args(file: &str) -> Vec<String> {
    ["env", "lean", file].map(str::to_string).into()
}

/// The source file of a project module, relative to the project.
pub fn module_file(module: &str) -> String {
    format!("{}.lean", module.replace('.', "/"))
}

/// The lines of a Lean or Lake log that report an error, trimmed.
pub fn errors(output: &str) -> Vec<String> {
    let lines = output.lines().filter(|line| line.contains("error:"));
    lines.map(|line| line.trim().to_string()).collect()
}

/// A Lean message with a position, `<severity>: <file>:<line>:<column>: ...`,
/// as whether it is an error, its file, its line and its column. `info:`
/// messages are not returned.
fn diagnostic(line: &str) -> Option<(bool, &str, usize, usize)> {
    let (error, rest) = match line.strip_prefix("error: ") {
        Some(rest) => (true, rest),
        None => (false, line.strip_prefix("warning: ")?),
    };
    let (position, _) = rest.split_once(": ")?;
    let mut parts = position.rsplitn(3, ':');
    let (column, number, file) = (parts.next()?, parts.next()?, parts.next()?);
    let column = column.parse().ok()?;
    let number = number.parse().ok()?;
    let file = file.trim_start_matches("./");
    file.ends_with(".lean")
        .then_some((error, file, number, column))
}

/// Every error and warning, which fails the build as well, that the log of a
/// `lake build` reports in the source files of `modules`, as module, line and
/// column.
pub fn proof_messages<'a>(output: &str, modules: &'a [String]) -> Vec<(&'a str, usize, usize)> {
    let files: Vec<String> = modules.iter().map(|module| module_file(module)).collect();
    output
        .lines()
        .filter_map(diagnostic)
        .filter_map(|(_, file, number, column)| {
            let index = files.iter().position(|own| own == file)?;
            Some((modules[index].as_str(), number, column))
        })
        .collect()
}

/// The lines of the log of a build without `--wfail` that report an error or
/// a warning other than ``declaration uses `sorry` `` in a `planned` file.
pub fn planned_problems(output: &str, planned: &[String]) -> Vec<String> {
    let allowed = |line: &str| {
        diagnostic(line).is_some_and(|(error, file, number, column)| {
            let sorry = format!("warning: {file}:{number}:{column}: declaration uses `sorry`");
            !error && planned.iter().any(|own| own == file) && line.trim_end() == sorry
        })
    };
    let message = |line: &&str| line.starts_with("error: ") || line.starts_with("warning: ");
    let lines = output.lines().filter(message).filter(|line| !allowed(line));
    lines.map(str::to_string).collect()
}

/// Parses `#print axioms` output, which may wrap long axiom lists.
pub fn parse_axioms(output: &str) -> BTreeMap<String, Vec<String>> {
    const DEPENDS: &str = "' depends on axioms: [";
    const NONE: &str = "' does not depend on any axioms";
    let mut result = BTreeMap::new();
    let joined = output.replace('\n', " ");
    let mut rest = joined.as_str();
    while let Some(start) = rest.find('\'') {
        let after = &rest[start + 1..];
        // A name may itself end with primes, so the entry ends at the first
        // marker rather than at the next quote.
        let none = after.find(NONE);
        let depends = after.find(DEPENDS).filter(|d| none.is_none_or(|n| *d < n));
        let (name, tail, axioms) = if let Some(d) = depends {
            let list = &after[d + DEPENDS.len()..];
            let close = list.find(']').unwrap_or(list.len());
            let axioms = list[..close]
                .split(',')
                .map(|axiom| axiom.trim().to_string())
                .filter(|axiom| !axiom.is_empty())
                .collect();
            (&after[..d], &list[close..], axioms)
        } else if let Some(n) = none {
            (&after[..n], &after[n + NONE.len()..], Vec::new())
        } else {
            break;
        };
        if name.chars().any(char::is_whitespace) {
            rest = after;
            continue;
        }
        result.insert(name.to_string(), axioms);
        rest = tail;
    }
    result
}

/// A token of Lean text: a name or a number as written, a doc comment, a
/// string literal that is not read alike as a plain and as an interpolated
/// string, or any other character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Name(String),
    Doc,
    Unread,
    Symbol(char),
}

/// The tokens of the Lean `text` with their lines. White space, comments,
/// and string, raw string and character literals are skipped, but the `{}`
/// parts of a string, which an interpolated string reads as code, are not.
pub fn tokens(text: &str) -> Vec<(usize, Token)> {
    let (chars, mut tokens) = (Vec::from_iter(text.chars()), Vec::new());
    scan(&chars, 0, false, &mut tokens);
    tokens.sort_by_key(|(start, _)| *start);
    let (mut line, mut counted) = (1, 0);
    let mut line_of = |start: usize| {
        line += chars[counted..start].iter().filter(|c| **c == '\n').count();
        counted = start;
        line
    };
    let lined = tokens.into_iter().map(|(at, token)| (line_of(at), token));
    lined.collect()
}

/// Reads the tokens of `chars` from `at`, each with its start, into
/// `tokens`, to the end or, in a `{}` part of a string (`braced`), to the
/// `}` that ends it, and returns where it stopped.
fn scan(chars: &[char], mut at: usize, braced: bool, tokens: &mut Vec<(usize, Token)>) -> usize {
    // Moves `at` past the next `end`, and in a literal past escapes.
    let ends = |at: &mut usize, end: char| {
        while chars.get(*at).is_some_and(|c| *c != end) {
            *at += 1 + usize::from(chars[*at] == '\\' && "\"'".contains(end));
        }
        *at += 1;
    };
    // The `#`s of a raw string literal `r#..."...` from `at`, after the `r`.
    let raw = |at: usize| {
        let hashes = chars[at..].iter().take_while(|c| **c == '#').count();
        (chars.get(at + hashes) == Some(&'"')).then_some(hashes)
    };
    let mut depth = 0;
    while let Some(&c) = chars.get(at) {
        let (start, next) = (at, chars.get(at + 1).copied());
        at += 1;
        match (c, next) {
            ('-', Some('-')) => ends(&mut at, '\n'),
            ('/', Some('-')) => {
                let (mut depth, doc) = (1, matches!(chars.get(at + 1), Some('-' | '!')));
                at += 1 + usize::from(doc);
                while depth > 0 && at < chars.len() {
                    match (chars[at], chars.get(at + 1)) {
                        ('/', Some('-')) => (depth, at) = (depth + 1, at + 2),
                        ('-', Some('/')) => (depth, at) = (depth - 1, at + 2),
                        _ => at += 1,
                    }
                }
                tokens.extend(doc.then_some((start, Token::Doc)));
            }
            // A string as a plain one, and with each `{}` part read as code.
            ('"', _) => {
                let mut plain = at;
                ends(&mut plain, '"');
                while let Some(&c) = chars.get(at).filter(|c| **c != '"') {
                    let after = at + 1 + usize::from(c == '\\');
                    let braced = (c == '{').then(|| scan(chars, at + 1, true, tokens));
                    at = braced.unwrap_or(after);
                }
                tokens.extend((at + 1 != plain).then_some((start, Token::Unread)));
                at = plain.min(at + 1);
            }
            ('r', _) if raw(at).is_some() => {
                let close = format!("\"{}", "#".repeat(raw(at).unwrap_or(0)));
                let close = Vec::from_iter(close.chars());
                let to = (at + close.len()..=chars.len()).find(|i| chars[*i..].starts_with(&close));
                at = to.map_or(chars.len(), |to| to + close.len());
            }
            ('\'', Some(n)) if n == '\\' || chars.get(at + 1) == Some(&'\'') => ends(&mut at, '\''),
            ('{', _) => depth += 1,
            ('}', _) if braced && depth == 0 => return at,
            ('}', _) => depth -= usize::from(depth > 0),
            _ if c == '«' || c == '_' || c.is_alphanumeric() => {
                at = start;
                let name = |c: &&char| c.is_alphanumeric() || "_'!?.«".contains(**c);
                while let Some(c) = chars.get(at).filter(name) {
                    at += 1;
                    if *c == '«' {
                        ends(&mut at, '»');
                    }
                }
                tokens.push((start, Token::Name(chars[start..at].iter().collect())));
            }
            _ if c.is_whitespace() => {}
            _ => tokens.push((start, Token::Symbol(c))),
        }
    }
    at
}

/// The problems of the source rules in the hand-written Lean file `path`
/// with `text`: outside `Krepi/` and `externals/`, not a module file, a
/// native decision that no item of `tcb` trusts, `axiom` outside
/// `externals/`, and on the statement side an import of the root or a proof.
pub fn source_problems(path: &str, text: &str, tcb: &[Item], layout: &Layout) -> Vec<String> {
    let own = format!("{}/{}", layout.project, layout.namespace);
    let below = |dir: &str| path.starts_with(&format!("{dir}/"));
    if !below(&own) && !below(layout.externals) {
        let outside = format!("outside {own}/ and {}/", layout.externals);
        return vec![format!("{path} is a Lean file {outside}")];
    }
    let trusted = |item: &Item| matches!(item, Item::NativeDecision { file, .. } if file == path);
    let (native, tokens) = (!tcb.iter().any(trusted), tokens(text));
    // The option `native` of `decide`, in any of its forms, such as
    // `+native` or `(native := true)`, is reported at the `decide` before it.
    let (mut problems, mut decide) = (Vec::new(), None);
    for (line, token) in &tokens {
        let word = match token {
            Token::Name(name) => name.as_str(),
            _ => "",
        };
        let (line, found) = match (token, word) {
            (Token::Unread, _) => (line, "a string that reads otherwise as interpolated"),
            (_, "axiom") if !below(layout.externals) => (line, word),
            (_, "native_decide" | "bv_decide") if native => (line, word),
            (_, "native" | "«native»") if native => (decide.unwrap_or(line), "decide +native"),
            (_, "decide") => {
                decide = Some(line);
                continue;
            }
            _ => continue,
        };
        problems.push(format!("{path}:{line}: {found}"));
    }
    let (module, imports) = guard::header_imports(&tokens);
    let header = format!("{path} is not a module file: its header has no `module`");
    problems.extend((!module).then_some(header));
    if guard::statement_side(path, layout) {
        let forbidden = guard::forbidden_imports(&imports, layout).into_iter();
        problems.extend(forbidden.map(|import| format!("{path} imports {import}")));
    }
    problems
}

/// Reads the JSON `text` of a registry into `T`, whose `schema` must be 1.
pub fn registry<T: DeserializeOwned>(text: &str, schema: fn(&T) -> u32) -> Result<T, String> {
    let read: T = serde_json::from_str(text).map_err(|error| error.to_string())?;
    let found = schema(&read);
    let read = (found == 1).then_some(read);
    read.ok_or(format!("schema {found} where 1 is expected"))
}

/// `verification/axioms.json`: the library axioms that targets may use.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Axioms {
    schema: u32,
    axioms: Vec<LibraryAxiom>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
#[expect(dead_code, reason = "the source and the reason are for the review")]
struct LibraryAxiom {
    name: String,
    source: String,
    reason: String,
}

/// The names in `verification/axioms.json`, `text`, which refuses the axiom
/// of a native decision: only an item of `verification/tcb.json` trusts it.
pub fn load_axioms(text: &str) -> Result<BTreeSet<String>, String> {
    let file: Axioms = registry(text, |file: &Axioms| file.schema)?;
    let names = BTreeSet::from_iter(file.axioms.into_iter().map(|axiom| axiom.name));
    let native = names.iter().find(|name| is_native(name));
    let native = native.map(|name| format!("{name} is the axiom of a native decision"));
    native.map_or(Ok(names.clone()), Err)
}

/// `verification/tcb.json`: the items of the trusted base.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Tcb {
    schema: u32,
    items: Vec<Item>,
}

/// An item of `verification/tcb.json`, by its `kind`, with its reason.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Item {
    /// The native decisions of `declaration`, in the hand-written `file`.
    NativeDecision {
        file: String,
        declaration: String,
        reason: String,
    },
    /// The axioms below `prefix` that a generated or external file declares.
    AxiomPattern { prefix: String, reason: String },
}

/// The items of `verification/tcb.json`, `text`.
pub fn load_tcb(text: &str) -> Result<Vec<Item>, String> {
    registry(text, |file: &Tcb| file.schema).map(|file| file.items)
}

/// Whether `axiom` is that of a native decision: Lean 4.35.0 adds one for
/// each, `<declaration>._native.<tactic>.ax_<i>_<j>`, private in a module.
pub fn is_native(axiom: &str) -> bool {
    axiom.split('.').any(|component| component == "_native")
}

/// The kind of an audited theorem: specification, qualification or target.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize, serde::Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Kind {
    Specification,
    Qualification,
    #[default]
    Target,
}

/// The allowlist, which every audit reads through [`allows`]: for each kind,
/// in order, which of the [`Sources`] admit an axiom besides the standard
/// ones: the case, `axioms.json`, `native-decision` and `axiom-pattern` items.
pub const KINDS: [(Kind, [bool; 4]); 3] = [
    (Kind::Specification, [false, false, false, false]),
    (Kind::Qualification, [true, false, false, false]),
    (Kind::Target, [false, true, true, true]),
];

/// The axioms of the case, the registries, the stage's declarations, and
/// the module that declares each native-decision axiom that the audit saw.
#[derive(Debug, Clone, Default)]
pub struct Sources {
    pub case: Vec<String>,
    pub registry: BTreeSet<String>,
    pub tcb: Vec<Item>,
    pub declared: BTreeSet<String>,
    pub native: BTreeMap<String, String>,
}

/// Whether a theorem of `kind` may depend on `axiom` with `sources`. Only a
/// `native-decision` item admits the axiom of a native decision, of its
/// declaration and declared in the module of its file.
pub fn allows(kind: Kind, axiom: &str, sources: &Sources) -> bool {
    let below = |name: &str, prefix: &str| {
        let rest = name.strip_prefix(prefix);
        rest.is_some_and(|rest| rest.is_empty() || rest.starts_with('.'))
    };
    // The axiom without the prefix `_private.<module>.0.` of a private name.
    let private = axiom.strip_prefix("_private.").unwrap_or_default();
    let public = private.split_once(".0.").map_or(axiom, |(_, name)| name);
    let native = is_native(axiom);
    let module = (sources.native.get(axiom)).map(|module| format!("/{}", module_file(module)));
    let declared_in = |file: &str| module.as_ref().is_some_and(|module| file.ends_with(module));
    let item = |item: &Item| match item {
        Item::NativeDecision { file: f, .. } if !declared_in(f) => false,
        Item::NativeDecision { declaration: d, .. } => below(public, &format!("{d}._native")),
        Item::AxiomPattern { prefix: p, .. } => !native && below(axiom, p),
    };
    let declared = sources.declared.contains(axiom);
    let admitted = [
        !native && sources.case.iter().any(|name| name == axiom),
        !native && sources.registry.contains(axiom),
        native && sources.tcb.iter().any(item),
        !native && declared && sources.tcb.iter().any(item),
    ];
    let (_, row) = KINDS[kind as usize];
    STANDARD_AXIOMS.contains(&axiom) || row.iter().zip(admitted).any(|(on, ok)| *on && ok)
}

/// The root module of a stage, which imports `modules`, every module below
/// the two namespaces in the stage.
pub fn root_source(modules: &BTreeSet<String>) -> String {
    let imports = modules.iter().map(|m| format!("public import {m}\n"));
    format!("module\n\n{}", imports.collect::<String>())
}

/// The line of the audit file at which the first `example` lies.
pub const FIRST_EXAMPLE: usize = 4;

/// The audit program, with names for `PLANNED` and `OWN` and pairs for
/// `STATEMENTS`: in each own module, a marker, the axioms of each theorem but
/// private, internal and planned ones, with the module of each native one,
/// and the line where each declaration range starts; then for each proved
/// statement its module, and whether its theorem has exactly its type.
const AUDIT_PROGRAM: &str = "open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf : Name → Name := fun n =>
    ((env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)).getD .anonymous
  let planned : Array Name := #[PLANNED]
  let own : Array Name := #[OWN]
  for (module, data) in env.header.moduleNames.zip env.header.moduleData do
    unless own.contains module do continue
    logInfo m!\"krepi-audit module {module}\"
    for decl in data.constNames do
      let some (.thmInfo _) := env.find? decl | continue
      unless isPrivateName decl || decl.isInternalDetail || planned.contains decl do
        elabCommand (← `(#print axioms $(mkIdent decl)))
        for ax in ← collectAxioms decl do
          if ax.components.contains `_native then
            logInfo m!\"krepi-audit native {ax} {moduleOf ax}\"
      if let some ranges ← findDeclarationRanges? decl then
        logInfo m!\"krepi-audit range {decl} {ranges.range.pos.line}\"
  for (statement, thm) in (#[STATEMENTS] : Array (Name × Name)) do
    let exact := (env.find? thm).any fun c => c.isTheorem && c.type == mkConst statement
    logInfo m!\"krepi-audit statement {statement} {moduleOf statement} {exact}\"
";

/// The audit file, not a module: it imports `root`, checks the type of each
/// proved statement's theorem, and audits `own` modules but planned theorems.
pub fn audit_source(root: &str, statements: &[Statement], own: &[String]) -> String {
    let quoted = |names: &mut dyn Iterator<Item = &String>| {
        let names: Vec<String> = names.map(|name| format!("`{name}")).collect();
        names.join(", ")
    };
    let (mut examples, mut planned, mut proved) = (String::new(), Vec::new(), Vec::new());
    for s in statements {
        let (name, theorem) = (&s.name, &s.theorem);
        match s.state {
            State::Proved => examples += &format!("example : {name} := {theorem}\n"),
            State::Planned => planned.push(theorem),
        }
        let pair = format!("(`{name}, `{theorem})");
        proved.extend((s.state == State::Proved).then_some(pair));
    }
    let program = AUDIT_PROGRAM.replace("PLANNED", &quoted(&mut planned.into_iter()));
    let program = program.replace("OWN", &quoted(&mut own.iter()));
    let program = program.replace("STATEMENTS", &proved.join(", "));
    format!("import {root}\nset_option pp.privateNames true\n\n{examples}\n{program}")
}

/// What the audit printed: module markers, each theorem's module and axioms,
/// its range line, the module of each native-decision axiom, each statement's
/// module and whether its theorem has exactly its type, and errors by line.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Audit {
    pub modules: BTreeSet<String>,
    pub theorems: BTreeMap<String, (String, Vec<String>)>,
    pub ranges: BTreeMap<String, (String, usize)>,
    pub native: BTreeMap<String, String>,
    pub statements: BTreeMap<String, (Option<String>, bool)>,
    pub errors: BTreeMap<usize, Vec<String>>,
}

/// Reads the output of `lake env lean` on the file of [`audit_source`]: its
/// markers, the axioms that each module part reports, and the errors.
pub fn audit_output(output: &str) -> Audit {
    let (mut audit, mut module) = (Audit::default(), String::new());
    let mut parts: BTreeMap<String, String> = BTreeMap::new();
    for line in output.lines() {
        let (_, marker) = line.split_once("krepi-audit ").unwrap_or_default();
        let fields = line.strip_prefix(AUDIT).unwrap_or_default();
        let fields: Vec<&str> = fields.splitn(4, ':').collect();
        let error = fields.get(3).is_some_and(|rest| rest.starts_with(" error"));
        let number = fields.get(1).filter(|_| error).and_then(|n| n.parse().ok());
        match (marker.split_once(' '), number) {
            (Some(("module", name)), _) => {
                module = name.to_string();
                audit.modules.insert(module.clone());
            }
            (Some(("range", rest)), _) => {
                let (name, number) = rest.rsplit_once(' ').unwrap_or_default();
                if let Ok(number) = number.parse() {
                    audit.ranges.insert(name.into(), (module.clone(), number));
                }
            }
            (Some(("native", rest)), _) => {
                let (name, found) = rest.split_once(' ').unwrap_or_default();
                audit.native.insert(name.to_string(), found.to_string());
            }
            (Some(("statement", rest)), _) => {
                let (name, rest) = rest.split_once(' ').unwrap_or((rest, ""));
                let (found, exact) = rest.split_once(' ').unwrap_or((rest, ""));
                let found = (found != "[anonymous]").then(|| found.to_string());
                let statement = (found, exact == "true");
                audit.statements.insert(name.to_string(), statement);
            }
            (_, Some(number)) => audit.errors.entry(number).or_default().push(line.into()),
            _ => *parts.entry(module.clone()).or_default() += &format!("{line}\n"),
        }
    }
    for (module, part) in parts.into_iter().filter(|(module, _)| !module.is_empty()) {
        for (name, axioms) in parse_axioms(&part) {
            audit.theorems.insert(name, (module.clone(), axioms));
        }
    }
    audit
}

/// Why the `theorems` of a target do not pass its audit `audit`: each must
/// be reported in one of its proof `modules` and use only axioms that the
/// allowlist admits for a target with `sources`, and the audit file has no
/// error.
pub fn target_problems(
    audit: &Audit,
    theorems: &[&String],
    modules: &[String],
    sources: &Sources,
) -> Vec<String> {
    let mut problems = Vec::from_iter(audit.errors.values().flatten().cloned());
    for theorem in theorems {
        match (audit.theorems.get(*theorem)).filter(|(module, _)| modules.contains(module)) {
            None => problems.push(format!(
                "the audit did not report {theorem} in a proof module"
            )),
            Some((_, axioms)) => {
                let rejected = axioms
                    .iter()
                    .filter(|axiom| !allows(Kind::Target, axiom, sources));
                problems.extend(rejected.map(|axiom| format!("{theorem} depends on {axiom}")));
            }
        }
    }
    problems
}

/// Why the output of `leanchecker`, `ran`, is not what it writes: an exit other
/// than 0 must report a module and a kernel problem not about a resource.
pub fn leanchecker_read(ran: &Ran) -> Result<(), String> {
    const RESOURCES: &str = "deterministic timeout,excessive memory,deep recursion,interrupted";
    let lines = || ran.output.lines();
    let module = lines().any(|line| line.starts_with("leanchecker found a problem in "));
    let resource = |text: &str| RESOURCES.split(',').any(|it| text.starts_with(it));
    let mut kernel = lines().filter_map(|line| line.split_once("(kernel) "));
    let report = module && kernel.any(|(_, text)| !resource(text));
    match ran.code() {
        Some(c) if c != 0 && !report => Err("it reported no kernel problem in a module".into()),
        _ => Ok(()),
    }
}

/// The version that `lean --version`, `ran`, printed: its line that starts
/// with `Lean (version `, when it exited with 0.
pub fn lean_version(ran: &Ran) -> Result<String, String> {
    let line = ran.output.lines().find(|l| l.starts_with("Lean (version "));
    let line = line.filter(|_| ran.code() == Some(0)).map(str::to_string);
    line.ok_or_else(|| "it did not print the version of Lean".to_string())
}

/// Mathlib's command that counts the heartbeats of the next command.
const COUNT: &str = "#count_heartbeats in";

/// The copy of `text` with [`COUNT`] before each line `at` which a theorem's
/// declaration range starts with a doc comment, an attribute, a modifier or
/// `theorem`, and the theorem of each inserted line; others are left out.
pub fn heartbeat_copy(text: &str, at: &[(String, usize)]) -> (String, BTreeMap<usize, String>) {
    const DECLARATION: &str = "theorem lemma public private protected nonrec";
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let mut starts = BTreeMap::new();
    for (theorem, line) in at {
        let text = lines.get(line.wrapping_sub(1)).copied().unwrap_or_default();
        let begins = match tokens(text).into_iter().next().map(|(_, token)| token) {
            Some(Token::Name(word)) => DECLARATION.split(' ').any(|start| start == word),
            first => matches!(first, Some(Token::Doc | Token::Symbol('@'))),
        };
        if begins {
            starts.entry(*line).or_insert_with(|| theorem.clone());
        }
    }
    let (mut copy, mut inserted) = (String::new(), BTreeMap::new());
    for (index, line) in lines.iter().enumerate() {
        if let Some(theorem) = starts.remove(&(index + 1)) {
            inserted.insert(index + 1 + inserted.len(), theorem);
            copy.push_str(&format!("{COUNT}\n"));
        }
        copy.push_str(line);
    }
    (copy, inserted)
}

/// The counts, in units of `maxHeartbeats`, that `lake env lean --json` gave
/// at the inserted lines of a copy of [`heartbeat_copy`], by theorem.
pub fn heartbeats(output: &str, inserted: &BTreeMap<usize, String>) -> BTreeMap<String, u64> {
    let count = |message: serde_json::Value| {
        let data = message["data"].as_str()?.strip_prefix("Used ")?;
        let (count, rest) = data.split_once(" heartbeats, which is ")?;
        let (relation, maximum) = rest.split_once(" than the current maximum of ")?;
        maximum.strip_suffix('.')?.parse::<u64>().ok()?;
        let information = message["severity"] == "information";
        let read = information && ["less", "greater"].contains(&relation);
        let line = usize::try_from(message["pos"]["line"].as_u64()?).ok()?;
        let theorem = inserted.get(&line).filter(|_| read)?;
        Some((theorem.clone(), count.parse().ok()?))
    };
    let messages = output.lines().filter_map(|l| serde_json::from_str(l).ok());
    messages.filter_map(count).collect()
}

/// The mode, size, modification and change times, and link target by path.
pub type Listing = BTreeMap<PathBuf, (u32, u64, [[i64; 2]; 2], Option<PathBuf>)>;

/// The listing of `roots`, parts of the tool installation that no command
/// may write: each entry below each root, without following links below it.
/// With the listing `before`, it fails, naming up to 20 paths, if they differ.
pub fn listing(roots: &[PathBuf], before: Option<&Listing>) -> Result<Listing, String> {
    let mut listing = Listing::new();
    for root in roots {
        let at = |error: std::io::Error| format!("{}: {error}", root.display());
        for entry in WalkDir::new(fs::canonicalize(root).map_err(at)?) {
            let entry = entry.map_err(|error| format!("cannot list the installation: {error}"))?;
            let data = entry.metadata().map_err(|error| error.to_string())?;
            let link = entry.path_is_symlink().then(|| fs::read_link(entry.path()));
            let modified = [data.mtime(), data.mtime_nsec()];
            let times = [modified, [data.ctime(), data.ctime_nsec()]];
            let link = link.transpose().map_err(|error| error.to_string())?;
            listing.insert(entry.into_path(), (data.mode(), data.size(), times, link));
        }
    }
    let before = before.unwrap_or(&listing);
    let mut paths = Vec::from_iter(BTreeSet::from_iter(before.keys().chain(listing.keys())));
    paths.retain(|p| before.get(*p) != listing.get(*p));
    let (count, shown) = (paths.len(), &paths[..paths.len().min(20)]);
    let error = format!("the tool installation changed during the phase; changed paths ({count})");
    let error = format!("{error}: {shown:?}");
    let listing = (count == 0).then_some(listing);
    listing.ok_or(error)
}

#[cfg(test)]
mod tests {
    //! The texts of `fixtures/base/` are what the pinned Lean 4.35.0 printed
    //! on `darwin-arm64` in the environment of the gate, in stages laid out
    //! as the base round lays them out: the qualification proofs with the
    //! generated modules of their cases, and, in the stage `counter`, the
    //! files of `fixtures/base/counter/` besides. The first line of each
    //! names the command; absolute paths are replaced.

    use std::time::Duration;

    use super::*;
    use crate::check::lean_problems;
    use crate::formal::process::{Ended, Limit, LimitBy};
    use crate::repo::{self, Entry, Tree};
    use crate::scratch::Scratch;

    fn modules(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| name.to_string()).collect()
    }

    /// A captured text without its first line, which names the command.
    fn captured(text: &str) -> &str {
        text.split_once('\n').expect("a header line").1
    }

    /// A command that ended by itself with `code` and printed `output`.
    fn ran(code: i32, output: &str) -> Ran {
        Ran {
            name: "tool".to_string(),
            group: None,
            ended: Ended::Exited(code),
            limit: Limit {
                duration: Duration::from_secs(1),
                by: LimitBy::Cap,
            },
            seconds: Duration::ZERO,
            stdout: None,
            stderr: None,
            output: output.to_string(),
            survivors: false,
        }
    }

    /// The problems of the source rules in the one file `path` with `text`.
    fn scanned(path: &str, text: &str, tcb: &str) -> Vec<String> {
        let tcb = if tcb.is_empty() {
            "{\"schema\": 1, \"items\": []}"
        } else {
            tcb
        };
        let files = [(path, text), ("verification/tcb.json", tcb)];
        lean_problems(&Tree::from_files(&files), &Layout::PRODUCTION)
    }

    #[test]
    fn a_lean_file_or_trusted_base_that_cannot_be_read_fails_the_scan() {
        let mut tree = Tree::from_files(&[("verification/Krepi/Spec/A.lean", "module\n")]);
        let unread = "it is not a tracked UTF-8 regular file";
        let problems = lean_problems(&tree, &Layout::PRODUCTION);
        assert_eq!(problems, [format!("verification/tcb.json: {unread}")]);
        tree.insert(
            "verification/tcb.json",
            Entry::File(b"{\"schema\": 1, \"items\": []}".to_vec()),
        );
        tree.insert("verification/Krepi/Spec/B.lean", Entry::File(vec![0xff]));
        tree.insert(
            "verification/Krepi/Spec/C.lean",
            Entry::Symlink("A.lean".to_string()),
        );
        let problems = lean_problems(&tree, &Layout::PRODUCTION);
        let path = |file: &str| format!("verification/Krepi/Spec/{file}.lean: {unread}");
        assert_eq!(problems, [path("B"), path("C")]);
    }

    #[test]
    fn axiom_lists_are_parsed_across_lines() {
        let output = "'A.b' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'C' does not depend on any axioms\n'D.e' depends on axioms: [sorryAx]\n";
        let parsed = parse_axioms(output);
        assert_eq!(parsed["A.b"], ["propext", "Classical.choice", "Quot.sound"]);
        assert!(parsed["C"].is_empty());
        assert_eq!(parsed["D.e"], ["sorryAx"]);
    }

    #[test]
    fn primed_names_are_parsed() {
        let output = "'A.zero_le'' depends on axioms: [propext]\n'B.x'' does not depend on any axioms\n'C.y' depends on axioms: [Quot.sound]\n";
        let parsed = parse_axioms(output);
        assert_eq!(parsed["A.zero_le'"], ["propext"]);
        assert!(parsed["B.x'"].is_empty());
        assert_eq!(parsed["C.y"], ["Quot.sound"]);
        assert_eq!(parsed.len(), 3);
    }

    #[test]
    fn the_messages_of_the_proofs_are_found_anywhere_in_a_log() {
        let proofs = modules(&["Krepi.Proofs.Base", "Krepi.Proofs.Main"]);
        let output = "✖ [2/8] Building KrepiGen.M.Types (234ms)\n\
            error: KrepiGen/M/Types.lean:5:31: Type mismatch\n\
            ✖ [8/8] Building Krepi.Proofs.Main (195ms)\n\
            error: ./Krepi/Proofs/Main.lean:1:0: unexpected token 'import'; expected command\n\
            info: Krepi/Proofs/Main.lean:3:0: 4\n\
            warning: Krepi/Proofs/Base.lean:8:8: declaration uses `sorry`\n\
            error: Krepi/Proofs/Main.lean: bad import 'Krepi.Spec.Missing'\n\
            error: Krepi/Proofs/Base.lean:12:4: unsolved goals\n\
            error: Lean exited with code 1\n\
            error: build failed\n";
        assert_eq!(
            proof_messages(output, &proofs),
            [
                ("Krepi.Proofs.Main", 1, 0),
                ("Krepi.Proofs.Base", 8, 8),
                ("Krepi.Proofs.Base", 12, 4)
            ]
        );
    }

    #[test]
    fn own_messages_of_a_captured_log_are_counted() {
        // An error in a proof, a warning in a statement file and an error in
        // a generated file; the replayed and failed jobs print the absolute
        // path of each file only in their `trace:` lines.
        let output = captured(include_str!("fixtures/base/build.txt"));
        let own = modules(&[
            "Krepi.Proofs.Main",
            "Krepi.Qualification.Arithmetic",
            "Krepi.Qualification.Checked",
            "Krepi.Qualification.Models.Arc",
            "Krepi.Qualification.Models.FromStr",
            "Krepi.Qualification.SingleLoop",
            "Krepi.Statements.Warn",
        ]);
        assert_eq!(
            proof_messages(output, &own),
            [
                ("Krepi.Proofs.Main", 6, 8),
                ("Krepi.Statements.Warn", 5, 21)
            ]
        );
        assert!(output.contains("error: KrepiGen/Qual/Checked/Funs.lean:47:17: Type mismatch"));
    }

    #[test]
    fn only_the_sorry_warning_of_a_planned_file_is_allowed() {
        // The forms that Lean 4.35.0 printed for a planned file.
        let sorry = "warning: Krepi/Proofs/Other.lean:12:15: declaration uses `sorry`\n";
        let other = "warning: Krepi/Proofs/Other.lean:10:26: Variable name `h` is not explicitly referenced.\n\
            \n\
            Hint: The binding can be removed (if unused) or named `_` (if used implicitly).\n\
            Note: This linter can be disabled with `set_option linter.unusedVariables false`\n";
        let planned = modules(&["Krepi/Proofs/Other.lean"]);
        let log = format!(
            "⚠ [1806/1806] Built Krepi.Proofs.Other (4.4s)\n{sorry}Build completed successfully (1806 jobs).\n"
        );
        assert!(planned_problems(&log, &planned).is_empty());
        assert_eq!(
            planned_problems(&format!("{other}{sorry}"), &planned),
            [
                "warning: Krepi/Proofs/Other.lean:10:26: Variable name `h` is not explicitly referenced."
            ]
        );
        // The same warning in a file that is not planned, an error and a
        // message without a position are problems too.
        for line in [
            "warning: Krepi/Proofs/Main.lean:12:15: declaration uses `sorry`",
            "error: Krepi/Proofs/Other.lean:12:15: declaration uses `sorry`",
            "warning: Krepi/Proofs/Other.lean:12:15: declaration uses `sorry` twice",
            "error: build failed",
        ] {
            assert_eq!(planned_problems(line, &planned), [line], "{line}");
        }
    }

    #[test]
    fn a_stage_holds_the_project_files_and_links_the_installation() {
        let scratch = Scratch::new("stage");
        let project = scratch.0.join("export/verification");
        for file in PROJECT_FILES {
            scratch.write(&format!("export/verification/{file}"), file);
        }
        scratch.write("export/verification/Krepi/Proof.lean", "");
        let backend = scratch.0.join("tools/backend");
        let stage = scratch.0.join("stage");
        let staged = create_stage(&project, &project, &stage, &backend).expect("a new stage");
        assert_eq!(staged, stage.join("verification"));
        for file in PROJECT_FILES {
            assert_eq!(
                fs::read_to_string(staged.join(file)).expect("a project file"),
                file
            );
        }
        // Only the project files are copied.
        assert!(!staged.join("Krepi").exists());
        let link = |name: &str| fs::read_link(stage.join(LINKS).join(name)).expect("a link");
        assert_eq!(link("aeneas"), backend);
        assert_eq!(link("packages"), backend.join(".lake/packages"));
        // A stage is new.
        let error = create_stage(&project, &project, &stage, &backend).expect_err("a used stage");
        assert!(error.starts_with("cannot create the stage "), "{error}");
        copy_into(&project, &staged, "Krepi/Proof.lean").expect("copy a module");
        assert!(staged.join("Krepi/Proof.lean").is_file());
    }

    #[test]
    fn a_stage_of_the_calibration_takes_the_toolchain_and_the_lock_of_production() {
        // The calibration project has its own Lake configuration and takes
        // the Lean toolchain and the Lake lock of the production project, the
        // lock with the name of the calibration project.
        let scratch = Scratch::new("calibration-stage");
        let layout = Layout::CALIBRATION;
        let export = scratch.0.join("export");
        let lakefile =
            include_str!("../../../verification/qualification/calibration/lakefile.toml");
        scratch.write(
            &format!("export/{}/lakefile.toml", layout.project),
            lakefile,
        );
        for file in &PROJECT_FILES[1..] {
            assert!(
                !repo::root().join(layout.project).join(file).exists(),
                "{file}"
            );
            let text = fs::read_to_string(repo::root().join(layout.root_project).join(file));
            let path = format!("export/{}/{file}", layout.root_project);
            scratch.write(&path, &text.expect("a project file of production"));
        }
        let (project, pins) = (
            export.join(layout.project),
            export.join(layout.root_project),
        );
        let backend = scratch.0.join("tools/backend");
        let stage = scratch.0.join("stage");
        let staged = create_stage(&project, &pins, &stage, &backend).expect("a new stage");
        assert_eq!(staged, stage.join("calibration"));
        let read = |path: &Path| fs::read_to_string(path).expect("a project file");
        assert_eq!(read(&staged.join(PROJECT_FILES[0])), lakefile);
        assert_eq!(
            read(&staged.join("lean-toolchain")),
            read(&pins.join("lean-toolchain"))
        );
        let lock = |path: &Path| -> serde_json::Value {
            serde_json::from_str(&read(&path.join("lake-manifest.json"))).expect("a lock")
        };
        let (mut production, calibration) = (lock(&pins), lock(&staged));
        assert_eq!(production["name"], "krepiVerification");
        assert_eq!(calibration["name"], "krepiCalibration");
        production["name"] = "krepiCalibration".into();
        assert_eq!(calibration, production);
        let link = |name: &str| fs::read_link(stage.join(LINKS).join(name)).expect("a link");
        assert_eq!(link("aeneas"), backend);
    }

    #[test]
    fn the_lake_commands_have_their_arguments() {
        assert_eq!(
            build_args(&["KrepiGen.Qual.F.Funs"], true),
            ["build", "--no-cache", "--wfail", "KrepiGen.Qual.F.Funs"]
        );
        assert_eq!(
            build_args(&["+A", "+B"], false),
            ["build", "--no-cache", "+A", "+B"]
        );
        assert_eq!(check_args("Audit.lean"), ["env", "lean", "Audit.lean"]);
        assert_eq!(
            module_file("Krepi.Qualification.F"),
            "Krepi/Qualification/F.lean"
        );
        assert_eq!(
            errors(
                "✖ [2/2] Building X\nerror: X.lean:1:0: bad\n  warning: no\n error: build failed\n"
            ),
            ["error: X.lean:1:0: bad", "error: build failed"]
        );
    }

    #[test]
    fn the_tokens_of_lean_text_skip_comments_and_strings() {
        let text = "module -- a comment\n\
            /- a /- nested -/ block axiom -/ def\n\
            /-- a doc /- nested -/ -/ /-! a module doc -/\n\
            \"a \\\"string\\\" axiom\" 'a' '\\'' '\\n' h' x.«y z».w get! find? α₁\n\
            Foo.bar+1";
        let found: Vec<(usize, Token)> = tokens(text);
        let name = |line, name: &str| (line, Token::Name(name.to_string()));
        assert_eq!(
            found,
            [
                name(1, "module"),
                name(2, "def"),
                (3, Token::Doc),
                (3, Token::Doc),
                name(4, "h'"),
                name(4, "x.«y z».w"),
                name(4, "get!"),
                name(4, "find?"),
                name(4, "α₁"),
                name(5, "Foo.bar"),
                (5, Token::Symbol('+')),
                name(5, "1"),
            ]
        );
        // A raw string has no escapes, and ends at a quote with its `#`s;
        // the text of a doc comment starts after `/--`; a number is a name.
        let text = "r\"C:\\\" a r#\"x\"y\"# b /--/ c -/ d 0x1F";
        let doc = (1, Token::Doc);
        assert_eq!(
            tokens(text),
            [
                name(1, "a"),
                name(1, "b"),
                doc,
                name(1, "d"),
                name(1, "0x1F")
            ]
        );
        // The `{}` part of a string is read as code, as an interpolated
        // string reads it; a string that the two readings end apart is
        // reported, and read on as a plain one.
        assert_eq!(
            tokens("s!\"{x} y\" e"),
            [name(1, "s!"), name(1, "x"), name(1, "e")]
        );
        let unread = tokens("\"{\" axiom \"}\"");
        assert_eq!(unread, [(1, Token::Unread), name(1, "axiom")]);
        // A comment or a string that does not end runs to the end.
        assert_eq!(tokens("a /- b"), [name(1, "a")]);
        assert_eq!(tokens("a \"b"), [name(1, "a")]);
        // A line comment ends at its line, whatever it ends with.
        assert_eq!(tokens("-- a \\\nb"), [name(2, "b")]);
    }

    #[test]
    fn a_native_decision_in_a_handwritten_file_fails_the_scan() {
        let path = "verification/Krepi/Proofs/X.lean";
        let text = "module\n\
            \n\
            theorem a : 2 ^ 10 = 1024 := by native_decide\n\
            theorem b : 3 ^ 5 = 243 := by decide +native\n\
            theorem c : 3 ^ 5 = 243 := by decide  +native\n\
            theorem d : 3 ^ 5 = 243 := by\n  \
              decide\n    \
                +kernel +native\n\
            theorem e (x y : BitVec 8) : x &&& y = y &&& x := by bv_decide\n\
            theorem f : 3 ^ 5 = 243 := by decide +kernel\n\
            -- native_decide in a comment\n\
            /- bv_decide, decide +native -/\n\
            def s := \"decide +native native_decide\"\n\
            def native_decide_count := 1\n\
            theorem g : 3 ^ 5 = 243 := by decide (native := true)\n\
            theorem h : 3 ^ 5 = 243 := by decide -kernel +native\n\
            theorem i : 3 ^ 5 = 243 := by decide (config := { native := true })\n\
            def r := r\"C:\\\"\n\
            theorem j : 2 ^ 10 = 1024 := by native_decide\n\
            def u := s!\"{x}\"\n";
        let problems = |tcb: &str| scanned(path, text, tcb);
        assert_eq!(
            problems(""),
            [
                format!("{path}:3: native_decide"),
                format!("{path}:4: decide +native"),
                format!("{path}:5: decide +native"),
                format!("{path}:7: decide +native"),
                format!("{path}:9: bv_decide"),
                format!("{path}:15: decide +native"),
                format!("{path}:16: decide +native"),
                format!("{path}:17: decide +native"),
                format!("{path}:19: native_decide"),
            ]
        );
        // The file passes with an item of the trusted base for it, and only
        // for it.
        let item = |file: &str| {
            format!(
                "{{\"schema\": 1, \"items\": [{{\"kind\": \"native-decision\", \"file\": \"{file}\", \
                 \"declaration\": \"Krepi.Proofs.X.a\", \"reason\": \"r\"}}]}}"
            )
        };
        assert!(problems(&item(path)).is_empty());
        assert_eq!(problems(&item("verification/Krepi/Proofs/Y.lean")).len(), 9);
        // A string that an interpolated string would read on is reported,
        // and the code after it is still read.
        let text =
            "module\ndef v := \"{\" ++ \"}\"\ntheorem k : 2 ^ 10 = 1024 := by native_decide\n";
        let unread = format!("{path}:2: a string that reads otherwise as interpolated");
        assert_eq!(
            scanned(path, text, ""),
            [unread, format!("{path}:3: native_decide")]
        );
        // A trusted base that cannot be read fails the step.
        let error = problems("{\"schema\": 1, \"items\": [{\"kind\": \"other\"}]}");
        assert!(
            error[0].starts_with("verification/tcb.json: unknown variant `other`"),
            "{error:?}"
        );
    }

    #[test]
    fn a_handwritten_axiom_outside_the_externals_fails_the_scan() {
        let text = "module\n\
            \n\
            axiom x1 : False\n\
            public axiom x2 : False\n\
            @[simp] axiom x3 : False\n\
            axiom\n  x4 : False\n\
            open Foo in axiom x5 : False\n\
            set_option pp.all true in axiom x6 : False\n\
            /- c -/ axiom x7 : False\n\
            def y := 1 axiom x8 : False\n\
            -- axiom in a comment\n\
            /-- axiom in a doc comment -/\n\
            def s := \"axiom\"\n\
            def axiom_count := 1\n\
            def z := Foo.axiom\n\
            def «axiom» := 1\n\
            def r := r\"C:\\\"\n\
            axiom x9 : False\n\
            /--/ \" -/ axiom x10 : False -- \"\n";
        for path in [
            "verification/Krepi/Spec/A.lean",
            "verification/Krepi/Proofs/B.lean",
        ] {
            let lines = [3, 4, 5, 6, 8, 9, 10, 11, 19, 20];
            let expected: Vec<String> = (lines.iter())
                .map(|line| format!("{path}:{line}: axiom"))
                .collect();
            assert_eq!(scanned(path, text, ""), expected);
        }
        let externals = "verification/externals/Qual/X/FunsExternal.lean";
        assert!(scanned(externals, text, "").is_empty());
    }

    #[test]
    fn hand_written_lean_files_are_module_files_in_the_two_directories() {
        let problems = |path: &str, text: &str| scanned(path, text, "");
        assert_eq!(
            problems("verification/Krepi/Spec/A.lean", "import Krepi.Spec.B\n"),
            ["verification/Krepi/Spec/A.lean is not a module file: its header has no `module`"]
        );
        for path in [
            "verification/Krepi.lean",
            "verification/Other/Foo.lean",
            "verification/KrepiGen/Qual/A/Funs.lean",
        ] {
            assert_eq!(
                problems(path, "module\n"),
                [format!(
                    "{path} is a Lean file outside verification/Krepi/ and verification/externals/"
                )]
            );
        }
        // Lean files elsewhere in the repository are not hand-written Lean
        // of the project.
        assert!(problems("xtask/src/formal/fixtures/A.lean", "axiom a : False\n").is_empty());
        // The committed files keep the rules.
        let tree = Tree::load(&crate::repo::root()).expect("the repository is readable");
        assert_eq!(
            lean_problems(&tree, &Layout::PRODUCTION),
            Vec::<String>::new()
        );
    }

    #[test]
    fn native_decision_axioms_are_recognised_by_name() {
        // The forms that `#print axioms` printed for the native decisions
        // of a module file and of a file that is not a module, and the
        // library's own.
        for axiom in [
            "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_native_decide._native.native_decide.ax_1_1",
            "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_decide_native._native.decide.ax_1_1",
            "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_bv_decide._native.bv_decide.ax_1_5",
            "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.a_rather_long_theorem_name_to_force_the_axiom_list_to_wrap_across_lines'._native.bv_decide.ax_1_6",
            "nm_two._native.native_decide.ax_1_2",
            "_private.Aeneas.Tactic.Solver.BvTac.Lemmas.0.Aeneas.Std.U64.bv_mod_size._native.bv_decide.ax_1_5",
        ] {
            assert!(is_native(axiom), "{axiom}");
        }
        for axiom in [
            "Krepi.native.ax_1_1",
            "foo_native.decide",
            "Quot.sound",
            "sorryAx",
        ] {
            assert!(!is_native(axiom), "{axiom}");
        }
        // An item of the trusted base names the declaration; its private
        // axioms match without the private prefix, and only its own.
        let tcb = vec![Item::NativeDecision {
            file: "verification/Krepi/Proofs/Native.lean".to_string(),
            declaration: "Krepi.Proofs.Native.n_bv_decide".to_string(),
            reason: "measured".to_string(),
        }];
        // The axioms that the audit saw, each declared in that module.
        let mut sources = Sources {
            tcb,
            native: BTreeMap::from([
                "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_bv_decide._native.bv_decide.ax_1_5",
                "Krepi.Proofs.Native.n_bv_decide._native.native_decide.ax_1_1",
                "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_bv_decide2._native.bv_decide.ax_1_5",
                "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_native_decide._native.native_decide.ax_1_1",
            ].map(|axiom| (axiom.to_string(), "Krepi.Proofs.Native".to_string()))),
            ..Sources::default()
        };
        let allowed = |axiom: &str, sources: &Sources| allows(Kind::Target, axiom, sources);
        let private = "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_bv_decide._native.bv_decide.ax_1_5";
        assert!(allowed(private, &sources));
        assert!(allowed(
            "Krepi.Proofs.Native.n_bv_decide._native.native_decide.ax_1_1",
            &sources
        ));
        assert!(!allowed(
            "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_bv_decide2._native.bv_decide.ax_1_5",
            &sources
        ));
        assert!(!allowed(
            "_private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.n_native_decide._native.native_decide.ax_1_1",
            &sources
        ));
        // An axiom of the name that another module declares, or that the
        // audit did not place, is not the item's.
        sources
            .native
            .insert(private.to_string(), "Krepi.Proofs.Forged".to_string());
        assert!(!allowed(private, &sources));
        sources.native.remove(private);
        assert!(!allowed(private, &sources));
        // What the audit printed for a native decision, and for an axiom of
        // its name that another module adds without the kernel.
        let audit = audit_output(captured(include_str!("fixtures/base/audit/native.txt")));
        let tcb = vec![Item::NativeDecision {
            file: "verification/Krepi/Proofs/Native.lean".to_string(),
            declaration: "Krepi.Proofs.Native.n".to_string(),
            reason: "measured".to_string(),
        }];
        let sources = Sources {
            tcb,
            native: audit.native.clone(),
            ..Sources::default()
        };
        let judged = |theorem: &str| {
            let axioms = &audit.theorems[theorem].1;
            Vec::from_iter(axioms.iter().map(|axiom| allowed(axiom, &sources)))
        };
        assert_eq!(judged("Krepi.Proofs.Native.n"), [true]);
        assert_eq!(judged("Krepi.Proofs.Forged.f"), [false]);
        assert_eq!(
            audit.native["Krepi.Proofs.Native.n._native.native_decide.ax_9_9"],
            "Krepi.Proofs.Forged"
        );
        assert!(!allowed("Krepi.Proofs.Native.n_bv_decide.helper", &sources));
    }

    #[test]
    fn a_native_decision_axiom_cannot_be_registered_in_axioms_json() {
        let file = |name: &str| {
            format!(
                "{{\"schema\": 1, \"axioms\": [{{\"name\": \"{name}\", \"source\": \"Aeneas.Std.Slice\", \"reason\": \"r\"}}]}}"
            )
        };
        let library = "Aeneas.Std.core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec";
        assert_eq!(
            load_axioms(&file(library)),
            Ok(BTreeSet::from([library.to_string()]))
        );
        let native = "_private.Aeneas.Tactic.Solver.BvTac.Lemmas.0.Aeneas.Std.U8.bv_mod_size._native.bv_decide.ax_1_5";
        assert_eq!(
            load_axioms(&file(native)),
            Err(format!("{native} is the axiom of a native decision"))
        );
        assert_eq!(
            load_axioms("{\"schema\": 2, \"axioms\": []}"),
            Err("schema 2 where 1 is expected".to_string())
        );
        for text in [
            "{\"schema\": 1, \"axioms\": [{\"name\": \"a\", \"source\": \"b\"}]}",
            "{\"schema\": 1, \"axioms\": [], \"other\": 1}",
        ] {
            assert!(load_axioms(text).is_err(), "{text}");
        }
        assert!(load_tcb("{\"schema\": 1, \"items\": [{\"kind\": \"axiom-pattern\", \"prefix\": \"P\", \"reason\": \"r\", \"file\": \"f\"}]}").is_err());
    }

    #[test]
    fn the_allowlist_is_one_table_by_kind() {
        let sources = Sources {
            case: vec!["case.declared".to_string()],
            registry: BTreeSet::from(["Aeneas.Std.registered".to_string()]),
            tcb: vec![
                Item::NativeDecision {
                    file: "verification/Krepi/Proofs/N.lean".to_string(),
                    declaration: "Krepi.Proofs.N.n".to_string(),
                    reason: "r".to_string(),
                },
                Item::AxiomPattern {
                    prefix: "KrepiGen.Qual.Arithmetic".to_string(),
                    reason: "r".to_string(),
                },
            ],
            declared: BTreeSet::from([
                "KrepiGen.Qual.Arithmetic.f".to_string(),
                "KrepiGen.Qual.ArithmeticX.g".to_string(),
                "Aeneas.Std.registered._native.decide.ax_1_1".to_string(),
                "KrepiGen.Qual.Arithmetic.f._native.decide.ax_1_1".to_string(),
            ]),
            native: BTreeMap::from([
                ("Krepi.Proofs.N.n._native.decide.ax_1_1", "Krepi.Proofs.N"),
                (
                    "Krepi.Proofs.N.n._native.decide.ax_9_9",
                    "Krepi.Proofs.Forged",
                ),
                ("Aeneas.Std.registered._native.decide.ax_1_1", "Aeneas.Std"),
            ])
            .into_iter()
            .map(|(axiom, module)| (axiom.to_string(), module.to_string()))
            .collect(),
        };
        // Each source, and what each kind admits from it.
        let rows = [
            ("propext", [true, true, true]),
            ("Quot.sound", [true, true, true]),
            ("case.declared", [false, true, false]),
            ("Aeneas.Std.registered", [false, false, true]),
            (
                "Krepi.Proofs.N.n._native.decide.ax_1_1",
                [false, false, true],
            ),
            ("KrepiGen.Qual.Arithmetic.f", [false, false, true]),
            // A prefix matches whole components, of declared axioms only.
            ("KrepiGen.Qual.ArithmeticX.g", [false, false, false]),
            ("KrepiGen.Qual.Arithmetic.forged", [false, false, false]),
            // Only an item for its declaration admits a native decision,
            // declared in the module of the item's file.
            (
                "Krepi.Proofs.N.n._native.decide.ax_9_9",
                [false, false, false],
            ),
            (
                "Aeneas.Std.registered._native.decide.ax_1_1",
                [false, false, false],
            ),
            // No pattern admits one, even when a generated file declares it.
            (
                "KrepiGen.Qual.Arithmetic.f._native.decide.ax_1_1",
                [false, false, false],
            ),
            ("sorryAx", [false, false, false]),
        ];
        let kinds = [Kind::Specification, Kind::Qualification, Kind::Target];
        for (axiom, admitted) in rows {
            for (kind, admitted) in kinds.into_iter().zip(admitted) {
                assert_eq!(allows(kind, axiom, &sources), admitted, "{kind:?} {axiom}");
            }
        }
        assert_eq!(KINDS.map(|(kind, _)| kind), kinds);
        let native = Sources {
            case: vec!["x._native.decide.ax_1_1".to_string()],
            ..Sources::default()
        };
        assert!(!allows(
            Kind::Qualification,
            "x._native.decide.ax_1_1",
            &native
        ));
    }

    #[test]
    fn the_root_module_imports_every_module_below_both_namespaces() {
        let modules: BTreeSet<String> = [
            "KrepiGen.Qual.SingleLoop.Types",
            "Krepi.Statements.Counter",
            "KrepiGen.Qual.Arithmetic.Funs",
            "Krepi.Qualification.Models.FromStr",
            "Krepi.Proofs.Other",
            "Krepi.Qualification.Arithmetic",
            "KrepiGen.Qual.Checked.Funs",
            "Krepi.HB.Fixture",
            "Krepi.Spec.Counter",
            "KrepiGen.Qual.Checked.Types",
            "Krepi.Qualification.Models.Arc",
            "Krepi.Proofs.Counter",
            "KrepiGen.Qual.SingleLoop.Funs",
            "Krepi.Qualification.SingleLoop",
            "KrepiGen.Qual.Arithmetic.Types",
            "Krepi.Qualification.Checked",
        ]
        .map(str::to_string)
        .into();
        // The root that the stage `counter` built.
        assert_eq!(
            root_source(&modules),
            include_str!("fixtures/base/root.lean")
        );
        assert_eq!(
            root_source(&BTreeSet::from(["B".to_string(), "A.C".to_string()])),
            "module\n\npublic import A.C\npublic import B\n"
        );
    }

    #[test]
    fn the_audit_file_checks_each_statement_and_lists_the_theorems() {
        let qualification = [
            "Krepi.Qualification.Arithmetic",
            "Krepi.Qualification.Checked",
            "Krepi.Qualification.Models.Arc",
            "Krepi.Qualification.Models.FromStr",
            "Krepi.Qualification.SingleLoop",
        ];
        // The audit files that the two stages ran.
        assert_eq!(
            audit_source("Krepi", &[], &modules(&qualification)),
            include_str!("fixtures/base/audit/base.lean")
        );
        let statement = |name: &str, theorem: &str, state| Statement {
            name: name.to_string(),
            theorem: theorem.to_string(),
            module: "Krepi.Proofs.Counter".to_string(),
            state,
        };
        // A planned statement has no example, and its theorem is not
        // audited.
        let statements = [
            statement(
                "Krepi.Statements.Counter.S",
                "Krepi.Proofs.Counter.t",
                State::Proved,
            ),
            statement(
                "Krepi.Statements.Counter.Later",
                "Krepi.Proofs.Other.u",
                State::Planned,
            ),
            statement(
                "Krepi.Proofs.Other.P",
                "Krepi.Proofs.Other.v",
                State::Proved,
            ),
            statement(
                "Krepi.Statements.Counter.Missing",
                "Krepi.Proofs.Counter.s",
                State::Proved,
            ),
            statement(
                "Krepi.Statements.Counter.W",
                "Krepi.Proofs.Coerced.c",
                State::Proved,
            ),
        ];
        let mut own = modules(&[
            "Krepi.HB.Fixture",
            "Krepi.Proofs.Coerced",
            "Krepi.Proofs.Counter",
            "Krepi.Proofs.Other",
        ]);
        own.extend(modules(&qualification));
        own.extend(modules(&["Krepi.Spec.Counter", "Krepi.Statements.Counter"]));
        let source = audit_source("Krepi", &statements, &own);
        assert_eq!(source, include_str!("fixtures/base/audit/counter.lean"));
        let line = source.lines().nth(FIRST_EXAMPLE - 1);
        assert_eq!(
            line,
            Some("example : Krepi.Statements.Counter.S := Krepi.Proofs.Counter.t")
        );
    }

    #[test]
    fn the_audit_output_is_read_by_module() {
        let audit = audit_output(captured(include_str!("fixtures/base/audit/counter.txt")));
        assert_eq!(audit.modules.len(), 11);
        assert!(audit.modules.contains("Krepi.Spec.Counter"));
        let theorem = |name: &str| {
            audit
                .theorems
                .get(name)
                .map(|(module, axioms)| (module.as_str(), axioms.join(", ")))
        };
        assert_eq!(
            theorem("Krepi.Proofs.Counter.t"),
            Some(("Krepi.Proofs.Counter", "propext, Quot.sound".to_string()))
        );
        assert_eq!(
            theorem("Krepi.Proofs.Other.v"),
            Some(("Krepi.Proofs.Other", String::new()))
        );
        assert_eq!(
            theorem("alloc.sync.Arc.mk.injEq"),
            Some(("Krepi.Qualification.Models.Arc", "propext".to_string()))
        );
        assert_eq!(
            theorem("Aeneas.Std.U64.checked_add_bv_spec.match_1.congr_eq_1"),
            Some(("Krepi.Qualification.Checked", String::new()))
        );
        // Planned and private theorems are not audited; the private one has
        // its range.
        assert_eq!(theorem("Krepi.Proofs.Other.u"), None);
        assert_eq!(audit.theorems.len(), 13);
        let range = |name: &str| {
            audit
                .ranges
                .get(name)
                .map(|(module, line)| (module.as_str(), *line))
        };
        assert_eq!(range("Krepi.HB.fx"), Some(("Krepi.HB.Fixture", 7)));
        assert_eq!(
            range("Krepi.Proofs.Other.u"),
            Some(("Krepi.Proofs.Other", 12))
        );
        assert_eq!(
            range("_private.Krepi.Proofs.Counter.0.Krepi.Proofs.Counter.helper"),
            Some(("Krepi.Proofs.Counter", 15))
        );
        assert_eq!(audit.ranges.len(), 10);
        // The module of each statement, and whether the theorem has exactly
        // its type: `t` proves the weaker `W`, and `c` proves `T` of the
        // proofs, which their coercion to `W` lets its `example` check.
        let found = |module: &str, exact| (Some(module.to_string()), exact);
        assert_eq!(
            audit.statements,
            BTreeMap::from([
                (
                    "Krepi.Proofs.Other.P".to_string(),
                    found("Krepi.Proofs.Other", true)
                ),
                (
                    "Krepi.Statements.Counter.Missing".to_string(),
                    (None, false)
                ),
                (
                    "Krepi.Statements.Counter.S".to_string(),
                    found("Krepi.Statements.Counter", false)
                ),
                (
                    "Krepi.Statements.Counter.W".to_string(),
                    found("Krepi.Statements.Counter", false)
                ),
            ])
        );
        assert!(audit.native.is_empty());
        // The errors of the examples at lines 4 and 6, as plain `lean`
        // prints them, with or without the name of the error; the example
        // of `c` at line 7 checks.
        assert_eq!(
            audit.errors,
            BTreeMap::from([
                (4, vec!["Audit.lean:4:40: error: Type mismatch".to_string()]),
                (
                    6,
                    vec!["Audit.lean:6:10: error(lean.unknownIdentifier): Unknown identifier `Krepi.Statements.Counter.Missing`".to_string()]
                ),
            ])
        );
        // The stage of today's tree.
        let base = audit_output(captured(include_str!("fixtures/base/audit/base.txt")));
        assert_eq!(base.modules.len(), 5);
        assert_eq!(base.theorems.len(), 8);
        assert!(base.errors.is_empty() && base.statements.is_empty());
        // Wrapped lists, primed and private names, as `#print axioms`
        // printed them.
        let output = "krepi-audit module Krepi.Proofs.PrivAx\n\
            'Krepi.Proofs.PrivAx.tp' depends on axioms: [propext,\n \
            Classical.choice,\n \
            Quot.sound,\n \
            _private.Krepi.Proofs.PrivAx.0.Krepi.Proofs.PrivAx.hidden]\n\
            krepi-audit range Krepi.Proofs.PrivAx.tp 9\n\
            krepi-audit module Krepi.Proofs.Native\n\
            'Krepi.Proofs.Native.long'' depends on axioms: [propext,\n \
            _private.Krepi.Proofs.Native.0.Krepi.Proofs.Native.long'._native.bv_decide.ax_1_6]\n\
            krepi-audit range Krepi.Proofs.Native.long' 12\n";
        let audit = audit_output(output);
        assert_eq!(
            audit.theorems["Krepi.Proofs.PrivAx.tp"].1,
            [
                "propext",
                "Classical.choice",
                "Quot.sound",
                "_private.Krepi.Proofs.PrivAx.0.Krepi.Proofs.PrivAx.hidden"
            ]
        );
        assert_eq!(
            audit.theorems["Krepi.Proofs.Native.long'"].0,
            "Krepi.Proofs.Native"
        );
        assert_eq!(
            audit.ranges["Krepi.Proofs.Native.long'"],
            ("Krepi.Proofs.Native".to_string(), 12)
        );
    }

    #[test]
    fn the_heartbeats_of_a_known_fixture_are_read() {
        // The heartbeat copies that the stages ran, what Lean printed for
        // each, and the line of the declaration range of each theorem from
        // the audit of the stage `counter`.
        let captures = [
            (
                include_str!("fixtures/base/heartbeats/Krepi/HB/Fixture.lean"),
                include_str!("fixtures/base/heartbeats/Krepi/HB/Fixture.json"),
                "Krepi.HB.fx",
                253,
            ),
            (
                include_str!("fixtures/base/heartbeats/Krepi/Qualification/Arithmetic.lean"),
                include_str!("fixtures/base/heartbeats/Krepi/Qualification/Arithmetic.json"),
                "Krepi.Qualification.Arithmetic.mul_mod_spec",
                1331,
            ),
            (
                include_str!("fixtures/base/heartbeats/Krepi/Qualification/Checked.lean"),
                include_str!("fixtures/base/heartbeats/Krepi/Qualification/Checked.json"),
                "Krepi.Qualification.Checked.add_within_spec",
                4369,
            ),
            (
                include_str!("fixtures/base/heartbeats/Krepi/Qualification/SingleLoop.lean"),
                include_str!("fixtures/base/heartbeats/Krepi/Qualification/SingleLoop.json"),
                "Krepi.Qualification.SingleLoop.charge_each_spec",
                5500,
            ),
        ];
        let audit = audit_output(captured(include_str!("fixtures/base/audit/counter.txt")));
        for (copy, output, theorem, count) in captures {
            let original = copy.replacen(&format!("{COUNT}\n"), "", 1);
            let line = audit.ranges[theorem].1;
            let (written, inserted) = heartbeat_copy(&original, &[(theorem.to_string(), line)]);
            assert_eq!(written, copy, "{theorem}");
            assert_eq!(inserted, BTreeMap::from([(line, theorem.to_string())]));
            let counts = heartbeats(output, &inserted);
            assert_eq!(counts, BTreeMap::from([(theorem.to_string(), count)]));
            // The known count, which the header records, is the smallest
            // limit with which the declaration elaborates: the count is never
            // below it and at most 2 % plus 50 above it.
            let known: u64 = (output.lines().next())
                .and_then(|header| header.split_once("known count "))
                .and_then(|(_, rest)| rest.split(',').next())
                .and_then(|known| known.parse().ok())
                .expect("the known count");
            assert!(
                known <= count && count <= known + known / 50 + 50,
                "{theorem}: {count} {known}"
            );
        }
        // Two counted theorems in one copy: the line inserted before the
        // first moves the second theorem, and the position of its count, one
        // line down.
        let copy = include_str!("fixtures/base/heartbeats/Krepi/HB/Pair.lean");
        let output = include_str!("fixtures/base/heartbeats/Krepi/HB/Pair.json");
        let pair = audit_output(captured(include_str!("fixtures/base/audit/pair.txt")));
        let names = ["Krepi.HB.pa", "Krepi.HB.pb"];
        let at = names.map(|theorem| (theorem.to_string(), pair.ranges[theorem].1));
        assert_eq!(at.each_ref().map(|(_, line)| *line), [7, 11]);
        let original = copy.replace(&format!("{COUNT}\n"), "");
        let (written, inserted) = heartbeat_copy(&original, &at);
        assert_eq!(written, copy);
        let names = names.map(str::to_string);
        let lines = BTreeMap::from([(7, names[0].clone()), (12, names[1].clone())]);
        assert_eq!(inserted, lines);
        let counts = heartbeats(output, &inserted);
        let expected = BTreeMap::from([(names[0].clone(), 151), (names[1].clone(), 372)]);
        assert_eq!(counts, expected);
        // Both lie above their known counts, which the header records; the
        // excess of the second, 59 over 313, is more than the 2 % plus 50 of
        // the proofs above, for which alone that relation is written.
        let header = output.lines().next().unwrap_or_default();
        assert!(header.contains("known counts 121 of pa and 313 of pb"));
        assert!(121 <= counts[&names[0]] && 313 <= counts[&names[1]]);
    }

    #[test]
    fn a_theorem_inside_another_command_has_no_heartbeat_count() {
        let text = "module\n\
            set_option maxHeartbeats 400000 in theorem a : True := trivial\n\
            /-- b -/\n\
            theorem b : True := trivial\n\
            @[simp] theorem c : True := trivial\n\
            example : True := by\n  exact d\nwhere d : True := trivial\n";
        // `a` follows another command on its line, `d` is part of another
        // command, and `e` starts on the line of `c`: none is counted.
        let at = [("a", 2), ("b", 3), ("c", 5), ("d", 8), ("e", 5)];
        let at = at.map(|(name, line)| (name.to_string(), line));
        let (copy, inserted) = heartbeat_copy(text, &at);
        assert_eq!(
            inserted,
            BTreeMap::from([(3, "b".to_string()), (6, "c".to_string())])
        );
        assert_eq!(copy.lines().nth(2), Some(COUNT));
        assert_eq!(copy.lines().nth(5), Some(COUNT));
        // Another message, or a count at another line, is not read.
        let output = "{\"severity\":\"information\",\"data\":\"Used 7 heartbeats, which is greater than the current maximum of 5.\",\"pos\":{\"line\":3,\"column\":0}}\n\
            {\"severity\":\"warning\",\"data\":\"Used 8 heartbeats, which is less than the current maximum of 200000.\",\"pos\":{\"line\":6,\"column\":0}}\n\
            {\"severity\":\"information\",\"data\":\"Used 9 heartbeats\",\"pos\":{\"line\":6,\"column\":0}}\n\
            {\"severity\":\"information\",\"data\":\"Used 9 heartbeats, which is less than the current maximum of 200000.\",\"pos\":{\"line\":4,\"column\":0}}\n\
            not json\n";
        assert_eq!(
            heartbeats(output, &inserted),
            BTreeMap::from([("b".to_string(), 7)])
        );
    }

    #[test]
    fn leanchecker_and_the_version_query_are_read() {
        // What `leanchecker` printed for a declaration added without the
        // kernel, without the `.olean` files it was asked for, and for a
        // resource exception of the kernel.
        let report = "leanchecker found a problem in Krepi.Proofs.Hack\n\
            uncaught exception: while replaying declaration 'Krepi.Proofs.Hack.bad':\n\
            (kernel) declaration type mismatch, 'Krepi.Proofs.Hack.bad' has type\n  True\n\
            but it is expected to have type\n  False\n";
        assert_eq!(leanchecker_read(&ran(1, report)), Ok(()));
        assert_eq!(leanchecker_read(&ran(0, "")), Ok(()));
        for output in [
            "uncaught exception: Could not find any oleans for: Krepi.Proofs\n",
            "leanchecker found a problem in Krepi.Proofs.Deep\n(kernel) deep recursion detected\n",
            "(kernel) declaration type mismatch\n",
        ] {
            let read = leanchecker_read(&ran(1, output));
            assert_eq!(
                read,
                Err("it reported no kernel problem in a module".to_string()),
                "{output}"
            );
        }
        let version = captured(include_str!("fixtures/base/lean-version.txt"));
        assert_eq!(
            lean_version(&ran(0, version)),
            Ok(version.trim_end().to_string())
        );
        for (code, output) in [(1, version), (0, ""), (0, "Lake version 5.0.0")] {
            assert!(lean_version(&ran(code, output)).is_err(), "{code} {output}");
        }
    }

    #[test]
    fn a_write_below_the_installation_is_found() {
        let scratch = Scratch::new("listing");
        scratch.write("tools/library/a.olean", "a");
        scratch.write("tools/library/b/c.olean", "c");
        scratch.write("tools/lean/bin/lean", "lean");
        std::os::unix::fs::symlink("b", scratch.0.join("tools/library/link")).expect("a link");
        std::os::unix::fs::symlink("tools/library", scratch.0.join("backend")).expect("a link");
        let roots = [
            scratch.0.join("backend"),
            scratch.0.join("tools/lean/bin/.."),
        ];
        let before = listing(&roots, None).expect("a listing");
        let library = fs::canonicalize(scratch.0.join("tools/library")).expect("a path");
        // The link of a root is resolved, and the links below it are not
        // followed.
        assert!(before.contains_key(&library.join("link")));
        assert!(!before.contains_key(&library.join("link/c.olean")));
        assert_eq!(before.len(), 8);
        assert_eq!(listing(&roots, Some(&before)), Ok(before.clone()));
        scratch.write("tools/library/b/c.olean", "changed");
        scratch.write("tools/lean/bin/new", "");
        let error = listing(&roots, Some(&before)).expect_err("a change");
        let lean = fs::canonicalize(scratch.0.join("tools/lean")).expect("a path");
        // The new file changes its directory too.
        let start = "the tool installation changed during the phase; changed paths (3): [";
        assert!(error.starts_with(start), "{error}");
        for path in [
            library.join("b/c.olean"),
            lean.join("bin"),
            lean.join("bin/new"),
        ] {
            assert!(error.contains(&format!("{path:?}")), "{error}");
        }
        let missing = listing(&[scratch.0.join("absent")], None).expect_err("no root");
        assert!(
            missing.starts_with(&scratch.0.join("absent").display().to_string()),
            "{missing}"
        );
    }
}
