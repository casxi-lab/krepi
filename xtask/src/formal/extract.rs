//! Charon extraction and Aeneas translation of selected Rust items, as
//! "Extraction" in `docs/formal-verification.md` describes them. Each
//! extraction has a new work directory and runs its two commands through the
//! [`Gate`], which limits and classifies them.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, ErrorKind};
use std::path::{Path, PathBuf};

use serde::Deserialize;
use toml::Table;

use super::Layout;
use super::outcome::{Class, Site};
use super::process::Ran;
use super::run::{self, Gate};
use super::toolchain::environment::{Tool, text};
use super::toolchain::{self, sha256};

/// The extraction configuration, `verification/extraction.toml`: how Charon
/// compiles each crate that the gate extracts.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Configuration {
    pub schema: u32,
    pub qualification: Crate,
    pub kernel: Kernel,
}

/// The qualification crate, which Charon compiles for the host: it is given
/// no `--target`, and Charon then adds the host's triple itself.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Crate {
    /// The triple of each host of the tool manifest.
    pub triples: BTreeMap<String, String>,
    pub features: Vec<String>,
    pub cfg: Vec<String>,
}

/// The kernel workspace, extracted for the extraction triple of the
/// [`Layout`], which is not the target of the kernel images.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Kernel {
    pub triple: String,
    pub features: Vec<String>,
    pub cfg: Vec<String>,
}

/// Reads the extraction configuration `text`, schema 1. The qualification
/// crate must have a triple for every host of the tool manifest and for no
/// other, whose value the gate does not check; the kernel's triple must be
/// the one of `layout`; and neither has features or `cfg` settings.
pub fn configuration(text: &str, layout: &Layout) -> Result<Configuration, String> {
    let configuration: Configuration = toml::from_str(text)
        .map_err(|error| format!("not an extraction configuration: {error}"))?;
    let hosts: BTreeSet<&str> = toolchain::HOSTS.into_iter().collect();
    let qualification = &configuration.qualification;
    let triples: BTreeSet<&str> = qualification.triples.keys().map(String::as_str).collect();
    let kernel = &configuration.kernel;
    let names = |set: &BTreeSet<&str>| set.iter().copied().collect::<Vec<_>>().join(", ");
    let problem = if configuration.schema != 1 {
        format!("schema {} where 1 is expected", configuration.schema)
    } else if triples != hosts {
        format!(
            "[qualification] has triples for {}, not for the hosts {}",
            names(&triples),
            names(&hosts)
        )
    } else if !qualification.features.is_empty() || !qualification.cfg.is_empty() {
        "[qualification] has features or cfg settings, which the gate does not pass".to_string()
    } else if kernel.triple != layout.triple {
        format!(
            "[kernel] has the triple {}, not {}",
            kernel.triple, layout.triple
        )
    } else if !kernel.features.is_empty() || !kernel.cfg.is_empty() {
        "[kernel] has features or cfg settings, which the gate does not pass".to_string()
    } else {
        return Ok(configuration);
    };
    Err(problem)
}

/// The tables of the manifest of the qualification crate, each with the
/// keys that it may hold. Any other key could change what Cargo compiles,
/// such as dependencies, features, a build script, profiles or patches, or
/// is read by Charon in addition to its arguments, as
/// `[package.metadata.charon]` is.
const MANIFEST: [(&str, &str); 4] = [
    (
        "package",
        "name version edition license publish description",
    ),
    ("workspace", ""),
    ("lib", "path"),
    ("lints", "rust"),
];

/// Why the Cargo manifest `text` of the qualification crate cannot be
/// extracted as the gate extracts it: it must be a workspace of its own and
/// hold only the tables and keys of [`MANIFEST`].
pub fn package_problems(text: &str) -> Result<Vec<String>, String> {
    let table: Table = text
        .parse()
        .map_err(|error| format!("not a Cargo manifest: {error}"))?;
    let mut problems = Vec::new();
    if !table.contains_key("workspace") {
        problems.push("it is not a workspace of its own: [workspace] is missing".to_string());
    }
    for (name, value) in &table {
        let allowed = MANIFEST.iter().find(|(table, _)| table == name);
        match (allowed, value.as_table()) {
            (Some((_, keys)), Some(table)) => problems.extend(
                (table.keys())
                    .filter(|key| !keys.split(' ').any(|allowed| allowed == key.as_str()))
                    .map(|key| format!("it has {name}.{key}, which the gate does not allow")),
            ),
            _ => problems.push(format!("it has [{name}], which the gate does not allow")),
        }
    }
    Ok(problems)
}

/// What to extract, for which unit and where.
pub struct Request<'a> {
    pub unit: &'a str,
    /// The Lean module path below the generated namespace, such as
    /// `Qual.Arithmetic`.
    pub module: &'a str,
    /// The Cargo package directory whose library is extracted.
    pub package: &'a Path,
    pub start_from: &'a [String],
    /// The patterns of the items translated without their bodies.
    pub opaque: &'a [String],
    /// A work directory that no extraction has used.
    pub work: &'a Path,
    /// The triple for which Cargo compiles the package, or none for the host.
    pub triple: Option<&'a str>,
}

/// The fields of `translation.json` that the gate reads; Aeneas writes all of
/// them, apart from `loop` (Aeneas `src/EmitJson.ml`).
#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
pub struct Translation {
    pub functions: Vec<Function>,
    pub types: Vec<Type>,
}

/// A translated function, or a loop of one, or the body of such a loop.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Function {
    pub rust_name: String,
    pub lean_name: String,
    /// The Lean file, relative to the directory of `translation.json`.
    pub lean_file: String,
    /// Whether the function is defined in the extracted crate.
    pub is_local: bool,
    /// Whether the function was translated without its body, as an axiom.
    pub is_opaque: bool,
    pub source: Source,
    /// The loop, on the entries of a loop and of its body.
    #[serde(rename = "loop")]
    pub loop_info: Option<Loop>,
}

/// A translated type.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Type {
    pub rust_name: String,
    pub lean_name: String,
    pub lean_file: String,
}

/// Where an item is written in Rust: relative to the package, or below
/// `/rustc/` for the standard library.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Source {
    pub file: String,
}

/// The loop record of a translated function.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Loop {
    /// Whether the entry is the body of the loop rather than the loop.
    pub is_body: bool,
}

/// The outcome of one extraction. A killed, timed-out or unstartable command,
/// or an output that cannot be read, is a tool failure of its unit; an
/// extraction that is not `complete` is a qualification result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Extraction {
    /// Whether Aeneas exited with 0, reported no `[Error]` and wrote at
    /// least one Lean file.
    pub complete: bool,
    /// The [`diagnostics`] of Charon, then those of Aeneas.
    pub diagnostics: Vec<String>,
    /// The generated namespace followed by the module.
    pub namespace: String,
    /// The output directory of Aeneas.
    pub generated: PathBuf,
    /// The Lean files of the module, relative to `generated`, with their
    /// SHA-256.
    pub files: BTreeMap<String, String>,
    /// The translation, empty when Aeneas wrote none.
    pub translation: Translation,
}

impl Extraction {
    /// Rust names of functions left without a body (external functions).
    pub fn external_functions(&self) -> Vec<String> {
        (self.translation.functions.iter())
            .filter(|entry| {
                entry.is_opaque && entry.lean_file.ends_with("FunsExternal_Template.lean")
            })
            .map(|entry| entry.rust_name.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// Rust names of types left without a definition.
    pub fn external_types(&self) -> Vec<String> {
        (self.translation.types.iter())
            .filter(|entry| entry.lean_file.ends_with("TypesExternal_Template.lean"))
            .map(|entry| entry.rust_name.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// Local (crate) functions translated with a body (`opaque == false`) or
    /// left as declarations (`opaque == true`), as
    /// `(rust name, source file, lean name)`.
    pub fn local_functions(&self, opaque: bool) -> Vec<(String, String, String)> {
        (self.translation.functions.iter())
            .filter(|entry| entry.is_local && entry.is_opaque == opaque)
            .map(|entry| {
                (
                    entry.rust_name.clone(),
                    entry.source.file.clone(),
                    entry.lean_name.clone(),
                )
            })
            .collect()
    }

    /// The translated loops of local functions, as `<lean name> <source
    /// file>` with the Lean name relative to the namespace. A loop is an
    /// entry whose `loop` record is not a body, such as `halve_loop`, not
    /// its `.body` nor a function whose name merely contains `_loop`; the
    /// tools can place a loop in the file of a standard macro.
    pub fn loop_sources(&self) -> Vec<String> {
        let prefix = format!("{}.", self.namespace);
        (self.translation.functions.iter())
            .filter(|entry| {
                entry.is_local
                    && !entry.is_opaque
                    && matches!(entry.loop_info, Some(Loop { is_body: false }))
            })
            .map(|entry| {
                let lean = &entry.lean_name;
                let file = &entry.source.file;
                format!("{} {file}", lean.strip_prefix(&prefix).unwrap_or(lean))
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
}

/// Removes terminal escapes and returns the `[Error]` and `[Warn]` messages
/// printed by Aeneas, and the `error` lines printed by Charon.
pub fn diagnostics(log: &str) -> Vec<String> {
    let mut clean = String::with_capacity(log.len());
    let mut characters = log.chars().peekable();
    while let Some(character) = characters.next() {
        if character == '\u{1b}' {
            // Skip a CSI sequence: ESC '[' parameters final-byte.
            if characters.peek() == Some(&'[') {
                characters.next();
                for next in characters.by_ref() {
                    if next.is_ascii_alphabetic() {
                        break;
                    }
                }
            }
            continue;
        }
        clean.push(if character == '\r' { '\n' } else { character });
    }
    let mut found = BTreeSet::new();
    for line in clean.lines() {
        for marker in ["[Error]", "[Warn ]"] {
            if let Some(index) = line.find(marker) {
                found.insert(line[index..].trim().to_string());
            }
        }
        let trimmed = line.trim_start();
        if trimmed.starts_with("error:") || trimmed.starts_with("error[") {
            found.insert(trimmed.to_string());
        }
    }
    found.into_iter().collect()
}

/// Runs Charon in the package and, if it passed and wrote the LLBC file,
/// Aeneas in the work directory, with the Cargo target directory `target` of
/// the work directory, removed when they have ended. An error is an internal
/// error of the gate, which stops the phase.
pub fn extract(gate: &mut Gate, request: &Request) -> Result<Extraction, String> {
    let generated = gate.layout().generated;
    let namespace = format!("{generated}.{}", request.module);
    if request.start_from.is_empty() {
        return Err(format!(
            "{namespace}: an extraction needs at least one root"
        ));
    }
    let work = request.work;
    fs::create_dir_all(work)
        .map_err(|error| format!("cannot create {}: {error}", work.display()))?;
    let llbc = work.join("extract.llbc");
    let output = work.join("aeneas");
    let cargo = work.join("target");
    for stale in [&llbc, &output, &cargo] {
        if fs::symlink_metadata(stale).is_ok() {
            return Err(format!(
                "{} already exists; an extraction needs a new work directory",
                stale.display()
            ));
        }
    }
    let mut charon_args: Vec<String> = ["cargo", "--preset=aeneas", "--sysroot", "default"]
        .map(str::to_string)
        .into();
    charon_args.extend(["--start-from".to_string(), request.start_from.join(",")]);
    for pattern in request.opaque {
        charon_args.extend(["--opaque".to_string(), pattern.clone()]);
    }
    charon_args.extend(["--dest-file".to_string(), text(&llbc)?]);
    charon_args.extend(["--", "--lib", "--locked"].map(str::to_string));
    let triple = request
        .triple
        .iter()
        .flat_map(|triple| ["--target", triple]);
    charon_args.extend(triple.map(str::to_string));
    // Aeneas runs on one thread (`-sequential`): its pool of threads takes a
    // time that varies with the load and, after an internal exception, can
    // report errors in other functions.
    let subdirectory = format!("{generated}/{}", request.module.replace('.', "/"));
    let mut aeneas_args: Vec<String> = ["-backend", "lean", "-namespace"]
        .map(str::to_string)
        .into();
    aeneas_args.extend([namespace.clone(), "-split-files".to_string()]);
    aeneas_args.extend(["-subdir".to_string(), subdirectory.clone()]);
    aeneas_args.extend(["-emit-json", "-no-progress-bar", "-sequential"].map(str::to_string));
    aeneas_args.extend(["-dest".to_string(), text(&output)?, text(&llbc)?]);
    // Incremental compilation is off: Charon sets
    // `CHARON_SELECTED_CRATE_<crate>` to a new value in every run, so an
    // incremental session of the crate would be written and never read.
    let (charon, verdict, _) = gate.run(
        request.unit,
        &run::Request {
            site: Site::Charon,
            tool: Tool::Charon { target_dir: &cargo },
            program: "charon",
            args: &charon_args,
            cwd: request.package,
            stdin: None,
        },
        |_| Ok(()),
    );
    let aeneas = run::Request {
        site: Site::Aeneas,
        tool: Tool::Aeneas { target_dir: &cargo },
        program: "aeneas",
        args: &aeneas_args,
        cwd: work,
        stdin: None,
    };
    let mut found = charon.map_or_else(Vec::new, |ran| diagnostics(&ran.output));
    let (mut status, mut read) = (None, None);
    if verdict.class != Class::Passed {
        gate.skip(request.unit, &aeneas, "charon did not pass");
    } else if !llbc.is_file() {
        gate.skip(request.unit, &aeneas, "charon wrote no extract.llbc");
    } else {
        let (ran, _, written) = gate.run(request.unit, &aeneas, |ran| {
            read_output(&output, &subdirectory, ran.code() == Some(0))
        });
        status = ran.as_ref().and_then(Ran::code);
        found.extend(ran.map_or_else(Vec::new, |ran| diagnostics(&ran.output)));
        read = written;
    }
    let (translation, files) = read.unwrap_or_default();
    let errors = found.iter().any(|line| line.starts_with("[Error]"));
    let extraction = Extraction {
        complete: status == Some(0) && !errors && !files.is_empty(),
        diagnostics: found,
        namespace,
        generated: output,
        files,
        translation,
    };
    match fs::remove_dir_all(&cargo) {
        Err(error) if error.kind() != ErrorKind::NotFound => Err(format!(
            "cannot remove the Cargo target directory {}: {error}",
            cargo.display()
        )),
        _ => Ok(extraction),
    }
}

/// What Aeneas wrote in `output`: its `translation.json`, which it writes at
/// the end of every run and must have written when it `passed`, and the
/// Lean files directly in its `subdirectory`, with their SHA-256.
fn read_output(
    output: &Path,
    subdirectory: &str,
    passed: bool,
) -> Result<(Translation, BTreeMap<String, String>), String> {
    let unreadable =
        |path: &Path, error: io::Error| format!("cannot read {}: {error}", path.display());
    let path = output.join("translation.json");
    let translation = match fs::read(&path) {
        Err(error) if error.kind() == ErrorKind::NotFound && !passed => Translation::default(),
        Err(error) => return Err(unreadable(&path, error)),
        Ok(bytes) => serde_json::from_slice(&bytes)
            .map_err(|error| format!("{} is not a translation: {error}", path.display()))?,
    };
    let directory = output.join(subdirectory);
    let mut files = BTreeMap::new();
    let entries = match fs::read_dir(&directory) {
        Err(error) if error.kind() == ErrorKind::NotFound => return Ok((translation, files)),
        Err(error) => return Err(unreadable(&directory, error)),
        Ok(entries) => entries,
    };
    for entry in entries {
        let entry = entry.map_err(|error| unreadable(&directory, error))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.ends_with(".lean") {
            let path = entry.path();
            let bytes = fs::read(&path).map_err(|error| unreadable(&path, error))?;
            files.insert(format!("{subdirectory}/{name}"), sha256(&bytes));
        }
    }
    Ok((translation, files))
}

#[cfg(test)]
mod tests {
    //! The translations of `fixtures/extraction/` are what the pinned
    //! Charon and Aeneas wrote, with the arguments of [`extract`], on
    //! `darwin-arm64` for three shapes of the qualification crate, each in a
    //! crate of its own: `arithmetic`, whose `pow_mod` has a loop,
    //! `shared-pointers`, which reaches `Arc` of the standard library, and
    //! `observations`, extracted with `--opaque crate::observations::Probe
    //! --opaque crate::observations::_::observe`. The final empty line of each
    //! template is left out.

    use std::collections::BTreeMap;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    use super::*;
    use crate::formal::Layout;
    use crate::formal::fixture::Fixture;
    use crate::formal::outcome::Status;
    use crate::formal::receipt::Command;
    use crate::formal::run::RUNS;
    use crate::formal::run::tests::{Done, LONG, gate, phase};
    use crate::formal::toolchain;

    const ARITHMETIC: &str = include_str!("fixtures/extraction/arithmetic/translation.json");
    const SHARED_POINTERS: &str =
        include_str!("fixtures/extraction/shared-pointers/translation.json");
    const OBSERVATIONS: &str = include_str!("fixtures/extraction/observations/translation.json");

    /// The unit of the extractions of these tests.
    const UNIT: &str = "qualification/f";

    /// A Charon stand-in that writes the LLBC file it is asked for.
    const WRITES_LLBC: &str = "while [ $# -gt 0 ]; do\n  \
        if [ \"$1\" = --dest-file ]; then : > \"$2\"; fi\n  shift\ndone";

    /// An Aeneas stand-in that writes a translation without items.
    const WRITES_TRANSLATION: &str = "while [ $# -gt 0 ]; do\n  \
        if [ \"$1\" = -dest ]; then mkdir -p \"$2\" && \
        echo '{\"functions\": [], \"types\": []}' > \"$2/translation.json\"; fi\n  \
        shift\ndone";

    /// An extraction to run.
    struct Case<'a> {
        module: &'a str,
        start_from: &'a [&'a str],
        opaque: &'a [&'a str],
    }

    /// The module `Qual.F`, from `crate::f`.
    const F: Case = Case {
        module: "Qual.F",
        start_from: &["crate::f"],
        opaque: &[],
    };

    /// What an extraction with stand-ins for the tools gave.
    struct Extracted {
        result: Result<Extraction, String>,
        done: Done,
        /// The work directory of the extraction.
        work: PathBuf,
        /// The fixture, which holds the files of the run.
        fixture: Fixture,
    }

    impl Extracted {
        fn extraction(&self) -> &Extraction {
            self.result.as_ref().expect("the extraction ends")
        }

        /// The command of the extraction at `site`.
        fn command(&self, site: Site) -> &Command {
            (self.done.receipt.commands.iter())
                .find(|command| command.site == site && command.unit.as_deref() == Some(UNIT))
                .unwrap_or_else(|| panic!("no {site:?} command"))
        }

        /// The class and the reason of the command at `site`.
        fn class(&self, site: Site) -> (Class, Option<&str>) {
            let command = self.command(site);
            (command.class, command.reason.as_deref())
        }

        /// The conclusion of the case: `VERIFIED`, as the phase concludes
        /// it, unless one of its commands forced another.
        fn status(&self) -> (Status, Option<&str>) {
            let unit = &self.done.receipt.units[UNIT];
            (unit.status, unit.reason.as_deref())
        }

        /// What the command at `site` wrote on its standard output.
        fn stdout(&self, site: Site) -> String {
            let log = self
                .command(site)
                .stdout
                .as_ref()
                .expect("the output is kept");
            fs::read_to_string(self.done.run.path.join(&log.path)).expect("the log is kept")
        }
    }

    /// Extracts `case` from the package `verification/qualification` of a
    /// new fixture `label`, with the stand-ins for Charon and Aeneas, the
    /// shell scripts `charon` and `aeneas`. The phase concludes the case
    /// `VERIFIED` after the extraction, as for a case whose extraction is as
    /// expected, and stops on an error of the extraction, as the
    /// qualification does.
    fn extract_case(label: &str, case: &Case, charon: &str, aeneas: &str) -> Extracted {
        let fixture = Fixture::new(label);
        fixture.write("verification/qualification/src/lib.rs", "pub fn f() {}\n");
        fixture.commit_all();
        fixture.tool("charon", charon);
        fixture.tool("aeneas", aeneas);
        let strings = |items: &[&str]| items.iter().map(|item| item.to_string()).collect();
        let (start_from, opaque): (Vec<String>, Vec<String>) =
            (strings(case.start_from), strings(case.opaque));
        let (mut result, mut work) = (None, PathBuf::new());
        let phases = vec![phase("qualification", LONG, &[UNIT], |gate| {
            let package = gate.source().join(gate.layout().qualification);
            work = gate.work().join("cases/f");
            let request = Request {
                unit: UNIT,
                module: case.module,
                package: &package,
                start_from: &start_from,
                opaque: &opaque,
                work: &work,
                triple: None,
            };
            let extracted = extract(gate, &request);
            let stopped = extracted.as_ref().err().cloned();
            result = Some(extracted);
            match stopped {
                Some(error) => Err(error),
                None => {
                    gate.conclude(UNIT, (Status::Verified, None));
                    Ok(())
                }
            }
        })];
        let done = gate(&fixture, &[], phases);
        Extracted {
            result: result.expect("the phase ran"),
            done,
            work,
            fixture,
        }
    }

    fn extract_with(label: &str, charon: &str, aeneas: &str) -> Extracted {
        extract_case(label, &F, charon, aeneas)
    }

    /// An Aeneas stand-in that writes, in the directory it is given, what
    /// the pinned Aeneas wrote for the shape `shape` of the qualification
    /// crate.
    fn writes_capture(shape: &str) -> String {
        let captured = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/formal/fixtures/extraction")
            .join(shape);
        let captured = captured.to_str().expect("a UTF-8 path");
        assert!(!captured.contains('\''), "{captured}");
        format!(
            "while [ $# -gt 0 ]; do\n  \
             if [ \"$1\" = -dest ]; then mkdir -p \"$2\" && cp -R '{captured}/.' \"$2\"; fi\n  \
             shift\ndone"
        )
    }

    /// The extraction of the module `module` that the captured translation
    /// `text` gives.
    fn captured(text: &str, module: &str) -> Extraction {
        Extraction {
            complete: true,
            diagnostics: Vec::new(),
            namespace: format!("{}.{module}", Layout::PRODUCTION.generated),
            generated: PathBuf::new(),
            files: BTreeMap::new(),
            translation: serde_json::from_str(text).expect("a captured translation"),
        }
    }

    #[test]
    fn the_extraction_commands_have_the_frozen_arguments_and_environment() {
        let case = Case {
            module: "Qual.F",
            start_from: &["crate::f", "crate::g"],
            opaque: &["crate::f::primitive", "crate::_::observe"],
        };
        let charon = format!("env\n{WRITES_LLBC}");
        let aeneas = format!("env\n{WRITES_TRANSLATION}");
        let extracted = extract_case("golden", &case, &charon, &aeneas);
        let (done, root) = (&extracted.done, extracted.fixture.root());
        let run = done.run.path.to_str().expect("a UTF-8 path");
        let root = root.to_str().expect("a UTF-8 path");
        let id = format!("{RUNS}/{}", done.run.id);
        let golden = |text: &str| text.replace(run, "RUN").replace(root, "ROOT");
        let charon = extracted.command(Site::Charon);
        assert_eq!(
            charon
                .argv
                .iter()
                .map(|arg| golden(arg))
                .collect::<Vec<_>>(),
            [
                "charon",
                "cargo",
                "--preset=aeneas",
                "--sysroot",
                "default",
                "--start-from",
                "crate::f,crate::g",
                "--opaque",
                "crate::f::primitive",
                "--opaque",
                "crate::_::observe",
                "--dest-file",
                "RUN/work/cases/f/extract.llbc",
                "--",
                "--lib",
                "--locked",
            ]
        );
        assert_eq!(
            charon.cwd.replace(&id, "RUN"),
            "RUN/work/source/verification/qualification"
        );
        let aeneas = extracted.command(Site::Aeneas);
        assert_eq!(
            aeneas
                .argv
                .iter()
                .map(|arg| golden(arg))
                .collect::<Vec<_>>(),
            [
                "aeneas",
                "-backend",
                "lean",
                "-namespace",
                "KrepiGen.Qual.F",
                "-split-files",
                "-subdir",
                "KrepiGen/Qual/F",
                "-emit-json",
                "-no-progress-bar",
                "-sequential",
                "-dest",
                "RUN/work/cases/f/aeneas",
                "RUN/work/cases/f/extract.llbc",
            ]
        );
        assert_eq!(aeneas.cwd.replace(&id, "RUN"), "RUN/work/cases/f");
        for command in [charon, aeneas] {
            assert_eq!(command.class, Class::Passed, "{command:?}");
            assert_eq!(command.phase.as_deref(), Some("qualification"));
        }
        // The variables that the tools see, apart from those that the shell
        // of a stand-in sets itself.
        let manifest = toolchain::parse(include_str!("../../../verification/toolchain.json"))
            .expect("the committed manifest parses");
        let host = done.receipt.host.as_deref().expect("a host");
        let locale = &manifest.hosts[host].locale;
        let tools = "ROOT/artifacts/formal/tools";
        let path =
            format!("{tools}/lean/bin:{tools}/bin:{tools}/cargo/bin:/usr/bin:/bin:/usr/sbin:/sbin");
        let expected: BTreeMap<&str, &str> = BTreeMap::from([
            ("CARGO_HOME", "ROOT/artifacts/formal/tools/cargo"),
            ("CARGO_INCREMENTAL", "0"),
            ("CARGO_NET_OFFLINE", "true"),
            ("CARGO_TARGET_DIR", "RUN/work/cases/f/target"),
            ("GIT_CONFIG_COUNT", "1"),
            ("GIT_CONFIG_GLOBAL", "/dev/null"),
            ("GIT_CONFIG_KEY_0", "safe.directory"),
            ("GIT_CONFIG_NOSYSTEM", "1"),
            ("GIT_CONFIG_VALUE_0", "*"),
            ("HOME", "RUN/work/home"),
            ("LAKE_ARTIFACT_CACHE", "false"),
            ("LANG", locale),
            ("LC_ALL", locale),
            ("PATH", &path),
            ("RUSTUP_HOME", "ROOT/artifacts/formal/tools/rustup"),
            ("RUSTUP_TOOLCHAIN", "nightly-2026-09-17"),
            ("TMPDIR", "RUN/work/tmp"),
        ]);
        assert_eq!(expected.len(), 17);
        for site in [Site::Charon, Site::Aeneas] {
            let text = golden(&extracted.stdout(site));
            let seen: BTreeMap<&str, &str> = text
                .lines()
                .map(|line| line.split_once('=').expect("NAME=value"))
                .filter(|(name, _)| !matches!(*name, "PWD" | "OLDPWD" | "SHLVL" | "_"))
                .collect();
            assert_eq!(seen, expected, "{site:?}");
        }
    }

    #[test]
    fn an_extraction_without_a_root_fails_before_charon_runs() {
        let case = Case {
            module: "Qual.F",
            start_from: &[],
            opaque: &[],
        };
        let extracted = extract_case("no-root", &case, WRITES_LLBC, "exit 0");
        let error = "KrepiGen.Qual.F: an extraction needs at least one root";
        assert_eq!(extracted.result, Err(error.to_string()));
        assert!(!extracted.work.exists());
        let done = &extracted.done;
        assert!(
            done.receipt
                .commands
                .iter()
                .all(|command| command.unit.is_none()),
            "{:?}",
            done.receipt.commands
        );
        assert_eq!(
            done.failures(),
            [format!("the phase qualification stopped: {error}")]
        );
        assert_eq!(done.receipt.status, Status::ToolFailure);
        assert_eq!(done.receipt.units[UNIT].status, Status::NotRun);
    }

    #[test]
    fn external_functions_are_the_opaque_entries_of_the_function_template() {
        let shared = captured(SHARED_POINTERS, "Qual.SharedPointers");
        assert_eq!(
            shared.external_functions(),
            [
                "alloc::sync::{alloc::sync::Arc<T>}::ptr_eq",
                "alloc::sync::{impl core::ops::deref::Deref<T> for alloc::sync::Arc<T>}::deref",
            ]
        );
        // A local function of the crate that is translated without its body
        // is external as well.
        let mut observations = captured(OBSERVATIONS, "Qual.Observations");
        let observe = "formal_qualification::observations::{formal_qualification::observations::Probe}::observe";
        assert_eq!(observations.external_functions(), [observe]);
        assert!(
            captured(ARITHMETIC, "Qual.Arithmetic")
                .external_functions()
                .is_empty()
        );
        // An entry needs both: no body, and the template.
        let entry = &mut observations.translation.functions[0];
        assert_eq!(entry.rust_name, observe);
        entry.is_opaque = false;
        assert!(observations.external_functions().is_empty());
        let entry = &mut observations.translation.functions[0];
        (entry.is_opaque, entry.lean_file) =
            (true, "KrepiGen/Qual/Observations/Funs.lean".to_string());
        assert!(observations.external_functions().is_empty());
    }

    #[test]
    fn external_types_are_the_entries_of_the_type_template() {
        assert_eq!(
            captured(SHARED_POINTERS, "Qual.SharedPointers").external_types(),
            ["alloc::sync::Arc"]
        );
        let mut observations = captured(OBSERVATIONS, "Qual.Observations");
        assert_eq!(
            observations.external_types(),
            ["formal_qualification::observations::Probe"]
        );
        assert!(
            captured(ARITHMETIC, "Qual.Arithmetic")
                .external_types()
                .is_empty()
        );
        observations.translation.types[0].lean_file =
            "KrepiGen/Qual/Observations/Types.lean".to_string();
        assert!(observations.external_types().is_empty());
    }

    #[test]
    fn local_functions_are_read_with_their_source_files() {
        let local = |rust: &str, lean: &str| {
            (
                format!("formal_qualification::{rust}"),
                "src/lib.rs".to_string(),
                lean.to_string(),
            )
        };
        let arithmetic = captured(ARITHMETIC, "Qual.Arithmetic");
        let lean = |name: &str| format!("KrepiGen.Qual.Arithmetic.arithmetic.{name}");
        assert_eq!(
            arithmetic.local_functions(false),
            [
                local("arithmetic::mul_mod", &lean("mul_mod")),
                local("arithmetic::sub_mod", &lean("sub_mod")),
                local("arithmetic::pow_mod", &lean("pow_mod_loop.body")),
                local("arithmetic::pow_mod", &lean("pow_mod_loop")),
                local("arithmetic::pow_mod", &lean("pow_mod")),
            ]
        );
        assert!(arithmetic.local_functions(true).is_empty());
        let observations = captured(OBSERVATIONS, "Qual.Observations");
        assert_eq!(
            observations.local_functions(true),
            [local(
                "observations::{formal_qualification::observations::Probe}::observe",
                "observations.Probe.observe"
            )]
        );
        assert_eq!(
            observations.local_functions(false),
            [local(
                "observations::observe_twice",
                "KrepiGen.Qual.Observations.observations.observe_twice"
            )]
        );
        // The functions of the standard library are not local.
        let shared = captured(SHARED_POINTERS, "Qual.SharedPointers");
        assert_eq!(
            shared.local_functions(false),
            [local(
                "shared_pointers::same",
                "KrepiGen.Qual.SharedPointers.shared_pointers.same"
            )]
        );
        assert!(shared.local_functions(true).is_empty());
    }

    #[test]
    fn loops_are_the_entries_whose_loop_is_not_a_body() {
        let arithmetic = captured(ARITHMETIC, "Qual.Arithmetic");
        let loops: Vec<(&str, bool)> = (arithmetic.translation.functions.iter())
            .filter_map(|entry| Some((entry.lean_name.as_str(), entry.loop_info.as_ref()?.is_body)))
            .collect();
        assert_eq!(
            loops,
            [
                (
                    "KrepiGen.Qual.Arithmetic.arithmetic.pow_mod_loop.body",
                    true
                ),
                ("KrepiGen.Qual.Arithmetic.arithmetic.pow_mod_loop", false),
            ]
        );
        assert_eq!(
            arithmetic.loop_sources(),
            ["arithmetic.pow_mod_loop src/lib.rs"]
        );
        for (text, module) in [
            (SHARED_POINTERS, "Qual.SharedPointers"),
            (OBSERVATIONS, "Qual.Observations"),
        ] {
            assert!(captured(text, module).loop_sources().is_empty(), "{module}");
        }
    }

    #[test]
    fn a_captured_translation_is_read_with_the_files_that_aeneas_wrote() {
        let case = Case {
            module: "Qual.Arithmetic",
            start_from: &["crate::arithmetic"],
            opaque: &[],
        };
        let extracted = extract_case(
            "captured",
            &case,
            WRITES_LLBC,
            &writes_capture("arithmetic"),
        );
        assert_eq!(extracted.class(Site::Aeneas), (Class::Passed, None));
        assert_eq!(extracted.status(), (Status::Verified, None));
        let extraction = extracted.extraction();
        let digest = |bytes: &[u8]| toolchain::sha256(bytes);
        let mut expected = captured(ARITHMETIC, "Qual.Arithmetic");
        expected.generated = extracted.work.join("aeneas");
        expected.files = BTreeMap::from([
            (
                "KrepiGen/Qual/Arithmetic/Funs.lean".to_string(),
                digest(include_bytes!(
                    "fixtures/extraction/arithmetic/KrepiGen/Qual/Arithmetic/Funs.lean"
                )),
            ),
            (
                "KrepiGen/Qual/Arithmetic/Types.lean".to_string(),
                digest(include_bytes!(
                    "fixtures/extraction/arithmetic/KrepiGen/Qual/Arithmetic/Types.lean"
                )),
            ),
        ]);
        assert_eq!(*extraction, expected);
        assert_eq!(
            extraction.loop_sources(),
            ["arithmetic.pow_mod_loop src/lib.rs"]
        );
        // Lean files of another module are not the module's.
        let elsewhere = extract_with("elsewhere", WRITES_LLBC, &writes_capture("arithmetic"));
        let extraction = elsewhere.extraction();
        assert!(extraction.files.is_empty());
        assert!(!extraction.complete);
        assert_eq!(elsewhere.status(), (Status::Verified, None));
    }

    #[test]
    fn a_killed_tool_is_a_tool_failure_and_no_rejection() {
        // The case concludes VERIFIED, as one that expects a rejection,
        // unless a command of it forces another conclusion.
        let killed = |label: &str, charon: &str, aeneas: &str, site: Site, reason: &str| {
            let extracted = extract_with(label, charon, aeneas);
            assert_eq!(
                extracted.class(site),
                (Class::ToolFailure, Some(reason)),
                "{label}"
            );
            assert_eq!(
                extracted.status(),
                (Status::ToolFailure, Some(reason)),
                "{label}"
            );
            assert!(!extracted.extraction().complete, "{label}");
            extracted
        };
        let charon = killed(
            "charon",
            "echo compiling; kill -9 $$",
            "exit 0",
            Site::Charon,
            "charon was ended by signal 9",
        );
        assert_eq!(
            charon.class(Site::Aeneas),
            (Class::NotRun, Some("not started: charon did not pass"))
        );
        // Cargo reports the Charon driver that the system killed.
        let cargo = "echo 'error: could not compile `f` (lib)' >&2\n\
            echo 'Caused by: process didn'\\''t exit successfully: `charon-driver` \
            (signal: 9, SIGKILL: kill)' >&2\nexit 101";
        killed(
            "driver",
            cargo,
            "exit 0",
            Site::Charon,
            "charon: Cargo reports a process ended by signal 9",
        );
        // Charon passes on the status of Cargo, and -1 for a signal.
        killed(
            "cargo",
            "exit 255",
            "exit 0",
            Site::Charon,
            "charon exited with 255: a signal ended the Cargo it runs",
        );
        killed(
            "aeneas",
            WRITES_LLBC,
            "kill -9 $$",
            Site::Aeneas,
            "aeneas was ended by signal 9",
        );
        // A tool that fails by itself rejects the code.
        let rejected = extract_with(
            "rejected",
            WRITES_LLBC,
            "echo '[Error] Nested borrows are not supported yet'; exit 2",
        );
        let extraction = rejected.extraction();
        assert!(!extraction.complete);
        assert_eq!(rejected.command(Site::Aeneas).exit_code, Some(2));
        assert_eq!(
            extraction.diagnostics,
            ["[Error] Nested borrows are not supported yet"]
        );
        assert_eq!(
            rejected.class(Site::Aeneas),
            (Class::ProofFailure, Some("aeneas exited with 2"))
        );
        assert_eq!(rejected.status(), (Status::Verified, None));
        let failed = extract_with("failed", "echo 'error: no such item' >&2; exit 1", "");
        let extraction = failed.extraction();
        assert!(!extraction.complete);
        assert_eq!(failed.command(Site::Aeneas).exit_code, None);
        assert_eq!(extraction.diagnostics, ["error: no such item"]);
        assert_eq!(
            failed.class(Site::Charon),
            (Class::ProofFailure, Some("charon exited with 1"))
        );
        // Aeneas does not start, which does not decide the case.
        assert_eq!(
            failed.class(Site::Aeneas),
            (Class::NotRun, Some("not started: charon did not pass"))
        );
        assert_eq!(failed.status(), (Status::Verified, None));
        // Nor does Aeneas start when Charon passes without its output.
        let silent = extract_with("silent", "exit 0", "exit 0");
        assert_eq!(
            silent.class(Site::Aeneas),
            (
                Class::NotRun,
                Some("not started: charon wrote no extract.llbc")
            )
        );
        assert_eq!(silent.status(), (Status::Verified, None));
    }

    #[test]
    fn a_tool_that_cannot_start_or_a_file_it_cannot_use_fails_the_extraction() {
        let failed = |label: &str, charon: &str, aeneas: &str| {
            let extracted = extract_with(label, charon, aeneas);
            let (class, reason) = extracted.class(Site::Aeneas);
            assert_eq!(class, Class::ToolFailure, "{label}");
            let reason = reason.expect("a reason").to_string();
            assert_eq!(
                extracted.status(),
                (Status::ToolFailure, Some(reason.as_str())),
                "{label}"
            );
            assert!(!extracted.extraction().complete, "{label}");
            reason
        };
        // Charon takes away the right to run Aeneas.
        let charon = format!("chmod -x \"$(dirname \"$0\")/aeneas\"\n{WRITES_LLBC}");
        let reason = failed("start", &charon, "exit 0");
        assert!(
            reason.starts_with("aeneas: cannot start aeneas: "),
            "{reason}"
        );
        // Aeneas writes a translation that cannot be parsed.
        let aeneas = "while [ $# -gt 0 ]; do\n  \
            if [ \"$1\" = -dest ]; then mkdir -p \"$2\" && echo '{' > \"$2/translation.json\"; fi\n  \
            shift\ndone";
        let reason = failed("translation", WRITES_LLBC, aeneas);
        assert!(reason.starts_with("aeneas: "), "{reason}");
        assert!(
            reason.contains("/aeneas/translation.json is not a translation: "),
            "{reason}"
        );
        // Aeneas writes generated definitions that cannot be read.
        let aeneas = "while [ $# -gt 0 ]; do\n  \
            case \"$1\" in -subdir) subdir=$2 ;; -dest) dest=$2 ;; esac\n  shift\ndone\n\
            mkdir -p \"$dest/$subdir\" && : > \"$dest/$subdir/Funs.lean\"\n\
            echo '{\"functions\": [], \"types\": []}' > \"$dest/translation.json\"\n\
            chmod 000 \"$dest/$subdir/Funs.lean\"";
        let reason = failed("unreadable", WRITES_LLBC, aeneas);
        assert!(reason.starts_with("aeneas: cannot read "), "{reason}");
        assert!(
            reason.contains("/KrepiGen/Qual/F/Funs.lean: Permission denied"),
            "{reason}"
        );
        // Charon leaves a target directory that the gate cannot remove,
        // which stops the phase.
        let charon = format!(
            "{WRITES_LLBC}\nmkdir -p \"$CARGO_TARGET_DIR/debug\" && \
             : > \"$CARGO_TARGET_DIR/debug/lock\" && chmod 500 \"$CARGO_TARGET_DIR/debug\""
        );
        let extracted = extract_with("unremovable", &charon, "exit 0");
        let error = extracted.result.clone().expect_err("an internal error");
        let target = extracted.work.join("target");
        assert!(
            error.starts_with(&format!(
                "cannot remove the Cargo target directory {}: ",
                target.display()
            )),
            "{error}"
        );
        assert_eq!(
            extracted.done.failures(),
            [format!("the phase qualification stopped: {error}")]
        );
        assert_eq!(extracted.done.receipt.status, Status::ToolFailure);
        assert!(!extracted.done.receipt.complete);
        fs::set_permissions(target.join("debug"), fs::Permissions::from_mode(0o755))
            .expect("let the fixture be removed");
    }

    #[test]
    fn an_unreadable_or_invalid_translation_is_a_tool_failure() {
        // Aeneas exits with 0 after it writes `translation.json` with the
        // shell command `write`.
        let unread = |label: &str, write: &str| {
            let aeneas = format!(
                "while [ $# -gt 0 ]; do\n  \
                 if [ \"$1\" = -dest ]; then dest=$2; fi\n  shift\ndone\n\
                 mkdir -p \"$dest\" && cd \"$dest\" && {write}"
            );
            let extracted = extract_with(label, WRITES_LLBC, &aeneas);
            let command = extracted.command(Site::Aeneas);
            assert_eq!(command.exit_code, Some(0), "{label}");
            let (class, reason) = (command.class, command.reason.clone().expect("a reason"));
            assert_eq!(class, Class::ToolFailure, "{label}");
            assert_eq!(
                extracted.status(),
                (Status::ToolFailure, Some(reason.as_str())),
                "{label}"
            );
            let extraction = extracted.extraction();
            assert_eq!(extraction.translation, Translation::default(), "{label}");
            assert!(!extraction.complete, "{label}");
            reason
        };
        let reason = unread(
            "no-permission",
            "echo '{\"functions\": [], \"types\": []}' > translation.json && \
             chmod 000 translation.json",
        );
        assert!(reason.starts_with("aeneas: cannot read "), "{reason}");
        assert!(
            reason.ends_with("/translation.json: Permission denied (os error 13)"),
            "{reason}"
        );
        let reason = unread("not-json", "echo '{' > translation.json");
        assert!(
            reason.contains("/translation.json is not a translation: EOF while parsing"),
            "{reason}"
        );
        let reason = unread(
            "not-a-translation",
            "echo '{\"functions\": []}' > translation.json",
        );
        assert!(
            reason.contains("/translation.json is not a translation: missing field `types`"),
            "{reason}"
        );
        let reason = unread("directory", "mkdir translation.json");
        assert!(reason.starts_with("aeneas: cannot read "), "{reason}");
        // Aeneas writes `translation.json` at the end of every run, so one
        // that passed without it is a tool failure; one that failed without
        // it rejects the shape.
        let reason = unread("missing", "true");
        assert!(
            reason.ends_with("/translation.json: No such file or directory (os error 2)"),
            "{reason}"
        );
        let extracted = extract_with("missing-after-failure", WRITES_LLBC, "exit 1");
        assert_eq!(extracted.class(Site::Aeneas).0, Class::ProofFailure);
        assert_eq!(extracted.extraction().translation, Translation::default());
        // The same translation with a field that the gate reads, and an
        // optional one, left out.
        let entry = "{\"rust_name\": \"r\", \"lean_name\": \"l\", \"lean_file\": \"f\", \
            \"is_local\": true, \"source\": {\"file\": \"src/lib.rs\"}}";
        let error = serde_json::from_str::<Translation>(&format!(
            "{{\"functions\": [{entry}], \"types\": []}}"
        ))
        .expect_err("is_opaque is missing");
        assert!(
            error.to_string().contains("missing field `is_opaque`"),
            "{error}"
        );
        let entry = entry.replace("}}", "}, \"is_opaque\": false}");
        let read: Translation =
            serde_json::from_str(&format!("{{\"functions\": [{entry}], \"types\": []}}"))
                .expect("a translation without a loop");
        assert_eq!(read.functions[0].loop_info, None);
    }

    #[test]
    fn the_target_directory_is_removed_after_the_extraction() {
        // Charon builds into the target directory, which Aeneas still sees.
        let charon = format!(
            "mkdir -p \"$CARGO_TARGET_DIR/debug\" && echo built > \"$CARGO_TARGET_DIR/debug/f\"\n\
             {WRITES_LLBC}"
        );
        let aeneas = format!(
            "test -f \"$CARGO_TARGET_DIR/debug/f\" || exit 3\n{}",
            writes_capture("arithmetic")
        );
        let extracted = extract_with("removed", &charon, &aeneas);
        assert_eq!(extracted.class(Site::Aeneas), (Class::Passed, None));
        let work = &extracted.work;
        assert!(!work.join("target").exists());
        assert!(work.join("extract.llbc").is_file());
        assert!(work.join("aeneas/translation.json").is_file());
        assert_eq!(extracted.extraction().generated, work.join("aeneas"));
        // So it is after a Charon that fails.
        let charon = "mkdir -p \"$CARGO_TARGET_DIR/debug\" && echo built > \"$CARGO_TARGET_DIR/debug/f\"\n\
                      exit 1";
        let extracted = extract_with("removed-after-failure", charon, "exit 0");
        assert_eq!(extracted.class(Site::Charon).0, Class::ProofFailure);
        assert!(extracted.work.is_dir());
        assert!(!extracted.work.join("target").exists());
    }

    #[test]
    fn a_used_work_directory_is_refused() {
        for stale in ["extract.llbc", "aeneas", "target"] {
            let fixture = Fixture::new("used");
            fixture.tool("charon", WRITES_LLBC);
            fixture.tool("aeneas", "exit 0");
            let roots = ["crate::f".to_string()];
            let mut result = None;
            let phases = vec![phase("qualification", LONG, &[UNIT], |gate| {
                let (package, work) = (gate.source(), gate.work().join("cases/f"));
                let made = match stale {
                    "extract.llbc" => {
                        fs::create_dir_all(&work).and_then(|()| fs::write(work.join(stale), ""))
                    }
                    _ => fs::create_dir_all(work.join(stale)),
                };
                made.map_err(|error| error.to_string())?;
                let request = Request {
                    unit: UNIT,
                    module: "Qual.F",
                    package: &package,
                    start_from: &roots,
                    opaque: &[],
                    work: &work,
                    triple: None,
                };
                result = Some(extract(gate, &request).map(|_| ()));
                Ok(())
            })];
            let done = gate(&fixture, &[], phases);
            let error = result
                .expect("the phase ran")
                .expect_err("a used directory");
            assert!(
                error.ends_with(&format!(
                    "/work/cases/f/{stale} already exists; an extraction needs a new work directory"
                )),
                "{error}"
            );
            assert!(
                done.receipt
                    .commands
                    .iter()
                    .all(|command| command.unit.is_none()),
                "{stale}"
            );
        }
    }

    #[test]
    fn charon_builds_without_incremental_compilation() {
        // The stand-in reports the variables that Cargo reads as an error.
        let charon = "echo \"error: incremental ${CARGO_INCREMENTAL-unset} \
            in $CARGO_TARGET_DIR\" >&2; exit 1";
        let extracted = extract_with("incremental", charon, "");
        let [line] = extracted.extraction().diagnostics.as_slice() else {
            panic!("{:?}", extracted.extraction().diagnostics);
        };
        assert!(line.starts_with("error: incremental 0 in "), "{line}");
        assert!(line.ends_with("/work/cases/f/target"), "{line}");
    }

    #[test]
    fn aeneas_translates_on_one_thread() {
        let extracted = extract_with("sequential", WRITES_LLBC, "exit 0");
        let run = extracted.done.run.path.to_str().expect("a UTF-8 path");
        let argv: Vec<String> = (extracted.command(Site::Aeneas).argv.iter())
            .map(|argument| argument.replace(run, "RUN"))
            .collect();
        assert_eq!(
            argv,
            [
                "aeneas",
                "-backend",
                "lean",
                "-namespace",
                "KrepiGen.Qual.F",
                "-split-files",
                "-subdir",
                "KrepiGen/Qual/F",
                "-emit-json",
                "-no-progress-bar",
                "-sequential",
                "-dest",
                "RUN/work/cases/f/aeneas",
                "RUN/work/cases/f/extract.llbc",
            ]
        );
    }

    #[test]
    fn loop_sources_name_each_translated_loop_with_its_file() {
        // `body` is the `is_body` field of the entry's `loop` record, if any.
        let entry = |lean: &str, file: &str, local: bool, opaque: bool, body: Option<bool>| {
            let record = body
                .map(|body| format!(", \"loop\": {{\"id\": 0, \"pos\": [0], \"is_body\": {body}}}"))
                .unwrap_or_default();
            format!(
                "{{\"rust_name\": \"r\", \"lean_name\": \"KrepiGen.Qual.M.{lean}\", \"lean_file\": \"KrepiGen/Qual/M/Funs.lean\", \"is_local\": {local}, \"is_opaque\": {opaque}, \"source\": {{\"file\": \"{file}\"}}{record}}}"
            )
        };
        let macros = "/rustc/library/core/src/macros/mod.rs";
        let translation = format!(
            "{{\"functions\": [{}], \"types\": []}}",
            [
                entry("m.halve_loop", macros, true, false, Some(false)),
                entry("m.halve_loop.body", macros, true, false, Some(true)),
                entry("m.halve", "src/lib.rs", true, false, None),
                // A function whose name contains `_loop` but that is no loop.
                entry("m.run_loop", "src/lib.rs", true, false, None),
                entry(
                    "m.T.method.default_loop0",
                    "src/lib.rs",
                    true,
                    false,
                    Some(false)
                ),
                entry("m.cut_loop", "src/lib.rs", true, true, Some(false)),
                entry("std.loop_loop", "src/lib.rs", false, false, Some(false)),
            ]
            .join(", ")
        );
        let extraction = captured(&translation, "Qual.M");
        assert_eq!(
            extraction.loop_sources(),
            vec![
                "m.T.method.default_loop0 src/lib.rs".to_string(),
                format!("m.halve_loop {macros}"),
            ]
        );
    }

    #[test]
    fn the_extraction_configuration_is_read() {
        let text = include_str!("../../../verification/extraction.toml");
        let layout = Layout::PRODUCTION;
        let read = configuration(text, &layout).expect("the committed configuration");
        let triples: Vec<(&str, &str)> = (read.qualification.triples.iter())
            .map(|(host, triple)| (host.as_str(), triple.as_str()))
            .collect();
        assert_eq!(
            triples,
            [
                ("darwin-arm64", "aarch64-apple-darwin"),
                ("linux-aarch64", "aarch64-unknown-linux-gnu")
            ]
        );
        assert_eq!(read.kernel.triple, layout.triple);
        let refused = |from: &str, to: &str| {
            assert!(text.contains(from), "{from}");
            configuration(&text.replacen(from, to, 1), &layout).expect_err(to)
        };
        assert_eq!(
            refused("schema = 1", "schema = 2"),
            "schema 2 where 1 is expected"
        );
        assert_eq!(
            refused("darwin-arm64 = ", "darwin-amd64 = "),
            "[qualification] has triples for darwin-amd64, linux-aarch64, not for the hosts \
             darwin-arm64, linux-aarch64"
        );
        let features = "[qualification]\nfeatures = []";
        assert_eq!(
            refused(features, "[qualification]\nfeatures = [\"x\"]"),
            "[qualification] has features or cfg settings, which the gate does not pass"
        );
        assert_eq!(
            refused("cfg = []", "cfg = [\"board=\\\"pi5\\\"\"]"),
            "[qualification] has features or cfg settings, which the gate does not pass"
        );
        assert_eq!(
            refused("\"aarch64-unknown-none\"", "\"x86_64-unknown-none\""),
            "[kernel] has the triple x86_64-unknown-none, not aarch64-unknown-none"
        );
        let unknown = refused("[kernel]\n", "[kernel]\ntarget = \"x\"\n");
        assert!(
            unknown.starts_with("not an extraction configuration: "),
            "{unknown}"
        );
    }

    #[test]
    fn the_extraction_triple_is_named_apart_from_the_target_of_the_images() {
        // The kernel images are built for the bare-metal target that
        // `rust-toolchain.toml` installs, another triple, which the
        // configuration and "Extraction" in the docs name beside the
        // extraction triple.
        let triple = Layout::PRODUCTION.triple;
        let toolchain: Table =
            toml::from_str(include_str!("../../../rust-toolchain.toml")).expect("the toolchain");
        let targets = toolchain["toolchain"]["targets"].as_array();
        let Some([image]) = targets.map(Vec::as_slice) else {
            panic!("not one target: {targets:?}");
        };
        let image = image.as_str().expect("a target");
        assert_ne!(triple, image);
        let text = include_str!("../../../verification/extraction.toml");
        let (_, kernel) = text
            .split_once("[qualification.triples]")
            .expect("the kernel");
        let kernel = kernel.replace("\n# ", " ");
        let docs = include_str!("../../../docs/formal-verification.md");
        let (_, section) = docs.split_once("\n### Extraction\n").expect("the section");
        let section = section
            .split("\n### ")
            .next()
            .expect("the section")
            .replace('\n', " ");
        let named = [
            (&kernel, "extracted for the extraction triple".to_string()),
            (
                &kernel,
                format!("the target of the kernel images, {image},"),
            ),
            (&section, format!("the extraction triple, `{triple}`,")),
            (
                &section,
                format!("the target of the kernel images, `{image}`,"),
            ),
        ];
        for (text, name) in named {
            assert!(text.contains(&name), "{name}: {text}");
        }
    }

    #[test]
    fn a_crate_manifest_that_charon_reads_or_that_changes_the_build_is_refused() {
        let manifest = "[package]\nname = \"q\"\nedition = \"2024\"\n\n[workspace]\n";
        assert_eq!(package_problems(manifest), Ok(Vec::new()));
        let with = |extra: &str| package_problems(&format!("{manifest}{extra}"));
        let refused = |what: &str| format!("it has {what}, which the gate does not allow");
        assert_eq!(
            with("\n[package.metadata.charon]\nopaque = []\n"),
            Ok(vec![refused("package.metadata")])
        );
        assert_eq!(
            with("\n[dependencies]\nx = \"1\"\n\n[dev-dependencies]\ny = \"1\"\n"),
            Ok(vec![
                refused("[dependencies]"),
                refused("[dev-dependencies]")
            ])
        );
        assert_eq!(
            with("\n[target.aarch64-unknown-none.build-dependencies]\nz = \"1\"\n"),
            Ok(vec![refused("[target]")])
        );
        // Features, a build script, profiles and patches change what Cargo
        // compiles.
        assert_eq!(
            with("\n[features]\ndefault = [\"pi5\"]\npi5 = []\n"),
            Ok(vec![refused("[features]")])
        );
        assert_eq!(
            package_problems(&manifest.replace("[package]\n", "[package]\nbuild = \"b.rs\"\n")),
            Ok(vec![refused("package.build")])
        );
        assert_eq!(
            with("\n[profile.dev]\ndebug-assertions = false\n\n[patch.crates-io]\n"),
            Ok(vec![refused("[patch]"), refused("[profile]")])
        );
        assert_eq!(
            with("\n[lib]\npath = \"src/lib.rs\"\nproc-macro = true\n"),
            Ok(vec![refused("lib.proc-macro")])
        );
        assert_eq!(
            package_problems(&manifest.replace("[workspace]\n", "[workspace]\nmembers = []\n")),
            Ok(vec![refused("workspace.members")])
        );
        assert_eq!(
            package_problems("[package]\nname = \"q\"\n"),
            Ok(vec![
                "it is not a workspace of its own: [workspace] is missing".to_string()
            ])
        );
        let error = package_problems("[package").expect_err("not TOML");
        assert!(error.starts_with("not a Cargo manifest: "), "{error}");
        let committed = include_str!("../../../verification/qualification/Cargo.toml");
        assert_eq!(package_problems(committed), Ok(Vec::new()));
    }

    #[test]
    fn diagnostics_strip_escapes_and_progress_bars() {
        let log = "Applied prepasses: [--] 1/9 \u{1b}[?25l\u{1b}[91mError\u{1b}[39m\n[\u{1b}[91mError\u{1b}[39m] Nested borrows are not supported yet\r[\u{1b}[93mWarn\u{1b}[39m ] Could not translate\nerror: could not compile `x`\n";
        assert_eq!(
            diagnostics(log),
            vec![
                "[Error] Nested borrows are not supported yet".to_string(),
                "[Warn ] Could not translate".to_string(),
                "error: could not compile `x`".to_string(),
            ]
        );
    }
}
