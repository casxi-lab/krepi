//! `cargo xtask formal vectors`: a component's test vectors, replayed through its
//! specification and compared with its host tests, as `docs/formal-verification.md` says.

use std::path::Path;
use std::time::{Duration, Instant};

use clap::{Arg, ArgMatches};
use serde::Deserialize;

use super::outcome::{self, Site::AxiomAudit, Site::BaseBuild};
use super::toolchain::environment::{self, RunDirs, Tool::LakeEnvLean};
use super::{Layout, base::read, guard::statement_side, lean, process, qualify, run, toolchain};
use crate::repo::Tree;

/// The time that the commands of one `cargo xtask formal vectors` share.
pub const BUDGET: Duration = Duration::from_secs(1_800);

/// The problems of a comparison, or why it could not compare.
pub type Found = Result<Vec<String>, String>;

/// A contract's `vectors` block: the vector file and, once it exists, the replay module.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Block {
    pub vectors: String,
    pub replay: Option<String>,
}

/// The `vectors` block of `Legacy test vectors` in the contract of
/// `component`, `<domain>/<name>`, in `tree`: the trimmed lines of the
/// section that start a fence are none, or ```` ```vectors ```` and ```` ``` ````.
pub fn block(tree: &Tree, component: &str) -> Result<Option<Block>, String> {
    let path = format!("docs/domains/{component}/contract.md");
    let text = (tree.text(&path)).filter(|_| component.split('/').count() == 2);
    let text = text.ok_or(format!("{path} is not a tracked contract"))?;
    let mut lines = text.lines().map(str::trim);
    lines.find(|line| line.strip_prefix("## ").map(str::trim) == Some("Legacy test vectors"));
    let section = Vec::from_iter(lines.take_while(|line| !line.starts_with("## ")));
    let fence = |at: &usize| section[*at].starts_with("```") || section[*at].starts_with("~~~");
    match Vec::from_iter((0..section.len()).filter(fence))[..] {
        [] => Ok(None),
        [open, end] if section[open] == "```vectors" && section[end] == "```" => {
            let block = toml::from_str(&section[open + 1..end].join("\n"));
            (block.map(Some)).map_err(|error| format!("{path}: {}", error.message()))
        }
        _ => Err(format!("{path}: not one vectors block in the section")),
    }
}

/// The problems of the result files `spec`, of the replay, and `host`, of
/// the host tests, for `vectors`, whose first line names its source: their
/// lines but `#` comments, compared in order by id and output.
pub fn compare<'a>(vectors: &'a str, spec: &'a str, host: &'a str) -> Vec<String> {
    let source = (vectors.strip_prefix('#')).and_then(|rest| rest.lines().next());
    let unsourced = !source.is_some_and(|source| !source.trim().is_empty());
    let lines = [vectors, spec, host].map(|text| text.split_terminator('\n'));
    let [vectors, spec, host] = lines.map(|l| Vec::from_iter(l.filter(|l| !l.starts_with('#'))));
    let fields = |line: &&'a str| Vec::from_iter(line.split('\t'));
    let ids = Vec::from_iter((vectors.iter().map(fields)).map(|f| (f.len() == 3).then_some(f[0])));
    let unsourced = unsourced.then_some("the first line of the vector file names no source");
    let empty = (vectors.is_empty()).then_some("the vector file holds no vector");
    let mut problems = Vec::from_iter(unsourced.into_iter().chain(empty).map(String::from));
    let shown = |line: Option<&&str>| line.map_or("nothing".into(), |line| format!("{line:?}"));
    for at in 0..vectors.len().max(spec.len()).max(host.len()) {
        let (replay, tests, id) = (spec.get(at), host.get(at), ids.get(at).copied().flatten());
        let formed = (replay.map(fields)).is_some_and(|f| f.len() == 2 && Some(f[0]) == id);
        let (same, [replay, tests]) = (replay == tests, [replay, tests].map(shown));
        problems.push(match ids.get(at) {
            None => format!("result {}: of no vector", at + 1),
            Some(None | Some("")) => format!("vector {}: not an id, input and output", at + 1),
            Some(id) if ids[..at].contains(id) => format!("vector {}: an id given twice", at + 1),
            Some(_) if formed && same => continue,
            Some(Some(id)) => format!("{id}: the replay gives {replay}, the host tests {tests}"),
        });
    }
    problems
}

/// Compares the vectors of `name` in `tree`: the replay module is built and
/// run in a stage of a new run directory, with commands that end by `end`
/// and fail as the gate's do or, the replay, by writing to standard error.
pub fn vectors(root: &Path, layout: &Layout, tree: &Tree, name: &str, end: Instant) -> Found {
    let block = block(tree, name)?.ok_or("the contract has no vectors block")?;
    let module = (block.replay).ok_or("the vectors block names no replay module")?;
    let below = format!("{}/{}/", layout.project, layout.namespace);
    let file = format!("{}/{}", layout.project, lean::module_file(&module));
    let own =
        qualify::is_module(&module) && file.starts_with(&below) && statement_side(&file, layout);
    let untracked = format!("{module} is not a tracked module of the statement side in {below}");
    (tree.text(&file).filter(|_| own)).ok_or(untracked)?;
    let vectors = (tree.text(&block.vectors)).ok_or("the vector file is not tracked text")?;
    let host_results = read(&root.join(format!("artifacts/formal/vectors/{name}.results")))?;
    let host = run::host().ok_or("the tools are pinned for linux-aarch64 and darwin-arm64")?;
    let manifest = toolchain::parse(&read(&root.join(layout.toolchain))?)?;
    let backend = environment::installation(&manifest, host, root)?.backend();
    let run = run::RunDir::create(root).map_err(|error| format!("no run directory: {error}"))?;
    let [stage, input, output, home, tmp] =
        ["stage", "vectors", "results", "home", "tmp"].map(|name| run.path.join("work").join(name));
    let project = root.join(layout.project);
    lean::create_stage(&project, &project, &stage, &backend)?;
    for (path, _) in (tree.entries()).filter(|(path, _)| path.starts_with(&below)) {
        lean::copy_into(root, &stage, path)?;
    }
    let (cwd, logs) = (&stage.join(layout.project), &run.path.join("logs"));
    let driver = include_str!("vectors/Driver.lean").replace("KrepiVectorsReplay", &module);
    let write = |path: &Path, text: &str| std::fs::write(path, text).map_err(|e| e.to_string());
    write(&cwd.join("Vectors.lean"), &driver).and(write(&input, vectors))?;
    let mut replay = Vec::from(["env", "lean", "--run", "Vectors.lean"].map(String::from));
    replay.extend([environment::text(&input)?, environment::text(&output)?]);
    let build = lean::build_args(&[format!("+{module}")], true);
    let env = environment::environment(LakeEnvLean, &manifest, host, root, &RunDirs { home, tmp })?;
    let commands = [("build", build, BaseBuild), ("replay", replay, AxiomAudit)];
    for (sequence, (name, args, site)) in (1..).zip(commands) {
        let left = (end.checked_duration_since(Instant::now())).filter(|left| !left.is_zero());
        let left = left.ok_or(format!("{name}: the budget was used up"))?;
        let ran = process::run(&process::Spec {
            name,
            program: "lake",
            args: &args,
            cwd,
            env: &env,
            stdin: None,
            logs,
            sequence,
            limit: run::limit(site.cap(), left, left),
        });
        let spoke = (ran.stderr.as_ref()).is_some_and(|log| name == "replay" && log.bytes > 0);
        let own = lean::proof_messages(&ran.output, std::slice::from_ref(&module)).len();
        let unread = spoke.then_some("it wrote to its standard error");
        if let Some(why) = outcome::classify(site, &ran, own, unread).reason {
            return Err(format!("{why}; its output is in {}", logs.display()));
        }
    }
    Ok(compare(vectors, &read(&output)?, &host_results))
}

/// The command line of `cargo xtask formal vectors`, with `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let component = Arg::new("component").value_name("DOMAIN/COMPONENT");
    let component = component.help("The component to compare, or each that names a replay");
    clap::Command::new("vectors").about(about).arg(component)
}

/// The lines of `cargo xtask formal vectors` in `root` but the counts.
fn report(root: &Path, layout: &Layout, named: Option<&String>, budget: Duration) -> Found {
    let (tree, end) = (Tree::load(root)?, Instant::now() + budget);
    let host = run::host().ok_or("the tools are pinned for linux-aarch64 and darwin-arm64")?;
    let manifest = toolchain::parse(&read(&root.join(layout.toolchain))?)?;
    let prefix = environment::installation(&manifest, host, root)?.prefix;
    let mut lines = vec![format!("host {host}, installation {}", prefix.display())];
    let paths = (tree.entries()).filter_map(|(path, _)| path.strip_prefix("docs/domains/"));
    let contracts = paths.filter_map(|path| path.strip_suffix("/contract.md"));
    let mut found = [Vec::from_iter(named.cloned()), Vec::new()];
    for component in contracts.filter(|c| named.is_none() && c.split('/').count() == 2) {
        if let Some(block) = block(&tree, component)? {
            found[usize::from(block.replay.is_none())].push(component.to_string());
        }
    }
    for component in &found[0] {
        lines.push(format!("compared {component}"));
        let problems = vectors(root, layout, &tree, component, end).unwrap_or_else(|e| vec![e]);
        lines.extend(problems.iter().map(|p| format!("FAILED {component}: {p}")));
    }
    lines.extend((found[1].iter()).map(|c| format!("not compared {c}: it names no replay")));
    Ok(lines)
}

/// Entry point of `cargo xtask formal vectors` in `root`: it prints the host
/// and the installation, each component compared or that names no replay, a
/// `FAILED` line for each problem and the counts, and exits with 1 on one.
pub fn command(root: &Path, layout: &Layout, matches: &ArgMatches) -> std::process::ExitCode {
    process::init();
    let lines = report(root, layout, matches.get_one("component"), BUDGET);
    let lines = lines.unwrap_or_else(|error| vec![format!("FAILED {error}")]);
    process::stop_if_asked();
    let failed = Vec::from_iter(lines.iter().filter(|line| line.starts_with("FAILED ")));
    let compared = Vec::from_iter(lines.iter().filter(|line| line.starts_with("compared ")));
    lines.iter().for_each(|line| println!("{line}"));
    println!("{} components, {} problems", compared.len(), failed.len());
    std::process::ExitCode::from(u8::from(!failed.is_empty()))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::fs;
    use std::path::PathBuf;
    use std::process::{Command, ExitCode, Stdio};

    use super::*;
    use crate::formal::fixture::Fixture;
    use crate::formal::toolchain::environment::Tool;
    use crate::scratch::Scratch;

    /// The fixture component `fixture/sum`: its contract, its vector file,
    /// its replay module and its host results, by their paths below a root,
    /// and the vector file, the replay and the host results themselves.
    const CONTRACT: &str = "docs/domains/fixture/sum/contract.md";
    const VECTORS: &str = "verification/vectors/fixture/sum.vectors";
    const REPLAY: &str = "verification/Krepi/SpecTests/Fixture/Sum.lean";
    const RESULTS: &str = "artifacts/formal/vectors/fixture/sum.results";
    const SUM_VECTORS: &str = include_str!("fixtures/vectors/sum.vectors");
    const SUM_REPLAY: &str = include_str!("fixtures/vectors/Sum.lean");
    const SUM_RESULTS: &str = include_str!("fixtures/vectors/sum.results");

    /// The vectors block of the fixture component.
    const BLOCK: &str = "```vectors\nvectors = \"verification/vectors/fixture/sum.vectors\"\n\
        replay = \"Krepi.SpecTests.Fixture.Sum\"\n```\n";

    /// The host results of the fixture with one item that differs.
    fn differing() -> String {
        let differing = SUM_RESULTS.replace("v2\t0\n", "v2\t1\n");
        assert_ne!(differing, SUM_RESULTS);
        differing
    }

    /// The contract of the fixture component, with `block` in its section
    /// `Legacy test vectors`.
    fn contract(block: &str) -> String {
        format!(
            "# Sum\n\n## Terms\n\nNone.\n\n## Legacy test vectors\n\nThree vectors, written \
             by construction.\n\n{block}\n## Current deviations\n\nNone.\n"
        )
    }

    /// The files of the fixture component with `contract`, and the Lake
    /// project files of this repository, by their paths below a root.
    fn component(contract: &str) -> Vec<(String, String)> {
        let repository = crate::repo::root();
        let mut files = Vec::from([CONTRACT, VECTORS, REPLAY].map(String::from))
            .into_iter()
            .zip([contract, SUM_VECTORS, SUM_REPLAY].map(String::from))
            .collect::<Vec<_>>();
        for file in lean::PROJECT_FILES {
            let path = format!("verification/{file}");
            let text = fs::read_to_string(repository.join(&path)).expect("a project file");
            files.push((path, text));
        }
        files
    }

    /// A repository with the fixture component and `contract` committed, the
    /// host results `results` and the Lake stand-in [`LAKE`].
    fn repository(label: &str, contract: &str, results: &str) -> Fixture {
        let fixture = Fixture::new(label);
        for (path, text) in component(contract) {
            fixture.write(&path, &text);
        }
        fixture.commit_all();
        fixture.write(RESULTS, results);
        lake(&fixture, "");
        fixture
    }

    /// A Lake stand-in that records each call and the environment of the
    /// replay, after the script `case`, and plays the program of the
    /// driver: it writes the id and the expected output of each vector, and
    /// an empty line for a line of another form.
    const LAKE: &str = r#"echo "$PWD $*" >> '@ROOT@/artifacts/lake-calls'
@CASE@
case $1 in
  build) echo 'Build completed successfully (1 jobs).' ;;
  env) env > '@ROOT@/artifacts/lake-env'
    awk -F '\t' '!/^#/ { print (NF == 3 ? $1 "\t" $3 : "") }' "$5" > "$6" ;;
esac"#;

    /// Installs [`LAKE`] in `fixture` with the script `case`.
    fn lake(fixture: &Fixture, case: &str) {
        let root = fixture.root().to_str().expect("a UTF-8 root");
        fixture.tool(
            "lake",
            &LAKE.replace("@ROOT@", root).replace("@CASE@", case),
        );
    }

    /// The run directories below `root`, in no order.
    fn runs(root: &Path) -> Vec<PathBuf> {
        let runs = fs::read_dir(root.join(run::RUNS)).into_iter().flatten();
        runs.map(|entry| entry.expect("a run directory").path())
            .collect()
    }

    /// The variable that makes the process of a test run
    /// `cargo xtask formal` with the root and the arguments that it holds,
    /// separated by tabs, and exit with the status of the command.
    const COMMAND: &str = "KREPI_XTASK_VECTORS";

    /// Runs the command of [`COMMAND`] if the variable is set.
    fn run_if_asked() {
        let Some(command) = std::env::var_os(COMMAND) else {
            return;
        };
        let command = command.into_string().expect("a UTF-8 command");
        let mut args = command.split('\t');
        let root = PathBuf::from(args.next().expect("a root"));
        let status = crate::formal::run(&root, &Vec::from_iter(args));
        let code = (0..=2).find(|code| ExitCode::from(*code) == status);
        std::process::exit(code.map_or(3, i32::from));
    }

    /// The exit status and the output lines of `cargo xtask formal vectors`
    /// with `args` in `root`, which the test `test` runs in the test
    /// executable started again.
    fn command_in(test: &str, root: &Path, args: &[&str]) -> (Option<i32>, Vec<String>) {
        let (_, tests) = module_path!()
            .split_once("::")
            .expect("a module path below the crate");
        let root = root.to_str().expect("a UTF-8 root");
        let command = Vec::from_iter([root, "vectors"].iter().chain(args).copied()).join("\t");
        let output = Command::new(std::env::current_exe().expect("the test executable"))
            .args([&format!("{tests}::{test}"), "--exact", "--nocapture"])
            .env(COMMAND, command)
            .stdin(Stdio::null())
            .output()
            .expect("run the test executable");
        let stdout = String::from_utf8(output.stdout).expect("UTF-8 output");
        let lines = stdout
            .lines()
            .filter(|line| !line.is_empty() && *line != "running 1 test");
        (output.status.code(), lines.map(String::from).collect())
    }

    /// The first line of the output of `cargo xtask formal vectors` in `root`.
    fn installation(root: &Path) -> String {
        let host = run::host().expect("a pinned host");
        let prefix = root.join("artifacts/formal/tools");
        format!("host {host}, installation {}", prefix.display())
    }

    #[test]
    fn a_result_that_differs_in_one_vector_fails_and_equal_results_pass() {
        run_if_asked();
        let test = "a_result_that_differs_in_one_vector_fails_and_equal_results_pass";
        let fixture = repository("vectors", &contract(BLOCK), SUM_RESULTS);
        let root = fixture.root();
        let failed =
            "FAILED fixture/sum: v2: the replay gives \"v2\\t0\", the host tests \"v2\\t1\"";
        let mut seen = Vec::new();
        for (results, code, lines) in [
            (SUM_RESULTS.to_string(), 0, vec!["1 components, 0 problems"]),
            (differing(), 1, vec![failed, "1 components, 1 problems"]),
        ] {
            fixture.write(RESULTS, &results);
            let (status, output) = command_in(test, root, &["fixture/sum"]);
            let head = [installation(root), "compared fixture/sum".to_string()];
            let expected =
                Vec::from_iter(head.into_iter().chain(lines.into_iter().map(String::from)));
            assert_eq!((status, output), (Some(code), expected));
            // Each comparison has a run directory of its own.
            let new = Vec::from_iter(runs(root).into_iter().filter(|run| !seen.contains(run)));
            let [run] = &new[..] else {
                panic!("{new:?}");
            };
            seen.push(run.clone());
            let stage = fs::canonicalize(run.join("work/stage/verification")).expect("the stage");
            let calls = fs::read_to_string(root.join("artifacts/lake-calls")).expect("the calls");
            let calls = Vec::from_iter(calls.lines().skip(2 * (seen.len() - 1)));
            let [vectors, results] = ["vectors", "results"].map(|file| run.join("work").join(file));
            assert_eq!(
                calls,
                [
                    format!(
                        "{} build --no-cache --wfail +Krepi.SpecTests.Fixture.Sum",
                        stage.display()
                    ),
                    format!(
                        "{} env lean --run Vectors.lean {} {}",
                        stage.display(),
                        vectors.display(),
                        results.display()
                    ),
                ]
            );
            assert_eq!(
                fs::read_to_string(&vectors).expect("the vectors"),
                SUM_VECTORS
            );
            let driver = fs::read_to_string(stage.join("Vectors.lean")).expect("the driver");
            let template = include_str!("vectors/Driver.lean");
            assert_eq!(
                driver,
                template.replace("KrepiVectorsReplay", "Krepi.SpecTests.Fixture.Sum")
            );
            assert!(
                driver.contains("\nimport Krepi.SpecTests.Fixture.Sum\n"),
                "{driver}"
            );
            // The replay ran with the environment of the gate and nothing else.
            let manifest = read(&root.join("verification/toolchain.json")).expect("the manifest");
            let manifest = toolchain::parse(&manifest).expect("the manifest parses");
            let [home, tmp] = ["home", "tmp"].map(|dir| run.join("work").join(dir));
            let host = run::host().expect("a pinned host");
            let env = environment::environment(
                Tool::LakeEnvLean,
                &manifest,
                host,
                root,
                &RunDirs { home, tmp },
            );
            let env = env.expect("the environment");
            let expected = BTreeMap::from_iter(
                env.vars()
                    .iter()
                    .map(|(name, value)| (*name, value.as_str())),
            );
            let recorded =
                fs::read_to_string(root.join("artifacts/lake-env")).expect("the environment");
            let shell = ["PWD", "SHLVL", "_"];
            let recorded = recorded.lines().filter_map(|line| line.split_once('='));
            let recorded = BTreeMap::from_iter(recorded.filter(|(name, _)| !shell.contains(name)));
            assert_eq!(recorded, expected);
        }
    }

    #[test]
    fn the_command_reports_and_exits() {
        run_if_asked();
        let test = "the_command_reports_and_exits";
        let fixture = Fixture::new("vectors-command");
        let root = fixture.root();
        let head = installation(root);
        let lines = |lines: &[&str]| {
            Vec::from_iter([head.as_str()].iter().chain(lines).map(|l| l.to_string()))
        };
        assert_eq!(
            command_in(test, root, &[]),
            (Some(0), lines(&["0 components, 0 problems"]))
        );
        let missing =
            "FAILED fixture/nope: docs/domains/fixture/nope/contract.md is not a tracked contract";
        assert_eq!(
            command_in(test, root, &["fixture/nope"]),
            (
                Some(1),
                lines(&["compared fixture/nope", missing, "1 components, 1 problems"])
            )
        );
        // A block without a replay is listed and not compared.
        let planned = BLOCK.replace("replay = \"Krepi.SpecTests.Fixture.Sum\"\n", "");
        for (path, text) in component(&contract(&planned)) {
            fixture.write(&path, &text);
        }
        fixture.commit_all();
        lake(&fixture, "");
        let unnamed = "not compared fixture/sum: it names no replay";
        assert_eq!(
            command_in(test, root, &[]),
            (Some(0), lines(&[unnamed, "0 components, 0 problems"]))
        );
        // With a replay, the component is compared without its name.
        fixture.write(CONTRACT, &contract(BLOCK));
        fixture.commit_all();
        fixture.write(RESULTS, SUM_RESULTS);
        assert_eq!(
            command_in(test, root, &[]),
            (
                Some(0),
                lines(&["compared fixture/sum", "1 components, 0 problems"])
            )
        );
        // A block that cannot be read fails the command, whichever contract holds it.
        fixture.write(
            "docs/domains/fixture/other/contract.md",
            &contract("```vectors\nvectors = 1\n```\n"),
        );
        fixture.commit_all();
        let (status, output) = command_in(test, root, &[]);
        assert_eq!(status, Some(1), "{output:?}");
        let failed = "FAILED docs/domains/fixture/other/contract.md: invalid type: integer `1`, \
            expected a string";
        assert_eq!(output, [failed, "0 components, 1 problems"]);
        assert_eq!(runs(root).len(), 1);
    }

    #[test]
    fn the_result_files_are_compared_in_order() {
        let vectors = "# Construction.\na\t1\t2\nb\t3\t4\n";
        let none = Vec::<String>::new();
        let same = |results: &str| compare(vectors, results, results);
        assert_eq!(
            compare(
                vectors,
                "a\t2\nb\t4\n",
                "# The host tests.\na\t2\n# b\nb\t4\n"
            ),
            none
        );
        assert_eq!(
            compare(vectors, "a\t2\nb\t4\n", "a\t2\nb\t5\n"),
            ["b: the replay gives \"b\\t4\", the host tests \"b\\t5\""]
        );
        assert_eq!(
            same("b\t4\na\t2\n"),
            [
                "a: the replay gives \"b\\t4\", the host tests \"b\\t4\"",
                "b: the replay gives \"a\\t2\", the host tests \"a\\t2\""
            ]
        );
        assert_eq!(
            compare(vectors, "a\t2\n", "a\t2\nb\t4\n"),
            ["b: the replay gives nothing, the host tests \"b\\t4\""]
        );
        assert_eq!(same("a\t2\nb\t4\nc\t5\n"), ["result 3: of no vector"]);
        assert_eq!(
            compare(vectors, "a\t2\nb\t4\nc\t5\n", "a\t2\nb\t4\n"),
            ["result 3: of no vector"]
        );
        // The vector file itself.
        assert_eq!(
            compare("# Construction.\n", "", ""),
            ["the vector file holds no vector"]
        );
        let twice = "# Construction.\na\t1\t2\na\t3\t4\n";
        assert_eq!(
            compare(twice, "a\t2\na\t4\n", "a\t2\na\t4\n"),
            ["vector 2: an id given twice"]
        );
        for unsourced in [
            "a\t1\t2\n",
            "#\na\t1\t2\n",
            "# \t \na\t1\t2\n",
            "\n# C.\na\t1\t2\n",
        ] {
            let problems = compare(unsourced, "a\t2\n", "a\t2\n");
            assert_eq!(
                problems[0], "the first line of the vector file names no source",
                "{unsourced:?}"
            );
        }
        for (malformed, results) in [
            ("# C.\na\t1\n", "a\t1\n"),
            ("# C.\na\t1\t2\t3\n", "a\t3\n"),
            ("# C.\n\t1\t2\n", "\t2\n"),
            ("# C.\n\n", ""),
        ] {
            assert_eq!(
                compare(malformed, results, results),
                ["vector 1: not an id, input and output"],
                "{malformed:?}"
            );
        }
        // A result with another field, which a tab in an output gives.
        assert_eq!(
            same("a\t2\tx\nb\t4\n"),
            ["a: the replay gives \"a\\t2\\tx\", the host tests \"a\\t2\\tx\""]
        );
        assert_eq!(
            same("a\nb\t4\n"),
            ["a: the replay gives \"a\", the host tests \"a\""]
        );
        // Outputs are text: a number above `u64::MAX` and another spelling of it.
        let large = "# C.\nv\ta=18446744073709551615 b=1\t18446744073709551616\n";
        assert_eq!(
            compare(
                large,
                "v\t18446744073709551616\n",
                "v\t18446744073709551616\n"
            ),
            none
        );
        for host in [
            "v\t18446744073709551616.0\n",
            "v\t18446744073709551615\n",
            "v\t18446744073709551616 \n",
        ] {
            assert_eq!(
                compare(large, "v\t18446744073709551616\n", host).len(),
                1,
                "{host:?}"
            );
        }
    }

    #[test]
    fn the_block_is_read_from_its_section() {
        let tree = |contract: &str| Tree::from_files(&[(CONTRACT, contract)]);
        let read = |contract: &str| block(&tree(contract), "fixture/sum");
        let named = read(&contract(BLOCK)).expect("a block").expect("a block");
        assert_eq!(named.vectors, VECTORS);
        assert_eq!(named.replay.as_deref(), Some("Krepi.SpecTests.Fixture.Sum"));
        let spaced = BLOCK
            .replace("```vectors\n", "  ```vectors \t\n")
            .replace("\n```\n", "\n ``` \n");
        assert!(read(&contract(&spaced)).expect("a block").is_some());
        // No block, and a block in another section.
        assert!(read(&contract("None yet.\n")).expect("no block").is_none());
        let elsewhere = format!("# Sum\n\n## Terms\n\n{BLOCK}\n## Legacy test vectors\n\nNone.\n");
        assert!(read(&elsewhere).expect("no block").is_none());
        let after = format!("# Sum\n\n## Legacy test vectors\n\nNone.\n\n## Terms\n\n{BLOCK}");
        assert!(read(&after).expect("no block").is_none());
        // A block that cannot be read, and any other fenced block of the section.
        for body in [
            BLOCK.replace("replay", "results = \"x\"\nreplay"),
            format!("{BLOCK}\n{BLOCK}"),
            BLOCK.replace("vectors = ", "vectors "),
            BLOCK.replace(
                "vectors = \"verification/vectors/fixture/sum.vectors\"\n",
                "",
            ),
            BLOCK.replace("\n```\n", "\n"),
            BLOCK
                .replace("```vectors", "~~~vectors")
                .replace("\n```\n", "\n~~~\n"),
            BLOCK
                .replace("```vectors", "````vectors")
                .replace("\n```\n", "\n````\n"),
            BLOCK.replace("```vectors", "``` vectors"),
            BLOCK.replace("```vectors", "```toml"),
            // A block that opens right and closes with another fence line.
            BLOCK.replace("\n```\n", "\n````\n"),
            BLOCK.replace("\n```\n", "\n```x\n"),
            BLOCK.replace("\n```\n", "\n``` x\n"),
            BLOCK.replace("\n```\n", "\n~~~\n"),
            format!("```text\nThe file.\n```\n\n{BLOCK}"),
            "```\nvectors = \"a\"\n```\n".to_string(),
        ] {
            assert!(read(&contract(&body)).is_err(), "{body}");
        }
        assert_eq!(
            block(&tree(&contract(BLOCK)), "fixture/other").map(|_| ()),
            Err("docs/domains/fixture/other/contract.md is not a tracked contract".to_string())
        );
        let nested = Tree::from_files(&[("docs/domains/a/b/c/contract.md", BLOCK)]);
        assert!(block(&nested, "a/b/c").is_err());
        // The replay module must be named, below the namespace and tracked.
        let compared = |block: &str, files: &[(&str, &str)]| {
            let contract = contract(block);
            let files = Vec::from_iter(
                [(CONTRACT, contract.as_str())]
                    .into_iter()
                    .chain(files.iter().copied()),
            );
            vectors(
                Path::new("/nonexistent"),
                &Layout::PRODUCTION,
                &Tree::from_files(&files),
                "fixture/sum",
                Instant::now(),
            )
        };
        let planned = BLOCK.replace("replay = \"Krepi.SpecTests.Fixture.Sum\"\n", "");
        let tracked = [(VECTORS, SUM_VECTORS), (REPLAY, SUM_REPLAY)];
        assert_eq!(
            compared(&planned, &tracked),
            Err("the vectors block names no replay module".to_string())
        );
        // The first four have their files tracked, so that only the rule of
        // the case refuses each: a name that is not a Lean module name, a
        // module outside the namespace, and one of the proofs, which lie
        // outside the statement side. The last two have no tracked file.
        for (module, file) in [
            ("Krepi.SpecTests/Fixture.Sum", REPLAY),
            ("KrepiGen.Sum", "verification/KrepiGen/Sum.lean"),
            ("Krepi", "verification/Krepi.lean"),
            ("Krepi.Proofs.Sum", "verification/Krepi/Proofs/Sum.lean"),
            (
                "Krepi.SpecTests.Fixture.Other",
                "verification/Krepi/SpecTests/Other.lean",
            ),
            ("Krepi.SpecTests.Fixture.Sum\nimport X", REPLAY),
        ] {
            let block = BLOCK.replace("Krepi.SpecTests.Fixture.Sum", &module.replace('\n', "\\n"));
            let files = Vec::from_iter(tracked.iter().copied().chain([(file, SUM_REPLAY)]));
            let expected = format!(
                "{module} is not a tracked module of the statement side in verification/Krepi/"
            );
            assert_eq!(compared(&block, &files), Err(expected), "{module:?}");
        }
        // A module of the statement side outside the conventional
        // `Krepi.SpecTests` passes these checks.
        let other = BLOCK.replace("SpecTests.Fixture.Sum", "Specs.Sum");
        let files = [
            (VECTORS, SUM_VECTORS),
            ("verification/Krepi/Specs/Sum.lean", SUM_REPLAY),
        ];
        let error = compared(&other, &files).expect_err("no host results");
        assert!(error.contains("sum.results: "), "{error}");
        assert_eq!(
            compared(BLOCK, &[(REPLAY, SUM_REPLAY)]),
            Err("the vector file is not tracked text".to_string())
        );
        // Every input is read before a tool runs: the host results here.
        let error = compared(BLOCK, &tracked).expect_err("no host results");
        assert!(
            error.starts_with("/nonexistent/artifacts/formal/vectors/fixture/sum.results: "),
            "{error}"
        );
    }

    #[test]
    fn a_replay_that_fails_does_not_compare() {
        let fixture = repository("vectors-failures", &contract(BLOCK), SUM_RESULTS);
        let root = fixture.root();
        let tree = Tree::load(root).expect("the tracked files");
        let compared = |end| vectors(root, &Layout::PRODUCTION, &tree, "fixture/sum", end);
        let long = || Instant::now() + Duration::from_secs(3_600);
        for (case, reason) in [
            (
                "[ $1 = build ] && echo 'error: Krepi/SpecTests/Fixture/Sum.lean:13:2: unknown' && exit 1",
                "build exited with 1: 1 errors or warnings in krepi's own modules",
            ),
            ("[ $1 = env ] && exit 3", "replay exited with 3"),
            (
                "[ $1 = env ] && echo 'PANIC at Krepi.SpecTests.Fixture.Sum.replay' >&2 && \
                 awk -F '\\t' '!/^#/ { print $1 \"\\t\" $3 }' \"$5\" > \"$6\" && exit 0",
                "replay: it wrote to its standard error",
            ),
            ("[ $1 = env ] && kill -9 $$", "replay was ended by signal 9"),
            (
                "[ $1 = env ] && exit 137",
                "replay: Lean was ended by signal 9",
            ),
        ] {
            lake(&fixture, case);
            let error = compared(long()).expect_err(case);
            assert!(
                error.starts_with(&format!("{reason}; its output is in {}/", root.display())),
                "{error}"
            );
            assert!(error.ends_with("/logs"), "{error}");
        }
        // The replay exits with 0 and writes no result file.
        lake(&fixture, "[ $1 = env ] && exit 0");
        let error = compared(long()).expect_err("no result file");
        assert!(
            error.ends_with("/work/results: No such file or directory (os error 2)"),
            "{error}"
        );
        // A command that hangs is stopped at the end of the budget.
        lake(&fixture, "[ $1 = build ] && exec sleep 30");
        let error = compared(Instant::now() + Duration::from_secs(1)).expect_err("a hang");
        assert!(
            error.starts_with("build ran longer than its limit of "),
            "{error}"
        );
        assert!(
            error.contains(" s, the rest of the budget of the gate, and was stopped; "),
            "{error}"
        );
        // No command starts once the budget is used up, and none before the
        // inputs are read.
        let calls = root.join("artifacts/lake-calls");
        fs::remove_file(&calls).expect("the calls");
        let error = compared(Instant::now()).expect_err("no budget");
        assert_eq!(error, "build: the budget was used up");
        fs::remove_file(root.join(RESULTS)).expect("the host results");
        let error = compared(long()).expect_err("no host results");
        assert!(
            error.starts_with(&format!("{}: ", root.join(RESULTS).display())),
            "{error}"
        );
        assert!(!calls.exists());
    }

    #[test]
    fn the_components_of_one_command_share_its_budget() {
        let fixture = repository("vectors-budget", &contract(BLOCK), SUM_RESULTS);
        let root = fixture.root();
        fixture.write("docs/domains/fixture/other/contract.md", &contract(BLOCK));
        fixture.commit_all();
        fixture.write(
            "artifacts/formal/vectors/fixture/other.results",
            SUM_RESULTS,
        );
        let head = installation(root);
        let compared = |budget| report(root, &Layout::PRODUCTION, None, budget);
        let both = [
            head.as_str(),
            "compared fixture/other",
            "compared fixture/sum",
        ];
        assert_eq!(compared(BUDGET), Ok(both.map(String::from).to_vec()));
        // The build of the first component hangs until the end of the budget
        // of the command, which leaves none for the second.
        lake(&fixture, "[ $1 = build ] && exec sleep 30");
        let lines = compared(Duration::from_secs(1)).expect("the lines");
        let [head, first, stopped, second, none] = &lines[..] else {
            panic!("{lines:?}");
        };
        assert_eq!([head, first, second], both);
        let stopped = stopped.strip_prefix("FAILED fixture/other: build ran longer than its limit");
        assert!(stopped.is_some(), "{lines:?}");
        assert_eq!(none, "FAILED fixture/sum: build: the budget was used up");
    }

    #[test]
    fn the_formal_workflow_runs_the_fixture_replay() {
        let workflow = include_str!("../../../.github/workflows/formal.yml");
        let steps = workflow.split("\n      - name: ");
        let step = steps
            .clone()
            .find(|step| step.starts_with("Compare the test vectors in the image\n"));
        let step = step.expect("the vectors step of the job formal run");
        let (_, tests) = module_path!()
            .split_once("::")
            .expect("a module path below the crate");
        let test = format!("{tests}::the_fixture_replays_with_the_pinned_lean");
        for text in [
            test.as_str(),
            "--exact --ignored --nocapture",
            "'^test result: ok\\. 1 passed; 0 failed'",
            "formal vectors",
        ] {
            assert!(step.contains(text), "{text}: {step}");
        }
        // The step compares on a change of the paths that the docs list,
        // since the merge base, and says that it compares nothing otherwise.
        let paths = ["kernel", "user", "verification", "docs/domains", "xtask"];
        let paths = Vec::from_iter(paths.map(|path| format!("`{path}/`")));
        let paths = [paths, vec!["`.github/workflows/formal.yml`".to_string()]].concat();
        let docs = include_str!("../../../docs/formal-verification.md");
        let (_, section) = docs
            .split_once("\n### Vectors in CI\n")
            .expect("the section");
        let section = section
            .split("\n### ")
            .next()
            .expect("the section")
            .replace('\n', " ");
        for path in &paths {
            assert!(section.contains(path), "{path}: {section}");
        }
        let paths = paths.join(" ").replace('`', "").replace("/ ", " ");
        let lines = Vec::from_iter(step.lines().map(str::trim));
        let listed = format!("paths=({paths})");
        let at = lines.iter().position(|line| *line == listed);
        let at = at.unwrap_or_else(|| panic!("{listed}: {step}"));
        let selected = "if git diff --quiet \"$merge_base\" \"$HEAD_SHA\" -- \"${paths[@]}\"; then";
        let nothing = "echo \"no change in the paths that select the comparison: 0 components\"";
        let merge_base = "merge_base=$(git merge-base \"$base\" \"$HEAD_SHA\")";
        let expected = [merge_base, &listed, selected, nothing, "else"];
        assert_eq!(lines[at - 1..at + 4], expected, "{step}");
        // Each container is removed when it ends, and ends within the step.
        assert_eq!(step.matches("docker run ").count(), 1, "{step}");
        assert!(
            step.contains("timeout --kill-after 1m \"$limit\" docker run --rm --name \"$name\""),
            "{step}"
        );
        assert!(step.contains("docker rm --force \"$name\""), "{step}");
    }

    /// The replay of the fixture by the pinned Lean, in a stage of the Lake
    /// project with the installation of the host: on CI in the image, whose
    /// prefix is absolute, and on darwin-arm64 with that of the checkout.
    #[test]
    #[ignore = "needs the pinned Lean"]
    fn the_fixture_replays_with_the_pinned_lean() {
        let scratch = Scratch::new("vectors-lean");
        let repository = crate::repo::root();
        let mut files = component(&contract(BLOCK));
        let manifest = fs::read_to_string(repository.join("verification/toolchain.json"));
        files.push((
            "verification/toolchain.json".to_string(),
            manifest.expect("the manifest"),
        ));
        for (path, text) in &files {
            scratch.write(path, text);
        }
        // The relative prefix of the darwin-arm64 column names the
        // installation of the checkout; that of the image is absolute.
        let tools = scratch.0.join("artifacts/formal/tools");
        fs::create_dir_all(scratch.0.join("artifacts/formal")).expect("a directory");
        std::os::unix::fs::symlink(repository.join("artifacts/formal/tools"), tools)
            .expect("a link");
        let tree = Tree::from_files(&Vec::from_iter(
            files
                .iter()
                .map(|(path, text)| (path.as_str(), text.as_str())),
        ));
        // The vector file with a blank line and lines of two and four fields
        // after its vectors.
        let malformed = format!("{SUM_VECTORS}\nv5\ta=1 b=2\nv6\ta=1 b=2\t3\tx\n");
        let malformed = Vec::from_iter(files.iter().map(|(path, text)| {
            let text = if path == VECTORS { &malformed } else { text };
            (path.as_str(), text.as_str())
        }));
        let malformed = Tree::from_files(&malformed);
        let end = Instant::now() + Duration::from_secs(300);
        let mut found = Vec::new();
        for (results, tree) in [
            (SUM_RESULTS.to_string(), &tree),
            (differing(), &tree),
            (SUM_RESULTS.to_string(), &malformed),
        ] {
            scratch.write(RESULTS, &results);
            found.push(vectors(
                &scratch.0,
                &Layout::PRODUCTION,
                tree,
                "fixture/sum",
                end,
            ));
        }
        for run in runs(&scratch.0) {
            for log in fs::read_dir(run.join("logs")).expect("the logs") {
                let log = log.expect("a log").path();
                println!(
                    "== {}\n{}",
                    log.display(),
                    fs::read_to_string(&log).unwrap_or_default()
                );
            }
            let results = fs::read_to_string(run.join("work/results")).unwrap_or_default();
            println!("== {}\n{results}", run.join("work/results").display());
        }
        let differs = "v2: the replay gives \"v2\\t0\", the host tests \"v2\\t1\"".to_string();
        let named = (4..=6).map(|at| format!("vector {at}: not an id, input and output"));
        assert_eq!(found, [Ok(vec![]), Ok(vec![differs]), Ok(named.collect())]);
    }
}
