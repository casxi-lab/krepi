//! The known-failures ledger, [`PATH`]: the tests known to fail, each with
//! the step of the check that runs it, the commit in which it first failed and
//! an opaque id of the finding that tracks it in the coordination records. The
//! steps that run libtest judge their tests against it ([`judge`]): the test
//! and release steps ([`run`]) and the host tests of the formal step.
//! `cargo xtask known-failures` writes it from a receipt ([`command`]).

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Arg, ArgAction, value_parser};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::lanes::{self, Stop};
use super::{Cmd, Facts, SLOW, Status, WORKSPACES};
use crate::formal::toolchain::is_hex;

/// The ledger, at the root of the repository and outside the gate inputs.
pub const PATH: &str = "known-failures.json";

/// The steps of the check that run libtest.
const STEPS: [&str; 3] = ["test", "test-release", "formal"];

/// An entry of the ledger. A test is named `workspace/executable/test`: the
/// test executable as Cargo names it without its hash, or `doc-tests <crate>`
/// for documentation tests, and the path or name that libtest reports.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    pub step: String,
    pub test: String,
    pub first_failed: String,
    pub finding: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Ledger {
    schema: u32,
    failures: Vec<Entry>,
}

/// The ledger of `entries`, as `cargo xtask known-failures` writes it.
pub fn render(entries: &[Entry]) -> String {
    let mut failures = entries.to_vec();
    failures.sort();
    let ledger = serde_json::json!({"schema": 1, "failures": failures});
    format!("{}\n", serde_json::to_string_pretty(&ledger).expect("JSON"))
}

/// The entries of the ledger `text`, which must be in the form that
/// [`render`] writes; a finding may be missing.
pub fn parse(text: &str) -> Result<Vec<Entry>, String> {
    let ledger: Ledger = serde_json::from_str(text).map_err(|error| format!("{PATH}: {error}"))?;
    let named = |e: &Entry| {
        let parts = Vec::from_iter(e.test.splitn(3, '/'));
        parts.len() == 3 && WORKSPACES.contains(&parts[0])
    };
    let known = |e: &&Entry| STEPS.contains(&&*e.step) && named(e) && is_hex(&e.first_failed, 40);
    if let Some(entry) = ledger.failures.iter().find(|entry| !known(entry)) {
        return Err(format!("{PATH}: a malformed entry: {entry:?}"));
    }
    if ledger.schema != 1 || render(&ledger.failures) != text {
        let form = "is not schema 1 in the form that `cargo xtask known-failures` writes";
        return Err(format!("{PATH}: {form}"));
    }
    Ok(ledger.failures)
}

/// The committed ledger of `root`, each entry with an opaque finding.
pub fn load(root: &Path) -> Result<Vec<Entry>, String> {
    let text = fs::read_to_string(root.join(PATH)).map_err(|error| format!("{PATH}: {error}"))?;
    let entries = parse(&text)?;
    let digits = |n: &str| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit());
    let opaque = |id: &str| id.strip_prefix("kd").is_some_and(digits);
    let unknown = |e: &&Entry| !e.finding.as_deref().is_some_and(opaque);
    match entries.iter().find(unknown) {
        Some(entry) => Err(format!("{PATH}: {} needs a finding like kd12", entry.test)),
        None => Ok(entries),
    }
}

/// The tests that a libtest command of `workspace` reported in `text`, with
/// whether each passed, but for the ignored tests and the failures section,
/// which holds the captured output of failed tests. `None` when a failure of
/// a command that did not pass cannot be put down to its tests: none failed,
/// or the last result line of an executable is missing or counts others.
pub fn results(workspace: &str, text: &str, passed: bool) -> Option<Vec<(String, bool)>> {
    let (mut tests, mut executable, mut failed) = (Vec::new(), String::new(), 0);
    let (mut result, mut details) = (Some(0), false);
    for line in text.lines() {
        let started = line.trim_start();
        let running = started
            .strip_prefix("Running ")
            .and_then(|r| r.rsplit_once('('));
        let doc = started.strip_prefix("Doc-tests ");
        if running.is_some() || doc.is_some() {
            let file = running.map(|(_, file)| file.trim_end_matches(')'));
            let stem = file.and_then(|file| Path::new(file).file_name()?.to_str());
            let stem = stem.map(|stem| stem.rsplit_once('-').map_or(stem, |(name, _)| name));
            let doc = || format!("doc-tests {}", doc.unwrap_or_default());
            executable = stem.map_or_else(doc, str::to_string);
            if result != Some(failed) {
                return None;
            }
            (failed, result, details) = (0, None, false);
        } else if let Some(counts) = line.strip_prefix("test result: ") {
            let count = counts
                .split("; ")
                .find_map(|part| part.strip_suffix(" failed"));
            result = count.and_then(|count| count.parse().ok());
        } else if line == "failures:" {
            details = true;
        } else if let Some((test, verdict)) = (line.strip_prefix("test ").filter(|_| !details))
            .and_then(|rest| rest.rsplit_once(" ... "))
            && (verdict == "ok" || verdict == "FAILED")
        {
            failed += usize::from(verdict == "FAILED");
            tests.push((format!("{workspace}/{executable}/{test}"), verdict == "ok"));
        }
    }
    let attributed = result == Some(failed) && (passed || tests.iter().any(|(_, ok)| !ok));
    attributed.then_some(tests)
}

/// Judges the results of `step` against `ledger`. Its facts are the count of
/// its tests, and, one per line, its failed tests and its stale tests: the
/// listed tests that passed or did not run, except, without `slow`, a slow
/// test, which runs only with `--slow`.
pub fn judge(
    step: &str,
    slow: bool,
    ledger: &[Entry],
    results: &[(String, bool)],
) -> (Status, Facts) {
    let listed = BTreeSet::from_iter(ledger.iter().filter(|e| e.step == step).map(|e| &e.test));
    let pick = |passed: bool, on: bool| {
        let picked = results
            .iter()
            .filter(|(t, ok)| *ok == passed && listed.contains(t) == on);
        Vec::from_iter(picked.map(|(test, _)| test.as_str()))
    };
    let ran = |test: &&&String| {
        results.iter().any(|(t, _)| t == **test) || (!slow && test.contains(SLOW))
    };
    let missing = listed
        .iter()
        .filter(|test| !ran(test))
        .map(|test| test.as_str());
    let (new, stale) = (
        pick(false, false),
        [pick(true, true), Vec::from_iter(missing)].concat(),
    );
    let failed = [pick(false, false), pick(false, true)].concat();
    let count = format!(
        "{} passed, {} failed",
        results.len() - failed.len(),
        failed.len()
    );
    let mut facts = vec![("tests".to_string(), count)];
    for (key, tests) in [("failed tests", &failed), ("stale tests", &stale)] {
        facts.extend((!tests.is_empty()).then(|| (key.to_string(), tests.join("\n"))));
    }
    let status = match (new.is_empty(), stale.is_empty()) {
        (false, _) => format!("tests failed that {PATH} does not list: {}", new.join(", ")),
        (_, false) => format!(
            "tests on {PATH} passed or did not run; delete their entries: {}",
            stale.join(", ")
        ),
        _ => return (Status::Passed, facts),
    };
    (Status::Failed(status), facts)
}

/// Runs the libtest command `cmd` and gives the tests that it reported, or
/// the status of its step when it did not run to its end or failed other
/// than in its tests.
pub fn tested(
    root: &Path,
    cmd: &Cmd,
    log: &Path,
    stop: &Stop,
) -> Result<Vec<(String, bool)>, Status> {
    let (passed, text) = lanes::tested(root, cmd, log, stop)?;
    let at = cmd.args.iter().position(|arg| arg == "--manifest-path");
    let manifest = at
        .and_then(|at| cmd.args.get(at + 1))
        .map_or("", String::as_str);
    let workspace = manifest.strip_suffix("/Cargo.toml").unwrap_or(manifest);
    let shown = cmd.args.join(" ");
    let failed = format!("`{shown}` failed, and not only in tests that it reported");
    results(workspace, &text, passed).ok_or(Status::Failed(failed))
}

/// The test and release steps: their libtest commands in order, each to its
/// end, judged against the committed ledger.
pub fn run(
    root: &Path,
    step: &str,
    commands: &[Cmd],
    log: &Path,
    stop: &Stop,
    facts: &mut Facts,
) -> Status {
    let judged = load(root).map_err(Status::Failed).and_then(|ledger| {
        let tests = commands.iter().map(|cmd| tested(root, cmd, log, stop));
        let tests = tests.collect::<Result<Vec<_>, _>>()?.concat();
        let slow = commands
            .iter()
            .any(|cmd| cmd.args.iter().any(|arg| arg == "--ignored"));
        Ok(judge(step, slow, &ledger, &tests))
    });
    let (status, judged) = judged.unwrap_or_else(|status| (status, Facts::new()));
    facts.extend(judged);
    status
}

/// The ledger that the receipt `receipt` of a check gives with `ledger`: for
/// each step of [`STEPS`] that recorded its tests, its entries but those of
/// its stale tests, and an entry for each failed test that it does not list,
/// with the commit of the receipt and the finding that `findings` gives, if
/// any; the other steps keep their entries.
pub fn generate(
    receipt: &Value,
    ledger: &[Entry],
    findings: &[(String, String)],
) -> Result<Vec<Entry>, String> {
    let commit = receipt["commit"]
        .as_str()
        .filter(|commit| is_hex(commit, 40));
    let commit = commit.ok_or_else(|| "the receipt names no commit".to_string())?;
    let lines = |step: &Value, key: &str| {
        let text = step["facts"][key].as_str().unwrap_or_default();
        Vec::from_iter(text.lines().map(str::to_string))
    };
    let recorded = |s: &&Value| {
        STEPS.contains(&s["name"].as_str().unwrap_or_default()) && s["facts"]["tests"].is_string()
    };
    let steps = Vec::from_iter(
        receipt["steps"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(recorded),
    );
    let of = |e: &Entry| steps.iter().find(|step| step["name"] == e.step.as_str());
    let kept = |e: &&Entry| of(e).is_none_or(|step| !lines(step, "stale tests").contains(&e.test));
    let mut entries = Vec::from_iter(ledger.iter().filter(kept).cloned());
    for step in &steps {
        let name = step["name"].as_str().unwrap_or_default().to_string();
        for test in lines(step, "failed tests") {
            if !ledger.iter().any(|e| e.step == name && e.test == test) {
                let finding = findings
                    .iter()
                    .find(|(t, _)| *t == test)
                    .map(|(_, id)| id.clone());
                let first_failed = commit.to_string();
                entries.push(Entry {
                    step: name.clone(),
                    test,
                    first_failed,
                    finding,
                });
            }
        }
    }
    Ok(entries)
}

/// `cargo xtask known-failures`.
pub fn command(root: &Path, args: &[&str]) -> ExitCode {
    let path = |id: &'static str, help| {
        let parser = value_parser!(PathBuf);
        Arg::new(id)
            .long(id)
            .value_name("PATH")
            .value_parser(parser)
            .help(help)
    };
    let finding = "The finding of a new failure, an opaque id: workspace/executable/test=ID";
    let cli = clap::Command::new("known-failures")
        .bin_name("cargo xtask known-failures")
        .no_binary_name(true)
        .about(
            "Write the known-failures ledger from the receipt of a check and the committed ledger",
        )
        .arg(path("receipt", "The receipt of a check").required(true))
        .arg(
            Arg::new("finding")
                .long("finding")
                .action(ArgAction::Append)
                .value_name("TEST=ID")
                .help(finding),
        )
        .arg(path(
            "output",
            "Where to write the ledger; standard output without it",
        ));
    let matches = match cli.try_get_matches_from(args) {
        Ok(matches) => matches,
        Err(error) => {
            let _ = error.print();
            return ExitCode::from(if error.use_stderr() { 2 } else { 0 });
        }
    };
    let given = matches.get_many::<String>("finding").into_iter().flatten();
    let pairs = given.filter_map(|given| given.rsplit_once('='));
    let findings = Vec::from_iter(pairs.map(|(test, id)| (test.to_string(), id.to_string())));
    let read =
        |path: &Path| fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()));
    let receipt = matches.get_one::<PathBuf>("receipt").expect("required");
    let written = read(receipt).and_then(|text| {
        let receipt: Value = serde_json::from_str(&text).map_err(|error| error.to_string())?;
        let ledger = parse(&read(&root.join(PATH))?)?;
        let text = render(&generate(&receipt, &ledger, &findings)?);
        match matches.get_one::<PathBuf>("output") {
            Some(path) => fs::write(path, text).map_err(|e| format!("{}: {e}", path.display())),
            None => {
                print!("{text}");
                Ok(())
            }
        }
    });
    match written {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("known-failures: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::super::lanes::run as run_steps;
    use super::super::{Action, Lane, Mode, Step};
    use super::*;
    use crate::scratch::Scratch;

    const KNOWN: &str = "kernel/krepi_kernel/fdt::tests::known";
    const COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";

    /// A libtest command of the kernel workspace whose executable reports
    /// `fdt::tests::known` with `verdict` and one passing test, and exits as
    /// libtest does.
    fn libtest(verdict: &str) -> Cmd {
        let failed = usize::from(verdict == "FAILED");
        let result = if failed == 1 { "FAILED" } else { "ok" };
        let lines = [
            "     Running unittests src/lib.rs (target/debug/deps/krepi_kernel-0123456789abcdef)"
                .to_string(),
            "running 2 tests".to_string(),
            format!("test fdt::tests::known ... {verdict}"),
            "test fdt::tests::fine ... ok".to_string(),
            format!("test result: {result}. 1 passed; {failed} failed; 0 ignored; 0 measured"),
        ];
        let quoted = Vec::from_iter(lines.iter().map(|line| format!("'{line}'")));
        let script = format!("printf '%s\\n' {}; exit {}", quoted.join(" "), failed * 101);
        let args = ["-c", &script, "sh", "--manifest-path", "kernel/Cargo.toml"];
        Cmd {
            program: "/bin/sh".into(),
            args: args.map(str::to_string).to_vec(),
        }
    }

    fn known(step: &str) -> Entry {
        Entry {
            step: step.to_string(),
            test: KNOWN.to_string(),
            first_failed: COMMIT.to_string(),
            finding: Some("kd1".to_string()),
        }
    }

    /// Runs the test and release steps with `cmd` in a repository whose
    /// ledger is `entries`.
    fn check(scratch: &Scratch, entries: &[Entry], cmd: &Cmd) -> Vec<Status> {
        scratch.write(PATH, &render(entries));
        let logs = scratch.0.join("logs");
        fs::create_dir_all(&logs).expect("the logs");
        let step = |name, lane| Step {
            name,
            lane,
            action: Action::Tests(vec![cmd.clone()]),
        };
        let steps = [
            step("test", Lane::Debug),
            step("test-release", Lane::Release),
        ];
        let run = run_steps(&scratch.0, &steps, Mode::Sequential, Ok(&logs));
        Vec::from_iter(run.outcomes.into_iter().map(|outcome| outcome.status))
    }

    #[test]
    fn a_failure_on_the_ledger_passes_the_check_in_each_step_that_runs_libtest() {
        let scratch = Scratch::new("ledger-known");
        let entries = STEPS.map(known);
        let statuses = check(&scratch, &entries, &libtest("FAILED"));
        assert_eq!(statuses, [Status::Passed, Status::Passed]);
        // The host tests of the formal step, judged as that step judges them.
        let log = scratch.0.join("logs/formal.log");
        let tests = tested(&scratch.0, &libtest("FAILED"), &log, &Stop::default());
        let ledger = load(&scratch.0).expect("the ledger");
        let (status, facts) = judge("formal", false, &ledger, &tests.expect("the tests"));
        assert_eq!(status, Status::Passed);
        let failed = ("failed tests".to_string(), KNOWN.to_string());
        assert!(facts.contains(&failed), "{facts:?}");
    }

    #[test]
    fn a_failure_off_the_ledger_fails_the_check() {
        let scratch = Scratch::new("ledger-new");
        let statuses = check(&scratch, &[], &libtest("FAILED"));
        let Status::Failed(detail) = &statuses[0] else {
            panic!("{statuses:?}")
        };
        assert!(
            detail.contains("does not list") && detail.contains(KNOWN),
            "{detail}"
        );
    }

    #[test]
    fn a_test_on_the_ledger_that_passes_fails_the_check() {
        let scratch = Scratch::new("ledger-fixed");
        let statuses = check(&scratch, &[known("test")], &libtest("ok"));
        let Status::Failed(detail) = &statuses[0] else {
            panic!("{statuses:?}")
        };
        assert!(
            detail.contains("delete their entries") && detail.contains(KNOWN),
            "{detail}"
        );
    }

    #[test]
    fn a_ledger_edited_by_hand_is_refused() {
        let text = render(&[known("test"), known("formal")]);
        assert_eq!(parse(&text), Ok(vec![known("formal"), known("test")]));
        // The same entries, written by hand in another order than the
        // generator's.
        let block = |step: &str| {
            let text = render(&[known(step)]);
            let list = text.split_once("[\n").expect("the list").1;
            list.rsplit_once("\n  ]").expect("its end").0.to_string()
        };
        let (test, formal) = (block("test"), block("formal"));
        let hand = format!("{{\n  \"schema\": 1,\n  \"failures\": [\n{test},\n{formal}\n  ]\n}}\n");
        let refused = parse(&hand).expect_err("refused");
        assert!(refused.contains("not schema 1 in the form"), "{refused}");
        // A finding that the coordination records do not give is refused by
        // the check, not by the generator.
        let scratch = Scratch::new("ledger-finding");
        let entry = Entry {
            finding: None,
            ..known("test")
        };
        scratch.write(PATH, &render(&[entry]));
        assert!(
            load(&scratch.0)
                .expect_err("refused")
                .contains("needs a finding")
        );
    }

    #[test]
    fn results_put_a_failure_down_to_tests_or_refuse_it() {
        let text = "   Doc-tests krepi_kernel\ntest src/lib.rs - a (line 3) ... ok\n\
                    test b ... ignored, slow\ntest result: ok. 1 passed; 0 failed; 1 ignored\n";
        let doc = "user/doc-tests krepi_kernel/src/lib.rs - a (line 3)".to_string();
        assert_eq!(results("user", text, true), Some(vec![(doc, true)]));
        // A failure without a failed test, such as a build error.
        assert_eq!(results("user", "error: could not compile\n", false), None);
        // A result line that counts another failure.
        let running = "     Running tests/a.rs (target/debug/deps/a-0a)\ntest t ... FAILED\n";
        let miscounted = format!("{running}test result: FAILED. 0 passed; 2 failed\n");
        assert_eq!(results("user", &miscounted, false), None);
        // An executable that ended without a result line, as on a signal.
        let crashed = format!("{running}     Running tests/b.rs (target/debug/deps/b-0b)\n");
        assert_eq!(results("user", &crashed, false), None);
        // The captured output of a failed test that holds a run of libtest
        // of its own belongs to the failures section.
        let nested = "test inner ... FAILED\ntest result: FAILED. 0 passed; 1 failed\n";
        let section = format!("\nfailures:\n\n---- t stdout ----\n{nested}\nfailures:\n    t\n\n");
        let text = format!("{running}{section}test result: FAILED. 0 passed; 1 failed\n");
        let t = ("user/a/t".to_string(), false);
        assert_eq!(results("user", &text, false), Some(vec![t]));
    }

    #[test]
    fn a_listed_test_that_did_not_run_fails_the_check_unless_it_is_slow() {
        let gone = Entry {
            test: "kernel/krepi_kernel/fdt::tests::gone".to_string(),
            ..known("test")
        };
        let slow = Entry {
            test: "kernel/krepi_kernel/fdt::tests::slow_walk".to_string(),
            ..known("test")
        };
        let results = [(KNOWN.to_string(), true)];
        let (status, _) = judge("test", false, std::slice::from_ref(&slow), &results);
        assert_eq!(status, Status::Passed);
        let Status::Failed(detail) = judge("test", false, &[gone, slow.clone()], &results).0 else {
            panic!("the step fails")
        };
        assert!(
            detail.contains("did not run") && detail.contains("::gone"),
            "{detail}"
        );
        assert!(!detail.contains("slow_walk"), "{detail}");
        // A check with --slow runs the slow tests.
        let (status, facts) = judge("test", true, std::slice::from_ref(&slow), &results);
        assert!(matches!(status, Status::Failed(_)), "{status:?}");
        let stale = ("stale tests".to_string(), slow.test.clone());
        assert!(facts.contains(&stale), "{facts:?}");
    }

    #[test]
    fn a_cargo_that_a_signal_ended_fails_the_step_even_after_a_listed_failure() {
        let scratch = Scratch::new("ledger-signal");
        let mut cmd = libtest("FAILED");
        cmd.args[1] = cmd.args[1].replace("exit 101", "kill -9 $$");
        let statuses = check(&scratch, &[known("test")], &cmd);
        let Status::Failed(detail) = &statuses[0] else {
            panic!("{statuses:?}")
        };
        assert!(detail.contains("exited with"), "{detail}");
    }

    #[test]
    fn the_generator_drops_stale_entries_and_adds_new_failures() {
        let new = "kernel/krepi_kernel/fdt::tests::new";
        let slow = Entry {
            test: "kernel/krepi_kernel/fdt::tests::slow_walk".to_string(),
            ..known("test")
        };
        let receipt = json!({
            "commit": "ab".repeat(20),
            "steps": [
                {"name": "test", "facts": {"tests": "1 passed, 2 failed", "failed tests": format!("{KNOWN}\n{new}")}},
                {"name": "test-release", "facts": {"tests": "2 passed, 0 failed", "stale tests": KNOWN}},
                {"name": "formal", "facts": {}},
            ],
        });
        let ledger = [
            known("test"),
            known("test-release"),
            known("formal"),
            slow.clone(),
        ];
        let findings = [(new.to_string(), "kd2".to_string())];
        let generated = generate(&receipt, &ledger, &findings).expect("the ledger");
        let added = Entry {
            test: new.to_string(),
            first_failed: "ab".repeat(20),
            finding: Some("kd2".into()),
            ..known("test")
        };
        // The listed failure keeps its entry once, the slow test that did not
        // run keeps its own, the release step's fixed test is dropped and the
        // formal step, which recorded no tests, keeps its entry.
        let mut expected = vec![known("test"), known("formal"), slow, added];
        expected.sort();
        let mut generated = generated;
        generated.sort();
        assert_eq!(generated, expected);
    }

    #[test]
    fn the_committed_ledger_is_in_the_form_of_the_generator() {
        assert!(load(&crate::repo::root()).is_ok());
    }
}
