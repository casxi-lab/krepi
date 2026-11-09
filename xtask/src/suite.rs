//! `cargo xtask suite`: the QEMU suites of `suites.toml`, each case run on
//! QEMU virt through the QEMU runner and judged by its expected output.
//!
//! ```sh
//! cargo xtask suite [--base REV] [--slow] [--images DIR --expect NAME=SHA256]... \
//!     [--qemu PATH] [--output-dir DIR]
//! ```
//!
//! # Manifest
//!
//! [`MANIFEST`] at the repository root lists the suites. Each `[[suite]]`
//! has a `name`, the `image` source of [`crate::image::SOURCES`] that it
//! boots, the `paths`, prefixes of repository paths below `kernel/` or
//! `user/` whose change selects it on a pull request, and its cases. Each
//! `[[suite.case]]` has a `name`, whether it is a `smoke` case, which every
//! pull request runs, whether it is `slow`, which only `--slow` runs, the
//! cold boots of the case (`runs`, 1 to [`MAX_RUNS`]) and the limit of one
//! run in seconds (`timeout`, 1 to 600). A case is not both smoke and slow;
//! names are unique and made of lowercase letters, digits and hyphens.
//!
//! # Selection
//!
//! With `--base REV`, the command takes the merge base of `REV` and `HEAD`
//! and the paths that `git diff --name-only --no-renames` gives between it
//! and `HEAD`, both sides of a rename or deletion included, and maps each
//! path by prefix as [`mapping`] does: a path below `tools/` or `xtask/`, the
//! toolchain files, `.cargo/`, the manifest or `.github/workflows/` other
//! than the files that start with `.github/workflows/formal` selects every
//! suite; a path below `kernel/` or `user/` selects the suites that list a
//! prefix of it; any other path selects none. The smoke cases run whatever
//! the paths, and a selected suite runs its other cases that are not slow.
//! Without `--base`, every suite runs its cases that are not slow. `--slow`
//! adds the slow cases of the suites that run.
//!
//! # Images and runs
//!
//! With `--images DIR`, the images come from `DIR/images.json`, the record
//! of `cargo xtask image`, and every image that a selected case boots needs
//! an `--expect NAME=SHA256`. The command computes the SHA-256 of each file
//! and requires it to equal the record's and the expected digest; any
//! difference, a missing entry or file, or a missing `--expect` ends the
//! run as `ERROR` before QEMU starts. Without `--images`, the command writes
//! the images into `images/` of its output directory as `cargo xtask image`
//! does.
//!
//! Each run of a case boots its image in a new QEMU process through
//! `krepi_tools::qemu_run::run_image`, with the host clock, the case's
//! `timeout` and [`MAX_BYTES`] bytes of serial output, into
//! `<suite>/<case>-<n>` of the output directory. A run passes when its
//! receipt has no errors, it ended as `guest_shutdown`, it booted the image
//! with the expected digest, its receipt describes its transcript and the
//! transcript is the expected output of the image; for the test image that
//! is `krepi_tools::test_elf::MESSAGE`. A case of more than one run also
//! needs equal exit reasons and identical transcripts.
//!
//! # Report and status
//!
//! The command creates the output directory, which must not exist, by
//! default `artifacts/suite/<UTC time>Z-<process ID>`, and writes
//! [`SUMMARY_FILE`] into it: the status, the times, the commit, the GitHub
//! Actions run, the selection with the changed paths, the images with their
//! digests, and each suite with why it runs and its selected cases, each
//! with why it runs, its runs and its checks. Cases that were not selected
//! are not listed. It prints a line for each suite, case and run, each
//! failed check and the status with the path of the report, and exits with
//! 0 for `PASS`, 1 for `FAIL`, 2 for `ERROR` and for a usage error, 130 for
//! `INTERRUPTED` and 120 when it cannot write its own output. Changed paths
//! are printed with their control characters escaped. SIGINT, SIGTERM and
//! SIGHUP are caught from immediately before the first QEMU starts, as by
//! the runner, and end the run that is under way and the suite.

use std::collections::BTreeSet;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::atomic::AtomicI32;

use clap::{Arg, ArgAction, value_parser};
use krepi_tools::qemu::Clock;
use krepi_tools::qemu_run::{self, Options};
use krepi_tools::report::{Value, utc_now};
use krepi_tools::timing::Timing;
use serde::Deserialize;
use serde_json::json;

use crate::formal::toolchain::sha256;
use crate::image::{self, Record};

/// The suite manifest at the repository root.
pub const MANIFEST: &str = "suites.toml";
/// The report in the output directory.
pub const SUMMARY_FILE: &str = "summary.json";
/// The version of the report format.
pub const FORMAT: u32 = 1;
/// The serial output limit of one run.
pub const MAX_BYTES: u64 = 4096;
/// The most runs of one case.
pub const MAX_RUNS: u32 = 10;
/// The output directories below the repository root.
const OUTPUT_DIR: &str = "artifacts/suite";

/// The prefixes of the paths whose change selects every suite: the host
/// tooling, the repository tasks, the toolchain files, the Cargo
/// configuration, the manifest and the workflows other than the formal ones.
pub const EVERY_SUITE: [&str; 7] = [
    "tools/",
    "xtask/",
    "rust-toolchain.toml",
    "toolchains.toml",
    ".cargo/",
    MANIFEST,
    ".github/workflows/",
];
/// The prefix of the workflows of the proof tooling, which select no suite.
pub const FORMAL_WORKFLOWS: &str = ".github/workflows/formal";
/// The workspaces below which a suite lists the paths that select it.
pub const LISTED: [&str; 2] = ["kernel/", "user/"];

/// One suite of the manifest.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Suite {
    pub name: String,
    pub image: String,
    pub paths: Vec<String>,
    #[serde(rename = "case")]
    pub cases: Vec<Case>,
}

/// One case of a suite.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Case {
    pub name: String,
    pub smoke: bool,
    pub slow: bool,
    pub runs: u32,
    pub timeout: u32,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    suite: Vec<Suite>,
}

/// Whether `name` is made of lowercase letters, digits and hyphens.
fn plain_name(name: &str) -> bool {
    !name.is_empty()
        && (name.bytes())
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
}

/// The suites of the manifest `text`, which must keep the rules of the
/// module documentation.
pub fn load(text: &str) -> Result<Vec<Suite>, String> {
    let manifest: Manifest =
        toml::from_str(text).map_err(|error| format!("{MANIFEST}: {error}"))?;
    let mut problems = Vec::new();
    if manifest.suite.is_empty() {
        problems.push("no suite".to_string());
    }
    let mut names = BTreeSet::new();
    for suite in &manifest.suite {
        let name = &suite.name;
        if !plain_name(name) {
            problems.push(format!("the suite name {name:?} is not plain"));
        }
        if !names.insert(name.as_str()) {
            problems.push(format!("the suite {name} occurs twice"));
        }
        if image::source(&suite.image).is_none() {
            problems.push(format!("suite {name}: no image source {}", suite.image));
        }
        for path in &suite.paths {
            if !LISTED.iter().any(|workspace| path.starts_with(workspace)) {
                problems.push(format!(
                    "suite {name}: the path {path} is not below {}",
                    LISTED.join(" or ")
                ));
            }
        }
        if suite.cases.is_empty() {
            problems.push(format!("suite {name}: no case"));
        }
        let mut cases = BTreeSet::new();
        for case in &suite.cases {
            let case_name = &case.name;
            let at = format!("suite {name}, case {case_name:?}");
            if !plain_name(case_name) {
                problems.push(format!("{at}: the name is not plain"));
            }
            if !cases.insert(case_name.as_str()) {
                problems.push(format!("{at}: the case occurs twice"));
            }
            if case.smoke && case.slow {
                problems.push(format!("{at}: a smoke case is not slow"));
            }
            if !(1..=MAX_RUNS).contains(&case.runs) {
                problems.push(format!("{at}: runs is not 1 to {MAX_RUNS}"));
            }
            if !(1..=qemu_run::MAX_TIMEOUT as u32).contains(&case.timeout) {
                problems.push(format!("{at}: timeout is not 1 to 600 seconds"));
            }
        }
    }
    if problems.is_empty() {
        Ok(manifest.suite)
    } else {
        Err(format!("{MANIFEST}: {}", problems.join("; ")))
    }
}

/// What a changed path selects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Selects {
    /// Every suite, by this prefix.
    Every(&'static str),
    /// The suites that list a prefix of the path below this workspace.
    Listed(&'static str),
    /// No suite.
    Nothing,
}

/// The row of the mapping that the changed path `path` falls in.
pub fn mapping(path: &str) -> Selects {
    if path.starts_with(FORMAL_WORKFLOWS) {
        return Selects::Nothing;
    }
    if let Some(prefix) = EVERY_SUITE.iter().find(|prefix| path.starts_with(**prefix)) {
        return Selects::Every(prefix);
    }
    match LISTED
        .iter()
        .find(|workspace| path.starts_with(**workspace))
    {
        Some(workspace) => Selects::Listed(workspace),
        None => Selects::Nothing,
    }
}

/// The prefix by which the changed path `path` selects `suite`, if it does.
pub fn selects(suite: &Suite, path: &str) -> Option<String> {
    match mapping(path) {
        Selects::Every(prefix) => Some(prefix.to_string()),
        Selects::Listed(_) => (suite.paths.iter())
            .find(|prefix| path.starts_with(prefix.as_str()))
            .cloned(),
        Selects::Nothing => None,
    }
}

/// Why a suite runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Why {
    /// No `--base`: every suite runs.
    Every,
    /// The changed paths that select it, each with its prefix; none when
    /// only its smoke cases run.
    Paths(Vec<(String, String)>),
}

/// A case that runs and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chosen<'a> {
    pub case: &'a Case,
    pub reasons: Vec<&'static str>,
}

/// A suite with why it runs and its cases that run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan<'a> {
    pub suite: &'a Suite,
    pub why: Why,
    pub cases: Vec<Chosen<'a>>,
}

/// The cases of `suites` that run for the changed paths `changed`, or for
/// every suite without them, with the slow cases when `slow` holds.
pub fn choose<'a>(suites: &'a [Suite], changed: Option<&[String]>, slow: bool) -> Vec<Plan<'a>> {
    (suites.iter())
        .map(|suite| {
            let why = match changed {
                None => Why::Every,
                Some(paths) => Why::Paths(
                    (paths.iter())
                        .filter_map(|path| {
                            selects(suite, path).map(|prefix| (path.clone(), prefix))
                        })
                        .collect(),
                ),
            };
            let selected = match &why {
                Why::Every => true,
                Why::Paths(paths) => !paths.is_empty(),
            };
            let cases = (suite.cases.iter())
                .filter_map(|case| {
                    let mut reasons = Vec::new();
                    if changed.is_some() && case.smoke {
                        reasons.push("smoke case");
                    }
                    if selected && (slow || !case.slow) {
                        reasons.push(match why {
                            Why::Every => "every suite runs",
                            Why::Paths(_) => "the changed paths select its suite",
                        });
                    }
                    if case.slow && !reasons.is_empty() {
                        reasons.push("slow cases run");
                    }
                    (!reasons.is_empty()).then_some(Chosen { case, reasons })
                })
                .collect();
            Plan { suite, why, cases }
        })
        .collect()
}

/// Runs git in `root` and returns its standard output.
fn git(root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|error| format!("cannot run git: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output.stdout)
}

/// The merge base of `base` and `HEAD` in `root` and the paths that differ
/// between it and `HEAD`, both sides of a rename included.
pub fn changed(root: &Path, base: &str) -> Result<(String, Vec<String>), String> {
    if base.starts_with('-') || base.is_empty() {
        return Err(format!("{base:?} is not a revision"));
    }
    let merge_base = git(root, &["merge-base", base, "HEAD"])?;
    let merge_base = String::from_utf8_lossy(&merge_base).trim().to_string();
    let diff = [
        "diff",
        "--name-only",
        "--no-renames",
        "-z",
        &merge_base,
        "HEAD",
    ];
    let paths = git(root, &diff)?;
    let paths = (paths.split(|&byte| byte == 0))
        .filter(|path| !path.is_empty())
        .map(|path| String::from_utf8_lossy(path).into_owned())
        .collect();
    Ok((merge_base, paths))
}

/// An image that the cases boot, with its digest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ready {
    pub name: String,
    pub path: PathBuf,
    pub bytes: u64,
    pub sha256: String,
    /// The digest that `--expect` gave, if the images came from a record.
    pub expected: Option<String>,
}

/// The images `needed` from the record in `dir`, each checked against the
/// file and against its digest in `expect`.
pub fn take_images(
    dir: &Path,
    needed: &BTreeSet<&str>,
    expect: &[(String, String)],
) -> Result<Vec<Ready>, Vec<String>> {
    let path = dir.join(image::RECORD);
    let record = fs::read_to_string(&path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))
        .and_then(|text| {
            Record::parse(&text).map_err(|error| format!("{}: {error}", path.display()))
        })
        .map_err(|error| vec![error])?;
    let mut ready = Vec::new();
    let mut problems = Vec::new();
    for name in needed {
        let Some(entry) = record.image(name) else {
            problems.push(format!("{} names no image {name}", path.display()));
            continue;
        };
        let expected = (expect.iter()).find(|(image, _)| image == name);
        let Some((_, expected)) = expected else {
            problems.push(format!("no --expect {name}=<SHA-256> is given"));
            continue;
        };
        if entry.file.is_empty() || entry.file.contains('/') || entry.file.starts_with('.') {
            problems.push(format!(
                "the file {:?} of {name} is not a plain name",
                entry.file
            ));
            continue;
        }
        let file = dir.join(&entry.file);
        let (sha256, bytes) = match image::digest(&file) {
            Ok(digest) => digest,
            Err(error) => {
                problems.push(error);
                continue;
            }
        };
        if sha256 != entry.sha256 || bytes != entry.bytes {
            problems.push(format!(
                "{name}: the file has {bytes} bytes with SHA-256 {sha256}, the record {} bytes with {}",
                entry.bytes, entry.sha256
            ));
        }
        if &sha256 != expected {
            problems.push(format!(
                "{name}: the SHA-256 of the file is {sha256}, not the expected {expected}"
            ));
        }
        ready.push(Ready {
            name: name.to_string(),
            path: file,
            bytes,
            sha256,
            expected: Some(expected.clone()),
        });
    }
    if problems.is_empty() {
        Ok(ready)
    } else {
        Err(problems)
    }
}

/// The output that the image `image` writes when it boots and passes.
pub fn expected_output(image: &str) -> Option<&'static [u8]> {
    match image {
        "test-elf" => Some(krepi_tools::test_elf::MESSAGE),
        _ => None,
    }
}

/// One check of a case: its name and why it failed, if it did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    pub name: String,
    pub failure: Option<String>,
}

impl Check {
    fn of(name: impl Into<String>, failure: Option<String>) -> Check {
        Check {
            name: name.into(),
            failure,
        }
    }

    fn report(&self) -> Value {
        match &self.failure {
            None => json!({"name": self.name, "status": "PASS"}),
            Some(detail) => json!({"name": self.name, "status": "FAIL", "detail": detail}),
        }
    }
}

/// One run of a case: the receipt of the runner and the transcript.
#[derive(Debug, Clone, PartialEq)]
pub struct Run {
    pub receipt: Value,
    pub transcript: Vec<u8>,
}

/// The first of `failures` that holds, if one does.
fn first(failures: impl IntoIterator<Item = (bool, String)>) -> Option<String> {
    (failures.into_iter()).find_map(|(failed, message)| failed.then_some(message))
}

/// The checks of `case` over its `runs` of the image `image` with the
/// digest `sha256`.
pub fn judge(image: &str, sha256_expected: &str, case: &Case, runs: &[Run]) -> Vec<Check> {
    let output = expected_output(image).unwrap_or_default();
    let mut checks = Vec::new();
    for (at, run) in runs.iter().enumerate() {
        let receipt = &run.receipt;
        let number = at + 1;
        checks.push(Check::of(
            format!("run {number} receipt"),
            first([
                (
                    receipt.get("errors").is_some(),
                    format!("the run has errors: {}", receipt["errors"]),
                ),
                (
                    receipt["exit_reason"] != "guest_shutdown",
                    format!(
                        "the run ended as {}, not as guest_shutdown",
                        receipt["exit_reason"]
                    ),
                ),
                (
                    receipt["image"]["sha256"] != sha256_expected,
                    format!(
                        "the run booted an image with SHA-256 {}, not {sha256_expected}",
                        receipt["image"]["sha256"]
                    ),
                ),
                (
                    receipt["transcript"]["sha256"] != sha256(&run.transcript).as_str(),
                    "the receipt does not describe the transcript".to_string(),
                ),
            ]),
        ));
        checks.push(Check::of(
            format!("run {number} transcript"),
            (run.transcript != output).then(|| {
                format!(
                    "the transcript is {}, not {}",
                    run.transcript.escape_ascii(),
                    output.escape_ascii()
                )
            }),
        ));
    }
    let count = usize::try_from(case.runs).unwrap_or(usize::MAX);
    checks.push(Check::of(
        "runs",
        (runs.len() != count).then(|| format!("{} runs, not {count}", runs.len())),
    ));
    if count > 1 {
        let reasons = runs
            .windows(2)
            .all(|pair| pair[0].receipt["exit_reason"] == pair[1].receipt["exit_reason"]);
        checks.push(Check::of(
            "equal exit reasons",
            (!reasons).then(|| "the runs ended for different reasons".to_string()),
        ));
        let transcripts = (runs.windows(2)).all(|pair| pair[0].transcript == pair[1].transcript);
        checks.push(Check::of(
            "identical transcripts",
            (!transcripts).then(|| "the transcripts of the runs differ".to_string()),
        ));
    }
    checks
}

/// How a case or the suite ended, from best to worst.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Outcome {
    Pass,
    Fail,
    Error,
    Interrupted,
}

impl Outcome {
    pub fn name(self) -> &'static str {
        match self {
            Outcome::Pass => "PASS",
            Outcome::Fail => "FAIL",
            Outcome::Error => "ERROR",
            Outcome::Interrupted => "INTERRUPTED",
        }
    }

    pub fn code(self) -> u8 {
        match self {
            Outcome::Pass => 0,
            Outcome::Fail => 1,
            Outcome::Error => 2,
            Outcome::Interrupted => 130,
        }
    }
}

/// Runs `case` of `suite` on `image` with the QEMU `qemu`, each run into
/// `<output>/<suite>/<case>-<n>`: its entry of the report and its outcome.
/// `say` gets a line for each run. A run that cannot start ends the case as
/// `Error`, and an interrupted run as `Interrupted`, without the runs after
/// it.
#[allow(clippy::too_many_arguments)]
pub fn run_case<'a>(
    suite: &Suite,
    chosen: &Chosen,
    image: &Ready,
    qemu: Option<&Path>,
    output: &Path,
    timing: &Timing,
    arm: &mut dyn FnMut() -> Result<&'a AtomicI32, krepi_tools::Failure>,
    say: &mut dyn FnMut(&str),
) -> (Value, Outcome) {
    let case = chosen.case;
    let options = Options {
        image: image.path.clone(),
        timeout: f64::from(case.timeout),
        max_bytes: MAX_BYTES,
        clock: Clock::Host,
        qemu: qemu.map(Path::to_path_buf),
        output: None,
    };
    let mut runs = Vec::new();
    let mut entries = Vec::new();
    let mut stopped = None;
    for number in 1..=case.runs {
        let name = format!("{}/{}-{number}", suite.name, case.name);
        let directory = output.join(&name);
        let receipt = match qemu_run::run_image(&options, &directory, timing, arm) {
            Ok(receipt) => receipt,
            Err(failure) => {
                say(&format!(
                    "{name}: the run could not start: {}",
                    printable(&failure.0)
                ));
                entries.push(json!({"directory": name, "error": failure.0}));
                stopped = Some(Outcome::Error);
                break;
            }
        };
        let transcript = fs::read(directory.join(qemu_run::TRANSCRIPT_FILE)).unwrap_or_default();
        let reason = receipt["exit_reason"]
            .as_str()
            .unwrap_or("error")
            .to_string();
        say(&format!(
            "{name}: {reason}, {} bytes of serial output",
            transcript.len()
        ));
        entries.push(json!({
            "directory": name,
            "exit_reason": reason,
            "receipt_sha256": sha256(format!("{receipt:#}\n").as_bytes()),
            "transcript_sha256": sha256(&transcript),
        }));
        runs.push(Run {
            receipt,
            transcript,
        });
        if reason == "interrupted" {
            stopped = Some(Outcome::Interrupted);
            break;
        }
    }
    let checks = judge(&suite.image, &image.sha256, case, &runs);
    let outcome = stopped.unwrap_or(if checks.iter().all(|check| check.failure.is_none()) {
        Outcome::Pass
    } else {
        Outcome::Fail
    });
    let entry = json!({
        "name": case.name,
        "smoke": case.smoke,
        "slow": case.slow,
        "runs": case.runs,
        "timeout": case.timeout,
        "reasons": chosen.reasons,
        "status": outcome.name(),
        "results": entries,
        "checks": checks.iter().map(Check::report).collect::<Vec<_>>(),
    });
    (entry, outcome)
}

/// The options of `cargo xtask suite`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Choice {
    pub base: Option<String>,
    pub slow: bool,
    pub images: Option<PathBuf>,
    pub expect: Vec<(String, String)>,
    pub qemu: Option<PathBuf>,
    pub output: Option<PathBuf>,
}

/// An `--expect` value: an image name, `=` and a SHA-256 in lowercase
/// hexadecimal.
fn expectation(value: &str) -> Result<(String, String), String> {
    let (name, digest) = value
        .split_once('=')
        .ok_or_else(|| "write NAME=SHA256".to_string())?;
    let hex = digest.len() == 64
        && (digest.bytes()).all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'));
    if !plain_name(name) || !hex {
        return Err("write NAME=SHA256 with a lowercase hexadecimal SHA-256".to_string());
    }
    Ok((name.to_string(), digest.to_string()))
}

/// The command line of `cargo xtask suite`.
fn cli() -> clap::Command {
    let about = (crate::COMMANDS.iter())
        .find(|command| command.name == "suite")
        .map_or("", |command| command.about);
    let path = |name: &'static str, value: &'static str, help: &'static str| {
        Arg::new(name)
            .long(name)
            .value_name(value)
            .help(help)
            .value_parser(value_parser!(PathBuf))
    };
    clap::Command::new("suite")
        .bin_name("cargo xtask suite")
        .no_binary_name(true)
        .about(about)
        .arg(
            Arg::new("base")
                .long("base")
                .value_name("REV")
                .help("Run the smoke cases and the suites that the paths changed since the merge base of REV and HEAD select"),
        )
        .arg(
            Arg::new("slow")
                .long("slow")
                .help("Also run the slow cases")
                .action(ArgAction::SetTrue),
        )
        .arg(path(
            "images",
            "DIR",
            "Take the images from DIR/images.json, the record of cargo xtask image",
        ))
        .arg(
            Arg::new("expect")
                .long("expect")
                .value_name("NAME=SHA256")
                .help("The SHA-256 that the image NAME of --images must have")
                .action(ArgAction::Append)
                .requires("images")
                .value_parser(expectation),
        )
        .arg(path(
            "qemu",
            "PATH",
            "QEMU executable; qemu-system-aarch64 on the search path without it",
        ))
        .arg(path(
            "output-dir",
            "DIR",
            "New directory for the runs and the report; must not exist",
        ))
}

/// The options in `args`, or clap's error.
pub fn parse(args: &[&str]) -> Result<Choice, clap::Error> {
    let matches = cli().try_get_matches_from(args)?;
    let path = |name: &str| matches.get_one::<PathBuf>(name).cloned();
    Ok(Choice {
        base: matches.get_one::<String>("base").cloned(),
        slow: matches.get_flag("slow"),
        images: path("images"),
        expect: (matches.get_many::<(String, String)>("expect"))
            .map(|values| values.cloned().collect())
            .unwrap_or_default(),
        qemu: path("qemu"),
        output: path("output-dir"),
    })
}

/// `text` with its control characters escaped, so that a line printed from
/// it stays one line.
pub fn printable(text: &str) -> String {
    (text.chars())
        .map(|character| {
            if character.is_control() {
                character.escape_default().to_string()
            } else {
                character.to_string()
            }
        })
        .collect()
}

/// The output streams of the command: a line that cannot be written makes
/// the status 120. The tests keep the lines instead.
#[derive(Default)]
struct Out {
    failed: bool,
    kept: Option<Vec<String>>,
}

impl Out {
    fn say(&mut self, text: &str) {
        match &mut self.kept {
            Some(lines) => lines.push(text.to_string()),
            None => {
                if writeln!(io::stdout().lock(), "{text}").is_err() {
                    self.failed = true;
                }
            }
        }
    }

    fn warn(&mut self, text: &str) {
        match &mut self.kept {
            Some(lines) => lines.push(format!("error: {text}")),
            None => {
                if writeln!(io::stderr().lock(), "{text}").is_err() {
                    self.failed = true;
                }
            }
        }
    }
}

/// Entry point of `cargo xtask suite`.
pub fn command(root: &Path, args: &[&str]) -> ExitCode {
    let choice = match parse(args) {
        Ok(choice) => choice,
        Err(error) => {
            let _ = error.print();
            return ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(2));
        }
    };
    let mut out = Out::default();
    let code = run(
        root,
        &choice,
        &Timing::QEMU_VIRT,
        &mut || krepi_tools::tty::catch_interrupts(),
        &mut out,
    );
    ExitCode::from(if out.failed { 120 } else { code })
}

/// One suite run with `choice` in `root`: its exit status.
fn run<'a>(
    root: &Path,
    choice: &Choice,
    timing: &Timing,
    arm: &mut dyn FnMut() -> Result<&'a AtomicI32, krepi_tools::Failure>,
    out: &mut Out,
) -> u8 {
    let fail = |out: &mut Out, error: &str| {
        out.warn(&format!("cargo xtask suite failed: {}", printable(error)));
        Outcome::Error.code()
    };
    let suites = match fs::read_to_string(root.join(MANIFEST))
        .map_err(|error| format!("cannot read {MANIFEST}: {error}"))
        .and_then(|text| load(&text))
    {
        Ok(suites) => suites,
        Err(error) => return fail(out, &error),
    };
    let base = match &choice.base {
        None => None,
        Some(base) => match changed(root, base) {
            Ok(changed) => Some((base.clone(), changed)),
            Err(error) => return fail(out, &error),
        },
    };
    let paths = base.as_ref().map(|(_, (_, paths))| paths.as_slice());
    let plans = choose(&suites, paths, choice.slow);
    let output = choice.output.clone().unwrap_or_else(|| {
        let stamp = krepi_tools::report::utc_stamp();
        root.join(OUTPUT_DIR)
            .join(format!("{stamp}-{}", std::process::id()))
    });
    if let Err(error) = image::create_new(&output) {
        return fail(out, &error);
    }
    let commit = image::commit(root);
    let mut report = json!({
        "format": FORMAT,
        "status": null,
        "started_at": utc_now(),
        "finished_at": null,
        "commit": commit.as_ref().ok(),
        "github": (crate::receipt::GITHUB.iter())
            .map(|name| (name.to_string(), std::env::var(name).ok().into()))
            .collect::<serde_json::Map<String, Value>>(),
        "selection": {
            "base": base.as_ref().map(|(base, _)| base),
            "merge_base": base.as_ref().map(|(_, (merge_base, _))| merge_base),
            "changed": paths,
            "slow": choice.slow,
        },
        "images": [],
        "suites": [],
    });
    match &base {
        Some((rev, (merge_base, paths))) => out.say(&format!(
            "{} paths changed since {merge_base}, the merge base of {} and HEAD",
            paths.len(),
            printable(rev)
        )),
        None => out.say("every suite runs"),
    }
    let needed: BTreeSet<&str> = (plans.iter())
        .filter(|plan| !plan.cases.is_empty())
        .map(|plan| plan.suite.image.as_str())
        .collect();
    let images = match &choice.images {
        Some(dir) => take_images(dir, &needed, &choice.expect),
        None => commit
            .clone()
            .and_then(|commit| image::write(&output.join("images"), &image::SOURCES, &commit))
            .map(|record| {
                (record.images.into_iter())
                    .map(|entry| Ready {
                        path: output.join("images").join(&entry.file),
                        name: entry.name,
                        bytes: entry.bytes,
                        sha256: entry.sha256,
                        expected: None,
                    })
                    .collect()
            })
            .map_err(|error| vec![error]),
    };
    let mut status = Outcome::Pass;
    match images {
        Err(problems) => {
            for problem in &problems {
                out.warn(&format!("cargo xtask suite: {}", printable(problem)));
            }
            report["errors"] = json!(problems);
            status = Outcome::Error;
        }
        Ok(images) => {
            report["images"] = (images.iter())
                .map(|image| {
                    json!({
                        "name": image.name,
                        "path": image.path.to_string_lossy(),
                        "bytes": image.bytes,
                        "sha256": image.sha256,
                        "expected": image.expected,
                    })
                })
                .collect();
            let mut entries = Vec::new();
            for plan in &plans {
                let (why, by) = match &plan.why {
                    Why::Every => ("every suite runs".to_string(), Value::Null),
                    Why::Paths(paths) if paths.is_empty() => {
                        ("no changed path selects it".to_string(), json!([]))
                    }
                    Why::Paths(paths) => (
                        format!(
                            "{} changed paths select it, first {} by {}",
                            paths.len(),
                            printable(&paths[0].0),
                            paths[0].1
                        ),
                        (paths.iter())
                            .map(|(path, prefix)| json!({"path": path, "prefix": prefix}))
                            .collect(),
                    ),
                };
                out.say(&format!("suite {}: {why}", plan.suite.name));
                let mut cases = Vec::new();
                for chosen in &plan.cases {
                    if status == Outcome::Interrupted {
                        break;
                    }
                    let image = images.iter().find(|image| image.name == plan.suite.image);
                    let image = image.expect("each needed image is ready");
                    let (entry, outcome) = run_case(
                        plan.suite,
                        chosen,
                        image,
                        choice.qemu.as_deref(),
                        &output,
                        timing,
                        arm,
                        &mut |line| out.say(line),
                    );
                    out.say(&format!(
                        "{}/{}: {} ({})",
                        plan.suite.name,
                        chosen.case.name,
                        outcome.name(),
                        chosen.reasons.join(", ")
                    ));
                    for check in (entry["checks"].as_array().into_iter().flatten())
                        .filter(|check| check["status"] == "FAIL")
                    {
                        out.say(&format!(
                            "FAILED {}/{} {}: {}",
                            plan.suite.name,
                            chosen.case.name,
                            check["name"].as_str().unwrap_or_default(),
                            printable(check["detail"].as_str().unwrap_or_default())
                        ));
                    }
                    status = status.max(outcome);
                    cases.push(entry);
                }
                entries.push(json!({
                    "name": plan.suite.name,
                    "image": plan.suite.image,
                    "selected": why,
                    "selected_by": by,
                    "cases": cases,
                }));
            }
            report["suites"] = entries.into();
        }
    }
    report["status"] = status.name().into();
    report["finished_at"] = utc_now().into();
    let summary = output.join(SUMMARY_FILE);
    if let Err(error) = fs::write(&summary, format!("{report:#}\n")) {
        return fail(out, &format!("cannot write {}: {error}", summary.display()));
    }
    out.say(&format!("{}: {}", status.name(), summary.display()));
    status.code()
}

#[cfg(test)]
mod tests;
