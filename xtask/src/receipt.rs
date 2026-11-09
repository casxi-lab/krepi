//! The receipt of `cargo xtask check --receipt <path>`: a JSON record of one
//! run, written whether the check passes, fails or is interrupted.
//!
//! The receipt holds the mode of the run (`parallel` or `sequential`),
//! whether it ran the slow tests, the commit checked out when the run
//! started, whether the working tree was clean before and after the run, the
//! result (`passed`, `failed` or `interrupted`) with the number of the stop
//! signal or `null`, the lanes with the names of their steps (a lane without
//! steps is listed with none), and each step with its lane, status (`passed`,
//! `failed`, `cancelled` or `not run`), the milliseconds from the start of
//! the check to its start (`null` for a step that did not run), its duration,
//! the detail of a failed or cancelled step and its facts (the toolchain
//! step's facts are the tool versions it found), then the runner image and
//! the GitHub Actions run. A value that cannot be read, or an environment
//! variable that is not set, is `null`. The text is the pretty form of
//! `serde_json`, with two-space indentation and the fields in the order in
//! which they are written.

use std::fs;
use std::io;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use serde_json::{Map, Value, json};

use crate::check::{Outcome, Report, Status};

/// The version of the receipt format.
pub const FORMAT: u32 = 2;

/// The variables that name the runner image. GitHub-hosted runners set them
/// in `/etc/environment`, which is read when the process environment lacks
/// them.
pub const IMAGE: [&str; 2] = ["ImageOS", "ImageVersion"];

/// The variables that identify a GitHub Actions run.
pub const GITHUB: [&str; 5] = [
    "GITHUB_RUN_ID",
    "GITHUB_RUN_ATTEMPT",
    "GITHUB_EVENT_NAME",
    "GITHUB_REF",
    "GITHUB_SHA",
];

/// The checked-out commit and whether the working tree is clean: no change
/// to a tracked file and no untracked file outside the ignored paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GitState {
    pub commit: Option<String>,
    pub clean: Option<bool>,
}

impl GitState {
    /// Reads the state of the working copy at `root`.
    pub fn read(root: &Path) -> GitState {
        let commit = git(root, &["rev-parse", "HEAD"]).map(|out| out.trim().to_string());
        let clean = git(root, &["status", "--porcelain", "--untracked-files=all"])
            .map(|out| out.trim().is_empty());
        GitState { commit, clean }
    }
}

fn git(root: &Path, args: &[&str]) -> Option<String> {
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .ok()?;
    if output.status.success() {
        String::from_utf8(output.stdout).ok()
    } else {
        None
    }
}

/// The values that the receipt takes from the environment, in the order of
/// [`IMAGE`] and [`GITHUB`]; `None` where a variable is not set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Environment {
    pub image: Vec<(&'static str, Option<String>)>,
    pub github: Vec<(&'static str, Option<String>)>,
}

impl Environment {
    /// Reads the process environment and `/etc/environment`.
    pub fn read() -> Environment {
        let etc_environment = fs::read_to_string("/etc/environment").ok();
        Environment::from_sources(|name| std::env::var(name).ok(), etc_environment.as_deref())
    }

    /// Takes each variable from `var`, and an image variable that `var`
    /// lacks from the `NAME=value` lines of `etc_environment`. An empty value
    /// counts as unset.
    pub fn from_sources(
        var: impl Fn(&str) -> Option<String>,
        etc_environment: Option<&str>,
    ) -> Self {
        let set = |name: &str| var(name).filter(|value| !value.is_empty());
        let image = IMAGE
            .iter()
            .map(|name| {
                let value =
                    set(name).or_else(|| etc_environment.and_then(|text| assignment(text, name)));
                (*name, value)
            })
            .collect();
        let github = GITHUB.iter().map(|name| (*name, set(name))).collect();
        Environment { image, github }
    }
}

/// The value of the last assignment to `name` in `NAME=value` lines, with
/// one pair of surrounding quotes removed.
fn assignment(text: &str, name: &str) -> Option<String> {
    let value = text
        .lines()
        .filter_map(|line| line.trim().split_once('='))
        .filter(|(key, _)| key.trim() == name)
        .map(|(_, value)| value.trim())
        .next_back()?;
    let unquoted = ['"', '\'']
        .into_iter()
        .find_map(|quote| {
            value
                .strip_prefix(quote)
                .and_then(|rest| rest.strip_suffix(quote))
        })
        .unwrap_or(value);
    (!unquoted.is_empty()).then(|| unquoted.to_string())
}

/// An object of the variables `values`, each a string or `null`, in their
/// order.
fn variables(values: &[(&'static str, Option<String>)]) -> Value {
    Value::Object(
        values
            .iter()
            .map(|(name, value)| (name.to_string(), Value::from(value.clone())))
            .collect(),
    )
}

/// Milliseconds, saturated at the largest number.
fn millis(duration: Duration) -> u64 {
    u64::try_from(duration.as_millis()).unwrap_or(u64::MAX)
}

fn step(outcome: &Outcome) -> Value {
    let mut step = json!({
        "name": outcome.step,
        "lane": outcome.lane.name(),
        "status": outcome.status.name(),
        "offset_ms": outcome.offset.map(millis),
        "duration_ms": millis(outcome.duration),
    });
    if let Status::Failed(detail) | Status::Cancelled(detail) = &outcome.status {
        step["detail"] = Value::from(detail.as_str());
    }
    let facts: Map<String, Value> = outcome
        .facts
        .iter()
        .map(|(key, value)| (key.clone(), Value::from(value.as_str())))
        .collect();
    step["facts"] = Value::Object(facts);
    step
}

/// The receipt of the run `report`, as JSON text ending in a newline.
pub fn render(
    before: &GitState,
    after: &GitState,
    report: &Report,
    environment: &Environment,
) -> String {
    let lanes: Vec<Value> = (report.layout.iter())
        .map(|lane| {
            json!({
                "name": lane.lane.name(),
                "segment": lane.lane.segment(),
                "steps": lane.steps,
            })
        })
        .collect();
    let steps: Vec<Value> = report.outcomes.iter().map(step).collect();
    let receipt = json!({
        "format": FORMAT,
        "command": "cargo xtask check",
        "mode": report.mode.name(),
        "slow": report.slow,
        "commit": before.commit,
        "clean_before": before.clean,
        "clean_after": after.clean,
        "result": report.verdict().name(),
        "signal": report.signal,
        "lanes": lanes,
        "steps": steps,
        "image": variables(&environment.image),
        "github": variables(&environment.github),
    });
    format!("{receipt:#}\n")
}

/// Writes `text` to `path`, creating the directories above it.
pub fn write(path: &Path, text: &str) -> io::Result<()> {
    if let Some(dir) = path.parent().filter(|dir| !dir.as_os_str().is_empty()) {
        fs::create_dir_all(dir)?;
    }
    fs::write(path, text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{Lane, LaneSteps, Mode};

    #[test]
    fn reads_image_variables_from_etc_environment() {
        let etc = "PATH=\"/usr/bin\"\nImageVersion=\"20261026.166.1\"\nImageOS=ubuntu24-arm64\n# ImageOS=commented=out\n";
        let environment = Environment::from_sources(|_| None, Some(etc));
        assert_eq!(
            environment.image,
            [
                ("ImageOS", Some("ubuntu24-arm64".to_string())),
                ("ImageVersion", Some("20261026.166.1".to_string())),
            ]
        );
        assert!(environment.github.iter().all(|(_, value)| value.is_none()));
    }

    #[test]
    fn the_process_environment_comes_first() {
        let var = |name: &str| match name {
            "ImageOS" => Some("from-env".to_string()),
            "ImageVersion" => Some(String::new()),
            "GITHUB_RUN_ID" => Some("42".to_string()),
            "GITHUB_REF" => Some("refs/heads/main".to_string()),
            _ => None,
        };
        let environment =
            Environment::from_sources(var, Some("ImageOS=from-file\nImageVersion='1.2'\n"));
        assert_eq!(
            environment.image,
            [
                ("ImageOS", Some("from-env".to_string())),
                ("ImageVersion", Some("1.2".to_string())),
            ]
        );
        assert_eq!(
            environment.github,
            [
                ("GITHUB_RUN_ID", Some("42".to_string())),
                ("GITHUB_RUN_ATTEMPT", None),
                ("GITHUB_EVENT_NAME", None),
                ("GITHUB_REF", Some("refs/heads/main".to_string())),
                ("GITHUB_SHA", None),
            ]
        );
        assert_eq!(
            Environment::from_sources(|_| None, None).image[0],
            ("ImageOS", None)
        );
    }

    /// An outcome of the step `step` in `lane`.
    fn outcome(step: &'static str, lane: Lane, status: Status, offset: Option<u64>) -> Outcome {
        Outcome {
            step,
            lane,
            status,
            offset: offset.map(Duration::from_millis),
            duration: Duration::ZERO,
            facts: Vec::new(),
        }
    }

    /// A report of `outcomes` in the lanes of the check, with the formal
    /// lane empty.
    fn report(outcomes: Vec<Outcome>) -> Report {
        let lane = |lane, steps| LaneSteps { lane, steps };
        Report {
            mode: Mode::Parallel,
            slow: false,
            layout: vec![
                lane(Lane::Lint, vec!["toolchain", "fmt"]),
                lane(Lane::Debug, vec!["test", "docs"]),
                lane(Lane::Release, vec!["test-release"]),
                lane(Lane::Formal, vec![]),
            ],
            outcomes,
            elapsed: Duration::from_secs(20),
            signal: None,
        }
    }

    #[test]
    fn renders_every_field() {
        let before = GitState {
            commit: Some("0123abc".to_string()),
            clean: Some(true),
        };
        let after = GitState {
            commit: Some("0123abc".to_string()),
            clean: None,
        };
        let mut toolchain = outcome("toolchain", Lane::Lint, Status::Passed, Some(0));
        toolchain.duration = Duration::from_millis(1250);
        toolchain.facts = vec![
            ("host".to_string(), "linux-aarch64".to_string()),
            (
                "clang".to_string(),
                "Ubuntu clang version 18.1.3 (1ubuntu1)".to_string(),
            ),
        ];
        let mut test = outcome(
            "test",
            Lane::Debug,
            Status::Cancelled("step test-release failed".to_string()),
            Some(15_020),
        );
        test.duration = Duration::from_micros(3_021_999);
        let mut release = outcome(
            "test-release",
            Lane::Release,
            Status::Failed("`cargo test` exited with \"101\"\nsee above".to_string()),
            Some(15_020),
        );
        release.duration = Duration::from_millis(3_000);
        let docs = outcome("docs", Lane::Debug, Status::NotRun, None);
        let mut report = report(vec![toolchain, test, release, docs]);
        report.slow = true;
        let environment = Environment::from_sources(
            |name| (name == "GITHUB_EVENT_NAME").then(|| "pull_request".to_string()),
            Some("ImageOS=ubuntu24-arm64\n"),
        );
        let expected = r#"{
  "format": 2,
  "command": "cargo xtask check",
  "mode": "parallel",
  "slow": true,
  "commit": "0123abc",
  "clean_before": true,
  "clean_after": null,
  "result": "failed",
  "signal": null,
  "lanes": [
    {
      "name": "lint",
      "segment": 1,
      "steps": [
        "toolchain",
        "fmt"
      ]
    },
    {
      "name": "debug",
      "segment": 2,
      "steps": [
        "test",
        "docs"
      ]
    },
    {
      "name": "release",
      "segment": 2,
      "steps": [
        "test-release"
      ]
    },
    {
      "name": "formal",
      "segment": 2,
      "steps": []
    }
  ],
  "steps": [
    {
      "name": "toolchain",
      "lane": "lint",
      "status": "passed",
      "offset_ms": 0,
      "duration_ms": 1250,
      "facts": {
        "host": "linux-aarch64",
        "clang": "Ubuntu clang version 18.1.3 (1ubuntu1)"
      }
    },
    {
      "name": "test",
      "lane": "debug",
      "status": "cancelled",
      "offset_ms": 15020,
      "duration_ms": 3021,
      "detail": "step test-release failed",
      "facts": {}
    },
    {
      "name": "test-release",
      "lane": "release",
      "status": "failed",
      "offset_ms": 15020,
      "duration_ms": 3000,
      "detail": "`cargo test` exited with \"101\"\nsee above",
      "facts": {}
    },
    {
      "name": "docs",
      "lane": "debug",
      "status": "not run",
      "offset_ms": null,
      "duration_ms": 0,
      "facts": {}
    }
  ],
  "image": {
    "ImageOS": "ubuntu24-arm64",
    "ImageVersion": null
  },
  "github": {
    "GITHUB_RUN_ID": null,
    "GITHUB_RUN_ATTEMPT": null,
    "GITHUB_EVENT_NAME": "pull_request",
    "GITHUB_REF": null,
    "GITHUB_SHA": null
  }
}
"#;
        assert_eq!(render(&before, &after, &report, &environment), expected);
    }

    /// The receipt text read back as JSON.
    fn parsed(text: &str) -> Value {
        serde_json::from_str(text).expect("the receipt is JSON")
    }

    #[test]
    fn a_run_with_every_step_passed_is_passed() {
        let state = GitState {
            commit: None,
            clean: Some(false),
        };
        let docs = outcome("docs", Lane::Debug, Status::Passed, Some(0));
        let mut sequential = report(vec![docs]);
        sequential.mode = Mode::Sequential;
        let environment = Environment::from_sources(|_| None, None);
        let receipt = parsed(&render(&state, &state, &sequential, &environment));
        assert_eq!(receipt["commit"], Value::Null);
        assert_eq!(receipt["clean_before"], false);
        assert_eq!(receipt["result"], "passed");
        assert_eq!(receipt["mode"], "sequential");
        assert_eq!(receipt["slow"], false);
        assert_eq!(receipt["signal"], Value::Null);
        let empty = parsed(&render(&state, &state, &report(Vec::new()), &environment));
        assert_eq!(empty["steps"], json!([]));
        assert_eq!(empty["result"], "passed");
        assert_eq!(
            empty["lanes"][3],
            json!({"name": "formal", "segment": 2, "steps": []})
        );
    }

    #[test]
    fn an_interrupted_run_records_its_signal() {
        let state = GitState {
            commit: None,
            clean: None,
        };
        let environment = Environment::from_sources(|_| None, None);
        // Interrupted whatever the steps did: one passed, one was cancelled.
        let outcomes = vec![
            outcome("toolchain", Lane::Lint, Status::Passed, Some(0)),
            outcome(
                "test",
                Lane::Debug,
                Status::Cancelled("SIGTERM".to_string()),
                Some(2),
            ),
        ];
        for signal in [libc::SIGTERM, libc::SIGINT] {
            let mut stopped = report(outcomes.clone());
            stopped.signal = Some(signal);
            let receipt = parsed(&render(&state, &state, &stopped, &environment));
            assert_eq!(receipt["result"], "interrupted");
            assert_eq!(receipt["signal"], signal);
            assert_eq!(receipt["steps"][1]["status"], "cancelled");
            assert_eq!(receipt["steps"][1]["detail"], "SIGTERM");
            assert_eq!(receipt["steps"][0].get("detail"), None);
        }
        let mut passed = report(outcomes[..1].to_vec());
        passed.signal = Some(libc::SIGHUP);
        let receipt = parsed(&render(&state, &state, &passed, &environment));
        assert_eq!(receipt["result"], "interrupted");
        assert_eq!(receipt["signal"], 1);
    }

    #[test]
    fn strings_with_json_specials_read_back_unchanged() {
        let text = "a \"b\" \\c\none\r\ttwo \u{0}\u{8}\u{c}\u{1b}\u{7f} casξ ✓";
        let state = GitState {
            commit: Some(text.to_string()),
            clean: None,
        };
        let mut failed = outcome("fmt", Lane::Lint, Status::Failed(text.to_string()), Some(1));
        failed.duration = Duration::from_millis(3);
        failed.facts = vec![(text.to_string(), text.to_string())];
        let environment = Environment::from_sources(
            |name| (name == "GITHUB_REF").then(|| text.to_string()),
            None,
        );
        // The reader rejects a control character that is not escaped inside
        // a string, so reading the receipt back also checks the escapes.
        let receipt = parsed(&render(&state, &state, &report(vec![failed]), &environment));
        assert_eq!(receipt["commit"], text);
        assert_eq!(receipt["steps"][0]["detail"], text);
        assert_eq!(receipt["steps"][0]["facts"][text], text);
        assert_eq!(receipt["github"]["GITHUB_REF"], text);
    }

    #[test]
    fn writes_into_a_new_directory() {
        // The build directory of this crate is ignored by Git.
        let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("target")
            .join(format!("receipt-test-{}", std::process::id()));
        let path = dir.join("nested/receipt.json");
        write(&path, "{}\n").expect("the receipt is written");
        assert_eq!(fs::read_to_string(&path).unwrap(), "{}\n");
        fs::remove_dir_all(&dir).unwrap();
    }
}
