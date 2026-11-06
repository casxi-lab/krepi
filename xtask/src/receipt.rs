//! The receipt of `cargo xtask check --receipt <path>`: a JSON record of one
//! run, written whether the check passes or fails.
//!
//! The receipt holds the commit checked out when the run started, whether the
//! working tree was clean before and after the run, each step with its
//! status, duration and facts (the toolchain step's facts are the tool
//! versions it found), the runner image and the GitHub Actions run. A value
//! that cannot be read, or an environment variable that is not set, is
//! `null`.

use std::fs;
use std::io;
use std::path::Path;
use std::process::Command;

use crate::check::{Outcome, Status};

/// The version of the receipt format.
pub const FORMAT: u32 = 1;

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

/// A JSON value.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Json {
    Null,
    Bool(bool),
    Number(u128),
    String(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

impl Json {
    fn text(value: &str) -> Json {
        Json::String(value.to_string())
    }

    fn optional(value: Option<&str>) -> Json {
        value.map_or(Json::Null, Json::text)
    }

    fn object(fields: Vec<(&str, Json)>) -> Json {
        Json::Object(
            fields
                .into_iter()
                .map(|(key, value)| (key.to_string(), value))
                .collect(),
        )
    }

    fn variables(values: &[(&'static str, Option<String>)]) -> Json {
        Json::object(
            values
                .iter()
                .map(|(name, value)| (*name, Json::optional(value.as_deref())))
                .collect(),
        )
    }

    /// Writes the value with two-space indentation, starting at `depth`.
    fn write(&self, depth: usize, out: &mut String) {
        let indent = |depth: usize| "  ".repeat(depth);
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
            Json::Number(value) => out.push_str(&value.to_string()),
            Json::String(value) => out.push_str(&quote(value)),
            Json::Array(items) if items.is_empty() => out.push_str("[]"),
            Json::Object(fields) if fields.is_empty() => out.push_str("{}"),
            Json::Array(items) => {
                out.push_str("[\n");
                for (index, item) in items.iter().enumerate() {
                    out.push_str(&indent(depth + 1));
                    item.write(depth + 1, out);
                    out.push_str(if index + 1 < items.len() { ",\n" } else { "\n" });
                }
                out.push_str(&indent(depth));
                out.push(']');
            }
            Json::Object(fields) => {
                out.push_str("{\n");
                for (index, (key, value)) in fields.iter().enumerate() {
                    out.push_str(&indent(depth + 1));
                    out.push_str(&quote(key));
                    out.push_str(": ");
                    value.write(depth + 1, out);
                    out.push_str(if index + 1 < fields.len() {
                        ",\n"
                    } else {
                        "\n"
                    });
                }
                out.push_str(&indent(depth));
                out.push('}');
            }
        }
    }
}

/// `text` as a JSON string literal: quotes, backslashes and control
/// characters are escaped, and everything else is kept as UTF-8.
fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if u32::from(c) < 0x20 || c == '\u{7f}' => {
                out.push_str(&format!("\\u{:04x}", u32::from(c)));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn step(outcome: &Outcome) -> Json {
    let status = match outcome.status {
        Status::Passed => "passed",
        Status::Failed(_) => "failed",
        Status::NotRun => "not run",
    };
    let mut fields = vec![
        ("name", Json::text(outcome.step)),
        ("status", Json::text(status)),
        ("duration_ms", Json::Number(outcome.duration.as_millis())),
    ];
    if let Status::Failed(detail) = &outcome.status {
        fields.push(("detail", Json::text(detail)));
    }
    let facts = outcome
        .facts
        .iter()
        .map(|(key, value)| (key.as_str(), Json::text(value)))
        .collect();
    fields.push(("facts", Json::object(facts)));
    Json::object(fields)
}

/// The receipt of a run, as JSON text ending in a newline.
pub fn render(
    before: &GitState,
    after: &GitState,
    outcomes: &[Outcome],
    environment: &Environment,
) -> String {
    let passed = outcomes
        .iter()
        .all(|outcome| outcome.status == Status::Passed);
    let receipt = Json::object(vec![
        ("format", Json::Number(u128::from(FORMAT))),
        ("command", Json::text("cargo xtask check")),
        ("commit", Json::optional(before.commit.as_deref())),
        ("clean_before", before.clean.map_or(Json::Null, Json::Bool)),
        ("clean_after", after.clean.map_or(Json::Null, Json::Bool)),
        (
            "result",
            Json::text(if passed { "passed" } else { "failed" }),
        ),
        ("steps", Json::Array(outcomes.iter().map(step).collect())),
        ("image", Json::variables(&environment.image)),
        ("github", Json::variables(&environment.github)),
    ]);
    let mut out = String::new();
    receipt.write(0, &mut out);
    out.push('\n');
    out
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
    use std::time::Duration;

    use super::*;

    #[test]
    fn quote_escapes_json_specials() {
        assert_eq!(quote("plain"), "\"plain\"");
        assert_eq!(quote("a \"b\" \\c"), r#""a \"b\" \\c""#);
        assert_eq!(quote("one\ntwo\r\tend"), r#""one\ntwo\r\tend""#);
        assert_eq!(quote("\u{0}\u{1b}\u{7f}"), r#""\u0000\u001b\u007f""#);
        assert_eq!(quote("casξ ✓"), "\"casξ ✓\"");
    }

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
        let outcomes = [
            Outcome {
                step: "toolchain",
                status: Status::Passed,
                duration: Duration::from_millis(1250),
                facts: vec![
                    ("host".to_string(), "linux-aarch64".to_string()),
                    (
                        "clang".to_string(),
                        "Ubuntu clang version 18.1.3 (1ubuntu1)".to_string(),
                    ),
                ],
            },
            Outcome {
                step: "fmt",
                status: Status::Failed("`cargo fmt` exited with \"1\"\nsee above".to_string()),
                duration: Duration::from_micros(7999),
                facts: Vec::new(),
            },
            Outcome {
                step: "clippy",
                status: Status::NotRun,
                duration: Duration::ZERO,
                facts: Vec::new(),
            },
        ];
        let environment = Environment::from_sources(
            |name| (name == "GITHUB_EVENT_NAME").then(|| "pull_request".to_string()),
            Some("ImageOS=ubuntu24-arm64\n"),
        );
        let expected = r#"{
  "format": 1,
  "command": "cargo xtask check",
  "commit": "0123abc",
  "clean_before": true,
  "clean_after": null,
  "result": "failed",
  "steps": [
    {
      "name": "toolchain",
      "status": "passed",
      "duration_ms": 1250,
      "facts": {
        "host": "linux-aarch64",
        "clang": "Ubuntu clang version 18.1.3 (1ubuntu1)"
      }
    },
    {
      "name": "fmt",
      "status": "failed",
      "duration_ms": 7,
      "detail": "`cargo fmt` exited with \"1\"\nsee above",
      "facts": {}
    },
    {
      "name": "clippy",
      "status": "not run",
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
        assert_eq!(render(&before, &after, &outcomes, &environment), expected);
    }

    #[test]
    fn a_run_with_every_step_passed_is_passed() {
        let state = GitState {
            commit: None,
            clean: Some(false),
        };
        let outcomes = [Outcome {
            step: "docs",
            status: Status::Passed,
            duration: Duration::ZERO,
            facts: Vec::new(),
        }];
        let text = render(
            &state,
            &state,
            &outcomes,
            &Environment::from_sources(|_| None, None),
        );
        assert!(text.contains("\n  \"commit\": null,\n"), "{text}");
        assert!(text.contains("\n  \"clean_before\": false,\n"), "{text}");
        assert!(text.contains("\n  \"result\": \"passed\",\n"), "{text}");
        assert!(
            render(
                &state,
                &state,
                &[],
                &Environment::from_sources(|_| None, None)
            )
            .contains("\n  \"steps\": [],\n")
        );
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
