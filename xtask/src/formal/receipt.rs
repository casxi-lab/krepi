//! The receipt of `cargo xtask formal run`, schema 1, as "Receipt" in
//! `docs/formal-verification.md` documents it.

use std::collections::BTreeMap;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use super::outcome::{Class, Site, Status};
use super::paths::Snapshot;
use super::process::LimitBy;
use super::qualify::Expect;

pub const SCHEMA: u32 = 1;

pub const COMMAND: &str = "cargo xtask formal run";

/// The receipt of one run; its fields are written in this order.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Receipt {
    pub schema: u32,
    pub command: String,
    pub status: Status,
    pub complete: bool,
    pub trigger: Trigger,
    pub targets: Vec<String>,
    pub host: Option<String>,
    pub run: String,
    pub directory: String,
    pub started: u64,
    pub seconds: f64,
    pub commit: Option<String>,
    pub tree: Option<String>,
    pub inputs: Inputs,
    pub budgets: Budgets,
    pub phases: BTreeMap<String, Phase>,
    pub units: BTreeMap<String, Unit>,
    pub qualification: Option<Qualification>,
    pub commands: Vec<Command>,
    pub failures: Vec<Failure>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Mode {
    Required,
    ForcedFull,
    Weekly,
    Scoped,
    #[default]
    Manual,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Trigger {
    pub mode: Mode,
    pub event: Option<String>,
    #[serde(rename = "ref")]
    pub reference: Option<String>,
    pub run_id: Option<String>,
    pub attempt: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Inputs {
    pub before: Option<Snapshot>,
    pub after: Option<Snapshot>,
    pub clean_after: Option<bool>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Budgets {
    pub gate_seconds: u64,
    pub receipt_margin_seconds: u64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Phase {
    pub budget_seconds: u64,
    pub seconds: f64,
    pub ran: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Unit {
    pub phase: String,
    pub status: Status,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Command {
    pub sequence: u32,
    pub phase: Option<String>,
    pub unit: Option<String>,
    pub site: Site,
    pub argv: Vec<String>,
    pub cwd: String,
    pub class: Class,
    pub reason: Option<String>,
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub timed_out: bool,
    pub limit_seconds: f64,
    pub limit: LimitBy,
    pub seconds: f64,
    pub group_survived: bool,
    pub stdout: Option<Log>,
    pub stderr: Option<Log>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Qualification {
    pub cases_sha256: String,
    pub extraction_sha256: String,
    pub cases: BTreeMap<String, QualificationCase>,
    pub theorems: BTreeMap<String, QualificationTheorem>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct QualificationCase {
    pub unit: String,
    pub module: String,
    pub parts: Vec<String>,
    pub expect: Expect,
    pub models: Option<String>,
    pub observed: Observed,
    pub type_errors: Option<TypeErrors>,
    pub differences: Vec<String>,
    pub generated: BTreeMap<String, String>,
    pub declarations: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Observed {
    pub complete: bool,
    pub diagnostics: Vec<String>,
    pub external_functions: Vec<String>,
    pub external_types: Vec<String>,
    pub loop_sources: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeErrors {
    pub file: String,
    pub errors: u64,
    pub in_file: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct QualificationTheorem {
    pub case: String,
    pub unit: String,
    pub axioms: Option<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Log {
    pub path: String,
    pub bytes: u64,
    pub sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Failure {
    pub status: Status,
    pub message: String,
}

/// `duration` in seconds, rounded to milliseconds, as the receipt writes
/// times so that it reads back as it was written.
pub fn seconds(duration: Duration) -> f64 {
    (duration.as_secs_f64() * 1_000.0).round() / 1_000.0
}

/// The text of `receipt`, with a final line break.
pub fn render(receipt: &Receipt) -> String {
    let text = serde_json::to_string_pretty(receipt);
    text.expect("a receipt has string keys and finite numbers") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formal::outcome::conventions::SITES;
    use crate::formal::outcome::word;
    use crate::formal::paths::Entry;

    fn entry(mode: &str, kind: &str, digit: char) -> Option<Entry> {
        Some(Entry {
            mode: mode.to_string(),
            kind: kind.to_string(),
            oid: digit.to_string().repeat(40),
        })
    }

    fn command(sequence: u32, site: Site, class: Class) -> Command {
        Command {
            sequence,
            phase: Some("base".to_string()),
            unit: Some("base".to_string()),
            site,
            argv: vec![word(&site), "--flag".to_string()],
            cwd: "artifacts/formal/runs/1-2/work/source".to_string(),
            class,
            reason: (class != Class::Passed).then(|| format!("{} failed", word(&site))),
            exit_code: Some(1),
            signal: None,
            timed_out: false,
            limit_seconds: 3_599.875,
            limit: LimitBy::Phase,
            seconds: 0.125,
            group_survived: false,
            stdout: Some(Log {
                path: format!("logs/{sequence:04}-{}.stdout", word(&site)),
                bytes: 3,
                sha256: "7".repeat(64),
            }),
            stderr: None,
        }
    }

    /// A receipt with every field set and every word of the schema used,
    /// apart from the modes of the trigger.
    fn full(mode: Mode) -> Receipt {
        let statuses = [
            Status::Verified,
            Status::Rejected,
            Status::Stale,
            Status::ToolFailure,
            Status::Budget,
            Status::NotRun,
            Status::Scoped,
        ];
        let classes = [
            Class::Passed,
            Class::ProofFailure,
            Class::ToolFailure,
            Class::Budget,
            Class::NotRun,
        ];
        let mut commands: Vec<Command> = (1..)
            .zip(SITES)
            .map(|(sequence, site)| command(sequence, site, classes[sequence as usize % 5]))
            .collect();
        commands[0].limit = LimitBy::Cap;
        commands[1].limit = LimitBy::Gate;
        commands[1].exit_code = None;
        commands[1].signal = Some(9);
        commands[2].timed_out = true;
        commands[2].group_survived = true;
        commands[3].phase = None;
        commands[3].unit = None;
        commands[3].stdout = None;
        let inputs = Snapshot::from([
            ("kernel".to_string(), entry("040000", "tree", 'a')),
            (
                "rust-toolchain.toml".to_string(),
                entry("100755", "blob", 'b'),
            ),
            ("verification/qualification".to_string(), None),
        ]);
        Receipt {
            schema: SCHEMA,
            command: COMMAND.to_string(),
            status: Status::ToolFailure,
            complete: false,
            trigger: Trigger {
                mode,
                event: Some("pull_request".to_string()),
                reference: Some("refs/pull/7/merge".to_string()),
                run_id: Some("123".to_string()),
                attempt: Some("2".to_string()),
            },
            targets: vec!["alpha".to_string(), "demo".to_string()],
            host: Some("linux-aarch64".to_string()),
            run: "1700000000-42".to_string(),
            directory: "artifacts/formal/runs/1700000000-42".to_string(),
            started: 1_700_000_000,
            seconds: 12.345,
            commit: Some("c".repeat(40)),
            tree: Some("d".repeat(40)),
            inputs: Inputs {
                before: Some(inputs.clone()),
                after: Some(inputs),
                clean_after: Some(true),
            },
            budgets: Budgets {
                gate_seconds: 7_200,
                receipt_margin_seconds: 300,
            },
            phases: BTreeMap::from([(
                "base".to_string(),
                Phase {
                    budget_seconds: 3_600,
                    seconds: 1.5,
                    ran: true,
                },
            )]),
            units: (0..)
                .zip(statuses)
                .map(|(index, status)| {
                    (
                        format!("u{index}"),
                        Unit {
                            phase: "base".to_string(),
                            status,
                            reason: Some(format!("reason {index}")),
                        },
                    )
                })
                .collect(),
            qualification: Some(qualification()),
            commands,
            failures: statuses
                .into_iter()
                .map(|status| Failure {
                    status,
                    message: format!("{status:?}"),
                })
                .collect(),
        }
    }

    /// The record of a qualification with a case of every expectation.
    fn qualification() -> Qualification {
        let case = |expect, type_errors| QualificationCase {
            unit: "qualification/c".to_string(),
            module: "Qual.C".to_string(),
            parts: vec!["Qual.C.A".to_string(), "Qual.C.B".to_string()],
            expect,
            models: Some("verification/externals/Qual/C".to_string()),
            observed: Observed {
                complete: true,
                diagnostics: vec!["[Warn ] w".to_string()],
                external_functions: vec!["f".to_string()],
                external_types: vec!["t".to_string()],
                loop_sources: vec!["c.f_loop src/lib.rs".to_string()],
            },
            type_errors,
            differences: vec!["diagnostics: expected but absent: x".to_string()],
            generated: BTreeMap::from([("KrepiGen/Qual/C/Funs.lean".to_string(), "8".repeat(64))]),
            declarations: vec!["c.f".to_string()],
        };
        let errors = TypeErrors {
            file: "Funs.lean".to_string(),
            errors: 2,
            in_file: 1,
        };
        Qualification {
            cases_sha256: "1".repeat(64),
            extraction_sha256: "2".repeat(64),
            cases: BTreeMap::from([
                ("a".to_string(), case(Expect::Translated, None)),
                ("b".to_string(), case(Expect::IllTyped, Some(errors))),
                ("c".to_string(), case(Expect::Rejected, None)),
            ]),
            theorems: BTreeMap::from([
                (
                    "Krepi.Qualification.C.t".to_string(),
                    QualificationTheorem {
                        case: "a".to_string(),
                        unit: "qualification/a/Krepi.Qualification.C.t".to_string(),
                        axioms: Some(vec!["propext".to_string()]),
                    },
                ),
                (
                    "Krepi.Qualification.C.u".to_string(),
                    QualificationTheorem {
                        case: "a".to_string(),
                        unit: "qualification/a/Krepi.Qualification.C.u".to_string(),
                        axioms: None,
                    },
                ),
            ]),
        }
    }

    #[test]
    fn a_receipt_reads_back_as_it_was_written() {
        let modes = [
            Mode::Required,
            Mode::ForcedFull,
            Mode::Weekly,
            Mode::Scoped,
            Mode::Manual,
        ];
        for mode in modes {
            let receipt = full(mode);
            let text = render(&receipt);
            assert!(text.ends_with("}\n"), "{text}");
            let back: Receipt = serde_json::from_str(&text).expect("the receipt reads back");
            assert_eq!(back, receipt);
            assert_eq!(render(&back), text);
        }
        let text = render(&full(Mode::Manual));
        for word in [
            "\"VERIFIED\"",
            "\"REJECTED\"",
            "\"STALE\"",
            "\"TOOL_FAILURE\"",
            "\"BUDGET\"",
            "\"NOT_RUN\"",
            "\"SCOPED\"",
            "\"PASSED\"",
            "\"PROOF_FAILURE\"",
            "\"cap\"",
            "\"phase\"",
            "\"gate\"",
            "\"ref\": \"refs/pull/7/merge\"",
            "\"type\": \"tree\"",
            "\"expect\": \"translated\"",
            "\"expect\": \"ill-typed\"",
            "\"expect\": \"rejected\"",
        ] {
            assert!(text.contains(word), "{word} is not in {text}");
        }
        for site in SITES {
            assert!(text.contains(&format!("\"site\": \"{}\"", word(&site))));
        }
    }

    #[test]
    fn a_receipt_has_the_documented_layout() {
        let receipt = Receipt {
            schema: SCHEMA,
            command: COMMAND.to_string(),
            status: Status::Verified,
            complete: true,
            trigger: Trigger {
                mode: Mode::Manual,
                event: None,
                reference: None,
                run_id: None,
                attempt: None,
            },
            targets: Vec::new(),
            host: Some("darwin-arm64".to_string()),
            run: "1700000000-42".to_string(),
            directory: "artifacts/formal/runs/1700000000-42".to_string(),
            started: 1_700_000_000,
            seconds: 0.5,
            commit: Some("c".repeat(40)),
            tree: Some("d".repeat(40)),
            inputs: Inputs {
                // Maps are written in the order of their keys.
                before: Some(Snapshot::from([
                    ("xtask".to_string(), None),
                    ("kernel".to_string(), entry("040000", "tree", 'a')),
                ])),
                after: None,
                clean_after: Some(true),
            },
            budgets: Budgets {
                gate_seconds: 7_200,
                receipt_margin_seconds: 300,
            },
            phases: BTreeMap::new(),
            units: BTreeMap::from([
                (
                    "zeta".to_string(),
                    Unit {
                        phase: "p".to_string(),
                        status: Status::Verified,
                        reason: None,
                    },
                ),
                (
                    "alpha".to_string(),
                    Unit {
                        phase: "p".to_string(),
                        status: Status::NotRun,
                        reason: Some("r".to_string()),
                    },
                ),
            ]),
            qualification: None,
            commands: vec![Command {
                sequence: 1,
                phase: None,
                unit: None,
                site: Site::Git,
                argv: vec!["git".to_string(), "status".to_string()],
                cwd: ".".to_string(),
                class: Class::Passed,
                reason: None,
                exit_code: Some(0),
                signal: None,
                timed_out: false,
                limit_seconds: 7_199.5,
                limit: LimitBy::Gate,
                seconds: 0.25,
                group_survived: false,
                stdout: Some(Log {
                    path: "logs/0001-git.stdout".to_string(),
                    bytes: 0,
                    sha256: "e".repeat(64),
                }),
                stderr: None,
            }],
            failures: Vec::new(),
        };
        let c = "c".repeat(40);
        let d = "d".repeat(40);
        let a = "a".repeat(40);
        let e = "e".repeat(64);
        let expected = format!(
            r#"{{
  "schema": 1,
  "command": "cargo xtask formal run",
  "status": "VERIFIED",
  "complete": true,
  "trigger": {{
    "mode": "MANUAL",
    "event": null,
    "ref": null,
    "run_id": null,
    "attempt": null
  }},
  "targets": [],
  "host": "darwin-arm64",
  "run": "1700000000-42",
  "directory": "artifacts/formal/runs/1700000000-42",
  "started": 1700000000,
  "seconds": 0.5,
  "commit": "{c}",
  "tree": "{d}",
  "inputs": {{
    "before": {{
      "kernel": {{
        "mode": "040000",
        "type": "tree",
        "oid": "{a}"
      }},
      "xtask": null
    }},
    "after": null,
    "clean_after": true
  }},
  "budgets": {{
    "gate_seconds": 7200,
    "receipt_margin_seconds": 300
  }},
  "phases": {{}},
  "units": {{
    "alpha": {{
      "phase": "p",
      "status": "NOT_RUN",
      "reason": "r"
    }},
    "zeta": {{
      "phase": "p",
      "status": "VERIFIED",
      "reason": null
    }}
  }},
  "qualification": null,
  "commands": [
    {{
      "sequence": 1,
      "phase": null,
      "unit": null,
      "site": "git",
      "argv": [
        "git",
        "status"
      ],
      "cwd": ".",
      "class": "PASSED",
      "reason": null,
      "exit_code": 0,
      "signal": null,
      "timed_out": false,
      "limit_seconds": 7199.5,
      "limit": "gate",
      "seconds": 0.25,
      "group_survived": false,
      "stdout": {{
        "path": "logs/0001-git.stdout",
        "bytes": 0,
        "sha256": "{e}"
      }},
      "stderr": null
    }}
  ],
  "failures": []
}}
"#
        );
        assert_eq!(render(&receipt), expected);
    }

    #[test]
    fn times_are_rounded_to_milliseconds() {
        assert_eq!(seconds(Duration::from_micros(1_234_567)), 1.235);
        assert_eq!(seconds(Duration::from_secs(7_200)), 7_200.0);
        assert_eq!(seconds(Duration::ZERO), 0.0);
    }
}
