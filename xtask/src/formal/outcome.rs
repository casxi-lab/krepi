//! The class of each command, from the one function that every call site
//! uses, the conclusion of each unit and the status of a run.

use std::collections::BTreeMap;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use super::process::{Ended, GROUP_END, LimitBy, Ran};
use super::receipt;

/// A place in the gate that runs a command.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Site {
    Charon,
    Aeneas,
    QualificationBuild,
    IllTypedBuild,
    CaseAudit,
    BaseBuild,
    TargetBuild,
    AxiomAudit,
    DeclarationRanges,
    CargoCheck,
    Leanchecker,
    Comparator,
    Git,
    CargoMetadata,
}

impl Site {
    /// The fixed cap of a command at the site, if it has one.
    pub fn cap(self) -> Option<Duration> {
        let seconds = match self {
            Site::Charon | Site::CaseAudit | Site::AxiomAudit => 1_800,
            Site::DeclarationRanges | Site::CargoCheck => 1_800,
            Site::Aeneas => 3_600,
            Site::QualificationBuild | Site::IllTypedBuild | Site::BaseBuild => 7_200,
            Site::TargetBuild => 7_200,
            Site::Leanchecker | Site::Comparator | Site::Git | Site::CargoMetadata => {
                return None;
            }
        };
        Some(Duration::from_secs(seconds))
    }
}

/// The class of a command's result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Class {
    Passed,
    ProofFailure,
    ToolFailure,
    /// A tool failure at the limit of a phase or of the gate.
    Budget,
    NotRun,
}

/// The conclusion of a unit, and the status of a run.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Status {
    Verified,
    Rejected,
    Stale,
    #[default]
    ToolFailure,
    Budget,
    NotRun,
    Scoped,
}

/// The name that the receipt gives `value`, a word of this module or a
/// [`LimitBy`].
pub fn word<T: Serialize>(value: &T) -> String {
    serde_json::to_value(value)
        .ok()
        .and_then(|value| value.as_str().map(str::to_string))
        .unwrap_or_default()
}

/// The class of a command's result, with the reason for any class but
/// [`Class::Passed`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Verdict {
    pub class: Class,
    pub reason: Option<String>,
}

/// The class of `ran` at `site` by the conventions under "Results" in
/// `docs/formal-verification.md`, where `own` counts the errors and warnings
/// that the base build reported in krepi's own modules and `unread` tells
/// why a file that the command wrote, and that the gate reads, could not be
/// read or is not what the tool writes.
pub fn classify(site: Site, ran: &Ran, own: usize, unread: Option<&str>) -> Verdict {
    let name = &ran.name;
    // Each gives a reason for any command that did not exit.
    let killed = match site {
        Site::Charon => charon_killed(ran),
        Site::QualificationBuild
        | Site::IllTypedBuild
        | Site::CaseAudit
        | Site::BaseBuild
        | Site::TargetBuild
        | Site::AxiomAudit => killed(ran),
        Site::DeclarationRanges => killed(ran),
        Site::Aeneas
        | Site::CargoCheck
        | Site::Leanchecker
        | Site::Comparator
        | Site::Git
        | Site::CargoMetadata => stopped(ran),
    };
    let signal = ran.code().filter(|code| *code > 128).map(|code| {
        format!("{name} exited with {code}, the status of a process that a signal ended")
    });
    let survivors = ran.survivors.then(|| {
        let after = GROUP_END.as_secs();
        format!("{name}: processes of its group were still there {after} s after they were killed")
    });
    let mut failed: Vec<String> = killed.or(signal).into_iter().chain(survivors).collect();
    // What a command wrote counts only when it ended by itself.
    if failed.is_empty() {
        failed.extend(unread.map(|problem| format!("{name}: {problem}")));
    }
    let budget = ran.ended == Ended::TimedOut && ran.limit.by != LimitBy::Cap && !ran.survivors;
    let code = ran.code().unwrap_or_default();
    let exited = format!("{name} exited with {code}");
    let owned = format!("{exited}: {own} errors or warnings in krepi's own modules");
    let unbuilt = (ran.output.lines()).any(|line| line.starts_with("error: Child exited with "));
    let (class, reason) = match site {
        _ if budget => (Class::Budget, failed.join("; ")),
        _ if !failed.is_empty() => (Class::ToolFailure, failed.join("; ")),
        _ if code == 0 => (Class::Passed, String::new()),
        Site::BaseBuild if own > 0 => (Class::ProofFailure, owned),
        Site::BaseBuild => (Class::ToolFailure, owned),
        Site::Comparator if code == 1 && unbuilt => (
            Class::ToolFailure,
            format!("{exited}: what it compares was not built"),
        ),
        Site::Comparator if code == 1 => (Class::ProofFailure, exited),
        Site::DeclarationRanges | Site::Comparator => (Class::ToolFailure, exited),
        Site::Git | Site::CargoMetadata => (Class::ToolFailure, exited),
        Site::Charon
        | Site::Aeneas
        | Site::QualificationBuild
        | Site::IllTypedBuild
        | Site::CaseAudit
        | Site::TargetBuild
        | Site::AxiomAudit
        | Site::CargoCheck
        | Site::Leanchecker => (Class::ProofFailure, exited),
    };
    let reason = (class != Class::Passed).then_some(reason);
    Verdict { class, reason }
}

/// Why the command did not end by itself: it could not start or keep its
/// output, a signal ended it, or it ran out of time.
fn stopped(ran: &Ran) -> Option<String> {
    let name = &ran.name;
    match &ran.ended {
        Ended::Exited(_) => None,
        Ended::Signaled(signal) => Some(format!("{name} was ended by signal {signal}")),
        Ended::TimedOut => {
            let set = match ran.limit.by {
                LimitBy::Cap => "",
                LimitBy::Phase => ", the rest of the budget of its phase,",
                LimitBy::Gate => ", the rest of the budget of the gate,",
                LimitBy::Target => ", the rest of the budget of its target,",
            };
            Some(format!(
                "{name} ran longer than its limit of {} s{set} and was stopped",
                receipt::seconds(ran.limit.duration)
            ))
        }
        Ended::Failed(message) => Some(format!("{name}: {message}")),
    }
}

/// Why a Lake command did not finish its work: Lake was ended by a signal or
/// ran out of time, or a Lean process that it ran was ended by a signal. Lean
/// reports such a process with the exit code 128 plus the signal, which
/// `lake env` passes on as its own status and `lake build` prints as `Lean
/// exited with code`.
pub fn killed(ran: &Ran) -> Option<String> {
    let signal = |code: i32| {
        (code > 128).then(|| format!("{}: Lean was ended by signal {}", ran.name, code - 128))
    };
    stopped(ran)
        .or_else(|| ran.code().and_then(signal))
        .or_else(|| {
            exit_codes(&ran.output)
                .into_iter()
                .filter_map(|code| code.parse().ok())
                .find_map(signal)
        })
}

/// The exit codes that a build log reports for the Lean processes that
/// failed, in order.
pub fn exit_codes(output: &str) -> Vec<&str> {
    output
        .lines()
        .filter_map(|line| line.strip_prefix("error: Lean exited with code "))
        .map(str::trim)
        .collect()
}

/// Why Charon did not finish by itself: it was ended by a signal or ran out
/// of time; it exited with 255, which it does only when a signal ended the
/// Cargo it runs; or Cargo reports that a process it ran, such as the Charon
/// driver, was ended by a signal, as in `(signal: 9, SIGKILL: kill)`.
pub fn charon_killed(charon: &Ran) -> Option<String> {
    const MARK: &str = "(signal: ";
    if charon.code() == Some(255) {
        return Some(format!(
            "{} exited with 255: a signal ended the Cargo it runs",
            charon.name
        ));
    }
    stopped(charon).or_else(|| {
        charon.output.lines().find_map(|line| {
            let rest = &line[line.find(MARK)? + MARK.len()..];
            let digits = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            (digits > 0).then(|| {
                format!(
                    "{}: Cargo reports a process ended by signal {}",
                    charon.name,
                    &rest[..digits]
                )
            })
        })
    })
}

/// The conclusion of a unit: its status and the reason for it.
pub type Conclusion = (Status, Option<String>);

/// The conclusion that a unit's verdicts force, with the reason of the first
/// command that forces it: a tool failure, else [`Status::Budget`] for a
/// command that met a budget or did not start because it was used up.
pub fn forced(verdicts: &[Verdict]) -> Option<Conclusion> {
    let first = |classes: &[Class]| {
        verdicts
            .iter()
            .find(|verdict| classes.contains(&verdict.class))
            .map(|verdict| verdict.reason.clone())
    };
    first(&[Class::ToolFailure])
        .map(|reason| (Status::ToolFailure, reason))
        .or_else(|| first(&[Class::Budget, Class::NotRun]).map(|reason| (Status::Budget, reason)))
}

/// The receipt entry of every unit of `registered`, with its phase: its one
/// conclusion, `NOT_RUN` for the reason `stopped` when the run stopped before
/// it was concluded, and otherwise a tool failure. Also the problems: a unit
/// with no conclusion or more than one, and a conclusion of a unit that is
/// not registered.
pub fn account(
    registered: &[(String, String)],
    conclusions: Vec<(String, Conclusion)>,
    stopped: Option<&str>,
) -> (BTreeMap<String, receipt::Unit>, Vec<String>) {
    let mut found: BTreeMap<String, Vec<Conclusion>> = BTreeMap::new();
    for (unit, conclusion) in conclusions {
        found.entry(unit).or_default().push(conclusion);
    }
    let (mut units, mut problems) = (BTreeMap::new(), Vec::new());
    for (unit, phase) in registered {
        let (status, reason) = match (found.remove(unit).as_deref(), stopped) {
            (Some([conclusion]), _) => conclusion.clone(),
            (None, Some(stopped)) => (Status::NotRun, Some(stopped.to_string())),
            (other, _) => {
                let problem = match other {
                    Some(many) => format!("has {} conclusions", many.len()),
                    None => "has no conclusion".to_string(),
                };
                problems.push(format!("the unit {unit} {problem}"));
                (Status::ToolFailure, Some(format!("the unit {problem}")))
            }
        };
        let phase = phase.clone();
        units.insert(
            unit.clone(),
            receipt::Unit {
                phase,
                status,
                reason,
            },
        );
    }
    let unregistered = |unit| format!("the unit {unit} has a conclusion but is not registered");
    problems.extend(found.keys().map(unregistered));
    (units, problems)
}

/// The status of a run whose failures and units have `statuses`, by the
/// precedence under "Results" in `docs/formal-verification.md`.
pub fn run_status(statuses: &[Status], scoped: bool) -> Status {
    use Status::{Budget, NotRun, Rejected, Scoped, Stale, ToolFailure, Verified};
    let order = [ToolFailure, Budget, Stale, Rejected, NotRun];
    match order.into_iter().find(|status| statuses.contains(status)) {
        Some(NotRun) => ToolFailure,
        Some(status) => status,
        None if scoped => Scoped,
        None => Verified,
    }
}

#[cfg(test)]
pub(crate) mod conventions {
    //! The conventions that decide the class of a command, one row each: a
    //! fake tool that behaves as the row says, the sites that the row applies
    //! to, the errors and warnings in krepi's own modules that the base build
    //! would report, and the class at each of them. The tests of the call
    //! sites run the same rows.

    use std::time::Duration;

    use super::{Class, Site};
    use crate::formal::process::{Ended, Limit, LimitBy};

    /// Every site.
    pub const SITES: [Site; 14] = [
        Site::Charon,
        Site::Aeneas,
        Site::QualificationBuild,
        Site::IllTypedBuild,
        Site::CaseAudit,
        Site::BaseBuild,
        Site::TargetBuild,
        Site::AxiomAudit,
        Site::DeclarationRanges,
        Site::CargoCheck,
        Site::Leanchecker,
        Site::Comparator,
        Site::Git,
        Site::CargoMetadata,
    ];

    /// The sites that run tools on the code: Charon, Aeneas, the four
    /// builds, the two audits and `leanchecker`.
    pub const TOOLS: &[Site] = &[
        Site::Charon,
        Site::Aeneas,
        Site::QualificationBuild,
        Site::IllTypedBuild,
        Site::CaseAudit,
        Site::BaseBuild,
        Site::TargetBuild,
        Site::AxiomAudit,
        Site::Leanchecker,
    ];

    /// The sites whose `lake build` log reports the Lean processes it ran.
    pub const BUILDS: &[Site] = &[
        Site::QualificationBuild,
        Site::IllTypedBuild,
        Site::BaseBuild,
        Site::TargetBuild,
    ];

    /// The limit of a fake tool that hangs. It only decides that the tool is
    /// stopped; nothing bounds how long a step takes.
    pub const SHORT: Duration = Duration::from_secs(1);

    /// The limit of a fake tool that ends by itself.
    pub const LONG: Duration = Duration::from_secs(3_600);

    /// A build log in which Lake reports a Lean process that signal 9 ended.
    pub const KILLED_LEAN: &str = "\u{2714} [7/8] Built Krepi.Proofs.Base (186ms)\n\
        \u{2716} [8/8] Building Krepi.Proofs.Main (195ms)\n\
        error: Lean exited with code 137\n\
        Some required targets logged failures:\n\
        - Krepi.Proofs.Main\n\
        error: build failed\n";

    pub struct Row {
        pub name: &'static str,
        /// The shell script of the fake tool, or `None` for a tool that
        /// cannot start.
        pub script: Option<&'static str>,
        pub limit: Limit,
        /// Whether the fake tool ended as the row means it to.
        pub ends: fn(&Ended) -> bool,
        pub sites: &'static [Site],
        /// The errors and warnings in krepi's own modules that the base build
        /// would report. A row of a tool failure that applies to the base
        /// build has one, so that there, too, only the row's own rule makes
        /// it a tool failure.
        pub own: usize,
        pub class: Class,
    }

    fn limit(duration: Duration, by: LimitBy) -> Limit {
        Limit { duration, by }
    }

    /// One error or warning in krepi's own modules: at the base build, the
    /// evidence of a proof failure.
    const OWN: usize = 1;

    pub fn rows() -> Vec<Row> {
        vec![
            Row {
                name: "timeout",
                script: Some("exec sleep 30"),
                limit: limit(SHORT, LimitBy::Cap),
                ends: |ended| *ended == Ended::TimedOut,
                sites: TOOLS,
                own: OWN,
                class: Class::ToolFailure,
            },
            Row {
                name: "timeout-at-budget",
                script: Some("exec sleep 30"),
                limit: limit(SHORT, LimitBy::Phase),
                ends: |ended| *ended == Ended::TimedOut,
                sites: TOOLS,
                own: OWN,
                class: Class::Budget,
            },
            Row {
                name: "signal",
                script: Some("kill -9 $$"),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Signaled(9),
                sites: TOOLS,
                own: OWN,
                class: Class::ToolFailure,
            },
            Row {
                name: "exit-above-128",
                script: Some("exit 137"),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(137),
                sites: TOOLS,
                own: OWN,
                class: Class::ToolFailure,
            },
            Row {
                name: "lean-exit-above-128",
                script: Some(
                    "printf '%s\\n' '\u{2714} [7/8] Built Krepi.Proofs.Base (186ms)' \
                     '\u{2716} [8/8] Building Krepi.Proofs.Main (195ms)' \
                     'error: Krepi/Proofs/Main.lean:3:8: unsolved goals' \
                     'error: Lean exited with code 137' \
                     'Some required targets logged failures:' \
                     '- Krepi.Proofs.Main' 'error: build failed'\nexit 1",
                ),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(1),
                sites: BUILDS,
                own: OWN,
                class: Class::ToolFailure,
            },
            Row {
                name: "charon-255",
                script: Some("exit 255"),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(255),
                sites: &[Site::Charon],
                own: 0,
                class: Class::ToolFailure,
            },
            Row {
                name: "cargo-reports-signal",
                script: Some(
                    "echo 'error: could not compile `a` (lib)' >&2\n\
                     echo \"Caused by: process didn't exit successfully: \\`charon-driver\\` \
                     (signal: 9, SIGKILL: kill)\" >&2\nexit 101",
                ),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(101),
                sites: &[Site::Charon],
                own: 0,
                class: Class::ToolFailure,
            },
            Row {
                name: "cannot-start",
                script: None,
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| matches!(ended, Ended::Failed(_)),
                sites: TOOLS,
                own: OWN,
                class: Class::ToolFailure,
            },
            Row {
                name: "own-module-error",
                script: Some(
                    "echo 'error: Krepi/Proofs/Main.lean:3:8: unsolved goals'\n\
                     echo 'error: build failed'\nexit 1",
                ),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(1),
                sites: &[Site::BaseBuild],
                own: OWN,
                class: Class::ProofFailure,
            },
            Row {
                name: "own-module-warning",
                script: Some(
                    "echo \"warning: Krepi/Proofs/Main.lean:3:8: declaration uses 'sorry'\"\n\
                     echo 'error: build failed'\nexit 1",
                ),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(1),
                sites: &[Site::BaseBuild],
                own: OWN,
                class: Class::ProofFailure,
            },
            Row {
                name: "no-own-message",
                script: Some("echo 'error: build failed'\nexit 1"),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(1),
                sites: &[Site::BaseBuild],
                own: 0,
                class: Class::ToolFailure,
            },
            Row {
                name: "comparator-build-failed",
                script: Some("echo 'error: Child exited with 1'\nexit 1"),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(1),
                sites: &[Site::Comparator],
                own: 0,
                class: Class::ToolFailure,
            },
            Row {
                name: "comparator-rejected",
                script: Some(
                    "echo 'error: Krepi.Spec.add: the statement does not match: type mismatch'\n\
                     exit 1",
                ),
                limit: limit(LONG, LimitBy::Cap),
                ends: |ended| *ended == Ended::Exited(1),
                sites: &[Site::Comparator],
                own: 0,
                class: Class::ProofFailure,
            },
        ]
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::fs;

    use super::conventions::{self, KILLED_LEAN, SITES};
    use super::*;
    use crate::formal::process::{self, Limit, Spec};
    use crate::formal::toolchain::environment::{Environment, SYSTEM_PATH};
    use crate::scratch::Scratch;

    const CAP: Limit = Limit {
        duration: Duration::from_secs(7_200),
        by: LimitBy::Cap,
    };

    /// A command `name` that ended as `ended` with `output` and the limit
    /// `limit`, with no group and no output files.
    fn ran_at(name: &str, ended: Ended, output: &str, limit: Limit) -> Ran {
        Ran {
            name: name.to_string(),
            group: None,
            ended,
            limit,
            seconds: Duration::ZERO,
            stdout: None,
            stderr: None,
            output: output.to_string(),
            survivors: false,
        }
    }

    fn ran(name: &str, ended: Ended, output: &str) -> Ran {
        ran_at(name, ended, output, CAP)
    }

    fn class(site: Site, ran: &Ran) -> Class {
        classify(site, ran, 0, None).class
    }

    #[test]
    fn every_convention_has_its_class_at_every_site_it_applies_to() {
        let scratch = Scratch::new("conventions");
        let logs = scratch.0.join("logs");
        fs::create_dir_all(&logs).expect("create the log directory");
        let env = Environment::of(&[("PATH", SYSTEM_PATH)]);
        let missing = scratch.0.join("missing-tool");
        let rows = conventions::rows();
        let names: BTreeSet<&str> = rows.iter().map(|row| row.name).collect();
        assert_eq!(names.len(), rows.len(), "two rows have the same name");
        for (sequence, row) in (0..).zip(&rows) {
            let (program, args) = match row.script {
                Some(script) => ("/bin/sh", vec!["-c".to_string(), script.to_string()]),
                None => (missing.to_str().expect("a UTF-8 path"), Vec::new()),
            };
            let ran = process::run(&Spec {
                name: row.name,
                program,
                args: &args,
                cwd: &scratch.0,
                env: &env,
                stdin: None,
                logs: &logs,
                sequence,
                limit: row.limit,
            });
            assert!((row.ends)(&ran.ended), "{}: {:?}", row.name, ran.ended);
            assert!(!row.sites.is_empty(), "{} applies nowhere", row.name);
            for &site in row.sites {
                let verdict = classify(site, &ran, row.own, None);
                assert_eq!(
                    verdict.class,
                    row.class,
                    "{} at {}: {verdict:?}",
                    row.name,
                    word(&site)
                );
                assert_eq!(
                    verdict.reason.is_some(),
                    verdict.class != Class::Passed,
                    "{} at {}: {verdict:?}",
                    row.name,
                    word(&site)
                );
            }
        }
    }

    #[test]
    fn a_lean_process_ended_by_a_signal_is_reported() {
        let build = |ended, output: &str| ran("lake-build", ended, output);
        let log = KILLED_LEAN;
        assert_eq!(
            killed(&build(Ended::Exited(1), log)).as_deref(),
            Some("lake-build: Lean was ended by signal 9")
        );
        // `lake env` ends with the exit code of Lean.
        assert_eq!(
            killed(&ran("axiom-audit", Ended::Exited(134), "")).as_deref(),
            Some("axiom-audit: Lean was ended by signal 6")
        );
        assert_eq!(
            killed(&build(Ended::Signaled(15), "")).as_deref(),
            Some("lake-build was ended by signal 15")
        );
        assert_eq!(
            killed(&build(Ended::TimedOut, "")).as_deref(),
            Some("lake-build ran longer than its limit of 7200 s and was stopped")
        );
        // Lean ends with code 1 on errors in the proofs.
        assert_eq!(
            killed(&build(Ended::Exited(1), &log.replace("137", "1"))),
            None
        );
        assert_eq!(
            killed(&build(Ended::Exited(0), "Build completed successfully.\n")),
            None
        );
        assert_eq!(exit_codes(log), ["137"]);
    }

    #[test]
    fn charon_killed_tells_how_charon_was_stopped() {
        let charon = |ended, output: &str| ran("charon", ended, output);
        assert_eq!(
            charon_killed(&charon(Ended::Signaled(9), "compiling\n")).as_deref(),
            Some("charon was ended by signal 9")
        );
        // Cargo reports the Charon driver that the system killed.
        let cargo = "error: could not compile `f` (lib)\n\
            Caused by: process didn't exit successfully: `charon-driver` \
            (signal: 9, SIGKILL: kill)\n";
        assert_eq!(
            charon_killed(&charon(Ended::Exited(101), cargo)).as_deref(),
            Some("charon: Cargo reports a process ended by signal 9")
        );
        // Charon passes on the status of Cargo, and -1 for a signal.
        assert_eq!(
            charon_killed(&charon(Ended::Exited(255), "")).as_deref(),
            Some("charon exited with 255: a signal ended the Cargo it runs")
        );
        // A Charon that fails by itself rejects the code.
        assert_eq!(
            charon_killed(&charon(Ended::Exited(1), "error: no such item\n")),
            None
        );
        assert_eq!(charon_killed(&charon(Ended::Exited(0), "")), None);
    }

    #[test]
    fn a_timeout_names_the_limit_that_stopped_the_command() {
        let at = |duration: Duration, by: LimitBy| {
            ran_at("aeneas", Ended::TimedOut, "", Limit { duration, by })
        };
        let verdict = classify(
            Site::Aeneas,
            &at(Duration::from_secs(3_600), LimitBy::Cap),
            0,
            None,
        );
        assert_eq!(
            verdict,
            Verdict {
                class: Class::ToolFailure,
                reason: Some(
                    "aeneas ran longer than its limit of 3600 s and was stopped".to_string()
                ),
            }
        );
        let verdict = classify(
            Site::Aeneas,
            &at(Duration::from_millis(1_250), LimitBy::Phase),
            0,
            None,
        );
        assert_eq!(
            verdict,
            Verdict {
                class: Class::Budget,
                reason: Some(
                    "aeneas ran longer than its limit of 1.25 s, the rest of the budget of its phase, and was stopped"
                        .to_string()
                ),
            }
        );
        let verdict = classify(
            Site::Git,
            &at(Duration::from_secs(10), LimitBy::Gate),
            0,
            None,
        );
        assert_eq!(verdict.class, Class::Budget);
        assert_eq!(
            verdict.reason.as_deref(),
            Some(
                "aeneas ran longer than its limit of 10 s, the rest of the budget of the gate, and was stopped"
            )
        );
    }

    #[test]
    fn the_lean_kill_marker_counts_only_where_lake_runs() {
        let build = ran("lake-build", Ended::Exited(1), KILLED_LEAN);
        assert_eq!(class(Site::BaseBuild, &build), Class::ToolFailure);
        // Elsewhere the exit is the tool's own.
        assert_eq!(class(Site::Charon, &build), Class::ProofFailure);
        assert_eq!(class(Site::Leanchecker, &build), Class::ProofFailure);
    }

    #[test]
    fn a_failed_gate_command_is_a_tool_failure() {
        for site in [Site::Git, Site::CargoMetadata] {
            let name = word(&site);
            let failed = ran(&name, Ended::Exited(128), "fatal: not a git repository\n");
            assert_eq!(
                classify(site, &failed, 0, None),
                Verdict {
                    class: Class::ToolFailure,
                    reason: Some(format!("{name} exited with 128")),
                }
            );
            assert_eq!(
                class(site, &ran(&name, Ended::Exited(1), "")),
                Class::ToolFailure
            );
            assert_eq!(
                classify(site, &ran(&name, Ended::Exited(0), ""), 0, None),
                Verdict {
                    class: Class::Passed,
                    reason: None,
                }
            );
        }
        // A comparator status other than 1 is no statement about the code.
        assert_eq!(
            class(Site::Comparator, &ran("comparator", Ended::Exited(2), "")),
            Class::ToolFailure
        );
    }

    #[test]
    fn a_group_that_survives_its_kill_is_a_tool_failure() {
        let mut leanchecker = ran("leanchecker", Ended::Exited(0), "");
        leanchecker.survivors = true;
        let verdict = classify(Site::Leanchecker, &leanchecker, 0, None);
        assert_eq!(verdict.class, Class::ToolFailure);
        assert_eq!(
            verdict.reason.as_deref(),
            Some(
                "leanchecker: processes of its group were still there 60 s after they were killed"
            )
        );
        // Survivors make a stop at the budget a tool failure too.
        let budget = Limit {
            duration: Duration::from_secs(5),
            by: LimitBy::Phase,
        };
        let mut build = ran_at("lake-build", Ended::TimedOut, "", budget);
        assert_eq!(class(Site::BaseBuild, &build), Class::Budget);
        build.survivors = true;
        let verdict = classify(Site::BaseBuild, &build, 0, None);
        assert_eq!(verdict.class, Class::ToolFailure);
        assert_eq!(
            verdict.reason.as_deref(),
            Some(
                "lake-build ran longer than its limit of 5 s, the rest of the budget of its phase, \
                 and was stopped; lake-build: processes of its group were still there 60 s after \
                 they were killed"
            )
        );
    }

    #[test]
    fn a_result_file_that_cannot_be_read_is_a_tool_failure() {
        let unread = Some("cannot read work/aeneas/translation.json: Permission denied");
        for code in [0, 2] {
            let aeneas = ran("aeneas", Ended::Exited(code), "");
            assert_eq!(
                classify(Site::Aeneas, &aeneas, 0, unread),
                Verdict {
                    class: Class::ToolFailure,
                    reason: Some(
                        "aeneas: cannot read work/aeneas/translation.json: Permission denied"
                            .to_string()
                    ),
                },
                "{code}"
            );
        }
        // A command that was stopped is reported as stopped, whatever it
        // left behind.
        let budget = Limit {
            duration: Duration::from_secs(5),
            by: LimitBy::Phase,
        };
        let stopped = ran_at("aeneas", Ended::TimedOut, "", budget);
        assert_eq!(
            classify(Site::Aeneas, &stopped, 0, unread),
            classify(Site::Aeneas, &stopped, 0, None)
        );
        assert_eq!(
            classify(Site::Aeneas, &stopped, 0, unread).class,
            Class::Budget
        );
        let killed = ran("aeneas", Ended::Signaled(9), "");
        assert_eq!(
            classify(Site::Aeneas, &killed, 0, unread).reason.as_deref(),
            Some("aeneas was ended by signal 9")
        );
    }

    #[test]
    fn a_tool_that_reports_a_failure_by_itself_is_a_proof_failure() {
        for site in conventions::TOOLS
            .iter()
            .copied()
            .filter(|site| *site != Site::BaseBuild)
        {
            let name = word(&site);
            let verdict = classify(site, &ran(&name, Ended::Exited(2), "error: x\n"), 0, None);
            assert_eq!(
                verdict,
                Verdict {
                    class: Class::ProofFailure,
                    reason: Some(format!("{name} exited with 2")),
                }
            );
        }
        // The base build needs the messages of its own modules.
        let build = ran("base-build", Ended::Exited(1), "error: build failed\n");
        assert_eq!(
            classify(Site::BaseBuild, &build, 0, None),
            Verdict {
                class: Class::ToolFailure,
                reason: Some(
                    "base-build exited with 1: 0 errors or warnings in krepi's own modules"
                        .to_string()
                ),
            }
        );
        assert_eq!(
            classify(Site::BaseBuild, &build, 3, None),
            Verdict {
                class: Class::ProofFailure,
                reason: Some(
                    "base-build exited with 1: 3 errors or warnings in krepi's own modules"
                        .to_string()
                ),
            }
        );
    }

    #[test]
    fn a_tool_failure_of_any_command_decides_the_unit() {
        use Class::{Budget, NotRun, Passed, ProofFailure, ToolFailure};
        let verdicts = |classes: &[Class]| -> Vec<Verdict> {
            (0..)
                .zip(classes)
                .map(|(index, class)| Verdict {
                    class: *class,
                    reason: Some(format!("command {index}")),
                })
                .collect()
        };
        let reason = |text: &str| Some(text.to_string());
        assert_eq!(
            forced(&verdicts(&[Passed, Budget, ToolFailure, ProofFailure])),
            Some((Status::ToolFailure, reason("command 2")))
        );
        assert_eq!(
            forced(&verdicts(&[Passed, NotRun, Budget])),
            Some((Status::Budget, reason("command 1")))
        );
        assert_eq!(forced(&verdicts(&[Passed, ProofFailure])), None);
        assert_eq!(forced(&[]), None);
    }

    #[test]
    fn accounting_finds_missing_duplicate_and_unregistered_conclusions() {
        let units = |names: &[&str]| {
            names
                .iter()
                .map(|name| (name.to_string(), "p".to_string()))
                .collect::<Vec<_>>()
        };
        let conclude = |pairs: &[(&str, Status)]| {
            pairs
                .iter()
                .map(|(unit, status)| (unit.to_string(), (*status, Some(format!("{unit} ran")))))
                .collect::<Vec<_>>()
        };
        let given = |unit: &str, status, text: &str| {
            let reason = Some(text.to_string());
            let phase = "p".to_string();
            (
                unit.to_string(),
                receipt::Unit {
                    phase,
                    status,
                    reason,
                },
            )
        };
        let (concluded, problems) = account(
            &units(&["u1", "u2"]),
            conclude(&[("u2", Status::Rejected), ("u1", Status::Verified)]),
            None,
        );
        assert_eq!(
            concluded,
            BTreeMap::from([
                given("u1", Status::Verified, "u1 ran"),
                given("u2", Status::Rejected, "u2 ran"),
            ])
        );
        assert_eq!(problems, Vec::<String>::new());
        let conclusions = conclude(&[
            ("u1", Status::Verified),
            ("u1", Status::Verified),
            ("u3", Status::NotRun),
            ("u4", Status::Verified),
            ("u4", Status::Rejected),
        ]);
        let registered = units(&["u1", "u2", "u3", "u3"]);
        let (concluded, problems) = account(&registered, conclusions.clone(), None);
        let none = "the unit has no conclusion";
        assert_eq!(
            concluded,
            BTreeMap::from([
                given("u1", Status::ToolFailure, "the unit has 2 conclusions"),
                given("u2", Status::ToolFailure, none),
                // A unit registered twice finds no conclusion the second time.
                given("u3", Status::ToolFailure, none),
            ])
        );
        let problems_of_conclusions = [
            "the unit u1 has 2 conclusions",
            "the unit u4 has a conclusion but is not registered",
        ];
        assert_eq!(
            problems,
            [
                problems_of_conclusions[0],
                "the unit u2 has no conclusion",
                "the unit u3 has no conclusion",
                problems_of_conclusions[1],
            ]
        );
        // After a stop, a unit without a conclusion was not run.
        let (concluded, problems) = account(&registered, conclusions, Some("stopped"));
        assert_eq!(concluded["u2"], given("u2", Status::NotRun, "stopped").1);
        assert_eq!(concluded["u1"].status, Status::ToolFailure);
        assert_eq!(problems, problems_of_conclusions);
    }

    #[test]
    fn the_run_status_follows_the_precedence_of_failures() {
        use Status::{Budget, NotRun, Rejected, Scoped, Stale, ToolFailure, Verified};
        let order = [ToolFailure, Budget, Stale, Rejected];
        for (index, status) in order.iter().enumerate() {
            let mut failures = order[index..].to_vec();
            failures.reverse();
            failures.extend([Verified, NotRun]);
            assert_eq!(run_status(&failures, false), *status, "{failures:?}");
            assert_eq!(run_status(&failures, true), *status, "{failures:?}");
        }
        assert_eq!(run_status(&[], false), Verified);
        assert_eq!(run_status(&[Verified], false), Verified);
        assert_eq!(run_status(&[], true), Scoped);
        // A unit that was not run, with no failure to explain it.
        assert_eq!(run_status(&[Verified, NotRun], false), ToolFailure);
        assert_eq!(run_status(&[NotRun], true), ToolFailure);
    }

    #[test]
    fn the_words_have_their_receipt_names_and_the_sites_their_caps() {
        let sites = [
            ("charon", Some(1_800)),
            ("aeneas", Some(3_600)),
            ("qualification-build", Some(7_200)),
            ("ill-typed-build", Some(7_200)),
            ("case-audit", Some(1_800)),
            ("base-build", Some(7_200)),
            ("target-build", Some(7_200)),
            ("axiom-audit", Some(1_800)),
            ("declaration-ranges", Some(1_800)),
            ("cargo-check", Some(1_800)),
            ("leanchecker", None),
            ("comparator", None),
            ("git", None),
            ("cargo-metadata", None),
        ];
        for (site, (text, cap)) in SITES.into_iter().zip(sites) {
            assert_eq!(word(&site), text);
            assert_eq!(site.cap().map(|cap| cap.as_secs()), cap, "{text}");
            let back: Site = serde_json::from_value(serde_json::to_value(site).unwrap()).unwrap();
            assert_eq!(back, site);
        }
        let words = [
            (word(&Class::Passed), "PASSED"),
            (word(&Class::ProofFailure), "PROOF_FAILURE"),
            (word(&Class::ToolFailure), "TOOL_FAILURE"),
            (word(&Class::Budget), "BUDGET"),
            (word(&Class::NotRun), "NOT_RUN"),
            (word(&Status::Verified), "VERIFIED"),
            (word(&Status::Rejected), "REJECTED"),
            (word(&Status::Stale), "STALE"),
            (word(&Status::ToolFailure), "TOOL_FAILURE"),
            (word(&Status::Budget), "BUDGET"),
            (word(&Status::NotRun), "NOT_RUN"),
            (word(&Status::Scoped), "SCOPED"),
            (word(&LimitBy::Cap), "cap"),
            (word(&LimitBy::Phase), "phase"),
            (word(&LimitBy::Gate), "gate"),
            (word(&LimitBy::Target), "target"),
        ];
        for (word, text) in words {
            assert_eq!(word, text);
        }
    }
}
