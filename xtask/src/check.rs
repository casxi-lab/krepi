//! `cargo xtask check`: the required host checks, in order, stopping at the
//! first failure.

use std::ffi::OsString;
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Duration, Instant};

use crate::formal::{Layout, lean, toolchain as tools};
use crate::repo::{Entry, Tree};
use crate::{docs, manifests, receipt, toolchain, workflows};

/// The Cargo workspaces that the format, Clippy and test steps cover, as
/// repository-relative directories.
pub const WORKSPACES: [&str; 4] = ["kernel", "user", "xtask", "tools"];

/// A command run in the repository root.
#[derive(Debug, Clone)]
pub struct Cmd {
    pub program: OsString,
    pub args: Vec<String>,
}

/// Named values that a step observed, in the order it observed them, for the
/// receipt. A step adds them as it goes, so they are kept when it fails.
pub type Facts = Vec<(String, String)>;

/// A check written in this crate, run with the repository root.
pub type Check = Box<dyn Fn(&Path, &mut Facts) -> Result<(), String>>;

/// What a step does.
pub enum Action {
    /// Run commands in order; each must exit with status 0.
    Commands(Vec<Cmd>),
    /// Run a check written in this crate.
    Internal(Check),
}

/// A named step of the check.
pub struct Step {
    pub name: &'static str,
    pub action: Action,
}

/// How a step ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    /// The step passed.
    Passed,
    /// The step failed, and why.
    Failed(String),
    /// An earlier step failed, so this one did not run.
    NotRun,
}

/// The result of one step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    pub step: &'static str,
    pub status: Status,
    pub duration: Duration,
    pub facts: Facts,
}

/// The Cargo that the steps run: `CARGO`, which Cargo sets for the commands it
/// runs, or else `cargo` from the search path.
pub fn cargo() -> OsString {
    std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into())
}

/// The same Cargo command for each workspace.
fn per_workspace(args: &[&str], trailing: &[&str]) -> Vec<Cmd> {
    WORKSPACES
        .iter()
        .map(|workspace| {
            let mut all: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
            all.push("--manifest-path".into());
            all.push(format!("{workspace}/Cargo.toml"));
            all.extend(trailing.iter().map(|arg| arg.to_string()));
            Cmd {
                program: cargo(),
                args: all,
            }
        })
        .collect()
}

/// The steps of `cargo xtask check`, in the order they run.
pub fn steps() -> Vec<Step> {
    vec![
        Step {
            name: "toolchain",
            action: Action::Internal(Box::new(toolchain::run)),
        },
        Step {
            name: "manifests",
            action: Action::Internal(Box::new(|root, _| manifests::run(root))),
        },
        Step {
            name: "fmt",
            action: Action::Commands(per_workspace(&["fmt", "--all", "--check"], &[])),
        },
        Step {
            name: "clippy",
            action: Action::Commands(per_workspace(
                &["clippy", "--workspace", "--all-targets", "--locked"],
                &["--", "-D", "warnings"],
            )),
        },
        Step {
            name: "test",
            action: Action::Commands(per_workspace(&["test", "--workspace", "--locked"], &[])),
        },
        Step {
            name: "docs",
            action: Action::Internal(Box::new(|root, _| docs::run(root))),
        },
        Step {
            name: "lean",
            action: Action::Internal(Box::new(|root, _| check_lean(root))),
        },
        Step {
            name: "workflows",
            action: Action::Internal(Box::new(check_workflows)),
        },
    ]
}

/// The workflows step on the tracked files; the files it read become facts.
fn check_workflows(root: &Path, facts: &mut Facts) -> Result<(), String> {
    let tree = Tree::load(root)?;
    let tracked = || {
        tree.entries().map(|(path, entry)| match entry {
            Entry::File(bytes) => (path, Some(bytes.as_slice())),
            Entry::Symlink(_) | Entry::Submodule => (path, None),
        })
    };
    let files: Vec<&str> = tracked()
        .map(|(path, _)| path)
        .filter(|path| workflows::is_workflow(path))
        .collect();
    if files.is_empty() {
        println!("workflows: no workflow files");
    } else {
        println!("workflows: {}", files.join(", "));
    }
    facts.push(("files".to_string(), files.join(", ")));
    let mut problems = workflows::check(tracked());
    problems.extend(image_problems(&tree));
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// The problems of the image references in the workflows of `tree` that run
/// on pull requests, against its image pin.
pub fn image_problems(tree: &Tree) -> Vec<String> {
    let pull = |file: &(&str, &str)| workflows::runs_on_pull_request(file.1);
    let files = tree
        .texts()
        .filter(|file| workflows::is_workflow(file.0) && pull(file));
    let pin = tree.text(Layout::PRODUCTION.image_pin).unwrap_or_default();
    tools::image_references(pin, &files.collect::<Vec<_>>())
}

/// The `lean` step on the tracked files: the source rules of the
/// hand-written Lean.
fn check_lean(root: &Path) -> Result<(), String> {
    let problems = lean_problems(&Tree::load(root)?, &Layout::PRODUCTION);
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// The problems of the source rules in the tracked Lean files of the Lake
/// project in `tree`, each of which must be a UTF-8 regular file, with the
/// items of its `tcb.json`, which must be read.
pub fn lean_problems(tree: &Tree, layout: &Layout) -> Vec<String> {
    let unread = || "it is not a tracked UTF-8 regular file".to_string();
    let tcb = tree.text(layout.tcb).ok_or_else(unread);
    let (items, mut problems) = match tcb.and_then(lean::load_tcb) {
        Ok(items) => (items, Vec::new()),
        Err(error) => (Vec::new(), vec![format!("{}: {error}", layout.tcb)]),
    };
    let project = format!("{}/", layout.project);
    let file = |path: &&str| path.starts_with(&project) && path.ends_with(".lean");
    for (path, _) in tree.entries().filter(|(path, _)| file(path)) {
        match tree.text(path) {
            Some(text) => problems.extend(lean::source_problems(path, text, &items, layout)),
            None => problems.push(format!("{path}: {}", unread())),
        }
    }
    problems
}

/// Runs `steps` in order in `root` and stops at the first failure. Every
/// step has an outcome; those after a failure did not run.
pub fn run_steps(root: &Path, steps: &[Step]) -> Vec<Outcome> {
    let mut outcomes = Vec::new();
    let mut failed = false;
    for step in steps {
        let mut facts = Facts::new();
        if failed {
            outcomes.push(Outcome {
                step: step.name,
                status: Status::NotRun,
                duration: Duration::ZERO,
                facts,
            });
            continue;
        }
        println!("==> {}", step.name);
        let started = Instant::now();
        let result = match &step.action {
            Action::Commands(commands) => {
                commands.iter().try_for_each(|cmd| run_command(root, cmd))
            }
            Action::Internal(check) => run_internal(check, root, &mut facts),
        };
        let status = match result {
            Ok(()) => Status::Passed,
            Err(detail) => {
                failed = true;
                Status::Failed(detail)
            }
        };
        outcomes.push(Outcome {
            step: step.name,
            status,
            duration: started.elapsed(),
            facts,
        });
    }
    outcomes
}

/// Runs a check written in this crate. A panic in it fails the step like an
/// error, so that the receipt is still written.
fn run_internal(check: &Check, root: &Path, facts: &mut Facts) -> Result<(), String> {
    panic::catch_unwind(AssertUnwindSafe(|| check(root, facts))).unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<&str>()
            .map(|text| text.to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_default();
        Err(format!("panicked: {message}"))
    })
}

/// The failed step and why it failed, if one did.
pub fn failure(outcomes: &[Outcome]) -> Option<(&'static str, &str)> {
    outcomes.iter().find_map(|outcome| match &outcome.status {
        Status::Failed(detail) => Some((outcome.step, detail.as_str())),
        _ => None,
    })
}

fn run_command(root: &Path, cmd: &Cmd) -> Result<(), String> {
    let shown = format!("{} {}", cmd.program.to_string_lossy(), cmd.args.join(" "));
    println!("$ {shown}");
    let status = Command::new(&cmd.program)
        .args(&cmd.args)
        .current_dir(root)
        .status()
        .map_err(|error| format!("cannot run `{shown}`: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("`{shown}` exited with {status}"))
    }
}

/// Entry point of `cargo xtask check`. With `receipt`, the run is recorded
/// there whether it passes or fails.
pub fn run(root: PathBuf, receipt: Option<PathBuf>) -> ExitCode {
    let before = receipt.as_ref().map(|_| receipt::GitState::read(&root));
    let outcomes = run_steps(&root, &steps());
    let mut code = match failure(&outcomes) {
        None => {
            println!("check passed");
            ExitCode::SUCCESS
        }
        Some((step, detail)) => {
            eprintln!("{detail}");
            eprintln!("check failed at step {step}");
            ExitCode::FAILURE
        }
    };
    if let (Some(path), Some(before)) = (receipt, before) {
        let after = receipt::GitState::read(&root);
        let text = receipt::render(&before, &after, &outcomes, &receipt::Environment::read());
        match receipt::write(&path, &text) {
            Ok(()) => println!("receipt written to {}", path.display()),
            Err(error) => {
                eprintln!("cannot write the receipt {}: {error}", path.display());
                code = ExitCode::FAILURE;
            }
        }
    }
    code
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;

    const ORDER: [&str; 8] = [
        "toolchain",
        "manifests",
        "fmt",
        "clippy",
        "test",
        "docs",
        "lean",
        "workflows",
    ];

    #[test]
    fn the_committed_workflows_pull_the_pinned_image() {
        let mut tree = Tree::load(&crate::repo::root()).expect("the tracked files");
        assert_eq!(image_problems(&tree), Vec::<String>::new());
        let pin = Layout::PRODUCTION.image_pin;
        let text = tree.text(pin).expect("the pin is tracked").to_string();
        let (_, pinned) = tools::image_pin(&text).expect("the pin reads");
        // A workflow that runs on pull requests only, or on push only.
        let workflow =
            |on: &str, image: &str| format!("on: {on}\njobs:\n  j:\n    image: {image}\n");
        let (repository, digest) = pinned.split_once('@').expect("a digest");
        let tag = format!("{repository}:latest");
        tree.insert(
            ".github/workflows/push.yml",
            Entry::File(workflow("push", &tag).into()),
        );
        tree.insert("docs/image.md", Entry::File(tag.clone().into()));
        assert_eq!(image_problems(&tree), Vec::<String>::new());
        let path = ".github/workflows/z.yml";
        tree.insert(path, Entry::File(workflow("pull_request", &tag).into()));
        assert_eq!(image_problems(&tree), [format!("{path}:4: not {pinned}")]);
        // Another pin than the one the workflows name.
        let other = text.replace(&digest[7..], &"0".repeat(64));
        tree.insert(path, Entry::File(workflow("pull_request", &pinned).into()));
        tree.insert(pin, Entry::File(other.clone().into()));
        let problems = image_problems(&tree);
        let (_, reference) = tools::image_pin(&other).expect("the other pin reads");
        assert!(
            problems.contains(&format!("no workflow names {reference}")),
            "{problems:?}"
        );
        assert!(
            problems.contains(&format!("{path}:4: not {reference}")),
            "{problems:?}"
        );
        // No pull request workflow names the image.
        let mut tree = Tree::from_files(&[(pin, &text), (".github/workflows/a.yml", "on: push\n")]);
        assert_eq!(
            image_problems(&tree),
            [format!("no workflow names {pinned}")]
        );
        tree.insert(pin, Entry::Symlink("elsewhere".to_string()));
        assert_eq!(image_problems(&tree).len(), 1);
    }

    #[test]
    fn the_workflows_step_checks_the_image_references() {
        // A repository that tracks the committed pin and the committed
        // workflow of the gate, which names the pinned image or a tag of it.
        let root = crate::repo::root();
        let scratch = crate::scratch::Scratch::temporary("workflows");
        let pin = Layout::PRODUCTION.image_pin;
        let text = std::fs::read_to_string(root.join(pin)).expect("the pin");
        let (repository, pinned) = tools::image_pin(&text).expect("the pin reads");
        let path = ".github/workflows/formal.yml";
        let workflow = std::fs::read_to_string(root.join(path)).expect("the workflow");
        assert!(workflow.contains(&pinned), "{path} names {pinned}");
        scratch.write(pin, &text);
        let git = |args: &[&str]| {
            let status = Command::new("git")
                .args(args)
                .current_dir(&scratch.0)
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        git(&["init", "--quiet"]);
        let tag = format!("{repository}:latest");
        for image in [pinned.as_str(), tag.as_str()] {
            scratch.write(path, &workflow.replace(&pinned, image));
            git(&["add", "--all"]);
            let mut facts = Facts::new();
            let result = check_workflows(&scratch.0, &mut facts);
            assert_eq!(facts, [("files".to_string(), path.to_string())]);
            if image == pinned {
                assert_eq!(result, Ok(()));
            } else {
                let problems = result.expect_err("a tag fails the step");
                assert!(problems.contains(&format!("no workflow names {pinned}")));
                let line = workflow.lines().position(|line| line.contains(&pinned));
                let line = line.expect("the line of the reference") + 1;
                let named = format!("{path}:{line}: not {pinned}");
                assert!(
                    problems.lines().any(|problem| problem == named),
                    "{problems}"
                );
            }
        }
    }

    #[test]
    fn steps_run_in_the_documented_order() {
        let names: Vec<&str> = steps().iter().map(|step| step.name).collect();
        assert_eq!(names, ORDER);
    }

    #[test]
    fn command_steps_cover_every_workspace() {
        for step in steps() {
            if let Action::Commands(commands) = step.action {
                let targets: Vec<&str> = commands
                    .iter()
                    .map(|cmd| {
                        let at = cmd.args.iter().position(|arg| arg == "--manifest-path");
                        cmd.args[at.expect("each command names a manifest") + 1].as_str()
                    })
                    .collect();
                assert_eq!(
                    targets,
                    [
                        "kernel/Cargo.toml",
                        "user/Cargo.toml",
                        "xtask/Cargo.toml",
                        "tools/Cargo.toml"
                    ]
                );
            }
        }
    }

    /// The real step list with `failing` replaced by a failing action and
    /// every other step replaced by one that records that it ran and adds a
    /// fact.
    fn with_failure(failing: &str, ran: &Rc<RefCell<Vec<&'static str>>>) -> Vec<Step> {
        steps()
            .into_iter()
            .map(|step| {
                let name = step.name;
                let action = if name == failing {
                    match step.action {
                        // A real process that exits with a non-zero status.
                        Action::Commands(_) => Action::Commands(vec![Cmd {
                            program: "sh".into(),
                            args: vec!["-c".into(), "exit 3".into()],
                        }]),
                        Action::Internal(_) => Action::Internal(Box::new(|_, facts| {
                            facts.push(("seen".to_string(), "before failing".to_string()));
                            Err("forced failure".to_string())
                        })),
                    }
                } else {
                    let ran = Rc::clone(ran);
                    Action::Internal(Box::new(move |_, facts| {
                        ran.borrow_mut().push(name);
                        facts.push(("ran".to_string(), name.to_string()));
                        Ok(())
                    }))
                };
                Step { name, action }
            })
            .collect()
    }

    fn assert_fails_at(failing: &'static str) {
        let ran = Rc::new(RefCell::new(Vec::new()));
        let steps = with_failure(failing, &ran);
        let outcomes = run_steps(Path::new("."), &steps);
        let (step, _) = failure(&outcomes).expect("the check fails");
        assert_eq!(step, failing);
        let before: Vec<&str> = ORDER
            .iter()
            .copied()
            .take_while(|name| *name != failing)
            .collect();
        assert_eq!(
            *ran.borrow(),
            before,
            "steps after the failure must not run"
        );
        let names: Vec<&str> = outcomes.iter().map(|outcome| outcome.step).collect();
        assert_eq!(names, ORDER, "every step has an outcome");
        for outcome in &outcomes {
            let index = ORDER.iter().position(|name| *name == outcome.step).unwrap();
            let failed_at = ORDER.iter().position(|name| *name == failing).unwrap();
            match index.cmp(&failed_at) {
                std::cmp::Ordering::Less => {
                    assert_eq!(outcome.status, Status::Passed);
                    assert_eq!(
                        outcome.facts,
                        [("ran".to_string(), outcome.step.to_string())]
                    );
                }
                std::cmp::Ordering::Equal => {
                    assert!(matches!(outcome.status, Status::Failed(_)), "{outcome:?}");
                }
                std::cmp::Ordering::Greater => {
                    assert_eq!(outcome.status, Status::NotRun);
                    assert_eq!(outcome.duration, Duration::ZERO);
                    assert!(outcome.facts.is_empty());
                }
            }
        }
    }

    #[test]
    fn a_format_failure_stops_the_check() {
        assert_fails_at("fmt");
    }

    #[test]
    fn a_clippy_failure_stops_the_check() {
        assert_fails_at("clippy");
    }

    #[test]
    fn a_test_failure_stops_the_check() {
        assert_fails_at("test");
    }

    #[test]
    fn a_docs_failure_stops_the_check() {
        assert_fails_at("docs");
    }

    #[test]
    fn a_lean_failure_stops_the_check() {
        assert_fails_at("lean");
    }

    #[test]
    fn a_workflows_failure_fails_the_check_after_every_other_step() {
        assert_fails_at("workflows");
    }

    #[test]
    fn a_panicking_step_fails_like_an_error_and_keeps_its_facts() {
        let ran = Rc::new(RefCell::new(Vec::new()));
        let mut steps = with_failure("docs", &ran);
        let docs = ORDER.iter().position(|name| *name == "docs").unwrap();
        steps[docs].action = Action::Internal(Box::new(|_, facts| {
            facts.push(("seen".to_string(), "before panicking".to_string()));
            panic!("forced {}", "panic");
        }));
        let outcomes = run_steps(Path::new("."), &steps);
        assert_eq!(
            outcomes[docs].status,
            Status::Failed("panicked: forced panic".to_string())
        );
        assert_eq!(
            outcomes[docs].facts,
            [("seen".to_string(), "before panicking".to_string())]
        );
        assert_eq!(outcomes[docs + 1].status, Status::NotRun);
    }

    #[test]
    fn a_failing_step_keeps_the_facts_it_added() {
        let ran = Rc::new(RefCell::new(Vec::new()));
        let outcomes = run_steps(Path::new("."), &with_failure("toolchain", &ran));
        assert_eq!(
            outcomes[0].facts,
            [("seen".to_string(), "before failing".to_string())]
        );
        assert_eq!(
            outcomes[0].status,
            Status::Failed("forced failure".to_string())
        );
    }
}
