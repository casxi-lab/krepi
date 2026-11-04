//! `cargo xtask check`: the required host checks, in order, stopping at the
//! first failure.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use crate::{docs, manifests, toolchain};

/// The Cargo workspaces that the format, Clippy and test steps cover, as
/// repository-relative directories.
pub const WORKSPACES: [&str; 3] = ["kernel", "user", "xtask"];

/// A command run in the repository root.
#[derive(Debug, Clone)]
pub struct Cmd {
    pub program: OsString,
    pub args: Vec<String>,
}

/// A check written in this crate, run with the repository root.
pub type Check = Box<dyn Fn(&Path) -> Result<(), String>>;

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

/// A failed step and why it failed.
#[derive(Debug, PartialEq, Eq)]
pub struct Failure {
    pub step: &'static str,
    pub detail: String,
}

fn cargo() -> OsString {
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
            action: Action::Internal(Box::new(manifests::run)),
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
            action: Action::Internal(Box::new(docs::run)),
        },
    ]
}

/// Runs `steps` in order in `root` and stops at the first failure.
pub fn run_steps(root: &Path, steps: &[Step]) -> Result<(), Failure> {
    for step in steps {
        println!("==> {}", step.name);
        let result = match &step.action {
            Action::Commands(commands) => {
                commands.iter().try_for_each(|cmd| run_command(root, cmd))
            }
            Action::Internal(check) => check(root),
        };
        result.map_err(|detail| Failure {
            step: step.name,
            detail,
        })?;
    }
    Ok(())
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

/// Entry point of `cargo xtask check`.
pub fn run(root: PathBuf) -> ExitCode {
    match run_steps(&root, &steps()) {
        Ok(()) => {
            println!("check passed");
            ExitCode::SUCCESS
        }
        Err(failure) => {
            eprintln!("{}", failure.detail);
            eprintln!("check failed at step {}", failure.step);
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;

    const ORDER: [&str; 6] = ["toolchain", "manifests", "fmt", "clippy", "test", "docs"];

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
                    ["kernel/Cargo.toml", "user/Cargo.toml", "xtask/Cargo.toml"]
                );
            }
        }
    }

    /// The real step list with `failing` replaced by a failing action and
    /// every other step replaced by one that records that it ran.
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
                        Action::Internal(_) => {
                            Action::Internal(Box::new(|_| Err("forced failure".to_string())))
                        }
                    }
                } else {
                    let ran = Rc::clone(ran);
                    Action::Internal(Box::new(move |_| {
                        ran.borrow_mut().push(name);
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
        let failure = run_steps(Path::new("."), &steps).expect_err("the check fails");
        assert_eq!(failure.step, failing);
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
}
