//! `cargo xtask formal`: the proof tooling.
//!
//! The paths and names that the formal commands share are gathered in one
//! [`Layout`]; the modules take them from there and never spell them out
//! themselves. The gate inputs are defined once, in [`paths`], which takes
//! the paths that other steps of `cargo xtask check` read from the constants
//! of those steps. The command line is read with `clap`.

pub mod extract;
#[cfg(test)]
mod fixture;
pub mod lean;
pub mod outcome;
pub mod paths;
pub mod process;
pub mod qualify;
pub mod receipt;
pub mod registry;
pub mod run;
pub mod toolchain;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::builder::NonEmptyStringValueParser;
use clap::{Arg, ArgAction, ArgMatches, value_parser};

use crate::Command;

/// The paths and names of the repository that the formal commands use.
#[derive(Debug, Clone, Copy)]
pub struct Layout {
    /// The kernel workspace, the input of extraction, relative to the
    /// repository root.
    pub kernel: &'static str,
    /// The qualification crate, an input of extraction, relative to the
    /// repository root.
    pub qualification: &'static str,
    /// The qualification cases, relative to the repository root.
    pub cases: &'static str,
    /// The extraction configuration, relative to the repository root.
    pub extraction: &'static str,
    /// The Lake project, relative to the repository root.
    pub project: &'static str,
    /// The directory of the reviewed external declarations, relative to
    /// the repository root.
    pub externals: &'static str,
    /// The Lean namespace of the handwritten modules: specifications,
    /// statements, proofs and qualification proofs.
    pub namespace: &'static str,
    /// The Lean namespace of the definitions that Aeneas generates, and
    /// their directory in the Lake project.
    pub generated: &'static str,
    /// The target triple for which the kernel workspace is extracted.
    pub triple: &'static str,
    /// The proof target registry, relative to the repository root.
    pub registry: &'static str,
    /// The tool manifest, relative to the repository root.
    pub toolchain: &'static str,
    /// The directory of the reviewed tool patches, relative to the
    /// repository root.
    pub tooling: &'static str,
}

impl Layout {
    /// The layout of the production kernel.
    pub const PRODUCTION: Layout = Layout {
        kernel: crate::manifests::KERNEL,
        qualification: "verification/qualification",
        cases: "verification/qualification/cases.json",
        extraction: "verification/extraction.toml",
        project: "verification",
        externals: "verification/externals",
        namespace: "Krepi",
        generated: "KrepiGen",
        triple: "aarch64-unknown-none",
        registry: "verification/targets.json",
        toolchain: "verification/toolchain.json",
        tooling: "verification/tooling",
    };
}

/// The subcommands of `cargo xtask formal`.
pub const COMMANDS: &[Command] = &[
    Command {
        name: "run",
        about: "Run the proof gate on a snapshot of the gate inputs, with the qualification of the tools, and write its receipt; --target NAME, which may be repeated, runs only the named targets",
        subcommands: &[],
    },
    Command {
        name: "toolchain-check",
        about: "With --aeneas <dir> --charon <dir>, check the Aeneas and Charon source trees and the Aeneas patch against verification/toolchain.json",
        subcommands: &[],
    },
];

/// The command line of `cargo xtask formal`, with the texts of [`COMMANDS`].
fn cli() -> clap::Command {
    let about = |name: &str| {
        COMMANDS
            .iter()
            .find(|command| command.name == name)
            .map_or("", |command| command.about)
    };
    let path = |name: &'static str| {
        Arg::new(name)
            .long(name)
            .value_name("DIR")
            .required(true)
            .value_parser(value_parser!(PathBuf))
    };
    clap::Command::new("formal")
        .bin_name("cargo xtask formal")
        .disable_help_subcommand(true)
        .subcommand(
            clap::Command::new("run").about(about("run")).arg(
                Arg::new("target")
                    .long("target")
                    .value_name("NAME")
                    .help("Run only this target; may be repeated")
                    .action(ArgAction::Append)
                    .value_parser(NonEmptyStringValueParser::new()),
            ),
        )
        .subcommand(
            clap::Command::new("toolchain-check")
                .about(about("toolchain-check"))
                .arg(path("aeneas"))
                .arg(path("charon")),
        )
}

/// The targets that `cargo xtask formal run` was given.
fn targets(matches: &ArgMatches) -> BTreeSet<String> {
    matches
        .get_many::<String>("target")
        .into_iter()
        .flatten()
        .cloned()
        .collect()
}

/// Entry point of `cargo xtask formal`, with the arguments that follow
/// `formal`. A usage error exits with 2; without a subcommand, the commands
/// are listed.
pub fn run(root: &Path, args: &[&str]) -> ExitCode {
    let matches =
        match cli().try_get_matches_from(std::iter::once("formal").chain(args.iter().copied())) {
            Ok(matches) => matches,
            Err(error) => {
                let _ = error.print();
                return ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(2));
            }
        };
    match matches.subcommand() {
        Some(("run", matches)) => run::command(root, &Layout::PRODUCTION, targets(matches)),
        Some(("toolchain-check", matches)) => {
            let path = |name| matches.get_one::<PathBuf>(name).expect("a required option");
            toolchain::command(root, &Layout::PRODUCTION, path("aeneas"), path("charon"))
        }
        _ => {
            let _ = cli().print_help();
            ExitCode::SUCCESS
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::{self, Tree};

    fn read(args: &[&str]) -> Result<ArgMatches, clap::Error> {
        cli().try_get_matches_from(std::iter::once("formal").chain(args.iter().copied()))
    }

    #[test]
    fn the_command_line_is_read() {
        let run_targets = |args: &[&str]| {
            let matches = read(args).expect("a valid command line");
            let (name, matches) = matches.subcommand().expect("a subcommand");
            assert_eq!(name, "run");
            targets(matches)
        };
        assert_eq!(run_targets(&["run"]), BTreeSet::new());
        assert_eq!(
            run_targets(&["run", "--target", "b", "--target", "a", "--target", "b"]),
            BTreeSet::from(["a".to_string(), "b".to_string()])
        );
        let matches = read(&["toolchain-check", "--charon", "c", "--aeneas", "a"])
            .expect("a valid command line");
        let (_, matches) = matches.subcommand().expect("a subcommand");
        assert_eq!(
            matches.get_one::<PathBuf>("aeneas"),
            Some(&PathBuf::from("a"))
        );
        for args in [
            &["run", "--target"][..],
            &["run", "--target", ""],
            &["run", "--keep"],
            &["run", "--targets", "a"],
            &["run", "a"],
            &["toolchain-check", "--aeneas", "a"],
            &["frobnicate"],
        ] {
            let error = read(args).expect_err("a usage error");
            assert_eq!(error.exit_code(), 2, "{args:?}: {error}");
        }
        let help = read(&["run", "--help"]).expect_err("the help");
        assert_eq!(help.exit_code(), 0);
        assert!(help.to_string().contains("--target <NAME>"), "{help}");
    }

    #[test]
    fn a_run_with_an_unknown_argument_is_a_usage_error() {
        assert_eq!(
            run(&repo::root(), &["run", "--frobnicate"]),
            ExitCode::from(2)
        );
    }

    #[test]
    fn the_proof_tooling_does_not_use_the_host_tooling_crate() {
        // The host tooling crate is not a gate input, so the code that runs
        // the gate must not depend on it.
        let crate_name = concat!("krepi", "_tools");
        let tree = Tree::load(&repo::root()).expect("the repository is readable");
        let sources: Vec<(&str, &str)> = tree
            .texts()
            .filter(|(path, _)| path.starts_with("xtask/src/formal/"))
            .collect();
        assert!(sources.iter().any(|(path, _)| path.ends_with("/run.rs")));
        for (path, text) in sources {
            assert!(!text.contains(crate_name), "{path} uses {crate_name}");
        }
    }

    #[test]
    fn the_production_layout_names_tracked_files() {
        let tree = Tree::load(&repo::root()).expect("the repository is readable");
        let layout = Layout::PRODUCTION;
        for path in [
            format!("{}/Cargo.toml", layout.kernel),
            format!("{}/Cargo.toml", layout.qualification),
            format!("{}/Cargo.lock", layout.qualification),
            layout.cases.to_string(),
            layout.extraction.to_string(),
            layout.registry.to_string(),
            layout.toolchain.to_string(),
            format!("{}/LICENSE-Apache-2.0", layout.tooling),
        ]
        .into_iter()
        .chain(
            lean::PROJECT_FILES
                .iter()
                .map(|file| format!("{}/{file}", layout.project)),
        ) {
            assert!(tree.exists(&path), "{path} is not tracked");
        }
        for path in [
            layout.qualification,
            layout.cases,
            layout.extraction,
            layout.externals,
        ] {
            assert!(
                path.starts_with(&format!("{}/", layout.project)),
                "{path} is not in the Lake project"
            );
        }
    }

    #[test]
    fn the_lake_project_pins_the_lean_and_mathlib_of_the_manifest() {
        let manifest = toolchain::parse(include_str!("../../../verification/toolchain.json"))
            .expect("the committed manifest parses");
        assert_eq!(
            include_str!("../../../verification/lean-toolchain").trim_end(),
            manifest.lean.toolchain
        );
        let lock: serde_json::Value =
            serde_json::from_str(include_str!("../../../verification/lake-manifest.json"))
                .expect("the Lake lock parses");
        let packages = lock["packages"].as_array().expect("the packages");
        let package = |name: &str| {
            (packages.iter())
                .find(|package| package["name"] == name)
                .unwrap_or_else(|| panic!("no package {name}"))
        };
        assert_eq!(package("mathlib")["rev"], manifest.aeneas.mathlib_commit);
        assert_eq!(package("aeneas")["type"], "path");
        assert_eq!(package("aeneas")["dir"], "../artifacts/formal/lake/aeneas");
        assert_eq!(lock["packagesDir"], "../artifacts/formal/lake/packages");
        // Every other package is that of the lock of the Aeneas library.
        for package in packages
            .iter()
            .filter(|package| package["name"] != "aeneas")
        {
            assert_eq!(package["inherited"], true, "{package}");
        }
    }

    #[test]
    fn the_generated_namespace_is_outside_the_handwritten_one() {
        let layout = Layout::PRODUCTION;
        assert_ne!(layout.generated, layout.namespace);
        assert!(
            !layout
                .generated
                .starts_with(&format!("{}.", layout.namespace)),
            "{layout:?}"
        );
        for name in [layout.namespace, layout.generated] {
            assert!(
                name.chars().next().is_some_and(|c| c.is_ascii_uppercase())
                    && name.chars().all(|c| c.is_ascii_alphanumeric()),
                "{name} is not a single Lean name component"
            );
        }
    }
}
