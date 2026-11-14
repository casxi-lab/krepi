//! `cargo xtask formal`: the proof tooling.
//!
//! The paths and names that the formal commands share are gathered in one
//! [`Layout`]; the modules take them from there and never spell them out
//! themselves. The gate inputs are defined once, in [`paths`], which takes
//! the paths that other steps of `cargo xtask check` read from the constants
//! of those steps. The command line is read with `clap`.

pub mod base;
pub mod canary;
pub mod classify;
pub mod externals;
pub mod extract;
#[cfg(test)]
mod fixture;
pub mod guard;
pub mod inventory;
pub mod lean;
pub mod merge;
pub mod mutants;
pub mod outcome;
pub mod paths;
pub mod process;
pub mod qualify;
pub mod receipt;
pub mod registry;
pub mod run;
pub mod storage;
pub mod toolchain;
pub mod vectors;
pub mod waiver;

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
    /// The root package of the kernel workspace, from which the kernel
    /// targets are extracted.
    pub package: &'static str,
    /// The qualification crate, an input of extraction, relative to the
    /// repository root.
    pub qualification: &'static str,
    /// The qualification cases, relative to the repository root.
    pub cases: &'static str,
    /// The extraction configuration, relative to the repository root.
    pub extraction: &'static str,
    /// The Lake project, relative to the repository root.
    pub project: &'static str,
    /// The Lake project whose Lean toolchain and Lake lock every stage takes,
    /// with the proofs of the qualification cases: that of production.
    pub root_project: &'static str,
    /// The directory of the reviewed external declarations, relative to
    /// the repository root.
    pub externals: &'static str,
    /// The Lean namespace of the handwritten modules: specifications,
    /// statements, proofs and qualification proofs.
    pub namespace: &'static str,
    /// The Lean namespace of the definitions that Aeneas generates, and
    /// their directory in the Lake project.
    pub generated: &'static str,
    /// The Lean module of the proofs, whose directory is the only part of
    /// the Lake project outside the statement side.
    pub proofs: &'static str,
    /// The statement registry, relative to the repository root.
    pub statements: &'static str,
    /// The registry of library axioms, relative to the repository root.
    pub axioms: &'static str,
    /// The registry of the trusted base, relative to the repository root.
    pub tcb: &'static str,
    /// The target triple for which the kernel workspace is extracted.
    pub triple: &'static str,
    /// The proof target registry, relative to the repository root.
    pub registry: &'static str,
    /// The model registry, relative to the repository root.
    pub models: &'static str,
    /// The open obligations that the contracts list, relative to the
    /// repository root, or none for code that no contract describes.
    pub open: &'static str,
    /// The directory of the lists of survivors of the source mutants.
    pub mutants: &'static str,
    /// The shard plan, relative to the repository root.
    pub shards: &'static str,
    /// The tool manifest, relative to the repository root.
    pub toolchain: &'static str,
    /// The pin of the image that the CI jobs run, relative to the
    /// repository root.
    pub image_pin: &'static str,
    /// The directory of the reviewed tool patches, relative to the
    /// repository root.
    pub tooling: &'static str,
    /// The waiver record, relative to the repository root, or none in a
    /// layout to which no waiver applies.
    pub waivers: &'static str,
}

impl Layout {
    /// The layout of the production kernel.
    pub const PRODUCTION: Layout = Layout {
        kernel: crate::manifests::KERNEL,
        package: crate::manifests::KERNEL_PACKAGE,
        qualification: "verification/qualification",
        cases: "verification/qualification/cases.json",
        extraction: "verification/extraction.toml",
        project: "verification",
        root_project: "verification",
        externals: "verification/externals",
        namespace: "Krepi",
        generated: "KrepiGen",
        proofs: "Krepi.Proofs",
        statements: "verification/statements.json",
        axioms: "verification/axioms.json",
        tcb: "verification/tcb.json",
        triple: "aarch64-unknown-none",
        registry: "verification/targets.json",
        models: "verification/models.json",
        open: "verification/open.json",
        mutants: "verification/mutants",
        shards: "verification/shards.json",
        toolchain: "verification/toolchain.json",
        image_pin: "verification/image-pin.json",
        tooling: "verification/tooling",
        waivers: "verification/waivers.json",
    };

    /// The layout of the calibration target: its workspace, Lake project and
    /// registries, with the qualification and the tools of production.
    pub const CALIBRATION: Layout = Layout {
        kernel: "verification/qualification/calibration",
        package: "formal-calibration",
        project: "verification/qualification/calibration",
        statements: "verification/qualification/calibration/statements.json",
        axioms: "verification/qualification/calibration/axioms.json",
        tcb: "verification/qualification/calibration/tcb.json",
        registry: "verification/qualification/calibration/targets.json",
        models: "verification/qualification/calibration/models.json",
        open: "",
        mutants: "verification/qualification/calibration/mutants",
        shards: "verification/qualification/calibration/shards.json",
        waivers: "",
        ..Layout::PRODUCTION
    };
}

/// The subcommands of `cargo xtask formal`.
pub const COMMANDS: &[Command] = &[
    Command {
        name: "run",
        about: "Run the proof gate on a snapshot of the gate inputs, with the qualification of the tools, the extraction of the targets, the base round, the targets and, on a pull request, the guard, and write its receipt; --target NAME, which may be repeated, runs only the named targets, --shard NAME only the qualification job, qualification, or the shard of a formal target, target/<name>, --calibration runs the calibration target, and --keep keeps the work directory of the run",
        subcommands: &[],
    },
    Command {
        name: "guard",
        about: "With --event PATH, the JSON of a pull_request event, check the pull request against the rules for changes of statements, proofs, sources and registries",
        subcommands: &[],
    },
    Command {
        name: "toolchain-check",
        about: "With --aeneas <dir> --charon <dir>, check the Aeneas and Charon source trees and the Aeneas patch against verification/toolchain.json",
        subcommands: &[],
    },
    Command {
        name: "check",
        about: "Check that every production function of the kernel workspace is in a target's proves or unclosed list or in verification/open.json, that this file is what the contracts give, that the target registry, verification/axioms.json and the waiver record verification/waivers.json keep their rules, with every key of a target in the inventory, that the registries hold nothing that the gate does not support, that every survivor of the lists of survivors has a class, and that the shard plan and the budget of each shard keep their rules; --write first writes the file, and --calibration checks the calibration target",
        subcommands: &[],
    },
    Command {
        name: "mutants",
        about: "Generate the source mutants of TARGET with every operator, or those that --operator names, run each through the proof gate with the theorems of the target, and write the survivors to the list of survivors of the target; --calibration takes a target of the calibration, and --keep keeps the work directory of the run",
        subcommands: &[],
    },
    Command {
        name: "impact",
        about: "With --base REV, list the merge base of REV and HEAD, each path changed since, whether the change affects the gate inputs, and the registered targets that it affects; it decides nothing",
        subcommands: &[],
    },
    Command {
        name: "merge",
        about: "Merge RECEIPT..., the receipts of the qualification job and of the shard of each formal target of the commit checked out, into the conclusion of the whole gate with the waivers of verification/waivers.json that hold, which passes when every unit and part outside them is VERIFIED, and write its record and summary; --calibration merges those of the calibration target",
        subcommands: &[],
    },
    Command {
        name: "receipt",
        about: "Judge RECORD, the record of a merge, by default artifacts/formal/merge/record.json, against the checkout: CURRENT when it has the gate inputs of the clean checkout, the pinned image and one conclusion for each registered unit, and is complete and VERIFIED, and WAIVED when it only passes within waivers that hold; --require-fresh also requires a run of CI without planned statements or waivers",
        subcommands: &[],
    },
    Command {
        name: "vectors",
        about: "Replay the test vectors of DOMAIN/COMPONENT, or of each component whose contract names a replay, through its specification with the pinned Lean, and compare the results line by line with those that its host tests wrote",
        subcommands: &[],
    },
    canary::COMMAND,
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
            clap::Command::new("run").about(about("run")).args([
                Arg::new("target")
                    .long("target")
                    .value_name("NAME")
                    .help("Run only this target; may be repeated")
                    .action(ArgAction::Append)
                    .value_parser(NonEmptyStringValueParser::new()),
                Arg::new("shard")
                    .long("shard")
                    .value_name("NAME")
                    .help("Run only the qualification job, qualification, or the shard of a formal target, target/<name>")
                    .conflicts_with("target")
                    .value_parser(merge::shard),
                clap::arg!(--calibration "Run in the layout of the calibration target"),
                keep(),
            ]),
        )
        .subcommand(guard::cli(about("guard")))
        .subcommand(
            clap::Command::new("toolchain-check")
                .about(about("toolchain-check"))
                .arg(path("aeneas"))
                .arg(path("charon")),
        )
        .subcommand(inventory::cli(about("check")))
        .subcommand(mutants::cli(about("mutants")).arg(keep()))
        .subcommand(paths::cli(about("impact")))
        .subcommand(merge::cli(about("merge")))
        .subcommand(receipt::cli(about("receipt")))
        .subcommand(vectors::cli(about("vectors")))
        .subcommand(canary::cli(about("canary")))
}

/// The flag of the commands that run the gate, which keeps the work
/// directory of the run.
fn keep() -> Arg {
    clap::arg!(--keep "Keep the work directory of the run, with its export, stages and extractions")
}

/// The layout that `--calibration` selects.
fn layout(matches: &ArgMatches) -> &'static Layout {
    [&Layout::PRODUCTION, &Layout::CALIBRATION][usize::from(matches.get_flag("calibration"))]
}

/// The targets that `cargo xtask formal run` was given, or that of its shard.
fn targets(matches: &ArgMatches) -> BTreeSet<String> {
    let targets = matches.get_many::<String>("target").into_iter().flatten();
    let shard = matches.get_one::<String>("shard");
    let shard = shard.and_then(|shard| merge::target(shard));
    targets.cloned().chain(shard.map(String::from)).collect()
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
        Some(("run", matches)) => {
            let (keep, shard) = (matches.get_flag("keep"), matches.get_one::<String>("shard"));
            let shard = shard.map(String::as_str);
            run::command(root, layout(matches), targets(matches), None, keep, shard)
        }
        Some(("mutants", matches)) => {
            let target = matches.get_one::<String>("target").cloned().into_iter();
            let operators = Some(mutants::operators(matches));
            run::command(
                root,
                layout(matches),
                BTreeSet::from_iter(target),
                operators,
                matches.get_flag("keep"),
                None,
            )
        }
        Some(("impact", matches)) => paths::command(root, &Layout::PRODUCTION, matches),
        Some(("merge", matches)) => merge::command(root, layout(matches), matches),
        Some(("receipt", matches)) => receipt::command(root, &Layout::PRODUCTION, matches),
        Some(("guard", matches)) => guard::command(root, &Layout::PRODUCTION, matches),
        Some(("toolchain-check", matches)) => {
            let path = |name| matches.get_one::<PathBuf>(name).expect("a required option");
            toolchain::command(root, &Layout::PRODUCTION, path("aeneas"), path("charon"))
        }
        Some(("check", matches)) => {
            inventory::command(root, layout(matches), matches.get_flag("write"))
        }
        Some(("vectors", matches)) => vectors::command(root, &Layout::PRODUCTION, matches),
        Some(("canary", matches)) => canary::command(root, &Layout::PRODUCTION, matches),
        _ => {
            let _ = cli().print_help();
            ExitCode::SUCCESS
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifests;
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
        for (args, calibration) in [(&["run"][..], false), (&["run", "--calibration"], true)] {
            let matches = read(args).expect("a valid command line");
            let (_, matches) = matches.subcommand().expect("a subcommand");
            assert_eq!(matches.get_flag("calibration"), calibration);
        }
        for (args, keep) in [
            (&["run"][..], false),
            (&["run", "--keep"], true),
            (&["mutants", "t"], false),
            (&["mutants", "t", "--keep"], true),
        ] {
            let matches = read(args).expect("a valid command line");
            let (_, matches) = matches.subcommand().expect("a subcommand");
            assert_eq!(matches.get_flag("keep"), keep, "{args:?}");
        }
        let mut run = cli()
            .find_subcommand("run")
            .cloned()
            .expect("the run command");
        let help = run.render_help().to_string();
        assert!(
            help.contains("Run in the layout of the calibration target"),
            "{help}"
        );
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
        let matches = read(&["guard", "--event", "event.json"]).expect("a valid command line");
        let (name, matches) = matches.subcommand().expect("a subcommand");
        assert_eq!(name, "guard");
        assert_eq!(
            matches.get_one::<PathBuf>("event"),
            Some(&PathBuf::from("event.json"))
        );
        for (args, write) in [(&["check"][..], false), (&["check", "--write"], true)] {
            let matches = read(args).expect("a valid command line");
            let (name, matches) = matches.subcommand().expect("a subcommand");
            assert_eq!((name, matches.get_flag("write")), ("check", write));
            assert!(!matches.get_flag("calibration"));
        }
        let matches = read(&["check", "--calibration"]).expect("a valid command line");
        assert!(
            matches
                .subcommand()
                .expect("check")
                .1
                .get_flag("calibration")
        );
        let mutants = |args: &[&str]| {
            let matches = read(args).expect("a valid command line");
            let (name, matches) = matches.subcommand().expect("a subcommand");
            assert_eq!(name, "mutants");
            let target = matches.get_one::<String>("target").cloned();
            (
                target,
                mutants::operators(matches),
                matches.get_flag("calibration"),
            )
        };
        let all = Vec::from_iter(mutants::OPERATORS.split(' ').map(String::from));
        assert_eq!(mutants(&["mutants", "t"]), (Some("t".into()), all, false));
        let args = [
            "mutants",
            "t",
            "--operator",
            "method",
            "--operator",
            "literal",
            "--calibration",
        ];
        let some = vec!["literal".to_string(), "method".to_string()];
        assert_eq!(mutants(&args), (Some("t".into()), some, true));
        for (args, component) in [(&["vectors"][..], None), (&["vectors", "d/c"], Some("d/c"))] {
            let matches = read(args).expect("a valid command line");
            let (name, matches) = matches.subcommand().expect("a subcommand");
            let component = component.map(String::from);
            assert_eq!(
                (name, matches.get_one("component")),
                ("vectors", component.as_ref())
            );
        }
        let matches = read(&["canary", "verdict", "--outcomes", "runner=success"]);
        let matches = matches.expect("a valid command line");
        let (name, matches) = matches.subcommand().expect("a subcommand");
        let text = |name| matches.get_one::<String>(name).map(String::as_str);
        assert_eq!(
            (name, text("step"), text("outcomes")),
            ("canary", Some("verdict"), Some("runner=success"))
        );
        // A shard names its targets: none for the qualification job.
        let shard = |args: &[&str]| {
            let matches = read(args).expect("a valid command line");
            let (_, matches) = matches.subcommand().expect("a subcommand");
            let shard = matches.get_one::<String>("shard").cloned();
            (shard, targets(matches), matches.get_flag("keep"))
        };
        let qualification = Some("qualification".to_string());
        assert_eq!(
            shard(&["run", "--shard", "qualification"]),
            (qualification, BTreeSet::new(), false)
        );
        let args = ["run", "--shard", "target/t", "--calibration", "--keep"];
        let t = BTreeSet::from(["t".to_string()]);
        assert_eq!(shard(&args), (Some("target/t".to_string()), t, true));
        let matches = read(&["impact", "--base", "origin/main"]).expect("a valid command line");
        let (name, matches) = matches.subcommand().expect("a subcommand");
        let base = matches.get_one::<String>("base").map(String::as_str);
        assert_eq!((name, base), ("impact", Some("origin/main")));
        let matches = read(&["merge", "a.json", "b.json", "--calibration"]);
        let matches = matches.expect("a valid command line");
        let (name, matches) = matches.subcommand().expect("a subcommand");
        let receipts = matches
            .get_many::<PathBuf>("RECEIPT")
            .expect("the receipts");
        let receipts = Vec::from_iter(receipts.cloned());
        assert_eq!(name, "merge");
        assert_eq!(receipts, [PathBuf::from("a.json"), PathBuf::from("b.json")]);
        assert!(matches.get_flag("calibration"));
        for (args, record, fresh) in [
            (&["receipt"][..], None, false),
            (&["receipt", "--require-fresh"], None, true),
            (
                &["receipt", "r.json", "--require-fresh"],
                Some("r.json"),
                true,
            ),
        ] {
            let matches = read(args).expect("a valid command line");
            let (name, matches) = matches.subcommand().expect("a subcommand");
            let found = matches.get_one::<PathBuf>("RECORD").cloned();
            let found = (name, found, matches.get_flag("require-fresh"));
            assert_eq!(found, ("receipt", record.map(PathBuf::from), fresh));
        }
        for args in [
            &["run", "--shard"][..],
            &["run", "--shard", "base"],
            &["run", "--shard", "target/"],
            &["run", "--shard", "targets/t"],
            &["run", "--shard", "qualification", "--target", "t"],
            &["run", "--target", "t", "--shard", "target/t"],
            &["run", "--shard", "qualification", "--shard", "target/t"],
            &["merge"],
            &["merge", "--keep"],
            &["merge", "--frobnicate"],
            &["receipt", "a", "b"],
            &["receipt", "--calibration"],
            &["run", "--reuse"],
        ] {
            let error = read(args).expect_err("a usage error");
            assert_eq!(error.exit_code(), 2, "{args:?}: {error}");
        }
        let help = read(&["merge", "--help"]).expect_err("the help");
        assert!(help.to_string().contains("<RECEIPT>..."), "{help}");
        let help = read(&["run", "--help"]).expect_err("the help");
        assert!(help.to_string().contains("--shard <NAME>"), "{help}");
        for args in [
            &["guard"][..],
            &["guard", "--event"],
            &["guard", "--event", "a", "b"],
            &["guard", "a"],
            &["impact"],
            &["impact", "--base"],
            &["impact", "--base", "a", "b"],
            &["run", "--target"],
            &["run", "--target", ""],
            &["run", "--targets", "a"],
            &["run", "a"],
            &["toolchain-check", "--aeneas", "a"],
            &["check", "a"],
            &["check", "--frobnicate"],
            &["check", "--keep"],
            &["vectors", "--keep"],
            &["vectors", "a", "b"],
            &["mutants"],
            &["mutants", "t", "--operator", "loops"],
            &["mutants", "t", "u"],
            &["vectors", "--frobnicate"],
            &["canary"],
            &["canary", "frobnicate"],
            &["canary", "patch", "fill"],
            &["canary", "verdict", "--outcomes"],
            &["frobnicate"],
        ] {
            let error = read(args).expect_err("a usage error");
            assert_eq!(error.exit_code(), 2, "{args:?}: {error}");
        }
        let help = read(&["run", "--help"]).expect_err("the help");
        assert_eq!(help.exit_code(), 0);
        assert!(help.to_string().contains("--target <NAME>"), "{help}");
        assert!(help.to_string().contains("--keep"), "{help}");
        let help = read(&["guard", "--help"]).expect_err("the help");
        assert!(help.to_string().contains("--event <PATH>"), "{help}");
        let help = read(&["vectors", "--help"]).expect_err("the help");
        assert!(help.to_string().contains("[DOMAIN/COMPONENT]"), "{help}");
        let help = read(&["canary", "--help"]).expect_err("the help");
        let help = help.to_string();
        assert!(
            help.contains("<STEP>") && help.contains("--outcomes <TEXT>"),
            "{help}"
        );
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
            layout.models.to_string(),
            layout.open.to_string(),
            layout.toolchain.to_string(),
            layout.statements.to_string(),
            layout.axioms.to_string(),
            layout.tcb.to_string(),
            layout.shards.to_string(),
            layout.waivers.to_string(),
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
            layout.statements,
            layout.axioms,
            layout.tcb,
            layout.waivers,
        ] {
            assert!(
                path.starts_with(&format!("{}/", layout.project)),
                "{path} is not in the Lake project"
            );
        }
    }

    #[test]
    fn the_calibration_layout_names_its_own_tracked_files_and_shares_the_rest() {
        let tree = Tree::load(&repo::root()).expect("the repository is readable");
        let (layout, production) = (Layout::CALIBRATION, Layout::PRODUCTION);
        let own = [
            layout.statements,
            layout.axioms,
            layout.tcb,
            layout.registry,
            layout.models,
            layout.shards,
        ];
        let manifest = format!("{}/Cargo.toml", layout.kernel);
        let lock = format!("{}/Cargo.lock", layout.kernel);
        let lakefile = format!("{}/lakefile.toml", layout.project);
        for path in own.into_iter().chain([manifest.as_str(), &lock, &lakefile]) {
            assert!(tree.exists(path), "{path} is not tracked");
            assert!(
                path.starts_with(&format!("{}/", layout.qualification)),
                "{path}"
            );
        }
        // The stages of the project take the other project files from the
        // production project.
        for file in &lean::PROJECT_FILES[1..] {
            assert!(
                !tree.exists(&format!("{}/{file}", layout.project)),
                "{file}"
            );
        }
        let package = manifests::root_package(tree.text(&manifest).expect("the manifest"));
        assert_eq!(package, Ok(Some(layout.package.to_string())));
        assert_ne!(layout.package, production.package);
        let shared = |layout: &Layout| {
            let paths = [
                layout.qualification,
                layout.cases,
                layout.extraction,
                layout.externals,
            ];
            let names = [
                layout.namespace,
                layout.generated,
                layout.proofs,
                layout.triple,
            ];
            let tools = [
                layout.root_project,
                layout.toolchain,
                layout.image_pin,
                layout.tooling,
            ];
            [paths, names, tools]
        };
        assert_eq!(shared(&layout), shared(&production));
        // No contract describes the calibration, whose survivors are its own,
        // and no waiver applies to it.
        assert!(layout.open.is_empty() && !production.open.is_empty());
        assert!(layout.waivers.is_empty() && !production.waivers.is_empty());
        let own = format!("{}/", layout.qualification);
        assert!(layout.mutants.starts_with(&own) && !production.mutants.starts_with(&own));
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
    fn the_lake_project_can_build_its_root_module() {
        let lakefile: toml::Table =
            toml::from_str(include_str!("../../../verification/lakefile.toml"))
                .expect("the Lake configuration parses");
        let libraries = lakefile["lean_lib"].as_array().expect("the libraries");
        let library = |name: &str| {
            (libraries.iter())
                .find(|library| library["name"].as_str() == Some(name))
                .unwrap_or_else(|| panic!("no library {name}"))
        };
        let layout = Layout::PRODUCTION;
        let names =
            |names: &[&str]| toml::Value::Array(names.iter().map(|name| (*name).into()).collect());
        // The root module is a library of its own, which the base round
        // builds as `+Krepi`; the library `Krepi` takes only the modules
        // below the root, so that a stage without the root builds it.
        assert_eq!(library("KrepiRoot")["roots"], names(&[layout.namespace]));
        let below = format!("{}.+", layout.namespace);
        assert_eq!(library(layout.namespace)["globs"], names(&[&below]));
        assert_eq!(lakefile["defaultTargets"], names(&[layout.namespace]));
        let proofs = format!("{}.", layout.namespace);
        assert!(layout.proofs.starts_with(&proofs), "{}", layout.proofs);
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
