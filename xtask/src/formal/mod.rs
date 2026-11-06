//! `cargo xtask formal`: the proof tooling.
//!
//! The paths and names that the formal commands share are gathered in one
//! [`Layout`]; the modules take them from there and never spell them out
//! themselves. This module uses only the standard library, apart from what
//! its submodules take from the crates of the xtask manifest.

pub mod toolchain;

use std::path::Path;
use std::process::ExitCode;

use crate::Command;

/// The paths and names of the repository that the formal commands use.
#[derive(Debug, Clone, Copy)]
pub struct Layout {
    /// The kernel workspace, the input of extraction, relative to the
    /// repository root.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the extraction is the first reader")
    )]
    pub kernel: &'static str,
    /// The Lean namespace of the handwritten modules: specifications,
    /// statements, proofs and qualification proofs.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the Lean build is the first reader")
    )]
    pub namespace: &'static str,
    /// The Lean namespace of the definitions that Aeneas generates.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the extraction is the first reader")
    )]
    pub generated: &'static str,
    /// The target triple for which the kernel workspace is extracted.
    pub triple: &'static str,
    /// The proof target registry, relative to the repository root.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the registry checks are the first reader")
    )]
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
        kernel: "kernel",
        namespace: "Krepi",
        generated: "KrepiGen",
        triple: "aarch64-unknown-none",
        registry: "verification/targets.json",
        toolchain: "verification/toolchain.json",
        tooling: "verification/tooling",
    };
}

/// The subcommands of `cargo xtask formal`.
pub const COMMANDS: &[Command] = &[Command {
    name: "toolchain-check",
    about: "With --aeneas <dir> --charon <dir>, check the Aeneas and Charon source trees and the Aeneas patch against verification/toolchain.json",
    subcommands: &[],
}];

fn print_help() {
    println!("Usage: cargo xtask formal <command>\n\nCommands:");
    for command in COMMANDS {
        println!("  {:<16} {}", command.name, command.about);
    }
}

/// Entry point of `cargo xtask formal`, with the arguments that follow
/// `formal`.
pub fn run(root: &Path, args: &[&str]) -> ExitCode {
    match args {
        ["toolchain-check", "--aeneas", aeneas, "--charon", charon] => toolchain::command(
            root,
            &Layout::PRODUCTION,
            Path::new(aeneas),
            Path::new(charon),
        ),
        [] => {
            print_help();
            ExitCode::SUCCESS
        }
        _ => {
            eprintln!("unknown command: cargo xtask formal {}\n", args.join(" "));
            print_help();
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::{self, Tree};

    #[test]
    fn the_production_layout_names_tracked_files() {
        let tree = Tree::load(&repo::root()).expect("the repository is readable");
        let layout = Layout::PRODUCTION;
        for path in [
            format!("{}/Cargo.toml", layout.kernel),
            layout.registry.to_string(),
            layout.toolchain.to_string(),
            format!("{}/LICENSE-Apache-2.0", layout.tooling),
        ] {
            assert!(tree.exists(&path), "{path} is not tracked");
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
