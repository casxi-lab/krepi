//! Repository tasks for krepi, run from the repository root as
//! `cargo xtask <command>`.

mod check;
mod docs;
mod manifests;
mod repo;
mod toolchain;

use std::process::ExitCode;

/// A command of `cargo xtask`, possibly with subcommands of its own.
pub struct Command {
    pub name: &'static str,
    pub about: &'static str,
    pub subcommands: &'static [Command],
}

/// Every command that `cargo xtask` provides. The documentation check
/// accepts a `cargo xtask` mention only when it names one of these.
pub const COMMANDS: &[Command] = &[
    Command {
        name: "check",
        about: "Run the toolchain, manifest, format, Clippy, test and documentation checks",
        subcommands: &[],
    },
    Command {
        name: "help",
        about: "List the commands",
        subcommands: &[],
    },
];

fn print_help() {
    println!("Usage: cargo xtask <command>\n\nCommands:");
    for command in COMMANDS {
        println!("  {:<8} {}", command.name, command.about);
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        ["check"] => check::run(repo::root()),
        [] | ["help"] => {
            print_help();
            ExitCode::SUCCESS
        }
        _ => {
            eprintln!("unknown command: cargo xtask {}\n", args.join(" "));
            print_help();
            ExitCode::from(2)
        }
    }
}
