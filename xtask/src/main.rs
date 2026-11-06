//! Repository tasks for krepi, run from the repository root as
//! `cargo xtask <command>`.

mod check;
mod docs;
mod manifests;
mod receipt;
mod repo;
mod toolchain;
mod workflows;

use std::path::PathBuf;
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
        about: "Run the toolchain, manifest, format, Clippy, test, documentation and workflow checks; with --receipt <path>, also write a JSON receipt of the run",
        subcommands: &[],
    },
    Command {
        name: "help",
        about: "List the commands",
        subcommands: &[],
    },
    Command {
        name: "serial-capture",
        about: "Record what a board sends over a serial port for a bounded time into a new directory, without evaluating its boot; --help lists the options",
        subcommands: &[],
    },
];

fn print_help() {
    println!("Usage: cargo xtask <command>\n\nCommands:");
    for command in COMMANDS {
        println!("  {:<14} {}", command.name, command.about);
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
        ["check"] => check::run(repo::root(), None),
        ["check", "--receipt", path] => check::run(repo::root(), Some(PathBuf::from(path))),
        ["serial-capture", rest @ ..] => {
            let args: Vec<String> = rest.iter().map(|arg| arg.to_string()).collect();
            let code = krepi_tools::serial_capture::main(&repo::root(), &args);
            // The command exits with 0, 2, 120 or 130.
            ExitCode::from(u8::try_from(code).unwrap_or(2))
        }
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
