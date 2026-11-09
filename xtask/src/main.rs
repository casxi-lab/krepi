//! Repository tasks for krepi, run from the repository root as
//! `cargo xtask <command>`.

mod check;
mod docs;
mod formal;
mod image;
mod manifests;
mod receipt;
mod repo;
#[cfg(test)]
mod scratch;
mod subset;
mod suite;
mod toolchain;
mod workflows;

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
        about: "Run the required host checks: the toolchain, manifest, format and Clippy checks, Clippy also on the kernel workspace for its bare-metal target, then at once the debug lane (the tests and the documentation, Lean source, provable-subset and workflow checks) and the release tests; the first failure or a stop signal cancels the other steps, and a summary gives the seconds of each step; --help lists the options",
        subcommands: &[],
    },
    Command {
        name: "formal",
        about: "The proof tooling; without a subcommand, list its commands",
        subcommands: formal::COMMANDS,
    },
    Command {
        name: "help",
        about: "List the commands",
        subcommands: &[],
    },
    Command {
        name: "image",
        about: "Write the images that the QEMU suites boot into a new directory, with images.json, which gives the size, SHA-256 and commit of each; --help lists the options",
        subcommands: &[],
    },
    Command {
        name: "qemu",
        about: "Run an ELF image on QEMU virt with one Cortex-A76 until the guest powers off or a limit ends the run, writing the serial transcript, QEMU's standard error and a receipt into a new directory; --help lists the options",
        subcommands: &[],
    },
    Command {
        name: "qemu-boot",
        about: "Build the QEMU virt default image and run the QEMU boot suite on it: three cold boots with the serial echo, each judged against fixed expected records, with a receipt of each run and of the suite in a new directory; --help lists the options",
        subcommands: &[],
    },
    Command {
        name: "serial-capture",
        about: "Record what a board sends over a serial port for a bounded time into a new directory, without evaluating its boot; --help lists the options",
        subcommands: &[],
    },
    Command {
        name: "suite",
        about: "Run the QEMU suites of suites.toml: the smoke cases and the suites that the paths changed since a base select, or every suite, with the slow cases on request, each case judged by its expected output, with a report in a new directory; --help lists the options",
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
    let words: Vec<&str> = args.iter().map(String::as_str).collect();
    // The options of the check may also be written before `check`.
    if let Some(rest) = check::arguments(&words) {
        return check::command(repo::root(), &rest);
    }
    match words.as_slice() {
        ["qemu", rest @ ..] => {
            let args: Vec<String> = rest.iter().map(|arg| arg.to_string()).collect();
            let code = krepi_tools::qemu_run::main(&repo::root(), &args);
            // The command exits with 0, 1, 2, 120 or 130.
            ExitCode::from(u8::try_from(code).unwrap_or(2))
        }
        ["qemu-boot", rest @ ..] => {
            let args: Vec<String> = rest.iter().map(|arg| arg.to_string()).collect();
            let code = krepi_tools::qemu_boot::main(&repo::root(), &args);
            // The command exits with 0, 1, 2, 120 or 130.
            ExitCode::from(u8::try_from(code).unwrap_or(2))
        }
        ["serial-capture", rest @ ..] => {
            let args: Vec<String> = rest.iter().map(|arg| arg.to_string()).collect();
            let code = krepi_tools::serial_capture::main(&repo::root(), &args);
            // The command exits with 0, 2, 120 or 130.
            ExitCode::from(u8::try_from(code).unwrap_or(2))
        }
        ["formal", rest @ ..] => formal::run(&repo::root(), rest),
        ["image", rest @ ..] => image::command(&repo::root(), rest),
        ["suite", rest @ ..] => suite::command(&repo::root(), rest),
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
