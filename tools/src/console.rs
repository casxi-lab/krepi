//! The terminal of a command of the host tools, `cargo xtask serial-capture`
//! or `cargo xtask qemu`: its two output streams, the exit status that a
//! failed write on them gives, and its interrupt handlers.
//!
//! After a failed write on standard output a command writes nothing more
//! there and ends with `<command>: cannot write standard output: <error>` on
//! standard error and status 120; a failed write on standard error makes the
//! status 120 as well.

use crate::Failure;
use crate::tty;
use clap::error::ErrorKind;
use std::io::{self, Write};
use std::sync::atomic::AtomicI32;

/// The terminal of a command: its two output streams and the interrupt
/// handlers.
pub struct Console<'a> {
    /// Writes one text and a newline on standard output.
    pub print: &'a mut dyn FnMut(&str) -> io::Result<()>,
    /// Writes one text and a newline on standard error.
    pub warn: &'a mut dyn FnMut(&str) -> io::Result<()>,
    /// Called immediately before the command starts what an interrupt
    /// should end, such as opening a port or starting QEMU: installs the
    /// interrupt handlers and returns the flag they set.
    pub arm: &'a mut dyn FnMut() -> Result<&'a AtomicI32, Failure>,
}

/// Runs `body` with the console of the process: each text goes to standard
/// output, which is flushed after it, or to standard error, and `arm`
/// installs the handlers of [`tty::catch_interrupts`].
pub(crate) fn with_process_console<T>(body: impl FnOnce(&mut Console) -> T) -> T {
    let console = &mut Console {
        print: &mut |text| {
            let mut stdout = io::stdout().lock();
            writeln!(stdout, "{text}").and_then(|()| stdout.flush())
        },
        warn: &mut |text| writeln!(io::stderr(), "{text}"),
        arm: &mut || tty::catch_interrupts(),
    };
    body(console)
}

/// The output streams of one run of the command `command`, with what failed
/// on them.
pub(crate) struct Streams<'c, 'a> {
    pub(crate) console: &'c mut Console<'a>,
    /// The name of the command in the report of a failed write.
    command: &'static str,
    /// The first write on standard output that failed; nothing more is
    /// written there after it.
    unwritten: Option<io::Error>,
    /// Whether a write on standard error failed.
    unwarned: bool,
}

impl<'c, 'a> Streams<'c, 'a> {
    pub(crate) fn new(command: &'static str, console: &'c mut Console<'a>) -> Self {
        Streams {
            console,
            command,
            unwritten: None,
            unwarned: false,
        }
    }

    pub(crate) fn print(&mut self, text: &str) {
        if self.unwritten.is_none()
            && let Err(error) = (self.console.print)(text)
        {
            self.unwritten = Some(error);
        }
    }

    pub(crate) fn warn(&mut self, text: &str) {
        if (self.console.warn)(text).is_err() {
            self.unwarned = true;
        }
    }

    /// Writes the error with which clap ended the reading of a command line:
    /// the help on standard output, which gives status 0, or a usage error on
    /// standard error, which gives status 2. Clap's text ends with a newline,
    /// which the streams add.
    pub(crate) fn clap_error(&mut self, error: &clap::Error) -> i32 {
        let text = error.render().to_string();
        let text = text.strip_suffix('\n').unwrap_or(&text);
        if error.kind() == ErrorKind::DisplayHelp {
            self.print(text);
            0
        } else {
            self.warn(text);
            2
        }
    }

    /// The exit status of a run whose work ended with `code`: 120 after a
    /// failed write, which on standard output is reported on standard error.
    pub(crate) fn exit(mut self, code: i32) -> i32 {
        if let Some(error) = self.unwritten.take() {
            let command = self.command;
            self.warn(&format!("{command}: cannot write standard output: {error}"));
            return 120;
        }
        if self.unwarned { 120 } else { code }
    }
}
