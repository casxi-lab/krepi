//! Host tooling for krepi tests: a bounded ELF64 reader, the JSON values
//! that tool reports are written from, the serial port transport with the
//! interrupt flag of a session, the serial capture of a board's serial port
//! behind `cargo xtask serial-capture`, the serial link over the standard
//! streams of a process, the QEMU virt command with the serial capture of a
//! guest on QEMU or behind a board's serial port and the process helpers,
//! the run of an image on QEMU behind `cargo xtask qemu`, the test image that
//! it boots in the tests, the QEMU boot suite of the kernel behind `cargo
//! xtask qemu-boot`, the terminal that these commands share, the line
//! matchers and record parsers of a guest's serial output, and the time
//! values of these tools per platform.
//!
//! The library runs on the development host and in CI, both Unix hosts. It
//! is not part of any krepi image and never runs the files that it reads on
//! the host: an image runs only inside QEMU.

#[cfg(not(unix))]
compile_error!("krepi-tools runs on Unix hosts only");

pub mod console;
pub mod elf;
pub mod qemu;
pub mod qemu_boot;
pub mod qemu_run;
pub mod receipt;
pub mod report;
pub mod serial;
pub mod serial_capture;
pub mod test_elf;
pub mod timing;
pub mod tty;

#[cfg(test)]
mod child;
#[cfg(test)]
mod pty;
#[cfg(test)]
mod scratch;

/// How long a test waits for something that it expects to happen, such as
/// bytes on a pseudo-terminal or the end of a child process. It elapses only
/// when the test fails, so it is generous: a slow host never reaches it.
#[cfg(test)]
const TEST_WAIT: std::time::Duration = std::time::Duration::from_secs(60);

/// A check that did not hold, with the message that describes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure(pub String);

impl Failure {
    pub fn new(message: impl Into<String>) -> Self {
        Failure(message.into())
    }
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Failure {}

/// The lowercase hexadecimal digits of `bytes`, two for each byte.
pub(crate) fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

impl From<std::io::Error> for Failure {
    fn from(error: std::io::Error) -> Self {
        Failure(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::Failure;

    #[test]
    fn a_failure_displays_its_message() {
        let failure = Failure::new("missing GNU build-id note");
        assert_eq!(failure.to_string(), "missing GNU build-id note");
        assert_eq!(failure, Failure("missing GNU build-id note".to_string()));
    }

    #[test]
    fn an_io_error_becomes_a_failure_with_its_text() {
        let error = std::io::Error::new(std::io::ErrorKind::NotFound, "no such image");
        assert_eq!(Failure::from(error), Failure::new("no such image"));
        // An operating-system error keeps the text that the standard library
        // gives it, with its error number.
        let os = std::io::Error::from_raw_os_error(2);
        let text = os.to_string();
        assert!(text.ends_with("(os error 2)"), "{text}");
        assert_eq!(Failure::from(os).0, text);
    }
}
