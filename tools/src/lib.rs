//! Host tooling for krepi tests: a bounded ELF64 reader and the JSON values
//! that tool reports are written from.
//!
//! The library runs on the development host and in CI. It is not part of any
//! krepi image and never executes the files it reads.

pub mod elf;
pub mod report;

#[cfg(test)]
mod scratch;

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
