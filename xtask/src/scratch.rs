//! A directory for the files of one unit test, removed with its value.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::check;

pub struct Scratch(pub PathBuf);

impl Scratch {
    /// A new directory below the profile directory of the build, whose
    /// `deps` directory holds the test executable.
    pub fn new(label: &str) -> Scratch {
        let executable = std::env::current_exe().expect("locate the test executable");
        let profile = executable
            .parent()
            .and_then(Path::parent)
            .expect("the test executable lies in the deps directory of a profile");
        Scratch::below(&profile.join("scratch"), label)
    }

    /// A new directory below the system's temporary directory, outside the
    /// repository, so that no Cargo configuration of the repository lies
    /// above it.
    pub fn temporary(label: &str) -> Scratch {
        Scratch::below(&std::env::temp_dir(), label)
    }

    fn below(base: &Path, label: &str) -> Scratch {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = base.join(format!(
            "krepi-xtask-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        // A directory of the same name can only be left over from an
        // earlier process with the same identifier.
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("create the scratch directory");
        Scratch(path)
    }

    /// Writes `text` to the relative path `name`, with its directories.
    pub fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().expect("a file has a directory"))
            .expect("create a scratch directory");
        fs::write(path, text).expect("write a scratch file");
    }

    /// Writes `Cargo.lock` for the kernel workspace, offline.
    pub fn lock(&self) {
        let output = Command::new(check::cargo())
            .args([
                "generate-lockfile",
                "--offline",
                "--manifest-path",
                "kernel/Cargo.toml",
            ])
            .current_dir(&self.0)
            .output()
            .expect("run cargo generate-lockfile");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stderr}");
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
