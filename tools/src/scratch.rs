//! A directory for the files of one unit test, below the build directory and
//! removed with its value.

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Distinguishes the directories of one test process.
static NEXT: AtomicUsize = AtomicUsize::new(0);

/// A fresh, empty directory that is removed when the value is dropped.
pub struct Scratch {
    path: PathBuf,
}

impl Scratch {
    /// Creates the directory, named after `label`, the process and a counter,
    /// in `scratch` below the profile directory of the build, whose `deps`
    /// directory holds the test executable. Test files thus never fill the
    /// system temporary directory.
    pub fn new(label: &str) -> Scratch {
        let executable = std::env::current_exe().expect("locate the test executable");
        let profile = executable
            .parent()
            .and_then(|deps| deps.parent())
            .expect("the test executable lies in the deps directory of a profile");
        let root = profile.join("scratch");
        std::fs::create_dir_all(&root).expect("create the scratch root");
        let path = root.join(format!(
            "krepi-tools-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        // A directory of the same name can only be left over from an earlier
        // process with the same identifier.
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir(&path).expect("create the scratch directory");
        Scratch { path }
    }

    /// The path of `name` inside the directory.
    pub fn path(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }

    /// Writes `data` to `name` inside the directory and returns its path.
    pub fn write(&self, name: &str, data: &[u8]) -> PathBuf {
        let path = self.path(name);
        std::fs::write(&path, data).expect("write a scratch file");
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}
