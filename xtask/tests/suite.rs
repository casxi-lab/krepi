//! The binaries of `cargo xtask image` and `cargo xtask suite` boot the test
//! image on the QEMU of the host, found on the search path as the commands
//! find it, as the image and suite jobs of CI do: the image command writes
//! the image with its digest, and the suite takes it by that digest. The
//! rules of both commands are tested in their modules with a fake QEMU; this
//! test starts the binary of this build, the one that `cargo xtask` runs, on
//! the real QEMU, with its output below the target's temporary directory.

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// The binary of this build.
const XTASK: &str = env!("CARGO_BIN_EXE_xtask");
/// The SHA-256 digest of the test image, from `shasum -a 256` of the file
/// that `krepi_tools::test_elf::write` writes.
const IMAGE_SHA256: &str = "976e92deeebc2bd2eb3c224f570facfef845c2c2adb987ef5960eb1061e7d7a6";

/// A directory below the target's temporary directory, removed at its end.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Self {
        let path = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("suite-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).unwrap();
        Scratch(path)
    }

    fn join(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Runs the binary with `args` in the repository root.
fn xtask(args: &[&str]) -> Output {
    Command::new(XTASK)
        .args(args)
        .current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap())
        .output()
        .expect("start the xtask binary")
}

fn report(dir: &Path) -> Value {
    serde_json::from_str(&std::fs::read_to_string(dir.join("summary.json")).unwrap()).unwrap()
}

/// The image command writes the test image with its digest; the suite boots
/// it with that digest, and refuses it before QEMU starts with another one.
#[test]
fn the_suite_boots_the_image_by_its_digest() {
    let scratch = Scratch::new("digest");
    let images = scratch.join("images");
    let images = images.to_str().unwrap();
    let image = xtask(&["image", "--output-dir", images]);
    assert_eq!(image.status.code(), Some(0), "{image:?}");
    let record: Value =
        serde_json::from_str(&std::fs::read_to_string(scratch.join("images/images.json")).unwrap())
            .unwrap();
    assert_eq!(record["images"][0]["sha256"], IMAGE_SHA256);
    let expect = format!("test-elf={IMAGE_SHA256}");
    let output = scratch.join("suite");
    let suite = xtask(&[
        "suite",
        "--images",
        images,
        "--expect",
        &expect,
        "--output-dir",
        output.to_str().unwrap(),
    ]);
    let stdout = String::from_utf8_lossy(&suite.stdout);
    assert_eq!(suite.status.code(), Some(0), "{stdout}{suite:?}");
    assert!(
        stdout.contains("\ntest-elf/boot-1: guest_shutdown, 54 bytes of serial output\n"),
        "{stdout}"
    );
    let passed = report(&output);
    assert_eq!(passed["status"], "PASS");
    assert_eq!(passed["images"][0]["sha256"], IMAGE_SHA256);
    assert_eq!(passed["images"][0]["expected"], IMAGE_SHA256);
    let cases = passed["suites"][0]["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 1, "{passed:#}");
    assert_eq!(cases[0]["name"], "boot");
    assert_eq!(cases[0]["status"], "PASS");
    // Another expected digest: an error before any run.
    let other = format!("test-elf={}", "0".repeat(64));
    let refused = scratch.join("refused");
    let suite = xtask(&[
        "suite",
        "--images",
        images,
        "--expect",
        &other,
        "--output-dir",
        refused.to_str().unwrap(),
    ]);
    assert_eq!(suite.status.code(), Some(2), "{suite:?}");
    assert_eq!(report(&refused)["status"], "ERROR");
    assert!(!refused.join("test-elf").exists());
}
