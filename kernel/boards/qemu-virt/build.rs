//! The build script of the QEMU virt crate: it gives the linker the link
//! script of the images when the crate is built for the bare-metal target,
//! to the default image and to the test images, the examples of the crate.
//! A test image is entered at its own `krepi_test_entry`, which is
//! `_start` or, on the machine with EL2, an entry that drops to EL1 before
//! it. Host builds link with the host's own defaults.
//!
//! Feature: krepi.platform.qemu-virt-boot

fn main() {
    println!("cargo::rerun-if-changed=link.ld");
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if target_os == "none" {
        let directory = std::env::var("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR");
        println!("cargo::rustc-link-arg-bins=-T{directory}/link.ld");
        println!("cargo::rustc-link-arg-examples=-T{directory}/link.ld");
        println!("cargo::rustc-link-arg-examples=--entry=krepi_test_entry");
    }
}
