//! The build script of the QEMU virt crate: it gives the linker the link
//! script of the default image when the crate is built for the bare-metal
//! target. Host builds link with the host's own defaults.
//!
//! Feature: krepi.platform.qemu-virt-boot

fn main() {
    println!("cargo::rerun-if-changed=link.ld");
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if target_os == "none" {
        let directory = std::env::var("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR");
        println!("cargo::rustc-link-arg-bins=-T{directory}/link.ld");
    }
}
