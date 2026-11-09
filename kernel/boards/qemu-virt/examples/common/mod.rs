//! What the test images of QEMU virt share: the start record, the records of
//! their self-checks and of their end, and their panic handler.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! A test image links the same production code as the default image, the
//! cold entry, the exception vectors, the console and the exception record,
//! and adds its own `kernel_main`, exception dispatch and trigger sequence.
//! Its output is a start record, the records of the exceptions that it takes,
//! one record for each of its self-checks and, when its code resumes after
//! the exceptions, an end record. The QEMU boot suite holds the output
//! against the record table of the boot contract.

use core::panic::PanicInfo;

use krepi_arch::cpu;
use krepi_qemu_virt::console::PanicLocation;
use krepi_qemu_virt::uart;

/// Sets the console up and writes the start record `CASXI_TEST
/// image=<image>`.
pub fn start(image: &str) {
    uart::init();
    uart::print(format_args!("CASXI_TEST image={image}\n"));
}

/// The failure mask of `checks`: bit `n` is set when check `n` is false.
pub fn failures(checks: &[bool]) -> u64 {
    checks
        .iter()
        .enumerate()
        .filter(|(_, held)| !**held)
        .fold(0, |mask, (bit, _)| mask | 1 << bit)
}

/// Writes the record of the self-check `name` with the mask of its failed
/// checks: `CASXI_CHECK name=<name> failures=0x<16>`, 0 when every check
/// held.
pub fn check(name: &str, checks: &[bool]) {
    let failures = failures(checks);
    uart::print(format_args!(
        "CASXI_CHECK name={name} failures={failures:#018x}\n"
    ));
}

/// Writes the end record `CASXI_RESUMED`, after which the image writes
/// nothing, and halts with every exception masked.
pub fn finish() -> ! {
    uart::print(format_args!("CASXI_RESUMED\n"));
    cpu::halt()
}

/// Writes the panic record, as the default image does, and halts.
#[panic_handler]
fn panic(info: &PanicInfo<'_>) -> ! {
    let location = info.location().map(|location| PanicLocation {
        file: location.file(),
        line: location.line(),
        column: location.column(),
    });
    uart::report_panic(info.message().as_str(), location);
    cpu::halt()
}
