<picture>
  <source media="(prefers-color-scheme: dark)" srcset=".github/assets/logo-dark.svg">
  <img alt="krepi" src=".github/assets/logo.svg" height="64">
</picture>

# krepi

krepi is the operating system of casξ, a portable workstation for
mathematics, science and programming built on the Raspberry Pi 5. The name
comes from κρηπίς, the stepped platform that a temple stands on.

krepi is a microkernel written in Rust for AArch64. The kernel runs at EL1
and keeps only the mechanisms that need privilege: memory protection,
scheduling, communication between processes and interrupt delivery. Device
drivers, file systems, program loaders and system policy run as ordinary
processes at EL0, each in its own address space, and receive only the
authority that the system grants them. Formal verification of the kernel is a
primary goal of the project: kernel code is to be written against
independent specifications and proved in Lean 4.

## Status

This repository is newly initialized. It contains this README, the krepi logo,
the contribution rules, the target architecture, the documentation conventions,
empty proof registries and a commit-message hook. There is no kernel source yet.
Nothing builds or boots, and there are no build, test or run commands.
Continuous integration is not set up.

An earlier prototype of the system is kept read-only and is not public. It is
the source for porting: boot code, board
support, drivers, services and tests are taken from it module by module, as
[porting](docs/conventions/porting.md) describes. A capability of the
prototype becomes a capability of krepi only after it has been ported,
tested and, where required, proved again in this repository.

## Hardware

- **Raspberry Pi 5.** The target board (BCM2712 with four Cortex-A76 cores).
- **QEMU virt with Cortex-A76.** Generic mechanisms are validated here first.
  QEMU virt is a generic ARM64 machine with its own addresses, interrupt
  routing and boot conditions; a result on QEMU says nothing about the Pi 5.

krepi is designed around one system image per supported board that serves
every product function. Product functions are never split into build-time
variants of the image that exclude each other.

## What krepi is for

krepi is the platform that the casξ applications run on: the computer algebra
system, graphing, compound documents, Python programming and local Lean proof
checking. The long-term target is a complete application platform with:

- Rust `std`, C and C++ standard libraries, and the full Go standard library
  with its runtime;
- POSIX and GNU interfaces, a general-purpose shell, dynamic linking with
  shared libraries and `dlopen`, and networking with TLS;
- Linux system-call and binary compatibility for unmodified Linux programs;
- the full CPython ecosystem, including the standard library, package
  installation and native extensions;
- Lean and Lake, compiling and checking proofs on the device;
- desktop application frameworks;
- parallel execution on all four cores, with the controls of the device
  staying responsive under full load.

The kernel stays `no_std`. Compatibility layers and frameworks are user-space
services and libraries.

On the verification side the target is a reproducible argument of functional
correctness and security for a declared configuration of the privileged
kernel, covering the Rust code, the necessary assembly and architecture
paths, concurrency and the delivered binary. Every claim names its
configuration and the trusted items it still relies on. See
[formal verification](docs/formal-verification.md).

## First release

The first release is planned to:

- boot on QEMU virt and on the Raspberry Pi 5 straight into a resident root
  process, without waiting for serial input;
- start the file, block, stream and UART services as separate EL0 processes;
- run the casξ CAS calculator, built from a pinned commit of the CAS library,
  as a job over the serial console, with the same output bytes on a
  development host, on QEMU and on the Pi 5, and with a budget, cancellation,
  forced stop and reclamation of its resources;
- run small Rust `std`, C and C++ programs built with the krepi SDK;
- ship a default image without diagnostic commands or fault probes;
- check proofs of the kernel object core, capabilities, IPC and waits,
  system-call dispatch and loader validation in CI, and publish a declaration
  of what is proved and which items are trusted.

None of this works yet.

## Related repositories

| Repository | Role |
| --- | --- |
| [casxi-lab/kalyx](https://github.com/casxi-lab/kalyx) | The CAS library; its code is still to be moved in |
| [casxi-lab/kosmo](https://github.com/casxi-lab/kosmo) | The user interface and graphical shell |

The CAS library runs on krepi as an ordinary user program; the UI runs on top
of the system services. Neither is part of the kernel.

## Documentation

| Document | Contents |
| --- | --- |
| [Architecture](docs/architecture.md) | Target design: protection domains, the resident root, objects and capabilities, IPC, scheduling, memory, multicore, devices |
| [Formal verification](docs/formal-verification.md) | How proofs, specifications and registries are organized |
| [Subject domains](docs/domains/README.md) | The complete target scope of the system, by subject |
| [Feature index](docs/features/README.md) | What the system provides today (empty) |
| [Documentation conventions](docs/conventions/documentation.md) | Feature documents, domain and component documents |
| [Testing](docs/conventions/testing.md) | Test layout, environments and evidence |
| [Porting](docs/conventions/porting.md) | How code is taken from the prototype tree |
| [Contributing](CONTRIBUTING.md) | Rules for changes, commits and evidence |

## License

krepi is released under the [MIT License](LICENSE). Copyright (c) 2026 The
casξ Authors; see [AUTHORS](AUTHORS).
