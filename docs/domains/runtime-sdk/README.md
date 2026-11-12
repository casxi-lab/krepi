# Runtime ABI and SDK

## Overview

The runtime ABI and SDK domain decides how a program at EL0 calls the
kernel, how it starts, and what it is built from and runs on. It covers the
dispatch of native system calls, with the revalidation of the calls that
load an image into a child, and the inventory of native operations; the
entry of an application with its C runtime start-up code (CRT); the sysroots
against which programs are built; the Rust standard library and the C and
C++ libraries; threads, thread-local storage (TLS) and the floating-point
environment of the runtimes; the Go runtime; and the SDK packages.

Three limits bound the domain. A native call passes its arguments in at most
six registers, `x0` to `x5`, with `x6` reserved, the major version of the
ABI in `x7` and the operation number in the low 16 bits of `x8`, and
receives its results in `x0` to `x5`; larger data goes through shared
buffers, through several calls, or through argument structures that the
kernel copies in once
([user-buffer access](../memory/README.md#user-buffer-access)). The kernel
parses no ELF file and runs no loader of its own: the loader of EL0 parses
an image of the boot bundle and asks the kernel for its segments one at a
time, and the kernel accepts only R, RX and RW segments, at most eight for
an image, all in the image window of the child; the R and RX pages are pages
of the boot bundle and the RW pages are private, so no page of a loaded
image is both writable and executable. EL0 uses the floating-point hardware
and starts every thread with one default environment, while the kernel
itself is built softfloat; a result on QEMU virt with one CPU does not show
the behaviour of the Pi 5 or of several CPUs.

The domain builds on others, listed in the
[subject-domain index](../README.md). The boot and platform domain gives the
exception vectors through which an `SVC` enters, and its
[context](../boot-platform/context/requirements.md) component the saved user
context of each thread, with its initial value, the results that a call
writes into it and the save and restore of its FP/SIMD and TLS registers;
the memory and address-spaces domain gives the entry from EL0 and the return
to it with the classes of exceptions and user faults, the layout of the EL0
window, the boot information of the root and the boot-bundle directory with
its capacity record, and
[W^X and code publication](../memory/README.md#wx-and-code-publication),
which bind every page that loading maps; the kernel objects and capabilities
domain gives the handles, rights and lookups through which an operation
acts, the creation of a child, which maps the image that the loading
component accepts and puts the initial capabilities into the child's table,
and the lifetimes of processes, which end a process at a user fault; the IPC
and waits and the scheduling and budgets domains give the operations that
most calls reach, the settlement of deadlines and the choice of the thread
that returns to EL0; the security and lifecycle domain decides which bytes
may be loaded and executed, by the
[integrity policy](../../security.md#integrity-policy) of the security
model, while this domain checks the form, the place and the limits of each
request to load; the EL0 services and storage domain holds the root, the
process manager and the process services, which load programs; and the
compatibility personalities build POSIX and Linux on the libraries of this
domain. The [dispatch](dispatch/requirements.md) component holds the
decoding of every native system call and its rejection, the checks that come
before those of an operation, the rule for the rights of an operation, the
results of a refused call, and the composition of every entry from EL0 into
one transition with the round trip of its plans through the architecture
crate; in its module `loader`, for which other contracts call the component
the loading component, it holds the revalidation of the segments and of the
commit of an image, the loading part of the capacity record and the image
window.

## Conventions

- **One table for native calls.** Every native system call enters by
  `svc #0` through one dispatch table, keyed by the major version and the
  operation number. The system calls of a Linux program never enter it: they
  reach the compatibility runtime of their process as upcalls.
- **Dispatch checks first.** The immediate of the `SVC`, the version, the
  operation number, the reserved register and the unused argument registers
  are checked, in this order, before any check of the operation; the checks
  of the operation follow in the order of errors of the
  [security model](../../security.md#internal-choices).
- **Rights are constants.** The rights that an operation needs are fixed by
  its contract and checked by the lookup of its handles; no argument of a
  call names or widens them.
- **A refusal changes nothing.** A refused call writes its status into `x0`
  and 0 into `x1` to `x5`, keeps every other register, changes no other
  state and counts nothing.
- **Numbers are never reused.** An operation number keeps its operation for
  good, and a deprecated operation keeps its meaning within its major
  version.
- **Loading is checked again.** The kernel checks every request to load an
  image itself, whatever the loader of EL0 has checked, against limits that
  the boot configuration sets.
- **Library state stays in EL0.** The POSIX state of a process, the TLS of a
  thread and its floating-point environment belong to the runtime of EL0 and
  to the saved context of the thread; the kernel keeps no state of a library
  and changes no environment of a thread.

## Feature index

| Feature | Scope | Feature documents | Components |
| --- | --- | --- | --- |
| [System-call dispatch](#system-call-dispatch) | The decoding of a native call, its rejection, the checks before those of an operation, rights, the results of a refusal, the composition of a transition, and the revalidation of the parameters of the calls that load an image | - | [dispatch](dispatch/requirements.md), with the revalidation of the parameters of the loading request calls |
| [The operation inventory](#the-operation-inventory) | The committed list of native operations with their numbers, versions, arguments, results, rights and errors; the ranges of numbers, versions and deprecation | - | The operation inventory, with the ABI crate that gives its data to EL0 |
| [Application entry and CRT](#application-entry-and-crt) | The start of a program: its image, its initial context and capabilities, its start message, and the CRT that runs before and after its main function | - | The CRT and the application entry of each runtime |
| [Sysroots](#sysroots) | The headers, libraries and start-up objects against which native programs are built, isolated from those of other systems | - | The sysroot recipes |
| [Rust std](#rust-std) | The Rust standard library on the native ABI | - | The port of the Rust standard library |
| [C and C++ libraries](#c-and-c-libraries) | The native C library, a port of glibc with its math library, and the C++ standard library on it | - | The C and C++ libraries |
| [Threads](#threads) | The threads of a process in the runtimes, their creation, their end and the synchronization of the libraries | - | The thread runtime |
| [TLS](#tls) | The thread-local storage of each thread, its block and the thread pointer | - | The thread-local storage of the runtimes |
| [The floating-point environment](#the-floating-point-environment) | The environment of each thread, its default, its inheritance and its preservation | - | The floating-point environment of the runtimes |
| [The Go runtime](#the-go-runtime) | The Go runtime and its standard library on the native ABI | - | The port of the Go runtime |
| [SDK packages](#sdk-packages) | The packages that deliver the SDK crate, the ABI crate, the sysroots and the libraries to the developers of native programs | - | The SDK packages |

## System-call dispatch

**Description.** A native system call is an `svc #0` at EL0 with the major
version of the ABI in `x7`, the operation number in the low 16 bits of `x8`,
its arguments in `x0` to `x5` and `x6` reserved. Dispatch checks, in this
order, the immediate of the `SVC`, the version and the operation number, and
then that `x6` and every argument register that the operation does not use
are 0, in ascending order of register; only then does the entry of the
operation make its own checks, in the order of errors of the
[security model](../../security.md#internal-choices): the form of the
arguments in registers before the resolution of handles, and the form of
argument structures copied in from user memory after the rights and the
range of their buffers, before the state of objects. A nonzero immediate, a
number with a bit above bit 15 set and a number without an entry in the
dispatch table of the running image, which includes every diagnostic number
in the default image, return `UNSUPPORTED_OPERATION`; a version that the
kernel does not serve returns `UNSUPPORTED_VERSION`; a reserved or unused
register that is not 0 returns `INVALID_ARGUMENT`. None of these is a fault,
and no refusal ends the process of the caller. A refused call writes its
status into `x0` and 0 into `x1` to `x5`, keeps every other register and
changes no other state. Dispatch reads no right that authorizes a call from
EL0: the rights that an operation needs are constants of its contract, which
the lookup of its handles checks. Loading fixes for each process an ABI
attribute, native or Linux; in a Linux process only an `SVC` from the code
range of its compatibility runtime takes native dispatch, and every other
takes the Linux path whatever its immediate. Every entry from EL0, a call, a
user fault or an interrupt, is one transition that dispatch composes: the
time is read once at the entry, the waits whose deadlines have passed
settle, the entry is handled by its class, a call by its operation and a
user fault by the end of its process, and the return chooses the thread that
runs next, checks its saved context and lets no thread return while an
interrupt is pending. With dispatch, the loading component checks again
every parameter of the calls that load the image of a child, the loading
request calls: the form of each segment, its access, R, RX or RW, its place
in the image window below the guard of the initial stack, its bytes within
the image in the boot-bundle directory, no page shared with a segment staged
before it, and the number of segments and the private pages of the image
within the limits of the boot configuration; and, at the commit, an entry
point aligned to 4 in an RX segment. A refused segment or commit changes
nothing. Dispatch parses no ELF file, maps and copies no page of an image,
and keeps no state of its own from one transition to the next.

**Design background.** One table keyed by the major version and the
operation number lets the kernel serve two major versions side by side
([system calls and the ABI](../../architecture.md#system-calls-and-the-abi)).
Checking the immediate, the version and the number before anything else
gives every value of the three one result, whatever the other registers
hold. Rights that are constants of the operation leave the authority of a
call wholly to the capabilities that it names
([unforgeable authority](../../security.md#unforgeable-authority)). The
loader of EL0 is not trusted to have checked what it asks for, and the
kernel parses no ELF, so the kernel checks each segment itself, as values in
registers. W^X holds by construction: the R and RX pages of an image are
pages of the boot bundle, which nothing maps writable, and its RW pages are
private frames, which nothing maps executable. Operations that change tables
or frames give plans instead of calling back into the hardware layer
([the provable core](../../architecture.md#the-provable-core)): the
architecture crate executes each plan, and dispatch hands the executed plan
back to the operation, which gives the next plan or its result.

**Consumers.** Every native program, through the libraries of the runtimes
and the SDK; the compatibility runtime of a Linux process, which makes
native calls from its code range; the root, the process manager and the
process services, whose loaders stage the images of the processes that they
create; and the contracts of the operations of the other domains, whose
checks follow those of dispatch.

**Interface.** The `SVC` with its registers. The statuses of dispatch,
`UNSUPPORTED_OPERATION`, `UNSUPPORTED_VERSION` and `INVALID_ARGUMENT`, are
errors ([rejection](dispatch/contract.md#rejection)); the result registers
of a refused call are fixed ([results](dispatch/contract.md#results)), and
the outcomes that an accepted call reports, such as a timeout, are states
that its operation writes. The checks of the loading component are those of
`loader::validate`, whose errors `spawn_segment` and `spawn_commit` of the
[creation](../objects-capabilities/creation/contract.md#child-processes)
component return in their order of errors
([load validation](dispatch/contract.md#load-validation)). The numbers of
the operations and the numeric values of the statuses belong to the
[operation inventory](#the-operation-inventory).

**Prerequisites.** [The operation inventory](#the-operation-inventory); the
[exception vectors](../boot-platform/README.md#exception-vectors) and the
[results of a call](../boot-platform/context/contract.md#results-of-a-call)
of the boot and platform domain; the
[entry and return](../memory/address-space/contract.md#entry-and-return),
the
[exception classes](../memory/address-space/contract.md#exception-classes)
and the
[boot-bundle directory](../memory/address-space/contract.md#boot-bundle-directory)
of the address-space component, and
[W^X and code publication](../memory/README.md#wx-and-code-publication); the
[capability tables](../objects-capabilities/README.md#capability-tables) and
the
[process and thread lifetimes](../objects-capabilities/README.md#process-and-thread-lifetimes)
of the kernel objects and capabilities domain;
[timeouts](../ipc-waits/README.md#timeouts) and
[preemption](../scheduling/README.md#preemption); the
[order of errors](dispatch/contract.md#order-of-errors) and the
[composition of a transition](dispatch/contract.md#composition-of-a-transition)
of the dispatch contract.

**Engineering notes.** A call takes a constant number of steps in dispatch:
its decoding, one match on the operation and the checks of at most seven
registers. The loops of a transition are bounded by the thread capacity: the
settlement of expired deadlines, and the return, which starts again each
time the saved context of the chosen thread is refused and so ends a
process. Dispatch has no long operation of its own: an operation that stops
at a preemption point stores its progress in its object, and the call is
executed again from the saved user registers. An operation fixes all its
plans during its checks and gives the first only after the write-back of its
write set; a plan does not fail, so no error follows the first plan, and the
next plan comes only after the previous one has been executed. The loading
component compares a segment at most once with each staged segment, of which
there are at most eight. The image window starts at `0x4020000000`, after
the window of the boot bundle, and ends at most at `0x4040000000`, the start
of the VM window; the initial stack of a child lies at its top, with an
unmapped guard page below it. The boot configuration sets the pages of the
window and of the stack, the number of segments, the private pages of an
image and those of the root
([loading configuration](dispatch/contract.md#loading-configuration)), and
the boot checks them once the boot-bundle directory is parsed, since the
capacity record lies in the bundle: it requires that the tables of a child
leave room for the tables of its image window and for the first tables of
its VM window, which bounds the image window of each boot, and it stops on a
field that it refuses rather than taking a default. A transition ends in a
return to EL0, in the wait of an idle CPU or, when the root leaves the state
Alive, in the halt of the system; on the way it hands plans to the
architecture crate. Dispatch keeps no state between transitions; the state
that a transition reaches is classified in the
[State fields](dispatch/contract.md#state-fields) of the dispatch contract
and of the components that own it.

**Verification.** Invariants: a refused call changes no state but its result
registers; every value of the immediate, the version and the number has one
result; every accepted segment has the access R, RX or RW, lies in the image
window below the guard of the stack and shares no page with another, so no
page of a loaded image is writable and executable. Required counterexamples:
an immediate other than 0; version 0, which is never served, and a version
above the current one; a number with a bit above bit 15 and a diagnostic
number in the default image; an `x6` and an unused argument register that
are not 0, for each operation; overlapping segments, a segment with write
and execute access, a segment outside the window or over the guard of the
stack, a misaligned address and a size that overflows; an entry point
outside every RX segment. Environments: host tests with the frozen vectors
of the prototype's ABI and loader, against an independent model of the order
of errors; QEMU runs from EL0 that make each rejection and compare the state
before and after.

## The operation inventory

**Description.** The operation inventory lists every native operation of the
kernel: its name, its operation number, the major version that added it, the
registers of its arguments and results, the encodings of their values, the
rights it needs and its errors, with the numeric values of every error and
status; the contracts of the components name the arguments and results and
fix the fields of a register that packs several of them. Number 0 is not
used; production operations take numbers from `0x0001` to `0x7FFF` and
diagnostic operations from `0x8000` to `0xFFFF`, and the inventory assigns
the numbers within each range. Diagnostic operations are registered only in
test builds, and a stable ABI contract freezes only the production range. A
new operation takes a new number and leaves the version unchanged; arguments
are extended by flags that must be zero and by structures that carry their
size, so there is no minor version and nothing to negotiate. An incompatible
change takes a new number and deprecates the old one, or raises the major
version, and the kernel serves the current major version and the one before
it. A deprecated operation keeps its meaning within its major version and is
removed only with a new major version, after which its number returns
`UNSUPPORTED_OPERATION`; a major version is retired only at a release
boundary of the stable ABI, after which it returns `UNSUPPORTED_VERSION`.
The inventory holds no system call of Linux, which never reaches native
dispatch.

**Design background.** The rules are those of the
[system calls and the ABI](../../architecture.md#system-calls-and-the-abi)
of the architecture. The core of the kernel depends on no crate, so its
dispatch table and the ABI crate each hold the operation numbers and the
error codes, and a check of `cargo xtask check` keeps both equal to the
inventory
([kernel workspace crates](../../architecture.md#kernel-workspace-crates)).
Flags that must be zero and structures that carry their size let an
operation grow without a version on which both sides would have to agree.

**Consumers.** The SDK and the libraries of every runtime, which make the
calls; the compatibility runtime of Linux programs, which makes native
calls; the contracts of the components, whose Entry points tables name the
operations that each adds to the inventory, as the
[creation contract](../objects-capabilities/creation/contract.md#entry-points)
does; the feature documents, whose `operations` field names operations as
the inventory writes them; and the conformance tests of the ABI.

**Interface.** No operation of its own: the inventory is data. The ABI crate
`krepi-abi` holds the data of the EL0 ABI and gives it to EL0, and
user-space crates reach the kernel workspace only through it
([source layout](../../architecture.md#source-layout)). A query of features
and limits, where the kernel offers one, is an ordinary production
operation.

**Prerequisites.** [System-call dispatch](#system-call-dispatch); the
[operation numbers and versions](dispatch/contract.md#operation-numbers-and-versions)
and the [rights](dispatch/contract.md#rights) of the dispatch contract.

**Engineering notes.** The rights of an operation in the inventory are the
constants of its contract, and its errors keep the order of that contract.
The default image of a board serves every production operation and holds no
diagnostic operation, so its dispatch table has no entry in the diagnostic
range. The check of the repository fails when the dispatch table or the ABI
crate differs from the inventory, so a drift on either side stops the change
that makes it. The inventory is data of the build and holds no state at run
time.

**Verification.** Invariants: every number of the default image lies in the
production range and names one operation; no number names two operations in
the major versions that the kernel serves. Required counterexamples: a
dispatch table and an ABI crate that each differ from the inventory; a
reused number; a diagnostic number in the default image. Environments: the
host check of the inventory against the dispatch table and the ABI crate;
QEMU runs from EL0 with one refused argument for each operation number and
one call each with an unknown number and an unknown version.

## Application entry and CRT

**Description.** A program starts at the entry point of its image, in an RX
segment, with the initial context of its thread: every general register,
both TLS registers and every vector register 0, the stack pointer at the top
of its initial stack and the default floating-point environment. The root,
which the kernel maps at boot from a segment description that the build
fixed, finds its boot information mapped read-only at a fixed address. A
child finds in slot 0 of its table a capability to itself and in slot 1 one
to its thread, each with the rights that its creator chose or none, and up
to four copies of capabilities of its creator in slots that the creator
names. Before the main function of a program, its CRT prepares the TLS of
its thread, takes its arguments and environment, initializes its libraries
and calls the main function, whose return ends the process with its exit
code. A child takes its arguments and environment from its creator by calls
on an endpoint that the creator granted it, two words at a time; which slot
holds that endpoint is a convention of the creator and the runtime, and a
POSIX process learns its process ID from this start message. The loader of
the creator's runtime parses and validates the static ELF image and stages
its segments with the loading request calls, which the kernel checks again.
Application entry resolves no shared library and changes no image of a
running process.

**Design background.** A static image that the kernel checks segment by
segment keeps the parsing of ELF out of the kernel, which parses no file
system or arbitrary ELF file
([protection domains](../../architecture.md#protection-domains)), and the
start of the root from a description that the build fixed needs no loader
before the file service exists
([boot and the resident root](../../architecture.md#boot-and-the-resident-root)).
A start message over IPC needs neither an endpoint of the child's own nor a
copy of user memory by the kernel. The CRT and the libraries follow the
procedure call standard of AArch64 for the calls within EL0.

**Consumers.** Every native program; the root, which starts from its boot
information; the process manager and the process services, which create
processes and answer their start messages; the C library, the Rust standard
library and the Go runtime, whose start-up the CRT runs; and the
compatibility runtime that loading places in a Linux process.

**Interface.** The
[initial context](../boot-platform/context/contract.md#initial-context) of a
thread; the
[initial capabilities](../objects-capabilities/creation/contract.md#initial-capabilities)
of a child, whose fixed slots 0 and 1 it names by their handles of
generation 1; the
[boot information](../memory/address-space/contract.md#first-process-and-boot-information)
of the root; the start message, a protocol of calls between the runtime of
the child and its creator, whose outcomes are those of
[calls](../ipc-waits/README.md#calls); and the exit of the process with its
code.

**Prerequisites.** [System-call dispatch](#system-call-dispatch),
[TLS](#tls),
[The floating-point environment](#the-floating-point-environment); the
[calls](../ipc-waits/README.md#calls) of the IPC and waits domain; the
[process and thread lifetimes](../objects-capabilities/README.md#process-and-thread-lifetimes)
of the kernel objects and capabilities domain.

**Engineering notes.** A message carries 16 bytes, so the arguments and the
environment take one call for every 16 bytes, and the start of a program
takes longer the larger they are. The segments of an image lie in the image
window below the guard of its initial stack, so a native program is linked
for the image window, and the size of the initial stack is a field of the
boot configuration. The kernel enables the alignment check of the stack
pointer at EL0, so an access through a misaligned stack pointer is a user
fault that ends the process: the initial stack pointer is page aligned, and
the CRT keeps the alignment of 16 bytes that the procedure call standard
requires. A new thread holds no value of its creator in its registers, so
the CRT finds what it needs only in its image, its initial capabilities and
its start message.

**Verification.** Invariants: a new thread starts with the values of its
initial context and holds no value of another thread; before its first call
a child holds only its initial capabilities. Required counterexamples: an
image whose entry point lies outside its RX segments, a start endpoint that
the creator does not answer, arguments that take several messages.
Environments: QEMU runs of a child that runs its entry, takes its start
message by calls, reads its data and its stack and exits with the code of
its main function; the same runs on the Pi 5.

## Sysroots

**Description.** A sysroot holds the headers, the static libraries, the
start-up objects of the CRT and the description of the target against which
the programs of a runtime are compiled and linked, among them the native C
library with its headers. A native sysroot is isolated: a build against it
sees only what the native libraries provide, so a configure probe for an
interface that the native C library does not provide, such as epoll,
eventfd, timerfd, pidfd or the mount interface, finds it missing. A program
built against a native sysroot is a static image that makes native calls
with the major version of its libraries. Linux programs are unmodified
binaries that use the Linux user-space libraries, not a native sysroot.

**Design background.** Configure scripts and build systems decide by probing
what a sysroot offers, so a sysroot that holds only what the native
libraries install gives the native answer, as the Linux-only interfaces of
the
[processes, POSIX and Linux compatibility](../../architecture.md#processes-posix-and-linux-compatibility)
require.

**Consumers.** The builds of native programs: the root, the services, the
drivers and the workers; the shell and the base tools; the interpreters and
proof tools of the application platform services.

**Interface.** None at run time: a directory tree for each target with its
headers, libraries and start-up objects, which a compiler and a linker
select by their target.

**Prerequisites.** [Application entry and CRT](#application-entry-and-crt),
[C and C++ libraries](#c-and-c-libraries), [Rust std](#rust-std),
[The operation inventory](#the-operation-inventory).

**Engineering notes.** A header of an interface that the library does not
provide is absent, not a stub: the native sysroot has no `sys/epoll.h`,
`sys/eventfd.h`, `sys/timerfd.h`, `sys/pidfd.h` or `sys/mount.h`, no `EFD_`
or `TFD_` constant and none of `PIDFD_NONBLOCK`, `P_PIDFD` and
`CLONE_NEWNS`. A sysroot is bound to the major version that its libraries
pass in `x7`; the kernel serves the current major version and the one before
it, so a program built against a sysroot runs while the kernel serves its
version.

**Verification.** Required counterexamples: a configure probe for each
Linux-only interface against the isolated sysroot, which finds it missing.
Environments: host builds of fixed programs against the sysroot; runs of the
images built from it on QEMU and the Pi 5.

## Rust std

**Description.** The Rust standard library runs on the native ABI: its
threads are threads of the process, its locks, condition variables and
one-time initialization wait and wake through futex-style waits, its heap
and stacks are the committed pages of VM regions of the process, its
monotonic clock reads the virtual counter, and its files, streams,
processes, arguments and environment go through the services of EL0 and the
start message of the process. It acts only with the authority of its
process, through capabilities and service sessions that the process holds.

**Design background.** `std` reaches the operating system through its
platform layer, so a port replaces that layer and keeps the public
interface: a program written for `std` builds for the native target as it
builds for others, as far as it uses what the platform provides.

**Consumers.** The root, the services, the drivers and the workers written
in Rust; Rust applications, such as the computer algebra system and the
desktop environment, which build on `std`.

**Interface.** The public interface of `std` for the native target, with the
errors that `std` defines; no kernel operation of its own.

**Prerequisites.** [Threads](#threads), [TLS](#tls),
[Application entry and CRT](#application-entry-and-crt),
[Sysroots](#sysroots); the
[futex-style waits](../ipc-waits/README.md#futex-style-waits) and
[wait sets](../ipc-waits/README.md#wait-sets) of the IPC and waits domain;
the
[VM objects and their kinds](../memory/README.md#vm-objects-and-their-kinds)
of the memory and address-spaces domain.

**Engineering notes.** The committed pages of a process stay within its
limit, so the allocator of `std` meets an exhausted heap at that limit and
not at the size of the RAM. The monotonic clock of `std` and the deadlines
of the waits that it makes are in the same count of the virtual counter,
which EL0 reads without a call.

**Verification.** The tests of the Rust standard library for the native
target, with those that the native ABI does not support stated as such.
Required counterexamples: a lock contended by several threads, an allocation
at the limit of committed pages, a timed wait whose deadline passes.
Environments: QEMU runs, then the Pi 5, each with its configuration.

## C and C++ libraries

**Description.** The native C library is a port of the GNU C Library
(glibc), with its math library, in each process. It keeps the POSIX state of
its process inside the process: the descriptor table, each entry a
capability to a session of a file, pipe, pseudo-terminal or socket with
library state such as an offset; the signal dispositions; the signal mask
and the pending signals of each thread; the working directory, a capability
to a directory session; the umask and the environment variables. It
allocates descriptor numbers, which are not kernel identifiers, and sends
the POSIX operations across processes, such as `fork`, `wait` and `kill`, to
the process service of its environment as calls. Its upcall entry takes the
pending signals, selects one by the mask, writes the saved context as a
`ucontext_t` on the stack of the thread or its `sigaltstack` and calls the
handler; `sigreturn` returns from the upcall with the context that the
handler may have changed. It provides no epoll, eventfd, timerfd, pidfd or
mount interface. The C++ standard library and its runtime support build on
the C library. The interfaces that the libraries provide, their baselines
and their conformance belong to the compatibility personalities; this
section gives the libraries as runtimes of EL0.

**Design background.** A C library that keeps the POSIX state in its process
lets the kernel keep no process IDs, signal dispositions or other POSIX
state
([processes, POSIX and Linux compatibility](../../architecture.md#processes-posix-and-linux-compatibility)).
The robust mutexes of the C library rely on the shared wait and wake of
futexes also when they are private to a process
([futexes and upcalls](../../architecture.md#futexes-and-upcalls)). The
native layer follows POSIX.1-2024 with XSI conformance and the interfaces
that glibc 2.42 exports for AArch64 Linux.

**Consumers.** C and C++ programs; the shell and the base tools; the
interpreters and proof tools of the application platform services; the POSIX
environments; Rust and Go programs that call C code.

**Interface.** The C and C++ standard interfaces and the POSIX and GNU
interfaces of the native layer, as the compatibility personalities state
them. Signals arrive as asynchronous upcalls; a blocking call that an upcall
interrupts returns the interrupted result, and the library restarts it for
`SA_RESTART`, since the kernel never restarts a call that an upcall
interrupted.

**Prerequisites.** [Threads](#threads), [TLS](#tls),
[The floating-point environment](#the-floating-point-environment),
[Application entry and CRT](#application-entry-and-crt); the
[futex-style waits](../ipc-waits/README.md#futex-style-waits) and
[wait sets](../ipc-waits/README.md#wait-sets) of the IPC and waits domain.

**Engineering notes.** The C library chooses the thread that takes a signal
directed to its process and keeps the masks and pending signals; the kernel
keeps none of them. Descriptor numbers are state of the library, so the
`fork` of the process service copies only native descriptors. Native
programs use `poll` and `waitid(P_PID, pid, WEXITED | WNOWAIT)` where Linux
programs would use the Linux-only interfaces.

**Verification.** The tests of glibc for the native port and the upstream
suites that the compatibility personalities name. Required counterexamples:
robust mutexes across processes that share an object; a signal during a
blocking call with and without `SA_RESTART`; a configure probe for a
Linux-only interface. Environments: QEMU runs, then the Pi 5.

## Threads

**Description.** The thread runtime gives the programs of a process several
threads of control. The POSIX threads of the C library, the threads of Rust
`std` and C++, and the threads on which the Go runtime runs its goroutines
are threads of the kernel in that process: they share its address space and
its capability table and form its POSIX thread group, and each has its own
saved context, stack, TLS and floating-point environment. A new thread is a
native thread creation with its entry and its stack; the thread library sets
a new POSIX thread to the floating-point environment of its creator before
the thread starts, and a join waits for the exit of the thread, which it
still sees when the thread exited before the join. Mutexes, condition
variables, barriers and one-time initialization wait and wake through
futex-style waits, keyed by the memory that holds their words.

**Design background.** Each thread of a POSIX process is a thread of the
kernel, so blocking, preemption and budgets apply to each thread
([processes, POSIX and Linux compatibility](../../architecture.md#processes-posix-and-linux-compatibility)).
A futex key follows from the memory that holds its word, so the private and
the shared operations of the libraries on one word agree
([futexes and upcalls](../../architecture.md#futexes-and-upcalls)).

**Consumers.** Multithreaded programs; the thread interfaces of the C
library, of Rust `std`, of C++ and of the Go runtime; the compatibility
runtime of Linux programs, which maps a `clone` that creates a thread to
native thread creation.

**Interface.** The thread interfaces of each library, such as
`pthread_create` and `pthread_join` of the C library and `std::thread` of
Rust; a creation that the kernel refuses returns an error of the library,
and the end of a thread is a state that a join reads.

**Prerequisites.** [TLS](#tls),
[The floating-point environment](#the-floating-point-environment); the
[process and thread lifetimes](../objects-capabilities/README.md#process-and-thread-lifetimes)
of the kernel objects and capabilities domain; the
[futex-style waits](../ipc-waits/README.md#futex-style-waits) of the IPC and
waits domain; the [admission](../scheduling/README.md#admission) of the
scheduling and budgets domain.

**Engineering notes.** A thread is admitted with a class and amounts carved
from the holdings of its creator, so the budgets of the threads of a process
come out of what it holds, and their number is bounded by the thread pool as
well. The kernel bounds the threads of each process; where a process has
only the thread created with it, a thread runtime runs with that thread
alone. The saved context of a thread is per-thread state of the
[context](../boot-platform/context/contract.md#state-fields) component.

**Verification.** Invariants: the threads of a process see one address
space; the TLS and the floating-point environment of a thread are its own.
Required counterexamples: a join on a thread that exited before the join; a
mutex contended by several threads with a timeout; a new thread whose
creator runs with an environment other than the default. Environments: QEMU
runs on one and on several vCPUs, then the Pi 5.

## TLS

**Description.** Each thread has a block of thread-local storage, which its
runtime allocates and initializes from the TLS image of its program before
the thread runs code that uses it, and the thread pointer `TPIDR_EL0` names
the block. The kernel saves `TPIDR_EL0` at every entry from EL0 and restores
it at every return, with the rest of the context of the thread, and loads
`TPIDRRO_EL0`, which EL0 reads and only the kernel writes; a new thread
starts with both 0. The TLS of a static image is reached at offsets that the
link fixes; the TLS of modules loaded at run time belongs to dynamic
loading.

**Design background.** On AArch64 `TPIDR_EL0` is the thread pointer, and the
TLS block of the executable lies at an offset fixed at link time after the
thread control block that it names, so a static image reaches its TLS
without a call (Drepper 2013; the ELF specification of the Arm 64-bit
architecture). The kernel treats both TLS registers as opaque values that it
never dereferences
([FP/SIMD and TLS state](../boot-platform/context/contract.md#fpsimd-and-tls-state)).

**Consumers.** The C library, for `errno` and its per-thread state; Rust
`std` and C++, for their thread-local variables; the thread runtime and the
Go runtime.

**Interface.** The thread pointer and the TLS models of the static linker;
no kernel operation: EL0 writes `TPIDR_EL0` itself.

**Prerequisites.** [Application entry and CRT](#application-entry-and-crt),
[Threads](#threads); the
[exception vectors](../boot-platform/README.md#exception-vectors) of the
boot and platform domain.

**Engineering notes.** The save of `TPIDR_EL0` is eager, so the thread
pointer of a thread that does not run is in its saved context; the save and
the restore are obligations of the context component, each with its test.
`TPIDRRO_EL0` is read-only at EL0, so a write of it there is an undefined
instruction and a user fault. The TLS registers are per-thread state of the
[context](../boot-platform/context/contract.md#state-fields) component.

**Verification.** Invariants: a thread reads its own TLS after every
preemption, call and migration; a new thread starts with 0 in both TLS
registers. Required counterexamples: two threads that write the same
thread-local variable; a thread preempted between a write of `TPIDR_EL0` and
its use; a write of `TPIDRRO_EL0` at EL0. Environments: QEMU runs, then the
Pi 5.

## The floating-point environment

**Description.** Each thread has its own floating-point environment, its
FPCR and FPSR, in the hardware that EL0 uses: binary64 addition,
subtraction, multiplication, division, square root and fused multiply-add
are the correctly rounded instructions of the hardware. Every new process
and thread starts with the default environment: round to nearest with ties
to even, FZ clear, every trap enable clear and the FEAT_AFP bits AH, FIZ and
NEP clear, and an FPSR of 0. Where POSIX makes a new thread inherit the
environment of its creator, EL0 sets it: the only thread of the child of
`fork` takes the saved context of the calling thread, FPCR and FPSR
included, and the thread library sets a new POSIX thread to the environment
of its creator before the thread starts. A new program image after `exec`
starts with the default, and so does a worker thread of the computer algebra
system, whose creation path sets the default. FPCR, FPSR and `q0` to `q31`
survive preemption, yield, system calls and IPC, the delivery of signals and
the return from them, and migration. The environment belongs to the thread,
and the system never changes the environment of a worker thread.

**Design background.** The rules are those of the
[floating-point state](../../architecture.md#floating-point-state) of the
architecture, on the arithmetic of IEEE 754. The kernel saves and restores
every vector register, FPCR and FPSR at every entry from EL0 and return to
it, eagerly and bit for bit
([FP/SIMD and TLS state](../boot-platform/context/contract.md#fpsimd-and-tls-state)),
and uses none of them itself, since it is built softfloat.

**Consumers.** The math library and `fenv.h` of the C library; the
floating-point arithmetic of Rust `std`, C++ and Go; the workers of the
computer algebra system, whose environment the system never changes; the
interpreters of the application platform services.

**Interface.** The `fenv.h` functions of the C library and their
counterparts in the other languages read and write the FPCR and FPSR of the
thread at EL0; no kernel operation. The default values are those of the
[initial context](../boot-platform/context/contract.md#initial-context).

**Prerequisites.** [Threads](#threads); the
[exception vectors](../boot-platform/README.md#exception-vectors) of the
boot and platform domain.

**Engineering notes.** The kernel copies no environment into a new context,
so the inheritance of an environment is the work of EL0 alone. On the
Cortex-A76 of both boards bits 0 to 18 of FPCR are RES0, so only RMode, FZ,
DN, AHP and FZ16 exist there, and no floating-point exception traps at EL0.
FPCR and FPSR are per-thread state of the
[context](../boot-platform/context/contract.md#state-fields) component.

**Verification.** Invariants: a new thread starts with the default FPCR and
an FPSR of 0; the floating-point registers of a thread are the same bit for
bit before and after every entry from EL0 and return to it. Required
counterexamples: a thread that changes its rounding mode while another
thread of the process keeps the default; a child of `fork` whose parent runs
with a rounding mode other than the default. Environments: QEMU and Pi 5
runs that set each rounding mode and check it across preemption, calls and
migration; the same binary64 computations on QEMU virt and the Pi 5,
compared bit for bit.

## The Go runtime

**Description.** The Go runtime and the Go standard library run on the
native ABI: the runtime schedules goroutines on threads of the process,
parks and wakes them through futex-style waits, waits for events through
wait sets, takes its heap and the stacks of its goroutines from the VM
regions of the process and reads time from the virtual counter. Its signal
safe points and its asynchronous preemption of goroutines use asynchronous
upcalls. It acts only with the authority of its process.

**Design background.** A goroutine that runs without reaching a safe point
is stopped by an asynchronous signal to its thread (Clements 2019); on the
native ABI that signal is an asynchronous upcall, which reaches the thread
when it next returns to EL0
([futexes and upcalls](../../architecture.md#futexes-and-upcalls)).

**Consumers.** Go programs and services, and the Go toolchain that builds
them.

**Interface.** The Go standard library for the native target; no kernel
operation of its own.

**Prerequisites.** [Threads](#threads), [TLS](#tls),
[Application entry and CRT](#application-entry-and-crt); the
[futex-style waits](../ipc-waits/README.md#futex-style-waits) and
[wait sets](../ipc-waits/README.md#wait-sets) of the IPC and waits domain;
the
[VM objects and their kinds](../memory/README.md#vm-objects-and-their-kinds)
of the memory and address-spaces domain.

**Engineering notes.** A thread takes upcalls only through an upcall area
that it registers, so the runtime registers one for every thread that it
preempts; a request to a thread without one fails with a fixed error.
Repeated requests of one kind coalesce in the pending bits of the thread,
and upcalls nested deeper than its save slots end the process as faulted.

**Verification.** The tests of the Go standard library for the native
target. Required counterexamples: a goroutine in a loop without a safe
point, which only asynchronous preemption stops; a preemption request during
a blocking call. Environments: QEMU runs on one and on several vCPUs, then
the Pi 5.

## SDK packages

**Description.** The SDK packages deliver what builds a native program: the
SDK crate `krepi-sdk` with the ABI crate `krepi-abi`, which it re-exports
and through which alone it reaches the kernel; the sysroots of the runtimes
with their libraries and start-up objects; and the description of the target
for the toolchain. The libraries of a package make their calls with the
major version of the ABI for which they are built. The packages that a
device installs, with their manifests and signatures, are not SDK packages.

**Design background.** User-space crates reach the kernel workspace only
through the ABI crate, so the SDK and the kernel share one definition of the
data of the ABI ([source layout](../../architecture.md#source-layout)).

**Consumers.** The developers of native programs on a host; the builds of
the user-space workspace; the application platform services and the language
runtimes, whose builds take the sysroots.

**Interface.** The crates and the sysroots, by version; no run-time
interface.

**Prerequisites.** [Sysroots](#sysroots),
[The operation inventory](#the-operation-inventory), [Rust std](#rust-std),
[C and C++ libraries](#c-and-c-libraries).

**Engineering notes.** Every crate of the repository is licensed MIT, and a
package that ships a library ported from another project carries that
project's licence with it. The ABI crate of a package is the one that the
check of the inventory compares with the dispatch table, so the SDK and the
kernel of one revision agree on every number and code.

**Verification.** Builds of fixed programs from the packages on a host that
holds nothing else of the SDK, and runs of the images built on QEMU and the
Pi 5. Required counterexample: a program built for a major version that the
kernel no longer serves, whose every call returns `UNSUPPORTED_VERSION`.

## Dependencies

| Feature | Depends on | Reason |
| --- | --- | --- |
| System-call dispatch | Exception vectors, Capability tables, Process and thread lifetimes, Timeouts, Preemption, W^X and code publication | An `SVC` enters through the vectors; operations resolve the capabilities that they name; a user fault ends its process, and a commit creates the child whose image loading accepts; a transition settles expired deadlines and chooses the thread that returns; the segments of an image keep W^X |
| The operation inventory | System-call dispatch | The inventory holds the numbers and versions that dispatch decodes and the statuses of its rejections |
| Application entry and CRT | System-call dispatch, Process and thread lifetimes, Calls, TLS, The floating-point environment | The image of a child is loaded through the loading request calls and starts with its initial capabilities; its start message arrives by calls; the CRT prepares the TLS and starts with the default environment |
| Sysroots | Application entry and CRT, C and C++ libraries, Rust std | A sysroot holds the start-up objects and the libraries |
| Rust std | Application entry and CRT, Threads, Futex-style waits, VM objects and their kinds | `std` starts from the CRT, runs threads, waits on futexes and commits its heap |
| C and C++ libraries | Application entry and CRT, Threads, Futex-style waits, Wait sets | The libraries start from the CRT, run threads, wait on futexes and poll through wait sets |
| Threads | Process and thread lifetimes, Admission, Futex-style waits, TLS, The floating-point environment | A thread is a kernel thread admitted with its budgets, synchronizes through futexes and has its own TLS and environment |
| TLS | Application entry and CRT, Exception vectors | The CRT and the thread runtime prepare each block; the context of a thread saves and restores the thread pointer |
| The floating-point environment | Exception vectors | The context of a thread saves and restores its floating-point registers |
| The Go runtime | Threads, Futex-style waits, Wait sets | Goroutines run on threads, park on futexes and wait for events through wait sets |
| SDK packages | Sysroots, The operation inventory | A package delivers the sysroots and the ABI crate with the data of the inventory |

## Exclusions

- The entry from EL0 and the return to it, the classes of exceptions and
  user faults, the layout of the EL0 window, the boot information of the
  root and the boot-bundle directory belong to the
  [memory and address spaces](../memory/README.md) domain; this domain
  composes them into a transition.
- The saved user context, its initial value and the save and restore of the
  FP/SIMD and TLS registers belong to the
  [context](../boot-platform/context/requirements.md) component of the boot
  and platform domain; this domain gives the environment and the TLS that
  the runtimes keep in them.
- The checks that follow those of dispatch, and the effects, rights and
  errors of each operation, belong to the contract of its component; the
  mapping and copying of a loaded image, the initial capabilities of a child
  and the creation right belong to the
  [kernel objects and capabilities](../objects-capabilities/README.md)
  domain.
- W^X and the publication of code belong to the memory and address-spaces
  domain; which bytes may be loaded and executed, the integrity of loading,
  `exec`, packages and updates, and who may add the execute right belong to
  the security and lifecycle domain.
- The root, the process manager and the process services, process creation
  authority, the file service and the read-only system image belong to the
  EL0 services and storage domain.
- The semantics of the native POSIX and GNU interfaces, the shell and the
  terminal, dynamic loading and `dlopen`, and Linux system-call and binary
  compatibility belong to the compatibility personalities.
- Networking and the TLS of secure transport, CPython, Lean and Lake belong
  to the application platform services domain; TLS on this page is
  thread-local storage.
- Threads on several CPUs, their migration and the per-CPU state of the
  kernel belong to the multicore domain.
- The desktop environment and the GUI framework, and the internal logic of
  language runtimes beyond their integration with the system, lie outside
  every domain ([subject-domain index](../README.md#out-of-scope)).

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>.
- Arm Limited, *Procedure Call Standard for the Arm 64-bit Architecture
  (AArch64)*,
  <https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst>.
- Arm Limited, *ELF for the Arm 64-bit Architecture (AArch64)*,
  <https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst>.
- A. Clements, *Proposal: Non-cooperative goroutine preemption*, Go design
  document 24543, 2019,
  <https://go.googlesource.com/proposal/+/master/design/24543-non-cooperative-preemption.md>.
- U. Drepper, *ELF Handling For Thread-Local Storage*, version 0.21, 2013,
  <https://www.akkadia.org/drepper/tls.pdf>.
- IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
- IEEE and The Open Group, *The Open Group Base Specifications Issue 8*,
  IEEE Std 1003.1-2024, <https://pubs.opengroup.org/onlinepubs/9799919799/>.
- The GNU C Library, *The GNU C Library Reference Manual*,
  <https://sourceware.org/glibc/manual/>.
- The Rust Project, *The Rust Standard Library*,
  <https://doc.rust-lang.org/std/>.
