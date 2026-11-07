#!/usr/bin/env bash
# Checks the built proof-tool image as the proof gate is to use it: as a
# user other than root (root owns the installation), and with the variables
# that `cargo xtask formal run` gives every tool command on linux-aarch64
# (xtask/src/formal/toolchain.rs; a test of xtask keeps the two lists equal
# apart from HOME and TMPDIR). The image workflows run it in the image:
#
#   bash non-root-check.sh DIR
#
# DIR is a directory that the user can write and that holds verification/
# with the files of the Lake project: lakefile.toml, lean-toolchain and
# lake-manifest.json. The check fails when the user is root, when an entry
# below /opt/krepi-formal cannot be read or can be written, or is a directory
# that cannot be searched, when a Mathlib build output cannot be read, when
# `lake env lean` cannot check a file that imports Aeneas in a Lake project
# laid out as the gate lays out its stages, when `git status` fails in the
# installed Mathlib package, when Cargo and rustc through the rustup
# proxies, Charon or Aeneas cannot print their versions, or when Charon and
# Aeneas cannot translate a crate of one function. It only records Git's
# answer without the safe.directory variables, the time of `git status` with
# core.checkStat=minimal, and whether Lake finds the installed library up to
# date.
set -euo pipefail

dir=$1
prefix=/opt/krepi-formal
packages=$prefix/backend/.lake/packages
tool_env=(
  LAKE_ARTIFACT_CACHE=false
  CARGO_NET_OFFLINE=true
  CARGO_HOME=/opt/krepi-formal/cargo
  RUSTUP_HOME=/opt/krepi-formal/rustup
  RUSTUP_TOOLCHAIN=nightly-2026-09-17
  LANG=C.UTF-8
  LC_ALL=C.UTF-8
  GIT_CONFIG_NOSYSTEM=1
  GIT_CONFIG_GLOBAL=/dev/null
  GIT_CONFIG_COUNT=1
  GIT_CONFIG_KEY_0=safe.directory
  GIT_CONFIG_VALUE_0='*'
  PATH=/opt/krepi-formal/lean/bin:/opt/krepi-formal/bin:/opt/krepi-formal/cargo/bin:/usr/bin:/bin:/usr/sbin:/sbin
  "HOME=$dir/home"
  "TMPDIR=$dir/tmp"
)
tool() { env -i "${tool_env[@]}" "$@"; }
mkdir -p "$dir/home" "$dir/tmp"

echo "== the user: $(id)"
if [ "$(id -u)" = 0 ]; then
  echo "the check runs as root; it must run as another user" >&2
  exit 1
fi

echo "== the modes below $prefix, without following links"
status=0
find "$prefix" ! -type l \( ! -readable -o -writable -o \( -type d ! -executable \) \) -print \
  >"$dir/modes.txt" || status=$?
head -n 20 "$dir/modes.txt"
if [ "$status" != 0 ] || [ -s "$dir/modes.txt" ]; then
  echo "$(wc -l <"$dir/modes.txt") entries are unreadable, writable or directories that" \
    "cannot be searched, and find exited with $status" >&2
  exit 1
fi
echo "$(find "$prefix" ! -type l | wc -l) entries: each readable and not writable"

echo "== a Mathlib build output"
sha256sum "$packages/mathlib/.lake/build/lib/lean/Mathlib.olean"

echo "== lake env lean on a file that imports Aeneas, in a project laid out as a stage"
mkdir -p "$dir/artifacts/formal/lake"
ln -sfn "$prefix/backend" "$dir/artifacts/formal/lake/aeneas"
ln -sfn "$packages" "$dir/artifacts/formal/lake/packages"
printf '%s\n' 'import Aeneas' 'example : (2 : Nat) + 2 = 4 := by decide' \
  >"$dir/verification/Check.lean"
(cd "$dir/verification" && tool lake env lean Check.lean)
echo "lake env lean passed"

echo "== git status in the installed Mathlib package"
tool /usr/bin/time -f 'git status: %e s' \
  git --no-optional-locks -C "$packages/mathlib" status --porcelain

echo "== the Rust tools through the rustup proxies, Charon and Aeneas"
tool cargo --version
tool rustc --version
tool charon version
tool aeneas -version

echo "== charon and aeneas on a crate of one function"
mkdir -p "$dir/crate/src"
printf '%s\n' '[package]' 'name = "check"' 'version = "0.0.0"' 'edition = "2024"' \
  '[workspace]' >"$dir/crate/Cargo.toml"
printf '%s\n' 'pub fn min(a: u32, b: u32) -> u32 {' '    if a < b { a } else { b }' '}' \
  >"$dir/crate/src/lib.rs"
(cd "$dir/crate" && tool env CARGO_INCREMENTAL=0 CARGO_TARGET_DIR="$dir/crate/target" \
  charon cargo --preset=aeneas --sysroot default --dest-file "$dir/check.llbc" -- --lib)
(cd "$dir" && tool aeneas -backend lean -no-progress-bar -dest "$dir/aeneas" "$dir/check.llbc")
find "$dir/aeneas" -name '*.lean' | grep .

echo "== recorded only: git without the safe.directory variables (128 expected)"
status=0
tool env -u GIT_CONFIG_COUNT -u GIT_CONFIG_KEY_0 -u GIT_CONFIG_VALUE_0 \
  git -C "$packages/mathlib" rev-parse HEAD || status=$?
echo "exit status $status"

echo "== recorded only: git status with core.checkStat=minimal"
status=0
tool /usr/bin/time -f 'git status with core.checkStat=minimal: %e s' \
  git --no-optional-locks -C "$packages/mathlib" -c core.checkStat=minimal status --porcelain \
  || status=$?
echo "exit status $status"

echo "== recorded only: lake build --no-build of Aeneas (0 up to date, 3 out of date)"
status=0
(cd "$dir/verification" && tool lake build --no-build --no-cache +Aeneas) || status=$?
echo "exit status $status"
