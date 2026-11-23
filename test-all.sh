#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lojita-offline.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
mkdir "$scratch/bin" "$scratch/tmp"
# Use the system utility path only to locate these executables. Child suites
# inherit the allowlist, including the assembler and linker used by cc.
system_path=$(command -p getconf PATH)
for tool in bash sh env dirname basename mkdir mktemp ln mv cp chmod find cat grep head file \
            timeout id chown ar as ld cc git python3; do
  path=$(PATH="$system_path" type -P "$tool")
  ln -s -- "$path" "$scratch/bin/$tool"
done
if path=$(PATH="$system_path" type -P docker); then ln -s -- "$path" "$scratch/bin/docker"; fi
export PATH="$HOME/.elan/bin:$scratch/bin" TMPDIR="$scratch/tmp"
{ ! command -v agda && ! command -v ghc && ! command -v runghc; } || {
  echo 'a retired compiler is visible on the cleanroom PATH' >&2
  exit 1
}
legacy=$(find . \( -name '*.agda' -o -name '*.agdai' -o -name '*.hs' \) -print -quit)
if [[ -n "$legacy" ]]; then
  echo "legacy source or interface found: $legacy" >&2
  exit 1
fi
./build.sh
for relay in .lake/build/relays/{term,fs,net,git,web}-relay; do
  file -b "$relay" | grep -qE '^ELF .*statically linked'
done
./test-s1-foundation.sh
./test-s2-kernel.sh
./test-s3-harness.sh
./test-prompts-lean4.sh
./test-s4-session.sh
./test-posix-channels.sh
echo 'All available Pure Lean 4 gates passed.'
