#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/ct-v8-inplace.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export AGDA_DIR="$scratch/agda" TMPDIR="$scratch/tmp"
mkdir -p "$AGDA_DIR" "$TMPDIR"
if [[ ! -x dump/dump || ! -x runtime/lean-prism/.lake/build/bin/harness-engine ]]; then
  ./build.sh
fi
build=tmp/v8-inplace-build
mkdir -p "$build"
agda --compile --ghc-flag=-O0 --ghc-flag=-threaded \
  --ghc-flag=-iruntime --ghc-flag=-iruntime/tools "--ghc-flag=$PWD/runtime/cli_host.c" \
  --compile-dir="$build" -i . -i /usr/share/agda-stdlib Test/InPlaceTowerRecoveryTest.agda \
  >"$build/compile.log" 2>&1 || { tail -45 "$build/compile.log" >&2; exit 1; }
for mode in prism legacy audit; do
  echo "Testing in-place tower recovery with $mode"
  CODETRANSPORT_BACKEND="$mode" timeout 1800 "$build/InPlaceTowerRecoveryTest"
done
