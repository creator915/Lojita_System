#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d /tmp/v7-suite.XXXXXX)
trap 'rm -r -- "$scratch"' EXIT
export AGDA_DIR="$scratch"
if [[ ! -x dump/dump || ! -x runtime/lean-prism/.lake/build/bin/harness-engine ]]; then
  ./build.sh
fi
build=tmp/v7-2d-e2e-build
mkdir -p "$build"
agda --compile --ghc-flag=-O0 --ghc-flag=-threaded \
  --ghc-flag=-iruntime --ghc-flag=-iruntime/tools "--ghc-flag=$PWD/runtime/cli_host.c" \
  --compile-dir="$build" -i . -i /usr/share/agda-stdlib Test/TwoDimRecoveryE2E.agda \
  >"$build/compile.log" 2>&1 || { tail -45 "$build/compile.log" >&2; exit 1; }
timeout 1200 "$build/TwoDimRecoveryE2E"
