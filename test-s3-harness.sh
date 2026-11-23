#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/v9-s3.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
export TMPDIR="$scratch"
lake build Lojita:static LojitaCtx:static test-s3-harness
timeout 120s lake exe test-s3-harness
./test-s1-foundation.sh
./test-s2-kernel.sh
echo "6  Session 1 and Session 2 regressions passed"
