#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
release=$(lean --print-prefix)
python3 Test/scripts/g1-release.py "$release"
export LEAN_SYSROOT="$release" PATH="$release/bin:$PATH"
python3 Test/scripts/io-size.py
lake build LojitaCtx
lake env lean --run Test/PosixPurity.lean
for input in 7 8; do
  lake env lean --run Test/audit/Lean436DataProbe.lean "$input"
done
Test/scripts/test-g1-regressions.sh
