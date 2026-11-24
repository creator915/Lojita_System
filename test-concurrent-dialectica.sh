#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/v9-dialectica.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
export TMPDIR="$scratch"

lake build test-concurrent-dialectica
suite=.lake/build/bin/test-concurrent-dialectica
"$suite" replay "$scratch"
"$suite" faults "$scratch"
"$suite" stress "$scratch"

serial="tmp/runs/gron-v9-posix"
if [[ -f "$serial/store/refs/trees/T3" ]]; then
  python3 scripts/extract_trace_fixture.py --check
fi
