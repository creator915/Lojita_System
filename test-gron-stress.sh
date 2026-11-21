#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"
exec python3 -B scripts/run_gron_stress.py "$@"
