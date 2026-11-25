#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")"
status=0
python3 Test/scripts/io-size.py || status=1
lake build LojitaCtx || exit 1
lake env lean Test/PosixPurity.lean || status=1
exit "$status"
