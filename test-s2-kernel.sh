#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/v9-s2.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
export TMPDIR="$scratch"
lake build Lojita:static LojitaCtx:static test-s2-kernel
timeout 120s lake exe test-s2-kernel
