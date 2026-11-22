#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"

python3 scripts/embed_prompts.py --check
if [[ ! -x dump/dump || ! -x runtime/lean-prism/.lake/build/bin/harness-engine ]]; then
  ./build.sh
fi
python3 scripts/embed_countermodel.py --check

scratch=$(mktemp -d "${TMPDIR:-/tmp}/v8-cm.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export AGDA_DIR="$scratch/agda-dir"
mkdir -p "$AGDA_DIR"

python3 -u Test/countermodel/check.py "$PWD" "$scratch"
