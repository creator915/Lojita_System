#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
flags=(-std=c11 -static -O2 -Wall -Wextra -Werror)
cc "${flags[@]}" runtime/lojita-sandbox.c -o "$scratch/launcher"
cc "${flags[@]}" Test/scripts/io-diff-linux.c -o "$scratch/probe" -lutil
lake build io-diff-model test-posix-host
.lake/build/bin/test-posix-host
python3 -B Test/scripts/io-diff.py "$scratch/launcher" "$scratch/probe" .lake/build/bin/io-diff-model "$@"
