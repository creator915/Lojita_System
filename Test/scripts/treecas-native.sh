#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build treeCasNativeTest
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cc -O2 -Wall -Wextra -Werror -ffunction-sections -fdata-sections \
  -Wl,--gc-sections -I"$(lean --print-prefix)/include" \
  Test/scripts/treecas-size.c -o "$scratch/test-size"
"$scratch/test-size"
python3 Test/scripts/treecas-native.py .lake/build/bin/treeCasNativeTest
