#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
lake build LojitaCtx Lojita test-kernel-taboos test-io-showcase test-vfs-twin \
  test-posix-host io-diff-model test-sandbox-owned treeCasNativeTest

kernel=0
io=0
.lake/build/bin/test-kernel-taboos || kernel=$?
./test-io-all.sh "$@" || io=$?
printf 'KernelTaboos exit=%d, IO gates exit=%d\n' "$kernel" "$io"
(( kernel == 0 && io == 0 ))
