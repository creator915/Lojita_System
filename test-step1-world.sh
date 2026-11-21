#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"

echo "=== [Step 1.1] Verify --safe headers & zero postulates on Clock.agda & World.agda ==="
for f in Context/Tools/Clock.agda Context/World.agda Test/Step1WorldTest.agda; do
  test "$(head -n 1 "$f")" = '{-# OPTIONS --safe #-}'
  if grep -En '^[[:space:]]*postulate\b|TERMINATING|primTrustMe|allow-unsolved-metas|\{!' "$f"; then
    echo "FAIL: forbidden escape in $f" >&2
    exit 1
  fi
done

echo "=== [Step 1.2] Agda --safe Typecheck of Clock, World, Sandboxes & Step1WorldTest ==="
./check.sh Context/Tools/Clock.agda
./check.sh Context/Tools/FsSandbox.agda
./check.sh Context/Tools/NetSandbox.agda
./check.sh Context/Tools/GitSandbox.agda
./check.sh Context/World.agda
./check.sh Test/Step1WorldTest.agda
./check.sh Test/Tools/FsConformance.agda
./check.sh Test/Tools/NetConformance.agda
./check.sh Test/Tools/GitConformance.agda
./check.sh Test/Tools/ExtToolsConformance.agda

echo "=== ALL STEP 1 ACCEPTANCE CHECKS PASSED ==="
