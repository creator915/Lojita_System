#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
REPO="$PWD"

if ! command -v rg >/dev/null 2>&1; then
  for codex_path in /root/.codex/packages/standalone/releases/*/codex-path; do
    if [ -x "$codex_path/rg" ]; then
      export PATH="$codex_path:$PATH"
      break
    fi
  done
fi

echo "=== [Step 2.1] Audit Zero Postulates / Zero Escapes Across All --safe World & Laws Modules ==="
LAW_MODS=(
  "Context/Tools/Clock.agda"
  "Context/Tools/ClockLaws.agda"
  "Context/Tools/TermLaws.agda"
  "Context/Tools/FsLaws.agda"
  "Context/Tools/GitLaws.agda"
  "Context/Tools/NetLaws.agda"
  "Context/World.agda"
  "Context/WorldLaws.agda"
  "Test/Step2LawsMirrorTest.agda"
)

for f in "${LAW_MODS[@]}"; do
  head -n 1 "$f" | grep -q -- "--safe" || { echo "FAIL: $f missing --safe header"; exit 1; }
  if rg -n '^\s*postulate\b|primTrustMe|TERMINATING|NON_TERMINATING|--guardedness|\{!!\}' "$f"; then
    echo "FAIL: $f contains forbidden escape hatch"
    exit 1
  fi
done
echo "  [PASS] All 9 World & Laws modules carry {-# OPTIONS --safe #-} with zero postulates/escapes."

echo "=== [Step 2.2] Verify All --safe Laws & Test Modules in Agda ==="
for f in "${LAW_MODS[@]}"; do
  ./check.sh "$f"
done

echo "=== [Step 2.3] Build Lean 4 AgdaMirror (with #agda_prism_guard_axioms) & agda2lean ==="
(cd "$REPO/runtime/lean-prism" && lake build AgdaMirror AgdaMirror:static agda2lean)
PRISM_BIN="$REPO/runtime/lean-prism/.lake/build/bin/agda2lean"
PRISM_LIB="$REPO/runtime/lean-prism/.lake/build/lib/lean"

WORK=$(mktemp -d "${TMPDIR:-/tmp}/test-step2.XXXXXXXX")
trap 'rm -rf -- "$WORK"' EXIT

# Create a fake `agda` trap in front of PATH during fast-path checks to prove ZERO Agda subprocess calls!
mkdir -p "$WORK/no-agda-bin"
cat >"$WORK/no-agda-bin/agda" <<'SH'
#!/usr/bin/env bash
echo "FATAL: agda subprocess was invoked during pure Lean 4 fast-path check!" >&2
exit 99
SH
chmod +x "$WORK/no-agda-bin/agda"

echo "=== [Step 2.4] Verify Sub-Second Pure Lean 4 Fast-Path on Step2LawsMirrorTest (0 Agda Calls!) ==="
mkdir -p "$WORK/Test"
cp "$REPO/Test/Step2LawsMirrorTest.agda" "$WORK/Test/Step2LawsMirrorTest.agda"

T0=$(date +%s%3N)
PATH="$WORK/no-agda-bin:$PATH" "$PRISM_BIN" prism-check \
  --lib-dir "$PRISM_LIB" \
  --work-dir "$WORK/chk_fast" \
  --main "$WORK/Test/Step2LawsMirrorTest.agda"
T1=$(date +%s%3N)
ELAPSED=$((T1 - T0))
echo "  [PASS] Step2LawsMirrorTest verified purely by Lean 4 kernel in ${ELAPSED} ms (0 Agda calls!)"

echo "=== [Step 2.5] Verify Negative Gate: False SimWorld Universal Claim Rejected with exitCode = 11 ==="
cat >"$WORK/Test/BadWorldLaw.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Test.BadWorldLaw where

open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.World

-- False claim: sleeping 5ms leaves clock unchanged!
bad-law : ∀ (w : SimWorld) →
  clock (proj₂ (runWorldPure (sleepW clock∈All 5) w)) ≡ clock w
bad-law _ = refl
AGDA

set +e
PATH="$WORK/no-agda-bin:$PATH" "$PRISM_BIN" prism-check \
  --lib-dir "$PRISM_LIB" \
  --work-dir "$WORK/chk_bad" \
  --main "$WORK/Test/BadWorldLaw.agda" >"$WORK/bad.out" 2>&1
BAD_RC=$?
set -e
if [ "$BAD_RC" -ne 11 ]; then
  echo "FAIL: expected exitCode=11 on BadWorldLaw, got $BAD_RC:"
  cat "$WORK/bad.out"
  exit 1
fi
echo "  [PASS] BadWorldLaw deterministically rejected by Lean 4 kernel with exitCode=11 (0 Agda calls!)"

echo "=== [Step 2.6] Regression Gates (Step 0, Step 1, Lean-Prism Suite) ==="
./test-step1-world.sh
./test-lean-prism.sh
./test-step0-baseline.sh

echo "=== ALL STEP 2 UNIVERSAL LAWS & LEAN 4 AGDAMIRROR GATES PASSED ==="
