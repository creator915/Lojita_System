#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
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

echo "=== [Step 0.1] Build Lean 4 Prism, harness-engine, relays & Main ==="
if [ ! -x "$REPO/Main" ] || [ ! -x "$REPO/runtime/lean-prism/.lake/build/bin/agda2lean" ] || [ ! -x "$REPO/tmp/term-build/web-relay" ]; then
  ./build.sh
else
  (cd "$REPO/runtime/lean-prism" && lake build liblean_cli_host AgdaMirror:static agda2lean)
fi
PRISM_BIN="$REPO/runtime/lean-prism/.lake/build/bin/agda2lean"
PRISM_LIB="$REPO/runtime/lean-prism/.lake/build/lib/lean"

WORK=$(mktemp -d "${TMPDIR:-/tmp}/test-step0.XXXXXXXX")
trap 'rm -rf -- "$WORK"' EXIT

echo "=== [Step 0.2] Verify --safe + Context.Terminal & PolyTransport Blindspot Fixes ==="
mkdir -p "$WORK/Gen/T0"

# Case A: --safe module importing Context.Terminal ONLY for Bytes / bytes
cat >"$WORK/Gen/T0/SafeBytesOnly.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Gen.T0.SafeBytesOnly where

open import Context.Terminal using (Bytes; bytes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

sample : Bytes
sample = bytes "gron"

sample-ok : sample ≡ bytes "gron"
sample-ok = refl
AGDA
"$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/chkA" --main "$WORK/Gen/T0/SafeBytesOnly.agda"
echo "  [PASS] Case A: --safe module importing Context.Terminal (Bytes only) -> exitCode=0"

# Case B: --safe module importing Key, Cell, TimedMachine, Timer, Event, Effect (no 8 hardcoded substrings)
cat >"$WORK/Gen/T0/SafeKeyCellTimed.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Gen.T0.SafeKeyCellTimed where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Terminal using (Key; up; encodeKey; bytes; Cell; cell; plain; TimedMachine; timed; emptyObs; Event; input; timeout; Effect; effect; stepTimed; sleepMs)

key-up : encodeKey up ≡ bytes "\ESC[A"
key-up = refl

c0 : Cell
c0 = cell 'x' plain

h : Event ℕ → ℕ → Effect ℕ ℕ
h (input _) s = effect s emptyObs []
h (timeout k) _ = effect k emptyObs []

m0 : TimedMachine ℕ ℕ
m0 = timed 0 7 [] emptyObs

m1-now : TimedMachine.now (proj₁ (stepTimed h (sleepMs 3) m0)) ≡ 3
m1-now = refl
AGDA
"$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/chkB" --main "$WORK/Gen/T0/SafeKeyCellTimed.agda"
echo "  [PASS] Case B: --safe module using Key, Cell, TimedMachine, stepTimed -> exitCode=0 (0 Agda calls)"

# Case C: Transitive --safe dependency where main has 0 Terminal substrings
cat >"$WORK/Gen/T0/ChildTerm.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Gen.T0.ChildTerm where

open import Data.List using (List)
open import Data.String using (String)
open import Context.Terminal using (Screen; blankScreen; stepANSI; screenLines; bytes)

render2x4 : String → List String
render2x4 s = screenLines (stepANSI (blankScreen 2 4) (bytes s))
AGDA

cat >"$WORK/Gen/T0/RootCaller.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Gen.T0.RootCaller where

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Gen.T0.ChildTerm as C

check-lf : C.render2x4 "ab\ncd" ≡ ("ab  " ∷ "  cd" ∷ [])
check-lf = refl

check-crlf : C.render2x4 "ab\r\ncd" ≡ ("ab  " ∷ "cd  " ∷ [])
check-crlf = refl
AGDA
"$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/chkC" \
  --dep "$WORK/Gen/T0/ChildTerm.agda" \
  --main "$WORK/Gen/T0/RootCaller.agda"
echo "  [PASS] Case C: Transitive --safe child importing Context.Terminal Screen/stepANSI -> exitCode=0"

# Case D: --safe module importing Context.PolyTransport
cat >"$WORK/Gen/T0/SafePoly.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Gen.T0.SafePoly where

open import Data.Nat using (ℕ)
open import Context.PolyTransport using (PortRel; idPort)

relNat : PortRel ℕ ℕ
relNat = idPort ℕ
AGDA
"$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/chkD" --main "$WORK/Gen/T0/SafePoly.agda"
echo "  [PASS] Case D: --safe module importing Context.PolyTransport -> exitCode=0"

# Case E: Negative check (--safe importing non-safe Context.Blueprint MUST still fail with exitCode=10)
set +e
"$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/chkE" --main "$REPO/Test/prism-corpus/negative/N23_SafeImportsUnsafe.agda" >/dev/null 2>&1
rcE=$?
set -e
[ "$rcE" -eq 10 ] || { echo "FAIL Case E: expected exitCode=10 on N23_SafeImportsUnsafe, got $rcE"; exit 1; }
echo "  [PASS] Case E: N23_SafeImportsUnsafe (--safe importing Context.Blueprint) rejected with exitCode=10"

echo "=== [Step 0.3] Verify WebOperad Pure Proofs & Ownership Tool Integration ==="
./check.sh Context/Tools/WebOperad.agda
./check.sh UI/OperadApp.agda
./check.sh Test/Tools/WebOperadConformance.agda
./check.sh Code/Tools/WebTool.agda
echo "  [PASS] WebOperad (--safe), UI/OperadApp (--safe), WebOperadConformance (--safe), WebTool all verified"

echo "=== ALL STEP 0 ACCEPTANCE CHECKS PASSED ==="
