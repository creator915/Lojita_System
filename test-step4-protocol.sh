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

echo "=== [Step 4.1] Audit --safe Header & Zero Postulates / Escapes in Context/Protocol.agda ==="
head -n 1 "$REPO/Context/Protocol.agda" | grep -q -- "--safe" || {
  echo "FAIL: Context/Protocol.agda missing --safe header" >&2
  exit 1
}
if rg -n '^\s*postulate\b|primTrustMe|TERMINATING|NON_TERMINATING|--guardedness|\{!!\}' "$REPO/Context/Protocol.agda"; then
  echo "FAIL: Context/Protocol.agda contains forbidden escape hatch" >&2
  exit 1
fi
echo "  [PASS] Context/Protocol.agda carries {-# OPTIONS --safe #-} with zero postulates/escapes."

echo "=== [Step 4.2] Build Lean 4 AgdaMirror.Protocol (with #agda_prism_guard_axioms) & agda2lean ==="
(cd "$REPO/runtime/lean-prism" && lake build liblean_cli_host AgdaMirror AgdaMirror:static agda2lean)
PRISM_BIN="$REPO/runtime/lean-prism/.lake/build/bin/agda2lean"
PRISM_LIB="$REPO/runtime/lean-prism/.lake/build/lib/lean"
test -x "$PRISM_BIN"
echo "  [PASS] AgdaMirror.Protocol & agda2lean built cleanly with zero axioms."

WORK=$(mktemp -d "${TMPDIR:-/tmp}/test-step4-proto.XXXXXXXX")
trap 'rm -rf -- "$WORK"' EXIT

mkdir -p "$WORK/repo/runtime/tools" "$WORK/agda_cfg"
cp -R "$REPO"/{Backend,Code,Context,Meta,OwnershipIO,Store,Test} "$WORK/repo/"
cp "$REPO"/Code.agda "$REPO"/Ownership.agda "$REPO"/OwnershipIO.agda "$REPO"/check.sh "$WORK/repo/"
cp "$REPO"/runtime/*.hs "$REPO"/runtime/*.c "$REPO"/runtime/*.h "$WORK/repo/runtime/"
cp "$REPO"/runtime/tools/*.hs "$REPO"/runtime/tools/*.c "$WORK/repo/runtime/tools/"
ln -s "$REPO/runtime/lean-prism" "$WORK/repo/runtime/lean-prism"
if [ -d "$REPO/dump" ]; then
  ln -s "$REPO/dump" "$WORK/repo/dump"
fi

echo "=== [Step 4.3] Verify Context/Protocol.agda & Test/ProtocolGluingTest.agda in Agda ==="
(cd "$WORK/repo" && AGDA_DIR="$WORK/agda_cfg" ./check.sh Context/Protocol.agda)
(cd "$WORK/repo" && AGDA_DIR="$WORK/agda_cfg" ./check.sh Test/ProtocolGluingTest.agda)
echo "  [PASS] Context/Protocol.agda & Test/ProtocolGluingTest.agda verified cleanly in Agda."

echo "=== [Step 4.4] Verify Pure Lean 4 Fast-Path Check & Negative Gate on Context.Protocol (0 Agda Calls!) ==="
mkdir -p "$WORK/no-agda-bin" "$WORK/probe/Gen"
cat >"$WORK/no-agda-bin/agda" <<'SH'
#!/usr/bin/env bash
echo "FATAL: agda subprocess invoked during pure Lean 4 fast-path check!" >&2
exit 99
SH
chmod +x "$WORK/no-agda-bin/agda"

cat >"$WORK/probe/Gen/ProtocolFastProbe.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Gen.ProtocolFastProbe where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.World using
  ( clockCap; ttyCap; fsCap; _∈_; here; there; _⊆_; ⊆-cons; ⊆-nil
  ; SimWorld; fs; defaultSimWorld; pure; reactiveApp; ReactiveApp; runWorldPure; runReactivePure )
open import Context.Protocol using
  ( Proto; pEnd; pSend; pRecv; pSelect; pOffer; dual; dual-involutive
  ; Endpoint; epDone; epSend; epRecv; epSelectL; epSelectR; epOffer
  ; coupleEndpoints; composeReactive; coupleReactive
  ; couple-done; couple-send-recv; couple-selectL-offer; couple-selectR-offer; couple-preserves-fs )

pSample : Proto ⊤
pSample = pSelect (pSend tt (pRecv tt pEnd)) (pOffer pEnd pEnd)

law-dual : dual (dual pSample) ≡ pSample
law-dual = dual-involutive pSample

law-done : coupleEndpoints {⊤} {[]} {λ _ → ℕ} (epDone 3) (epDone 4) ≡ pure (3 , 4)
law-done = couple-done {⊤} {[]} {λ _ → ℕ} 3 4

law-send-recv :
  coupleEndpoints {⊤} {[]} {λ _ → ℕ} {pSend tt pEnd}
    (epSend 9 (epDone 1))
    (epRecv (λ x → epDone (x + 2)))
    ≡ pure (1 , 11)
law-send-recv = couple-send-recv {⊤} {[]} {λ _ → ℕ} {tt} {pEnd} 9 (epDone 1) (λ x → epDone (x + 2))

law-selectL :
  coupleEndpoints {⊤} {[]} {λ _ → ℕ} {pSelect pEnd pEnd}
    (epSelectL (epDone 5))
    (epOffer (epDone 6) (epDone 7))
    ≡ pure (5 , 6)
law-selectL = couple-selectL-offer {⊤} {[]} {λ _ → ℕ} {pEnd} {pEnd} (epDone 5) (epDone 6) (epDone 7)

law-selectR :
  coupleEndpoints {⊤} {[]} {λ _ → ℕ} {pSelect pEnd pEnd}
    (epSelectR (epDone 5))
    (epOffer (epDone 6) (epDone 7))
    ≡ pure (5 , 7)
law-selectR = couple-selectR-offer {⊤} {[]} {λ _ → ℕ} {pEnd} {pEnd} (epDone 5) (epDone 6) (epDone 7)

noFs : fsCap ∈ (clockCap ∷ ttyCap ∷ []) → ⊥
noFs (there (there ()))

law-frame-fs :
  ∀ (epA : Endpoint (clockCap ∷ ttyCap ∷ []) (λ (_ : ⊤) → ℕ) (pSend tt pEnd) ℕ)
    (epB : Endpoint (clockCap ∷ ttyCap ∷ []) (λ (_ : ⊤) → ℕ) (pRecv tt pEnd) ℕ)
    (w   : SimWorld) →
  fs (proj₂ (runWorldPure (coupleEndpoints epA epB) w)) ≡ fs w
law-frame-fs = couple-preserves-fs noFs

clk⊆ : (clockCap ∷ []) ⊆ (clockCap ∷ ttyCap ∷ [])
clk⊆ = ⊆-cons here ⊆-nil

tty⊆ : (ttyCap ∷ []) ⊆ (clockCap ∷ ttyCap ∷ [])
tty⊆ = ⊆-cons (there here) ⊆-nil

coupledApp : ReactiveApp (clockCap ∷ ttyCap ∷ []) (ℕ × ℕ)
coupledApp =
  coupleReactive {Tag = ⊤} {Payload = λ _ → ℕ} {P = pSend tt pEnd}
    clk⊆ tty⊆ (pure 1) (pure 2)
    (λ _ s₁ → epSend (suc s₁) (epDone (inj₁ (suc s₁))))
    (λ s₂ → epRecv (λ m → epDone (inj₁ (s₂ + m))))

law-reactive-init : proj₁ (runReactivePure coupledApp [] defaultSimWorld) ≡ inj₁ (1 , 2)
law-reactive-init = refl
AGDA

T0=$(date +%s%3N)
PATH="$WORK/no-agda-bin:$PATH" "$PRISM_BIN" prism-check \
  --lib-dir "$PRISM_LIB" \
  --work-dir "$WORK/chk_fast" \
  --main "$WORK/probe/Gen/ProtocolFastProbe.agda"
T1=$(date +%s%3N)
echo "  [PASS] Gen.ProtocolFastProbe verified on pure Lean 4 fast path in $((T1 - T0)) ms (0 Agda calls!)."

cat >"$WORK/probe/Gen/BadProtocolLaw.agda" <<'AGDA'
{-# OPTIONS --safe #-}
module Gen.BadProtocolLaw where

open import Data.List using ([]; _∷_)
open import Data.Product using (proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Terminal using (bytes)
open import Context.World using (fsCap; FsError; here; writeFileW; SimWorld; fs; runWorldPure)
open import Context.Protocol using (pEnd; pSend; pRecv; epDone; epSend; epRecv; liftProgToEndpoint; coupleEndpoints)

-- False claim: writing to disk in a coupled session leaves `SimWorld.fs` unchanged!
bad-fs-law : ∀ (w : SimWorld) →
  fs (proj₂ (runWorldPure
    (coupleEndpoints {⊤} {fsCap ∷ []} {λ _ → ⊤} {pSend tt pEnd} {⊤} {FsError ⊎ ⊤}
      (epSend tt (epDone tt))
      (epRecv (λ _ → liftProgToEndpoint (writeFileW here "vault/record.txt" (bytes "x")) epDone)))
    w)) ≡ fs w
bad-fs-law _ = refl
AGDA

set +e
PATH="$WORK/no-agda-bin:$PATH" "$PRISM_BIN" prism-check \
  --lib-dir "$PRISM_LIB" \
  --work-dir "$WORK/chk_bad" \
  --main "$WORK/probe/Gen/BadProtocolLaw.agda" >"$WORK/bad.out" 2>&1
BAD_RC=$?
set -e
if [ "$BAD_RC" -ne 11 ]; then
  echo "FAIL: expected exitCode=11 on BadProtocolLaw, got $BAD_RC:" >&2
  cat "$WORK/bad.out" >&2
  exit 1
fi
echo "  [PASS] BadProtocolLaw deterministically rejected by Lean 4 kernel with exitCode=11 (0 Agda calls!)."

echo "=== [Step 4.5] Compile & Run End-to-End Multi-Node Dialectica Tree Gluing Test (ProtocolGluingTest) ==="
CLI_HOST_C="$WORK/repo/runtime/cli_host.c"
mkdir -p "$WORK/tool-build"
(
  cd "$WORK/repo"
  AGDA_DIR="$WORK/agda_cfg" agda --compile \
    --ghc-flag=-O0 --ghc-flag=-threaded \
    --ghc-flag=-iruntime --ghc-flag=-iruntime/tools \
    "--ghc-flag=$CLI_HOST_C" \
    "--compile-dir=$WORK/tool-build" \
    -i . -i /usr/share/agda-stdlib \
    Test/ProtocolGluingTest.agda >"$WORK/compile.log" 2>&1 || {
      tail -n 100 "$WORK/compile.log" >&2
      exit 1
    }
  timeout 180 "$WORK/tool-build/ProtocolGluingTest"
)

echo "=== ALL STEP 4 CLOSED-WORLD MICROSERVICE PROTOCOL GLUING GATES PASSED ==="
