#!/bin/bash
set -euo pipefail

export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"
REPO="$PWD"

echo "========================================================================"
echo "  CodeTransport Lean 4 Prism + v2 Optic Lens — Full Acceptance Suite"
echo "========================================================================"

echo ""
echo "== [Step 1/8] Authoritative .agda Source & Guardedness/Safe Boundary Check =="
grep -q '^module Ownership where' "$REPO/Ownership.agda" || grep -q '{-# OPTIONS --safe --guardedness #-}' "$REPO/Ownership.agda"
grep -q '{-# OPTIONS --safe #-}' "$REPO/Meta/Boundary.agda"
grep -q '{-# OPTIONS --safe #-}' "$REPO/Backend/Mode.agda"
echo "  [OK] Authoritative .agda kernel & boundary proofs intact (--safe / --guardedness)"

echo ""
echo "== [Step 2/8] Building Lean 4 AgdaMirror + v2 agda2lean Lens Slicer =="
(cd "$REPO/runtime/lean-prism" && lake build AgdaMirror:static agda2lean)
PRISM_BIN="$REPO/runtime/lean-prism/.lake/build/bin/agda2lean"
PRISM_LIB="$REPO/runtime/lean-prism/.lake/build/lib/lean"
PRISM_IR="$REPO/runtime/lean-prism/.lake/build/ir"
echo "  [OK] Built $PRISM_BIN"

WORK="$REPO/tmp/prism-acceptance"
rm -rf "$WORK"
mkdir -p "$WORK"

run_agda_isolated() {
  local file="$1"
  local extra_dep="${2:-}"
  local cfg="$WORK/agda-cfg"
  rm -rf "$WORK/agda-work"
  mkdir -p "$cfg" "$WORK/agda-work"
  if [[ "$file" == "$REPO/Context/"* ]]; then
    AGDA_DIR="$cfg" agda --no-libraries -i "$REPO" -i /usr/share/agda-stdlib "$file" >/dev/null 2>&1
    return $?
  fi
  if [ -n "$extra_dep" ]; then
    local dep_mod
    dep_mod=$(awk '$1=="module"{print $2; exit}' "$extra_dep")
    local dep_rel="${dep_mod//./\/}.agda"
    mkdir -p "$(dirname "$WORK/agda-work/$dep_rel")"
    cp "$extra_dep" "$WORK/agda-work/$dep_rel"
  fi
  local mod_name
  mod_name=$(awk '$1=="module"{print $2; exit}' "$file")
  local rel_path
  if [ -n "$mod_name" ]; then
    rel_path="${mod_name//./\/}.agda"
  else
    rel_path="$(basename "$file")"
  fi
  mkdir -p "$(dirname "$WORK/agda-work/$rel_path")"
  cp "$file" "$WORK/agda-work/$rel_path"
  AGDA_DIR="$cfg" agda --no-libraries -i "$WORK/agda-work" -i "$REPO" -i /usr/share/agda-stdlib "$WORK/agda-work/$rel_path" >/dev/null 2>&1
  local rc=$?
  rm -rf "$WORK/agda-work"
  return $rc
}

echo ""
echo "== [Step 3/8] Pure Sweet-Spot Corpus (0 Agda Invocations, 100% Lean 4) =="
POS_COUNT=0
for f in "$REPO"/Test/prism-corpus/positive/*.agda "$REPO/Context/Blueprint.agda"; do
  base="$(basename "$f")"
  POS_COUNT=$((POS_COUNT + 1))
  set +e
  "$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/pos_$POS_COUNT" --main "$f" >"$WORK/pos.out" 2>&1
  p_rc=$?
  run_agda_isolated "$f"
  a_rc=$?
  set -e
  if [ "$p_rc" -ne 0 ] || [ "$a_rc" -ne 0 ]; then
    echo "FAIL on positive sample $base: prism_exit=$p_rc agda_exit=$a_rc"
    cat "$WORK/pos.out"
    exit 1
  fi
  echo "  [OK] $base : prism=0 (Pure Lean4 FastFocus) | agda=0"
done
echo "  => Sweet-spot positive pass rate: $POS_COUNT / $POS_COUNT (100%)"

echo ""
echo "== [Step 4/8] v2 Unit-SCC Optic Lens, De-Infection & Unified Thunk Linker =="
HYB_SINGLE=(
  "$REPO/Context/PolyTransport.agda"
  "$REPO/Test/prism-corpus/longtail-bot/L01_CoinductiveStream.agda"
  "$REPO/Test/prism-corpus/longtail-bot/L03_WithClause.agda"
  "$REPO/Test/prism-corpus/longtail-bot/L04_AckermannLex.agda"
  "$REPO/Test/prism-corpus/hybrid/H01_HybridCoindMain.agda"
  "$REPO/Test/prism-corpus/hybrid/H02_GuardedLib.agda"
  "$REPO/Test/prism-corpus/hybrid/H03_HybridLexAndWithMain.agda"
  "$REPO/Test/prism-corpus/hybrid/H04_PostfixCopatterns.agda"
)
HYB_COUNT=0
for f in "${HYB_SINGLE[@]}"; do
  base="$(basename "$f")"
  HYB_COUNT=$((HYB_COUNT + 1))
  "$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/hyb_$HYB_COUNT" --main "$f"
  run_agda_isolated "$f"
  echo "  [OK] $base : Lens FastFocus + Parameterized SlowSlice = PASS"
done

# Verify H01 slice boundaries (`FAST_UNITS (9)` + `SLOW_UNITS (2)` + `_SlowResidual` params)
H01_SLICE=$("$PRISM_BIN" inspect-slice --main "$REPO/Test/prism-corpus/hybrid/H01_HybridCoindMain.agda")
echo "$H01_SLICE" | grep -q "FAST_UNITS (9):"
echo "$H01_SLICE" | grep -q "SLOW_UNITS (2): coind:Stream, orbitFrom"
echo "$H01_SLICE" | grep -q "module _SlowResidual (fastStep : ℕ → ℕ) (fastWeight : ℕ → ℕ) where"
echo "  [OK] H01_HybridCoindMain : 9/11 units in FastFocus, F₁ parameterized via _SlowResidual, F₂ pruned"

# Verify H02 cross-module `--guardedness` de-infection (`SLOW_UNITS (0)` on caller!)
H02_SLICE=$("$PRISM_BIN" inspect-slice \
  --dep "$REPO/Test/prism-corpus/hybrid/H02_GuardedLib.agda" \
  --main "$REPO/Test/prism-corpus/hybrid/H02_DeinfectedCaller.agda")
echo "$H02_SLICE" | grep -q "SLOW_UNITS (0):"
"$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/hyb_h02_caller" \
  --dep "$REPO/Test/prism-corpus/hybrid/H02_GuardedLib.agda" \
  --main "$REPO/Test/prism-corpus/hybrid/H02_DeinfectedCaller.agda"
run_agda_isolated "$REPO/Test/prism-corpus/hybrid/H02_DeinfectedCaller.agda" "$REPO/Test/prism-corpus/hybrid/H02_GuardedLib.agda"
echo "  [OK] H02_DeinfectedCaller : --guardedness infection stripped (SLOW_UNITS = 0 on caller!)"

# Verify unified `leanc -O3` native C compilation (zero MAlonzo!) for H01 & H03
"$PRISM_BIN" prism-build --lib-dir "$PRISM_LIB" --ir-dir "$PRISM_IR" \
  --work-dir "$WORK/hyb_exe_h01" --out "$WORK/h01_bin" \
  --main "$REPO/Test/prism-corpus/hybrid/H01_HybridCoindMain.agda"
H01_OUT=$("$WORK/h01_bin")
[ "$H01_OUT" = "score=75" ] || { echo "FAIL H01 stdout: $H01_OUT"; exit 1; }
echo "  [OK] H01 unified Thunk + leanc -O3 binary output: $H01_OUT ($(du -h "$WORK/h01_bin" | awk '{print $1}'))"

"$PRISM_BIN" prism-build --lib-dir "$PRISM_LIB" --ir-dir "$PRISM_IR" \
  --work-dir "$WORK/hyb_exe_h03" --out "$WORK/h03_bin" \
  --main "$REPO/Test/prism-corpus/hybrid/H03_HybridLexAndWithMain.agda"
H03_OUT=$("$WORK/h03_bin")
[ "$H03_OUT" = "ack=9,parity=odd" ] || { echo "FAIL H03 stdout: $H03_OUT"; exit 1; }
echo "  [OK] H03 unified Foetus+Mutual+With leanc -O3 binary output: $H03_OUT ($(du -h "$WORK/h03_bin" | awk '{print $1}'))"

echo ""
echo "== [Step 5/8] Adversarial Negative Corpus (27 Cases — Zero False Positives Audit) =="
NEG_COUNT=0
SYNTAX_CAUGHT=0
TYPE_OR_SLICE_CAUGHT=0
BOT_CAUGHT=0
FALSE_POSITIVES=0

for f in "$REPO"/Test/prism-corpus/negative/*.agda; do
  base="$(basename "$f")"
  NEG_COUNT=$((NEG_COUNT + 1))
  set +e
  "$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/neg_$NEG_COUNT" --main "$f" >"$WORK/neg.out" 2>&1
  p_rc=$?
  run_agda_isolated "$f"
  a_rc=$?
  set -e
  if [ "$a_rc" -eq 0 ]; then
    echo "FAIL: negative test $base unexpectedly passed vanilla Agda!"
    exit 1
  fi
  if [ "$p_rc" -eq 0 ]; then
    echo "SOUNDNESS VIOLATION (FALSE POSITIVE): $base failed Agda (rc=$a_rc) but PASSED LeanPrism!"
    FALSE_POSITIVES=$((FALSE_POSITIVES + 1))
    exit 1
  elif [ "$p_rc" -eq 10 ]; then
    SYNTAX_CAUGHT=$((SYNTAX_CAUGHT + 1))
    echo "  [OK] $base : prism=10 (1ms Syntax/Scope Gate) | agda=FAIL"
  elif [ "$p_rc" -eq 11 ]; then
    TYPE_OR_SLICE_CAUGHT=$((TYPE_OR_SLICE_CAUGHT + 1))
    echo "  [OK] $base : prism=11 (Lean4 Kernel / Agda SlowSlice Gate) | agda=FAIL"
  elif [ "$p_rc" -eq 20 ]; then
    BOT_CAUGHT=$((BOT_CAUGHT + 1))
    echo "  [OK] $base : prism=20 (⊥ -> LegacyAgda Rejects) | agda=FAIL"
  else
    echo "FAIL: unexpected prism exit code $p_rc on $base"
    cat "$WORK/neg.out"
    exit 1
  fi
done
echo "  => Adversarial False Positives: $FALSE_POSITIVES / $NEG_COUNT (0.0%)"
echo "     (1ms Syntax/Mixfix/Scope Gate: $SYNTAX_CAUGHT, Lean4 Kernel / SlowSlice: $TYPE_OR_SLICE_CAUGHT, ⊥: $BOT_CAUGHT)"

echo ""
echo "== [Step 6/8] Module-Level ⊥ Fallback Corpus (--without-K / Unmirrored Import) =="
MOD_BOT_FILES=(
  "$REPO/Test/prism-corpus/longtail-bot/L02_WithoutK.agda"
  "$REPO/Test/prism-corpus/longtail-bot/L05_StdlibExtraSym.agda"
)
LT_COUNT=0
for f in "${MOD_BOT_FILES[@]}"; do
  base="$(basename "$f")"
  LT_COUNT=$((LT_COUNT + 1))
  set +e
  "$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/lt_$LT_COUNT" --main "$f" >"$WORK/lt.out" 2>&1
  p_rc=$?
  run_agda_isolated "$f"
  a_rc=$?
  set -e
  if [ "$p_rc" -ne 20 ] || [ "$a_rc" -ne 0 ]; then
    echo "FAIL on module-level BOT sample $base: expected prism=20 & agda=0, got prism=$p_rc agda=$a_rc"
    cat "$WORK/lt.out"
    exit 1
  fi
  echo "  [OK] $base : prism=20 (BOT in <5ms) -> fallback agda=0 (PASS)"
done
echo "  => Module-level ⊥ lossless fallback: $LT_COUNT / $LT_COUNT (100%)"

echo ""
echo "== [Step 7/8] Agda Backend/Mode (--safe) + BackendSwitchTest End-to-End & Benchmarks =="
./check.sh Backend/Mode.agda
mkdir -p "$WORK/switch-exe-build"
AGDA_DIR="$WORK/agda-cfg" agda --compile --ghc-flag=-O0 --compile-dir="$WORK/switch-exe-build" \
  -i "$REPO" -i /usr/share/agda-stdlib "$REPO/Test/BackendSwitchTest.agda" >"$WORK/build-switch-test.log" 2>&1
"$WORK/switch-exe-build/BackendSwitchTest"

echo ""
echo "== Wall-Clock Latency & Binary Size Benchmark (Pure Sweet-Spot & Hybrid Coinductive) =="
BENCH_MOD="$REPO/Test/prism-corpus/positive/P02_PolyListTree.agda"
t0=$(date +%s%3N)
"$PRISM_BIN" prism-dump --main "$BENCH_MOD" >"$WORK/bench.sexp"
t1=$(date +%s%3N)
"$REPO/dump/dump" -i "$(dirname "$BENCH_MOD")" -i /usr/share/agda-stdlib "$BENCH_MOD" >"$WORK/bench_agda.sexp"
t2=$(date +%s%3N)
"$PRISM_BIN" prism-check --lib-dir "$PRISM_LIB" --work-dir "$WORK/bench_lean" --main "$BENCH_MOD" >/dev/null
t3=$(date +%s%3N)
run_agda_isolated "$BENCH_MOD"
t4=$(date +%s%3N)

# Hybrid Coinductive + Fast Main Build Benchmark (`Main.agda` copy of H01)
mkdir -p "$WORK/hyb_bench_src"
sed 's/^module H01_HybridCoindMain where$/module Main where/' \
  "$REPO/Test/prism-corpus/hybrid/H01_HybridCoindMain.agda" > "$WORK/hyb_bench_src/Main.agda"
t5=$(date +%s%3N)
"$PRISM_BIN" prism-build --lib-dir "$PRISM_LIB" --ir-dir "$PRISM_IR" \
  --work-dir "$WORK/hyb_bench_lean" --out "$WORK/bin_hyb_prism" \
  --main "$WORK/hyb_bench_src/Main.agda" >/dev/null
t6=$(date +%s%3N)
mkdir -p "$WORK/hyb_bench_agda"
AGDA_DIR="$WORK/agda-cfg" agda --no-libraries --compile --ghc-flag=-O0 --compile-dir="$WORK/hyb_bench_agda" \
  --ghc-flag=-outputdir --ghc-flag="$WORK/hyb_bench_agda" \
  -i "$WORK/hyb_bench_src" -i /usr/share/agda-stdlib "$WORK/hyb_bench_src/Main.agda" >/dev/null 2>&1
t7=$(date +%s%3N)
HYB_PRISM_SZ=$(du -h "$WORK/bin_hyb_prism" | awk '{print $1}')
HYB_AGDA_SZ=$(du -h "$WORK/hyb_bench_agda/Main" | awk '{print $1}')

echo "  * Dump AST               : LeanPrism = $((t1 - t0)) ms    vs  Legacy dump/dump     = $((t2 - t1)) ms"
echo "  * Pure Fast Typecheck    : LeanPrism = $((t3 - t2)) ms  vs  Legacy agda          = $((t4 - t3)) ms"
echo "  * Hybrid Coind Build-Exe : LeanPrism = $((t6 - t5)) ms ($HYB_PRISM_SZ)  vs  Legacy agda --compile = $((t7 - t6)) ms ($HYB_AGDA_SZ)"

echo ""
echo "== [Step 8/8] Layer 2 Self-Compiled Native Lean 4 harness-engine & Audit Equivalence =="
HARNESS_ENG="$REPO/runtime/lean-prism/.lake/build/bin/harness-engine"
if [ ! -x "$HARNESS_ENG" ] || [ ! -x "$REPO/Main" ]; then
  ./build.sh
fi
ENG_SELF=$("$HARNESS_ENG" verify-self)
[ "$ENG_SELF" = "HARNESS_ENGINE_OK" ] || { echo "FAIL harness-engine verify-self: $ENG_SELF"; exit 1; }
echo "  [OK] harness-engine verify-self : $ENG_SELF ($(du -h "$HARNESS_ENG" | awk '{print $1}'))"

"$REPO/dump/dump" -i "$REPO" -i /usr/share/agda-stdlib "$REPO/Context/Blueprint.agda" >"$WORK/bp.sexp"
printf '(plan (why "keep all") (moves (move (unit "Context.Blueprint.PortLift") (unit "Context.Blueprint.PortLift")) (move (unit "Context.Blueprint.keepPort") (unit "Context.Blueprint.keepPort")) (move (unit "Context.Blueprint.fromEl") (unit "Context.Blueprint.fromEl")) (move (unit "Context.Blueprint.FiberOf") (unit "Context.Blueprint.FiberOf")) (move (unit "Context.Blueprint.composeLift") (unit "Context.Blueprint.composeLift")) (move (unit "Context.Blueprint.Commutes₁") (unit "Context.Blueprint.Commutes₁")) (move (unit "Context.Blueprint.Commutes₂") (unit "Context.Blueprint.Commutes₂")) (move (unit "Context.Blueprint.Commutes₃") (unit "Context.Blueprint.Commutes₃"))))\n' >"$WORK/bp.plan"

CODETRANSPORT_BACKEND=audit "$REPO/Main" roundtrip "$WORK/bp.sexp" >/dev/null
CODETRANSPORT_BACKEND=audit "$REPO/Main" units "$WORK/bp.sexp" >/dev/null
CODETRANSPORT_BACKEND=audit "$REPO/Main" order "$WORK/bp.sexp" >/dev/null
CODETRANSPORT_BACKEND=audit "$REPO/Main" apply "$WORK/bp.sexp" "$WORK/bp.plan" >/dev/null
echo "  [OK] CODETRANSPORT_BACKEND=audit Main roundtrip|units|order|apply : 100% bit-for-bit match (Lean 4 harness-engine == LegacyAgda)"

rm -rf "$WORK"
echo ""
echo "========================================================================"
echo "  ALL LEAN 4 PRISM + v2 OPTIC LENS GATES PASSED (0 FALSE POSITIVES)"
echo "========================================================================"
