#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
REPO="$PWD"

echo "=== [Step 3.1] Audit Abolition of Bare CLIHost & Single WorldRunner Boundary ==="
if [ -e "$REPO/OwnershipIO/CLIHost.agda" ]; then
  echo "FAIL: legacy bare OwnershipIO/CLIHost.agda still exists!" >&2
  exit 1
fi
echo "  [PASS] Legacy bare OwnershipIO/CLIHost.agda removed; OwnershipIO/WorldRunner.agda is the sole target IO boundary."

WORK=$(mktemp -d "${TMPDIR:-/tmp}/test-world-conf.XXXXXXXX")
trap 'rm -rf -- "$WORK"' EXIT

mkdir -p "$WORK/repo/runtime/tools" "$WORK/agda_cfg"
cp -R "$REPO"/{Backend,Code,Context,Meta,OwnershipIO,Store,Test} "$WORK/repo/"
cp "$REPO"/Code.agda "$REPO"/Ownership.agda "$REPO"/OwnershipIO.agda "$REPO"/check.sh "$WORK/repo/"
cp "$REPO"/runtime/*.hs "$REPO"/runtime/*.c "$REPO"/runtime/*.h "$WORK/repo/runtime/"
cp "$REPO"/runtime/tools/*.hs "$REPO"/runtime/tools/*.c "$WORK/repo/runtime/tools/"

echo "=== [Step 3.2] Verify --safe Target Modules (Agda + Pure Lean 4 Fast Path) ==="
(cd "$WORK/repo" && AGDA_DIR="$WORK/agda_cfg" ./check.sh Test/WorldFuzzTarget.agda)
(cd "$WORK/repo" && AGDA_DIR="$WORK/agda_cfg" ./check.sh Test/WorldReactiveTarget.agda)
(cd "$WORK/repo" && AGDA_DIR="$WORK/agda_cfg" ./check.sh OwnershipIO/WorldRunner.agda)

PRISM_BIN="$REPO/runtime/lean-prism/.lake/build/bin/agda2lean"
PRISM_LIB="$REPO/runtime/lean-prism/.lake/build/lib/lean"
PRISM_IR="$REPO/runtime/lean-prism/.lake/build/ir"
if [ ! -x "$PRISM_BIN" ]; then
  (cd "$REPO/runtime/lean-prism" && lake build liblean_cli_host AgdaMirror:static agda2lean)
else
  (cd "$REPO/runtime/lean-prism" && lake build liblean_cli_host >/dev/null)
fi

mkdir -p "$WORK/src/Gen" "$WORK/relays" "$WORK/runner_build"
sed 's/^module Test\.WorldFuzzTarget where$/module Gen.WorldFuzzTarget where/' \
  "$WORK/repo/Test/WorldFuzzTarget.agda" > "$WORK/src/Gen/WorldFuzzTarget.agda"
sed 's/^module Test\.WorldReactiveTarget where$/module Gen.WorldReactiveTarget where/' \
  "$WORK/repo/Test/WorldReactiveTarget.agda" > "$WORK/src/Gen/WorldReactiveTarget.agda"

# Verify pure Lean 4 fast-path check (zero Agda calls!)
mkdir -p "$WORK/no-agda"
cat >"$WORK/no-agda/agda" <<'SH'
#!/usr/bin/env bash
echo "FATAL: agda invoked during pure Lean 4 fast-path check!" >&2
exit 99
SH
chmod +x "$WORK/no-agda/agda"

PATH="$WORK/no-agda:$PATH" "$PRISM_BIN" prism-check \
  --lib-dir "$PRISM_LIB" \
  --work-dir "$WORK/chk_fuzz" \
  --main "$WORK/src/Gen/WorldFuzzTarget.agda"
PATH="$WORK/no-agda:$PATH" "$PRISM_BIN" prism-check \
  --lib-dir "$PRISM_LIB" \
  --work-dir "$WORK/chk_react" \
  --main "$WORK/src/Gen/WorldReactiveTarget.agda"
echo "  [PASS] Gen.WorldFuzzTarget & Gen.WorldReactiveTarget verified on pure Lean 4 fast path (0 Agda calls)."

echo "=== [Step 3.3] Build Static Native WorldRunner Binaries (runCliIO & runReactiveIO) ==="
cat >"$WORK/src/MainCli.agda" <<'AGDA'
{-# OPTIONS --guardedness #-}
module Main where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import OwnershipIO.WorldRunner using (runCliIO)
import Gen.WorldFuzzTarget as Target

main : IO ⊤
main = runCliIO Target.fuzzCliApp
AGDA

cat >"$WORK/src/MainReactive.agda" <<'AGDA'
{-# OPTIONS --guardedness #-}
module Main where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import OwnershipIO.WorldRunner using (runReactiveIO)
import Gen.WorldReactiveTarget as Target

main : IO ⊤
main = runReactiveIO Target.reactiveCounter
AGDA

mkdir -p "$WORK/cli_src" "$WORK/react_src"
cp -R "$WORK/src/Gen" "$WORK/cli_src/"
cp "$WORK/src/MainCli.agda" "$WORK/cli_src/Main.agda"
cp -R "$WORK/src/Gen" "$WORK/react_src/"
cp "$WORK/src/MainReactive.agda" "$WORK/react_src/Main.agda"

PATH="$WORK/no-agda:$PATH" "$PRISM_BIN" prism-build \
  --lib-dir "$PRISM_LIB" \
  --ir-dir "$PRISM_IR" \
  --work-dir "$WORK/build_cli" \
  --out "$WORK/fuzz_cand" \
  --dep "$WORK/cli_src/Gen/WorldFuzzTarget.agda" \
  --main "$WORK/cli_src/Main.agda"

PATH="$WORK/no-agda:$PATH" "$PRISM_BIN" prism-build \
  --lib-dir "$PRISM_LIB" \
  --ir-dir "$PRISM_IR" \
  --work-dir "$WORK/build_react" \
  --out "$WORK/react_cand" \
  --dep "$WORK/react_src/Gen/WorldReactiveTarget.agda" \
  --main "$WORK/react_src/Main.agda"

file "$WORK/fuzz_cand" | grep -q "statically linked"
file "$WORK/react_cand" | grep -q "statically linked"
echo "  [PASS] Both runCliIO & runReactiveIO static ELF binaries linked cleanly via WorldRunner."

echo "=== [Step 3.4] Build Sandbox Relays & Run Differential Conformance Fuzzing (local + Docker) ==="
cc -std=c11 -O2 -Wall -Wextra -Werror -static "$REPO/runtime/term-relay.c" -o "$WORK/relays/term-relay"
cc -std=c11 -O2 -Wall -Wextra -Werror -static "$REPO/runtime/tools/fs-relay.c" -o "$WORK/relays/fs-relay"
cc -std=c11 -O2 -Wall -Wextra -Werror -static "$REPO/runtime/tools/net-relay.c" -o "$WORK/relays/net-relay"
cc -std=c11 -O2 -Wall -Wextra -Werror -static "$REPO/runtime/tools/git-relay.c" -o "$WORK/relays/git-relay"
cc -std=c11 -O2 -Wall -Wextra -Werror -static "$REPO/runtime/tools/web-relay.c" -o "$WORK/relays/web-relay"

(cd "$WORK/repo" && agda --compile --ghc-flag=-O0 \
  "--ghc-flag=-i$WORK/repo/runtime" \
  "--ghc-flag=-i$WORK/repo/runtime/tools" \
  "--ghc-flag=$WORK/repo/runtime/cli_host.c" \
  "--compile-dir=$WORK/runner_build" \
  -i . -i /usr/share/agda-stdlib Test/WorldConformanceTest.agda) >"$WORK/compile_runner.log" 2>&1 || {
    tail -n 60 "$WORK/compile_runner.log" >&2
    exit 1
  }

DOCKER_IMG="none"
CLEANROOM_CAND="programbench/tomnomnom_1776_gron.88a6234:task_cleanroom_v6"
if command -v docker >/dev/null 2>&1 && docker image inspect "$CLEANROOM_CAND" >/dev/null 2>&1; then
  DOCKER_IMG="$CLEANROOM_CAND"
fi

"$WORK/runner_build/WorldConformanceTest" \
  "$WORK/fuzz_cand" \
  "$WORK/react_cand" \
  "$WORK/relays/term-relay" \
  "$WORK/scratch" \
  "$DOCKER_IMG"
