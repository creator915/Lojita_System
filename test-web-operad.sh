#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"
build=tmp/web-build
mkdir -p "$build" tmp/web-sandboxes tmp/web-lifecycle-build

if ! command -v rg >/dev/null 2>&1; then
  for codex_path in /root/.codex/packages/standalone/releases/*/codex-path; do
    if [ -x "$codex_path/rg" ]; then
      export PATH="$codex_path:$PATH"
      break
    fi
  done
fi

tracked_clean() {
  test -z "$(git status --porcelain --untracked-files=no)"
}
tracked_clean
pure=(Context/Tools/WebOperad.agda UI/OperadApp.agda Test/Tools/WebOperadConformance.agda)
for file in "${pure[@]}"; do
  test "$(head -n 1 "$file")" = '{-# OPTIONS --safe #-}'
done
if grep -En 'postulate|TERMINATING|primTrustMe|allow-unsolved-metas|\{!' "${pure[@]}"; then
  echo 'Pure module contains a forbidden escape' >&2
  exit 1
fi
for file in "${pure[@]}" Code/Tools/WebTool.agda; do ./check.sh "$file"; done

# Every negative module must reach an actual type mismatch in its own source.
bad="$build/negative"
mkdir -p "$bad"
negative() {
  local name=$1
  {
    echo '{-# OPTIONS --safe #-}'
    echo "module $name where"
    cat <<'AGDA'
open import Context.Tools.WebOperad
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true)
open import Data.Integer.Base using (+_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
AGDA
    cat
  } >"$bad/$name.agda"
  if agda -i "$bad" -i . -i /usr/share/agda-stdlib "$bad/$name.agda" >"$bad/$name.log" 2>&1; then
    echo "Unexpectedly accepted $name" >&2
    exit 1
  fi
  grep -En "/$name.agda:[0-9]+,[0-9]+" "$bad/$name.log" >/dev/null
  grep -En '!=|≠' "$bad/$name.log" >/dev/null
  echo "PASS rejected $name"
}
negative BadArity <<'AGDA'
bad : LayoutOp [] (slotColor (size 1 1) Bool)
bad = idOp
AGDA
negative BadSlotColour <<'AGDA'
bad : LayoutOp [] (slotColor (size 1 1) ℕ)
bad = plugOp here idOp (buttonOp (size 1 1) "x" defaultColour true)
AGDA
negative BadOcclusion <<'AGDA'
r = rect (+ 0) (+ 0) 2 2
bad : hitTest (over (occludeRect defaultColour r) (hitRect 7 defaultColour r))
              (fromPixel (pt (+ 0) (+ 0))) ≡ just 7
bad = refl
AGDA

cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/web-relay.c -o "$build/web-relay"
compile=(agda --compile --ghc-flag=-O0 --ghc-flag=-iruntime --ghc-flag=-iruntime/tools
  --ghc-flag=-outputdir --ghc-flag="$build" --compile-dir="$build" -i . -i /usr/share/agda-stdlib)
"${compile[@]}" Test/Tools/WebToolIO.agda >"$build/io.log" 2>&1 || { tail -80 "$build/io.log"; exit 1; }
ghc -O0 -threaded -Wall -Werror -iruntime -iruntime/tools -outputdir tmp/web-lifecycle-build \
  Test/Tools/WebLifecycle.hs -o tmp/web-lifecycle-build/lifecycle
# Both executables always run localSandbox. Each independently probes Docker
# so direct invocation observes the same contract as this suite.
timeout 180 "$build/WebToolIO"
timeout 150 tmp/web-lifecycle-build/lifecycle
for dir in tmp/web-sandboxes tmp/web-lifecycle-sandboxes; do
  test -z "$(find "$dir" -mindepth 1 -print -quit)"
done

python3 scripts/bundle_agda_js.py >"$build/bundle.log" 2>&1 || { tail -60 "$build/bundle.log"; exit 1; }
tail -1 "$build/bundle.log"
test -s ui/dist/agda-bundle.js
if grep -En '\brequire[[:space:]]*\(' ui/dist/agda-bundle.js; then exit 1; fi
if command -v node >/dev/null 2>&1; then
  node <<'JS'
const fs = require("fs"), vm = require("vm");
const window = {};
vm.runInNewContext(fs.readFileSync("ui/dist/agda-bundle.js", "utf8"), {window});
const api = window.AgdaOperadApp;
let a = api.initWorkbench(640n)(360n);
const render = () => api.renderWorkbenchWire(a);
if (!render().startsWith("SAVE\nCLIP 0 0 640 360")) throw Error("first frame");
a = api.clickWorkbench(304n)(12n)(a);
if (!render().includes("FILL 209 222 225")) throw Error("missing dialog");
a = api.clickWorkbench(485n)(237n)(a);
a = api.panWorkbench(4n)(1n)(a);
if (!render().includes("TRANSFORM 3 2")) throw Error("zoom");
a = api.clickWorkbench(402n)(12n)(a);
a = api.tickWorkbench(500n)(a);
if (!render().includes("5665726966696564")) throw Error("timer did not fire");
a = api.resizeWorkbench(200n)(100n)(a);
if (!render().startsWith("SAVE\nCLIP 0 0 200 100")) throw Error("resize");
console.log("PASS compiled JavaScript interaction");
JS
fi

./test-evalio.sh
if docker info >/dev/null 2>&1; then
  ./test-term.sh
elif [[ ${REQUIRE_DOCKER:-0} == 1 ]]; then
  echo 'Docker required and unavailable' >&2
  exit 1
else
  # The unchanged test-term.sh requires the Docker image before it starts
  # any local test. Run its actual local suite and lifecycle in this case.
  echo 'Docker unavailable; running the terminal baseline local cases'
  baseline="$build/terminal-baseline"
  mkdir -p "$baseline" tmp/term-build tmp/term-sandboxes
  cat >"$baseline/LocalTermBaseline.agda" <<'AGDA'
{-# OPTIONS --guardedness #-}
module LocalTermBaseline where
import Test.TermIO as Baseline
import Context.Terminal as T
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import OwnershipIO.FFI using (currentDirectory; exitFailure)
open import Data.Bool using (if_then_else_)
open import Data.Unit using (⊤; tt)
main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd → F.readFile "runtime/term-fixture.py" IO.>>= λ src →
  Baseline.suite cwd src T.localSandbox IO.>>= λ ok → if ok then IO.return tt else exitFailure
AGDA
  cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o tmp/term-build/term-relay
  "${compile[@]}" -i "$baseline" "$baseline/LocalTermBaseline.agda" >"$baseline/build.log" 2>&1 || {
    tail -60 "$baseline/build.log"; exit 1;
  }
  HOST_SECRET_LEAK=1 timeout 180 "$build/LocalTermBaseline"
  ghc -O0 -Wall -Werror -iruntime -outputdir "$baseline" Test/TermTransportLifecycle.hs -o "$baseline/lifecycle"
  timeout 60 "$baseline/lifecycle"
  test -z "$(find tmp/term-sandboxes -mindepth 1 -print -quit)"
fi
tracked_clean
echo 'PASS web operad suite'
