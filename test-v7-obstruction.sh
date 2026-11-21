#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"
repo=$PWD
mkdir -p tmp
scratch=$(mktemp -d "$repo/tmp/v7-obstruction.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export AGDA_DIR="$scratch/agda" TMPDIR="$scratch/tmp"
mkdir -p "$AGDA_DIR" "$TMPDIR" "$scratch/src"

# Keep generated interfaces and compiler output private, even in concurrent runs.
tar --exclude='*.agdai' -cf - Backend Code Context Meta OwnershipIO Store Code.agda Ownership*.agda \
  Test/{HarnessPure,HarnessLiftObstruction}.agda | tar -xf - -C "$scratch/src"
(
  cd "$scratch/src"
  agda --no-libraries --compile --ghc-flag=-O0 --ghc-flag=-threaded \
    "--ghc-flag=-i$repo/runtime" "--ghc-flag=-i$repo/runtime/tools" "--ghc-flag=$repo/runtime/cli_host.c" \
    --compile-dir="$scratch/build" -i . -i /usr/share/agda-stdlib Test/HarnessLiftObstruction.agda
) >"$scratch/compile.log" 2>&1 || { tail -60 "$scratch/compile.log" >&2; exit 1; }

cat >"$scratch/base.agda" <<'AGDA'
module Gen.T0.ParseLine where
open import Data.Bool using (Bool; true)
open import Data.Maybe using (Maybe; just; nothing)

data LineTag : Set where
  KRefDef KText : LineTag

parseLine₀ : LineTag → Maybe Bool
parseLine₀ KRefDef = nothing
parseLine₀ KText = just true
AGDA
cat >"$scratch/spec.agda" <<'AGDA'
module Gen.T1.Root where
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Gen.T0.ParseLine as Base

postulate
  mdToHtml : Maybe Bool → Bool
  emptyDoc : mdToHtml nothing ≡ false
  referenceLink : mdToHtml (Base.parseLine₀ Base.KRefDef) ≡ true
AGDA
cat >"$scratch/proof.agda" <<'AGDA'
module PandocObstruction where
open import Data.Bool using (true; false)
open import Data.Maybe using (nothing)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import Gen.T0.ParseLine as Base
import Gen.T1.Root as Spec

discarded : Base.parseLine₀ Base.KRefDef ≡ nothing
discarded = refl

false≢true : false ≡ true → ⊥
false≢true ()

absurd : ⊥
absurd = false≢true (trans (sym Spec.emptyDoc) (trans (sym (cong Spec.mdToHtml discarded)) Spec.referenceLink))
AGDA
sed 's/Gen\.T1\.Root/Gen.T1.ParseLine/g' "$scratch/spec.agda" >"$scratch/child.agda"
sed 's/Gen\.T1\.Root/Gen.T1.ParseLine/g' "$scratch/proof.agda" >"$scratch/child-proof.agda"

runner="$scratch/build/HarnessLiftObstruction"
"$runner" pure "$repo" "$scratch"
engine="$repo/runtime/lean-prism/.lake/build/bin/harness-engine"
actual=$("$engine" check-lift-refute Gen.T1.Root "$scratch/bundle.sexp")
expected=$'OK:liftObstruction\nCULPRIT_BASE_UNITS: Gen.T0.ParseLine.parseLine₀ Gen.T0.ParseLine.LineTag'
[[ "$actual" == "$expected" ]] || { echo "Unexpected native gate result: $actual" >&2; exit 1; }
echo "PASS native check-lift-refute with exact culprits"
for mode in prism legacy audit; do
  CODETRANSPORT_BACKEND="$mode" "$runner" live "$repo" "$scratch" 2>&1 | tee "$scratch/$mode.log"
  if grep -Fq SHADOW_AUDIT_VIOLATION "$scratch/$mode.log"; then exit 1; fi
done

python3 - "$repo" "$scratch" <<'PY'
import json
from pathlib import Path
import subprocess
import sys

repo, scratch = map(Path, sys.argv[1:])
build = repo / "runtime/lean-prism/.lake/build"
ctx = scratch / "mcp"
ancestors = ctx / "ancestors"
ancestors.mkdir(parents=True)
(ancestors / "ParseLine.agda").write_text((scratch / "base.agda").read_text())
spec = (scratch / "spec.agda").read_text()
proof = (scratch / "proof.agda").read_text()

def prompt(src):
    (ctx / "node-prompt.txt").write_text(f"\nSPECIFICATION\n{src}\nREFUTATION EXTRA POSTULATES\n")

def rpc(method, params):
    request = dict(jsonrpc="2.0", id=1, method=method, params=params)
    output = subprocess.check_output(
        [build / "bin/agda2lean", "mcp", "--mode", "node", "--repo", repo,
         "--lib-dir", build / "lib/lean", "--ir-dir", build / "ir",
         "--ctx-dir", ctx, "--dump-bin", repo / "dump/dump"],
        input=json.dumps(request) + "\n", text=True, timeout=120)
    return json.loads(output)["result"]

def check(src, ok, expected, **params):
    result = rpc("tools/call", dict(name="check_agda", arguments=dict(main_block=src, **params)))
    text = result["content"][0]["text"]
    if result["isError"] == ok or expected not in text or (ok and not text.startswith("OK:")):
        raise AssertionError((params, expected, text))

prompt(spec)
schema = next(t for t in rpc("tools/list", {})["tools"] if t["name"] == "check_agda")
assert schema["inputSchema"]["properties"]["refute_lift"]["type"] == "boolean"
for params in ({}, {"refute_spec": True}, {"refute_lift": True}, {"role": "refute-lift"}):
    check(proof, True, "[witness: refute-lift]", **params)
check(proof.replace("discarded = refl", "discarded = false"), False, "", refute_lift=True)
check(proof.replace("import Gen.T0", "import Algebra.Core\nimport Gen.T0"),
      False, "Expose a closed", refute_spec=True)

prompt("module Gen.T1.Root where\nopen import Data.Empty using (⊥)\npostulate impossible : ⊥\n")
pure = """module PureRefutation where
open import Data.Empty using (⊥)
import Gen.T1.Root as Spec
absurd : ⊥
absurd = Spec.impossible
"""
check(pure, True, "[witness: contradiction]", refute_spec=True)
check(pure, False, "missingBaseReference", refute_lift=True)
check(pure.replace("import Gen.T1", "import Gen.T0.ParseLine\nimport Gen.T1"), False, "missingBaseReference")
print("PASS check_agda implicit and explicit lift witnesses, compiler rejection, import boundary and contradiction")
PY
