#!/bin/bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd "$(dirname "$0")"

REPO="$(pwd)"
MCP_BIN="$REPO/runtime/lean-prism/.lake/build/bin/agda2lean"
LIB_DIR="$REPO/runtime/lean-prism/.lake/build/lib/lean"
IR_DIR="$REPO/runtime/lean-prism/.lake/build/ir"
DUMP_BIN="$REPO/dump/dump"
ENGINE_BIN="$REPO/runtime/lean-prism/.lake/build/bin/harness-engine"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ct-whitebox-XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

echo "[1/6] Testing MCP check_agda SPECIFICATION interface pre-check (∀ c → vs (c : Char) →)..."
CTX_NODE="$TMP_DIR/mcp_node"
mkdir -p "$CTX_NODE/drafts"
NARROW_LOG="$TMP_DIR/narrowing-events.jsonl"

cat >"$CTX_NODE/node-prompt.txt" <<'EOF'
# Mock Node Prompt
CURRENT CODE
module Gen.T2.Demo where

SPECIFICATION
module Gen.T2.Demo where

open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  idChar : Char → Char
  charLaw : ∀ c → idChar c ≡ c

REFUTATION EXTRA POSTULATES ({{SPEC_MOD}})
-- (no extra test postulates beyond core specification)
EOF

python3 - "$MCP_BIN" "$REPO" "$LIB_DIR" "$IR_DIR" "$DUMP_BIN" "$CTX_NODE" "$NARROW_LOG" <<'PY'
import json, subprocess, sys

mcp_bin, repo, lib_dir, ir_dir, dump_bin, ctx_dir, narrow_log = sys.argv[1:]

bad_impl = """module Gen.T2.Demo where

open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

idChar : Char → Char
idChar c = c

charLaw : (c : Char) → idChar c ≡ c
charLaw c = refl
"""

good_impl = """module Gen.T2.Demo where

open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

idChar : Char → Char
idChar c = c

charLaw : ∀ c → idChar c ≡ c
charLaw c = refl
"""

reqs = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {
        "name": "write_draft", "arguments": {"name": "main", "content": bad_impl}}},
    {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {
        "name": "check_agda", "arguments": {"main_block": "main"}}},
    {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {
        "name": "patch_draft", "arguments": {
            "name": "main",
            "old_text": "charLaw : (c : Char) → idChar c ≡ c",
            "new_text": "charLaw : ∀ c → idChar c ≡ c"}}},
    {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {
        "name": "check_agda", "arguments": {"main_block": "main"}}},
]

inp = "".join(json.dumps(r) + "\n" for r in reqs)
proc = subprocess.run(
    [mcp_bin, "mcp", "--mode", "node", "--repo", repo, "--lib-dir", lib_dir,
     "--ir-dir", ir_dir, "--dump-bin", dump_bin, "--ctx-dir", ctx_dir,
     "--narrow-log", narrow_log],
    input=inp, text=True, capture_output=True, check=True
)
resps = {json.loads(line)["id"]: json.loads(line)["result"]
         for line in proc.stdout.strip().splitlines() if line.strip()}

r3 = resps[3]
txt3 = r3["content"][0]["text"]
assert r3["isError"] is True, f"Expected interface error on (c : Char), got: {r3}"
assert "SPECIFICATION_INTERFACE_MISMATCH" in txt3, f"Missing mismatch header: {txt3}"
assert "expected (SPECIFICATION):" in txt3 and "actual   (your module):" in txt3, f"Missing expected/actual witness: {txt3}"

r5 = resps[5]
txt5 = r5["content"][0]["text"]
assert r5["isError"] is False, f"Expected OK after patch_draft, got: {txt5}"
assert "OK: 'Gen.T2.Demo'" in txt5 and "[Lens:" in txt5, f"Missing OK / Lens summary: {txt5}"
print("  PASS: check_agda caught (c : Char) vs ∀ c → before submission and passed after 1-line patch_draft!")
PY

echo "[2/6] Testing operator section (x ∷_) vs (λ section → x ∷ section) AST isomorphism..."
cat >"$TMP_DIR/SecSpec.agda" <<'EOF'
module Gen.T2.Sec where

open import Data.List using (List; _∷_; map)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

prependAll : ℕ → List (List ℕ) → List (List ℕ)
prependAll x xss = map (x ∷_) xss

postulate
  f : ℕ → ℕ
EOF

cat >"$TMP_DIR/SecCand.agda" <<'EOF'
module Gen.T2.Sec where

open import Data.List using (List; _∷_; map)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

prependAll : ℕ → List (List ℕ) → List (List ℕ)
prependAll x xss = map (λ section → x ∷ section) xss

f : ℕ → ℕ
f n = n
EOF

"$MCP_BIN" prism-dump --work-dir "$TMP_DIR/parse" --main "$TMP_DIR/SecSpec.agda" >"$TMP_DIR/sec_spec.sexp"
"$MCP_BIN" prism-dump --work-dir "$TMP_DIR/parse" --main "$TMP_DIR/SecCand.agda" >"$TMP_DIR/sec_cand.sexp"
IFACE_OUT="$("$ENGINE_BIN" check-interface "$TMP_DIR/sec_spec.sexp" "$TMP_DIR/sec_cand.sexp")"
[[ "$IFACE_OUT" == "OK" ]] || { echo "Expected OK on operator section interface, got: $IFACE_OUT"; exit 1; }
echo "  PASS: (x ∷_) and (λ section → x ∷ section) produce identical canonical ASTs!"

echo "[3/6] Testing single-quote ''' roundtrip + inspectSourceDiag white-box line witness..."
cat >"$TMP_DIR/QuoteMod.agda" <<'EOF'
module Gen.T2.QuoteMod where

open import Data.Char using (Char)

sq : Char
sq = '\''
EOF
"$MCP_BIN" prism-dump --work-dir "$TMP_DIR/parse" --main "$TMP_DIR/QuoteMod.agda" >"$TMP_DIR/quote.sexp"
RT_AGDA="$("$ENGINE_BIN" roundtrip "$TMP_DIR/quote.sexp")"
echo "$RT_AGDA" | grep -q "'\\\\''" || { echo "Expected escaped '\\'' in roundtrip output, got: $RT_AGDA"; exit 1; }
echo "  PASS: Code/Render.agda renders single-quote char literal as valid '\\''!"

echo "[4/6] Testing side-channel narrowing-events.jsonl telemetry on SlowSlice / fallback..."
python3 - "$MCP_BIN" "$REPO" "$LIB_DIR" "$IR_DIR" "$DUMP_BIN" "$CTX_NODE" "$NARROW_LOG" <<'PY'
import json, os, subprocess, sys

mcp_bin, repo, lib_dir, ir_dir, dump_bin, ctx_dir, narrow_log = sys.argv[1:]

slow_mod = """module Gen.T2.SlowDemo where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Structural descent alternates between the two arguments.
f : ℕ → ℕ → ℕ
f zero n = suc n
f (suc m) zero = f m (suc zero)
f (suc m) (suc n) = f m (f (suc m) n)
"""

reqs = [
    {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
    {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {
        "name": "check_agda", "arguments": {"main_block": slow_mod}}},
]
inp = "".join(json.dumps(r) + "\n" for r in reqs)
proc = subprocess.run(
    [mcp_bin, "mcp", "--mode", "node", "--repo", repo, "--lib-dir", lib_dir,
     "--ir-dir", ir_dir, "--dump-bin", dump_bin, "--ctx-dir", ctx_dir,
     "--narrow-log", narrow_log],
    input=inp, text=True, capture_output=True, check=True
)
resps = {json.loads(line)["id"]: json.loads(line)["result"]
         for line in proc.stdout.strip().splitlines() if line.strip()}
txt = resps[2]["content"][0]["text"]
assert resps[2]["isError"] is False, f"Expected SlowDemo to pass: {txt}"
assert "SlowSlice units in Agda (f)" in txt, f"Expected SlowSlice attribution in output: {txt}"
assert os.path.exists(narrow_log), "Expected narrowing-events.jsonl to be created"
with open(narrow_log, "r", encoding="utf-8") as fh:
    events = [json.loads(l) for l in fh if l.strip()]
assert any(e["kind"] == "prism_slow_slice" and e["module"] == "Gen.T2.SlowDemo" for e in events), f"Missing slow_slice event: {events}"
print("  PASS: SlowSlice attribution + narrowing-events.jsonl telemetry verified!")
PY

echo "[5/6] Checking resident scope-only imports, diagnostics, and request isolation..."
python3 scripts/test_dump_daemon.py "$DUMP_BIN" "$TMP_DIR/daemon"

echo "[6/6] Testing read-only MCP check_plan, native plan gates, and structured certificates..."
python3 - "$MCP_BIN" "$REPO" "$LIB_DIR" "$IR_DIR" "$DUMP_BIN" "$TMP_DIR" "$NARROW_LOG" <<'PYTEST'
import json
import subprocess
import sys
from pathlib import Path

mcp, repo, lib, ir, dump, tmp, ledger = sys.argv[1:]
tmp = Path(tmp)
ctx = tmp / "plan-node"
ctx.mkdir()
(ctx / "drafts").mkdir()
module = "Gen.T2.Preview"
header = f"""module {module} where

data Tag : Set where
  t : Tag

"""
old = header + "u : Tag\nu = t\n\nv : Tag\nv = u\n\nretained : Tag\nretained = t\n"
candidate = header + "u : Tag → Tag\nu x = x\n\nv : Tag\nv = u t\n"
spec = header + "postulate v : Tag\n"

def dump_source(stem, src):
    path = tmp / f"{stem}.agda"
    path.write_text(src)
    return subprocess.check_output([mcp, "prism-dump", "--dump-bin", dump, "--lib-dir", lib,
                                    "--work-dir", str(tmp / "surface"), "--main", str(path)], text=True).strip()

old_code = dump_source("old", old)
spec_code = dump_source("spec", spec)
(ctx / "plan-context.sexp").write_text(
    f"(plan-context {old_code} {spec_code} (seeds) (flags) (ancestors none) (bases) (lift) (bindings) (siblings))")
(ctx / "node-prompt.txt").write_text(
    f"CURRENT CODE\n{old}\nSPECIFICATION\n{spec}\nREFUTATION EXTRA POSTULATES\n")
(ctx / "drafts/candidate.block").write_text(candidate)

def move(x):
    return f'(move (unit "{module}.{x}") (unit "{module}.{x}"))'

full = f"(moves {move('u')} {move('v')})"
partial = f"(moves {move('u')})"
envelope = f'(submission (kind plan) (why "change u") (main @candidate) {full})'
deep = module + ".Child.Grandchild.Overflow"
lawmod = module + ".Child"
law = f"""module {lawmod} where
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
postulate same : (x : String) → primStringEquality x x ≡ true
"""
unsafe = candidate.replace("data Tag", "open import Agda.Builtin.TrustMe\n\ndata Tag")
bad_sig = candidate.replace("v : Tag\nv = u t", "v : Tag → Tag\nv = u")
requests = [("tools/list", {})]

def call(tool, **args):
    requests.append(("tools/call", {"name": tool, "arguments": args}))

call("check_plan", submission=envelope)
call("check_plan", main="@candidate", moves=partial)
call("check_plan", main="@candidate", moves=full, subspecs={deep: f"module {deep} where\npostulate X : Set\n"})
call("check_plan", main=unsafe, moves=full)
call("check_plan", main=bad_sig, moves=full)
call("check_plan", main="@candidate", moves=full, subspecs={lawmod: law})
call("check_agda", main_block=unsafe)
call("check_agda", main_block=law, allow_postulates=True)
call("check_plan", main="@candidate", moves="(moves (move bot))")
call("run_agda_script", script_block="hidden session tool")
call("check_plan", main="@candidate", moves=full, lift='(lift "Other" "Gen.T2.Preview" () ())')

lawhead = law.split("postulate same")[0]
closed_true = lawhead + """postulate lit : primStringEquality "" "" ≡ true
"""
tautology = lawhead + "postulate taut : (x : String) → primStringEquality x x ≡ primStringEquality x x\n"
unrelated = lawhead.replace("using (_≡_)", "using (_≡_; refl)") + """ok : (x : String) → primStringEquality x x ≡ primStringEquality x x
ok x = refl
bad : String
bad = true
"""
roundtrip = lawhead.replace("primStringEquality)", "primStringFromList; primStringToList)") + """
postulate round : (s : String) → primStringFromList (primStringToList s) ≡ s
"""
for src in (closed_true, tautology):
    call("check_agda", main_block=src, allow_postulates=True)
call("check_agda", main_block=unrelated)
call("check_agda", main_block=roundtrip, allow_postulates=True)
exo_error = """module PreviewResidual where
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (true)
f : Nat → Nat → Nat
f zero n = true
f (suc m) zero = f m (suc zero)
f (suc m) (suc n) = f m (f (suc m) n)
"""
call("check_agda", main_block=exo_error)
no_k = "{-# OPTIONS --without-K #-}\n" + candidate
call("check_agda", main_block=no_k)
call("check_plan", main=no_k, moves=full)
hybrid = candidate.replace("data Tag", "open import Agda.Builtin.Nat using (Nat; zero; suc)\n\ndata Tag") + """
f : Nat → Nat → Nat
f zero n = suc n
f (suc m) zero = f m (suc zero)
f (suc m) (suc n) = f m (f (suc m) n)
"""
call("check_plan", main=hybrid, moves=full[:-1] + f' (move bot (unit "{module}.f")))')
call("check_plan", main=candidate.split("v : Tag")[0],
     moves=f'(moves {move("u")} (move (unit "{module}.v") bot))')
call("check_plan", main=unsafe.replace("Agda.Builtin.TrustMe", "Data.String.Unsafe"), moves=full)

def snapshot():
    return {p.relative_to(ctx): p.read_bytes() if p.is_file() else None for p in ctx.rglob("*")}

before = snapshot()
wire = "".join(json.dumps(dict(jsonrpc="2.0", id=i, method=method, params=params)) + "\n"
               for i, (method, params) in enumerate(requests))
cmd = [mcp, "mcp", "--mode", "node", "--repo", repo, "--lib-dir", lib, "--ir-dir", ir,
       "--dump-bin", dump, "--ctx-dir", str(ctx), "--narrow-log", ledger]
out = subprocess.run(cmd, input=wire, text=True, capture_output=True, check=True, timeout=60)
results = {r["id"]: r["result"] for r in map(json.loads, out.stdout.splitlines())}
assert before == snapshot(), "check_plan mutated node context or drafts"
tools = {t["name"]: t for t in results[0]["tools"]}
assert tools["check_plan"]["annotations"]["readOnlyHint"] and "run_agda_script" not in tools
session_cmd = list(cmd)
session_cmd[session_cmd.index("--mode") + 1] = "session"
session_wire = "\n".join(json.dumps(dict(jsonrpc="2.0", id=i, method=m, params=p)) for i, (m, p) in enumerate(requests[:2]))
session_out = subprocess.run(session_cmd, input=session_wire + "\n", text=True, capture_output=True, check=True, timeout=30)
session_list, session_call = [json.loads(line)["result"] for line in session_out.stdout.splitlines()]
assert "check_plan" not in {tool["name"] for tool in session_list["tools"]}
assert session_call["isError"] and "unknown tool" in session_call["content"][0]["text"], session_call
assert before == snapshot()
valid = results[1]
assert not valid["isError"], valid
preview = valid["structuredContent"]
assert preview["ok"] and preview["frontier"] == [] and preview["satisfiesDetails"] == [], preview
split = preview["pushoutSplitPlan"]
assert module + ".u" in split["SweetMod"] and split["ExoMod"] == [], split
assert module + ".Tag" in split["M0"]["units"] and module + ".retained" in split["SweetMod"], split

def cert_at(i, kind, witness):
    result = results[i]
    assert result["isError"], result
    cert = next((c for c in result["structuredContent"]["certificates"]
                 if c["kind"] == kind and witness in c["witness"]), None)
    assert cert and all(cert[k] for k in ("kind", "witness", "cause", "detour")), result
    text = result["content"][0]["text"]
    assert all(f"[{key.upper()}] {cert[key]}" in text for key in cert), text
    return cert

front = cert_at(2, "frontier_incomplete", module + ".v")
assert module + ".u" in front["cause"] and "move" in front["detour"], front
assert any(module + ".v" in o for o in results[2]["structuredContent"]["frontier"])
cert_at(3, "subspec_narrowing", deep)
unsafe_cert = cert_at(4, "unsafe_module", "Agda.Builtin.TrustMe")
cert_at(5, "subspec_narrowing", module + ".v")
assert any("expected (SPECIFICATION):" in s for s in results[5]["structuredContent"]["satisfiesDetails"])
cert_at(6, "subspec_laundering", lawmod + ".same")
assert cert_at(7, "unsafe_module", "Agda.Builtin.TrustMe") == unsafe_cert
cert_at(8, "primitive_taboo", "Agda.Builtin.String.primStringEquality")
assert results[9]["isError"] and results[10]["isError"], results
assert results[11]["isError"] and "checkLift" in results[11]["content"][0]["text"], results[11]
for i in [12, 13, 14]:
    assert all(c["kind"] != "primitive_taboo" for c in results[i]["structuredContent"]["certificates"]), results[i]
cert_at(15, "primitive_taboo", "Agda.Builtin.String.primStringFromList")
exo = cert_at(16, "exo_residual_error", "PreviewResidual.f")
assert "true" in exo["cause"] and "agda_slice_" not in exo["cause"], exo
for i in [17, 18]:
    cert = cert_at(i, "exo_residual_error", module)
    assert "--without-K" in cert["cause"] and "Agda" in cert["detour"], cert
assert results[18]["structuredContent"]["pushoutSplitPlan"] is None
assert not results[19]["isError"], results[19]
hybrid_plan = results[19]["structuredContent"]["pushoutSplitPlan"]
assert hybrid_plan["hasResidual"] and hybrid_plan["ExoMod"] == [module + ".f"], hybrid_plan
assert module + ".retained" in hybrid_plan["SweetMod"] and module + ".Tag" in hybrid_plan["M0"]["units"], hybrid_plan
assert module + ".f" in hybrid_plan["M0"]["leanAssumes"], hybrid_plan
cert_at(20, "subspec_narrowing", module + ".v")
assert any("missing core unit " + module + ".v" in d for d in results[20]["structuredContent"]["satisfiesDetails"])
cert_at(21, "unsafe_module", "Data.String.Unsafe")
rows = [json.loads(l) for l in Path(ledger).read_text().splitlines() if l]
assert any(all(e.get(k) == v for k, v in front.items()) for e in rows), rows
print("  PASS: authoritative plan, frontier, interface, lift, subspec and import gates; structured JSONL certificates")
PYTEST

echo "ALL WHITE-BOX FAIL-CLOSED GATES PASSED!"
