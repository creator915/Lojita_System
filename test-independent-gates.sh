#!/usr/bin/env bash
set -euo pipefail
export LANG=C.UTF-8 LC_ALL=C.UTF-8
cd -- "$(dirname -- "$0")"
fixture=$(mktemp -d "${TMPDIR:-/tmp}/test-independent.XXXXXXXX")
trap 'rm -rf -- "$fixture"' EXIT
if ! agda --compile --ghc-flag=-O0 --ghc-flag=-iruntime --ghc-flag=-iruntime/tools \
    "--ghc-flag=$PWD/runtime/cli_host.c" --compile-dir=tmp/tool-build \
    -i . -i /usr/share/agda-stdlib Test/IndependentSession.agda >"$fixture/compile.log" 2>&1; then
  tail -100 "$fixture/compile.log" >&2
  exit 1
fi
python3 -u - "$PWD" "$fixture" <<'PY'
import json
import os
from pathlib import Path
import select
import subprocess
import sys
import time

repo, tmp = map(Path, sys.argv[1:])
build = repo / "runtime/lean-prism/.lake/build"
prism, lib = build / "bin/agda2lean", build / "lib/lean"
engine = build / "bin/harness-engine"
ctx = tmp / "mcp"
(ctx / "drafts").mkdir(parents=True)
inner_log = tmp / "narrowing-events.jsonl"
primitive_import = "open import Agda.Builtin.String using (primStringEquality)"
safe_import = "open import Context.Tools.FsSandbox using (eqStr)"
module = "Gen.T2.JsonInput"
spec = f"""module {module} where
{primitive_import}
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

data Json : Set where
  jsonNull : Json

postulate
  matchingValues : String → List (String × Json) → List Json
  noMatchingValues : (k : String) → matchingValues k [] ≡ []
  nextMatchingValue : (k : String) (v : Json) (fields : List (String × Json)) → matchingValues k ((k , v) ∷ fields) ≡ v ∷ matchingValues k fields
  otherMatchingValue : (k l : String) (v : Json) (fields : List (String × Json)) → primStringEquality k l ≡ false → matchingValues k ((l , v) ∷ fields) ≡ matchingValues k fields
"""
safe_spec = spec.replace(primitive_import, safe_import).replace("primStringEquality", "eqStr")
witness_header = f"""module UnprovableRefute where
open import Context.Taboo using (SafeTaboo; taboo-primStrRefl)
import {module} as Spec
"""
miss_equation = ("trans (sym (cong present (Spec.nextMatchingValue k Spec.jsonNull []))) "
                 "(trans (cong present (Spec.otherMatchingValue k k Spec.jsonNull [] p)) "
                 "(cong present (Spec.noMatchingValues k)))")
witness = witness_header + f"""{primitive_import}
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

present : List Spec.Json → Bool
present [] = false
present (_ ∷ _) = true

impossibleMiss : (k : String) → primStringEquality k k ≡ false → true ≡ false
impossibleMiss k p = {miss_equation}

mustMatch : (b : Bool) → (b ≡ false → true ≡ false) → b ≡ true
mustMatch true h = refl
mustMatch false h = sym (h refl)

witness : SafeTaboo
witness = taboo-primStrRefl (λ k → mustMatch (primStringEquality k k) (impossibleMiss k))
"""
laws = [line.strip() for line in safe_spec.split("postulate\n")[1].splitlines()]
impl = safe_spec.split("postulate\n")[0].replace("using (true; false)", "using (true; false; if_then_else_)").replace("using (_≡_)", "using (_≡_; refl; cong)")
impl = impl.replace("data Json", """open import Context.Tools.FsLaws using (eqStr-refl)

data Json""")
impl += f"""{laws[0]}
matchingValues k [] = []
matchingValues k ((l , v) ∷ fields) = if eqStr k l then v ∷ matchingValues k fields else matchingValues k fields

{laws[1]}
noMatchingValues k = refl

{laws[2]}
nextMatchingValue k v fields = cong (λ b → if b then v ∷ matchingValues k fields else matchingValues k fields) (eqStr-refl k)

{laws[3]}
otherMatchingValue k l v fields h = cong (λ b → if b then v ∷ matchingValues k fields else matchingValues k fields) h
"""


def check(cond, detail):
    if not cond:
        raise AssertionError(detail)


def command(args, timeout=180, **kwargs):
    p = subprocess.run(args, capture_output=True, text=True, timeout=timeout, **kwargs)
    check(p.returncode == 0, f"{args[0]} exited {p.returncode}\n{p.stdout[-7000:]}\n{p.stderr[-7000:]}")
    return p.stdout


def mcp_args(mode):
    return [prism, "mcp", "--mode", mode, "--repo", repo, "--lib-dir", lib,
            "--ir-dir", build / "ir", "--dump-bin", repo / "dump/dump",
            "--ctx-dir", ctx, "--workspace", tmp, "--narrow-log", inner_log]


def rpc(proc, request):
    proc.stdin.write(json.dumps(request) + "\n")
    proc.stdin.flush()
    check(select.select([proc.stdout], [], [], 30)[0], "MCP response timed out")
    return json.loads(proc.stdout.readline())["result"]


def check_mcp(name, args, *, error=False, matches=(), proc=None):
    request = dict(jsonrpc="2.0", id=1, method="tools/call", params=dict(name=name, arguments=args))
    if proc is None:
        mode = "node" if name == "check_agda" else "session"
        out = command(mcp_args(mode), input=json.dumps(request) + "\n")
        res = json.loads(out)["result"]
    else:
        res = rpc(proc, request)
    msg = res["content"][0]["text"]
    check(res["isError"] == error and all(s in msg for s in matches), (name, matches, msg))
    return msg


def prompt(src):
    (ctx / "node-prompt.txt").write_text(
        f"CURRENT CODE\nmodule {module} where\n\nSPECIFICATION\n{src}\n"
        "REFUTATION EXTRA POSTULATES ({{SPEC_MOD}})\n"
        "-- (no extra test postulates beyond core specification)\nLOCKED SEEDS\n")


def independent(src, why=None, field="refute"):
    reason = "" if why is None else f" (why {json.dumps(why)})"
    return f"(submission (kind independent){reason} ({field} @proof))\n```agda proof\n{src}\n```\n"


def plan(src, sub=None):
    extra = "" if sub is None else f' (subspecs ("{sub.split()[1]}" @sub))'
    wire = f'(submission (kind plan) (why "implement matching values") (main @main){extra} (moves))\n```agda main\n{src}\n```\n'
    return wire if sub is None else wire + f"```agda sub\n{sub}\n```\n"


def session(label, src, proposals):
    ws = tmp / label
    ws.mkdir()
    source = ws / "spec.agda"
    source.write_text(src)
    files = [ws / f"proposal-{i}" for i in range(len(proposals))]
    for path, wire in zip(files, proposals):
        path.write_text(wire)
    env = dict(os.environ, CODETRANSPORT_BACKEND="prism")
    msg = command([repo / "tmp/tool-build/IndependentSession", repo, ws, "T2", source, *files],
                  env=env, timeout=180 + 20 * len(files))
    prompts = [Path(str(f) + ".prompt").read_text().rsplit("\nTRANSIENT DIAGNOSTIC\n", 1)[-1] for f in files]
    return msg, prompts[1:], ws


def events(path):
    return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []


prompt(spec)
(ctx / "drafts/unprovable.block").write_text(witness)
with subprocess.Popen(mcp_args("node"), stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True) as server:
    try:
        rpc(server, dict(jsonrpc="2.0", id=0, method="initialize", params={}))
        start = time.monotonic()
        check_mcp("check_agda", {"main_block": "unprovable"}, proc=server, matches=("FastFocus", "0 SlowSlice"))
        elapsed = time.monotonic() - start
        edited = witness.replace("mustMatch false h = sym (h refl)", "mustMatch false h = trans (sym (h refl)) refl")
        check_mcp("check_agda", {"main_block": edited}, proc=server, matches=("FastFocus", "0 SlowSlice"))
        check_mcp("check_agda", {"main_block": edited.replace("(impossibleMiss k)", "(λ h → refl)")},
                  proc=server, error=True)
        prompt(spec.replace("matchingValues k [] ≡ []", "matchingValues k [] ≡ matchingValues k []"))
        check_mcp("check_agda", {"main_block": edited}, proc=server, error=True)
        prompt(spec)
    finally:
        server.stdin.close()
check(elapsed < 1, f"FastFocus witness took {elapsed:.3f}s")
check(not any(e["kind"] == "prism_bot_fallback" for e in events(inner_log)), events(inner_log))
msg, _, ws = session("opaque", spec, [independent(witness, "open-key reflexivity")])
check(all(s in msg for s in ("independent T2", "open-key reflexivity", "SafeTaboo", "eqStr", "UnprovableRefute")), msg)
check((ws / "trees/T2/verdict").read_text().strip() == "independent", msg)
check(not (ws / "generated/T2").exists(), "independence published an implementation")
print(f"PASS gron witness in {elapsed:.3f}s and scripted independent verdict")

# A terminal witness is checked on its authored source. A postulate admitted
# by an unrelated ancestor may typecheck in the Lean bundle but lies outside
# the native --safe assumption telescope.
dual = tmp / "dual"
dual.mkdir()
base, logical, authored, proof = [dual / f"{name}.agda" for name in ("Base", "Law", "Raw", "Proof")]
base.write_text("module Ancestor where\nopen import Data.Bool using (Bool)\nflag : Bool\nflag = Bool.true\n")
short_spec = """module SpecStub where
import Ancestor
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)
postulate sameKey : (k : String) → primStringEquality k k ≡ true
"""
logical.write_text(short_spec)
authored.write_text(short_spec)
proof.write_text("""module Evidence where
open import Context.Taboo using (SafeTaboo; taboo-primStrRefl)
import SpecStub as Spec
witness : SafeTaboo
witness = taboo-primStrRefl Spec.sameKey
""")
scratch = dual / "check"
scratch.mkdir()
request = [repo / "tmp/tool-build/IndependentSession", "check-independent", repo, scratch,
           base, logical, authored, proof]
check("INDEPENDENT_CONFIRMED" in command(request), "short witness failed")
authored.write_text("")
missing = subprocess.run(request, capture_output=True, text=True, timeout=90)
check(missing.returncode != 0 and "missing authored SPECIFICATION" in missing.stderr + missing.stdout,
      "independence accepted a missing authored specification")
authored.write_text(short_spec.replace("primStringEquality k k ≡ true", "true ≡ true"))
stale = subprocess.run(request, capture_output=True, text=True, timeout=90)
check(stale.returncode != 0 and "authored SPECIFICATION and staged postulate stub disagree" in stale.stderr,
      stale.stderr)
authored.write_text(short_spec)
base.write_text("module Ancestor where\nopen import Data.Bool using (Bool)\npostulate external : Bool\n")
unconfirmed = subprocess.run(request, capture_output=True, text=True, timeout=90)
check(unconfirmed.returncode != 0 and "INDEPENDENCE_AGDA_ERROR" in unconfirmed.stderr and
      "Cannot postulate external with safe flag" in unconfirmed.stderr, unconfirmed.stderr)
print("PASS dual-kernel short witness, stale raw specification, mandatory native --safe confirmation")

# The archived root appended a singleton to the tail's matches. On empty
# fields the two equations still force primitive reflexivity on an open key.
append_spec = spec.replace("List; []; _∷_", "List; []; _∷_; _++_").replace(
    "≡ v ∷ matchingValues k fields", "≡ matchingValues k fields ++ (v ∷ [])")
append_witness = witness.replace("List; []; _∷_", "List; []; _∷_; _++_").replace(
    "impossibleMiss :", "presentAppended : List Spec.Json → Bool\npresentAppended xs = present (xs ++ (Spec.jsonNull ∷ []))\n\nimpossibleMiss :")
append_witness = append_witness.replace(miss_equation,
    f"trans (sym (cong presentAppended (Spec.noMatchingValues k))) ({miss_equation})")
prompt(append_spec)
check_mcp("check_agda", {"main_block": append_witness}, matches=("FastFocus", "0 SlowSlice"))
msg, _, _ = session("archived-order", append_spec, [independent(append_witness, field="witness")])
check("independent T2\n" in msg, msg)
print("PASS archived append-order laws and witness field with omitted reason")

prompt(safe_spec)
bad = [
    ("missing witness", witness_header + "open import Data.Bool using (Bool; true)\nb : Bool\nb = true\n"),
    ("invalid proof", witness_header + "open import Relation.Binary.PropositionalEquality using (refl)\nwitness : SafeTaboo\nwitness = taboo-primStrRefl (λ k → refl)\n"),
    ("postulate", witness_header + "postulate witness : SafeTaboo\n"),
    ("shadowed goal", f"""module Context where
import {module} as Spec
module Taboo where
  data SafeTaboo : Set where
    fake : SafeTaboo
witness : Taboo.SafeTaboo
witness = Taboo.fake
"""),
]
unsafe_mods = ["Agda.Builtin.TrustMe", "Data.String.Unsafe"]
for unsafe in unsafe_mods:
    bad.append((unsafe, witness_header + f"open import {unsafe}\npostulate witness : SafeTaboo\n"))
for _, draft in bad:
    check_mcp("check_agda", {"main_block": draft}, error=True)
check_mcp("check_agda", {"main_block": impl})

unsafe_plans = []
for name in unsafe_mods:
    dirty = impl.replace(safe_import, f"open import {name}\n" + safe_import)
    for tool, field in (("check_agda", "main_block"), ("check_spec", "spec_block")):
        check_mcp(tool, {field: dirty}, error=True, matches=("TrustMe", "Unsafe", "independent"))
    check_mcp("check_entry", {"entry": module + ".app", "dep_blocks": [dirty]},
              error=True, matches=("TrustMe", "Unsafe", "independent"))
    unsafe_plans.append(plan(dirty))
# Ordinary identifiers can contain these substrings. Only a complete path
# component is reserved.
harmless = """module Gen.T2.UnsafeLooking where
open import Data.Bool using (Bool; true)
almostTrustMe : Bool
almostTrustMe = true
"""
check_mcp("check_agda", {"main_block": harmless})
print("PASS unsafe imports blocked at the three MCP entry points and harmless names accepted")

launder = """module Gen.T2.JsonInput.Comparison.Primitive where
open import Agda.Builtin.Char using (Char; primCharEquality)
import Data.Char.Properties as Char
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  charAgreement : (c d : Char) → primCharEquality c d ≡ does (c Char.≟ d)
"""
deep = """module Gen.T2.Root.C1.C2.C3 where
open import Data.Bool using (Bool)
postulate flag : Bool
"""
gates = [(launder, "subspec_axiom_laundering", "axiom-laundering"), (deep, "subspec_depth_cap", "Gen.<Epoch>.<Root>.<Child>.<Grandchild>")]
for draft, _, hint in gates:
    check_mcp("check_agda", {"main_block": draft, "allow_postulates": True},
              error=True, matches=(hint, "independent"))
proposals = [independent(s, field="witness") for _, s in bad] + unsafe_plans
proposals += [plan(impl, draft) for draft, _, _ in gates] + [plan(impl)]
msg, retries, ws = session("reflective", safe_spec, proposals)
check("ok T2" in msg and (ws / "trees/T2/verdict").read_text().strip() == "ok", msg)
for i, ((label, _), diagnostic) in enumerate(zip(bad, (
        "missingTabooProof", "LEAN_TYPE_ERROR", "unimplementedPostulate",
        "unauthorizedImport", *unsafe_mods), strict=True)):
    check(diagnostic in retries[i], (label, retries[i]))
for i, name in enumerate(unsafe_mods):
    check(any(s in retries[len(bad) + i].lower() for s in ("unsafe", "forbidden", "trustme")), retries[len(bad) + i])
for i, (draft, kind, hint) in enumerate(gates):
    check(hint in retries[-len(gates) + i], retries[-len(gates) + i])
    for path in (inner_log, ws / "narrowing-events.jsonl"):
        check(any(e["kind"] == kind and e["module"] == draft.split()[1] for e in events(path)), (path, events(path)))
print("PASS provable plan, rejected independence attempts, outer unsafe gate, narrowing diagnostics and inner/outer telemetry")

mirror = tmp / "MirrorProbe.agda"
mirror.write_text("""module MirrorProbe where
open import Context.Taboo using (SafeTaboo; taboo-primStrRefl)
open import Agda.Builtin.String.Properties using (primStringToListInjective; primStringFromListInjective)
open import Data.String.Properties using (toList-injective)
open import Data.String.Base using (String; toList; fromList)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List)
open import Data.Bool.Base using (true)
open import Relation.Nullary using (Dec; yes)
open import Relation.Nullary.Decidable using (isYes; map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

inj : (s t : String) → toList s ≡ toList t → s ≡ t
inj = primStringToListInjective

viaAlias : (s t : String) → toList s ≡ toList t → s ≡ t
viaAlias = toList-injective

chars : (xs ys : List Char) → fromList xs ≡ fromList ys → xs ≡ ys
chars = primStringFromListInjective

decision : isYes (map′ (λ (x : true ≡ true) → x) (λ x → x) (yes refl)) ≡ true
decision = refl
""")
command(["agda", "-i", tmp, "-i", repo, "-i", "/usr/share/agda-stdlib", mirror], cwd=tmp)
command([prism, "prism-check", "--lib-dir", lib, "--work-dir", tmp / "mirror-check", "--main", mirror])
print("PASS Lean mirror canonical names and decision computation")

# Check constructor types against the Agda declarations themselves, including
# the dependent pair in the WLPO and Markov witnesses.
taboo_source = (repo / "Context/Taboo.agda").read_text()
imports, constructors = taboo_source.split("module Context.Taboo where\n")[1].split("data SafeTaboo : Set where\n")
consumer = "module TabooConstructors where\nopen import Context.Taboo\n" + imports
for i, decl in enumerate(constructors.strip().splitlines()):
    name, signature = decl.strip().split(" : ", 1)
    consumer += f"\nwrap{i} : {signature}\nwrap{i} = {name.strip()}\n"
all_ctors = tmp / "TabooConstructors.agda"
all_ctors.write_text(consumer)
command(["agda", "-i", tmp, "-i", repo, "-i", "/usr/share/agda-stdlib", all_ctors], cwd=tmp)
command([prism, "prism-check", "--lib-dir", lib, "--work-dir", tmp / "constructor-check", "--main", all_ctors])
print("PASS all SafeTaboo constructor signatures in both kernels")

# The kernel may use only postulates from the staged specification. Check the
# rejection transitively and independently of how particular Agda terms emit.
audit = tmp / "WitnessAudit.lean"
audit.write_text("""import AgdaMirror.Context
import AgdaMirror.AxiomGuard
open AgdaMirror.Context
axiom specLaw : (True = True) → SafeTaboo
noncomputable def clean : SafeTaboo := specLaw rfl
#agda_prism_guard_witness clean assuming [specLaw]
""")
lean_env = dict(os.environ, LEAN_PATH=str(lib))
command(["lean", audit], cwd=tmp, env=lean_env)
with audit.open("a") as f:
    f.write("""axiom otherLaw : SafeTaboo
noncomputable def wrongStub : SafeTaboo := otherLaw
noncomputable def ext : SafeTaboo := specLaw (propext Iff.rfl)
noncomputable def choice : SafeTaboo := Classical.choice (show Nonempty SafeTaboo from ⟨clean⟩)
theorem quotient (r : Nat → Nat → Prop) (h : r 0 0) : Quot.mk r 0 = Quot.mk r 0 := Quot.sound h
theorem unfinished : True := by sorry
#agda_prism_guard_witness wrongStub assuming [specLaw]
#agda_prism_guard_witness ext assuming [specLaw]
#agda_prism_guard_witness choice assuming [specLaw]
#agda_prism_guard_witness quotient assuming []
#agda_prism_guard_witness unfinished assuming []
""")
rejected = subprocess.run(["lean", audit], cwd=tmp, env=lean_env, capture_output=True, text=True, timeout=30)
errors = rejected.stdout + rejected.stderr
check(rejected.returncode != 0 and errors.count("INDEPENDENCE_AXIOM_ERROR") == 5, errors)
check(all(name in errors for name in ("otherLaw", "propext", "Classical.choice", "Quot.sound", "sorryAx")), errors)
print("PASS witness audit rejects all four dirty axioms and unrelated assumptions")
# A traversal can revisit the inductive before reaching its axiom-bearing constructor.
# Check every root in both orders, before and after loading the ancestor's .olean.
cycle = tmp / "CycleAncestor.lean"
cycle_check = """open Lean in
run_cmd do
  let env ← getEnv
  let base ← importModules #[{ module := `Init }] {} (trustLevel := 0)
  let roots := #[``Rose.branch, ``Forest.cons, ``Rose, ``Forest.leaf, ``Forest]
  for order in [roots, roots.reverse] do
    let mut complete := {}
    for root in order do
      let axs := Prism.collectRootAxioms env complete root (some base)
      unless axs == #[``boundaryType] && !Prism.CatStructure.guardAxiomsAssuming #[] axs do
        throwError "incorrect axiom footprint for {root}: {axs}"
      complete := complete.insert root axs
"""
cycle.write_text("""import Prism.CatStructure
axiom boundaryType : Type
mutual
  inductive Rose where
    | branch : Forest → Rose
  inductive Forest where
    | nil : Forest
    | cons : Rose → Forest → Forest
    | leaf : boundaryType → Forest
end
""" + cycle_check)
command(["lean", "-o", cycle.with_suffix(".olean"), cycle], cwd=tmp, env=lean_env)
consumer = tmp / "CycleAudit.lean"
consumer.write_text("import CycleAncestor\n" + cycle_check)
command(["lean", consumer], cwd=tmp, env=dict(lean_env, LEAN_PATH=os.pathsep.join(map(str, [tmp, lib]))))
print("PASS cyclic axiom footprints in local and imported declarations")
check_mcp("check_spec", {"spec_block": spec}, matches=("OK", "[SAFE_INDEPENDENCE_HINT]"))
check_mcp("check_agda", {"main_block": spec, "allow_postulates": True}, matches=("OK", "[SAFE_INDEPENDENCE_HINT]"))
print("PASS non-blocking independence hints")
PY
