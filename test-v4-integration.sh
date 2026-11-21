#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"

./build.sh
test -x ./Main
test -x ./runtime/lean-prism/.lake/build/bin/agda2lean
test -x ./runtime/lean-prism/.lake/build/bin/harness-engine

fixture=$(mktemp -d "${TMPDIR:-/tmp}/test-v4-integration.XXXXXXXX")
trap 'rm -rf -- "$fixture"' EXIT

cat >"$fixture/mock-mcp-codex" <<'MOCK'
#!/usr/bin/env python3
import json, os, re, subprocess, sys

args = sys.argv[1:]
out_file = None
mode = "new"
parent = ""
mcp_cfg = None

i = 0
while i < len(args):
    a = args[i]
    if a == "-o" and i + 1 < len(args):
        out_file = args[i + 1]
        i += 2
    elif a in ("fork", "resume") and i + 1 < len(args):
        mode = a
        parent = args[i + 1]
        i += 2
    elif a == "-c" and i + 1 < len(args):
        val = args[i + 1]
        log_path = os.environ.get("V4_MCP_LOG", "")
        if log_path:
            with open(log_path, "a", encoding="utf-8") as lf:
                lf.write(val + "\n")
        if val.startswith("mcp_servers.codetransport="):
            mcp_cfg = val
        i += 2
    elif a == "-m" and i + 1 < len(args):
        log_path = os.environ.get("V4_MCP_LOG", "")
        if log_path:
            with open(log_path, "a", encoding="utf-8") as lf:
                lf.write(f"model={args[i+1]}\n")
        i += 2
    else:
        i += 1

prompt = sys.stdin.read()
codex_home = os.environ.get("CODEX_HOME", "/tmp")
sess_dir = os.path.join(codex_home, "sessions", "2026", "11", "20")
os.makedirs(sess_dir, exist_ok=True)

if mode == "resume":
    tid = parent
else:
    ser_file = os.path.join(codex_home, "serial")
    ser = int(open(ser_file).read().strip()) + 1 if os.path.exists(ser_file) else 1
    open(ser_file, "w").write(str(ser))
    tid = f"00000000-0000-4000-b000-{ser:012d}"

open(os.path.join(sess_dir, f"rollout-2026-11-20T09-00-00-{tid}.jsonl"), "a").write(prompt + "\n")

if "Reply READY" in prompt:
    reply = "READY"
elif "Acknowledge only" in prompt:
    reply = "OK"
else:
    # Actually spawn and exercise the native Lean 4 MCP server configured via `-c`!
    m_cmd = re.search(r'command="([^"]+)"', mcp_cfg or "")
    m_args = re.search(r'args=\[(.*)\]', mcp_cfg or "")
    assert m_cmd and m_args, f"missing mcp_servers.codetransport in {mcp_cfg}"
    cmd_bin = m_cmd.group(1)
    cmd_args = json.loads("[" + m_args.group(1) + "]")

    proc = subprocess.Popen([cmd_bin] + cmd_args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    def rpc(req):
        proc.stdin.write(json.dumps(req) + "\n")
        proc.stdin.flush()
        return json.loads(proc.stdout.readline())

    rpc({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-06-18"}})
    # 1. Write initial draft with a type error (`twice n = "bad"`)
    rpc({"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {
        "name": "write_draft",
        "arguments": {
            "name": "main",
            "content": "module Gen.M0.Target where\nopen import Data.Nat using (ℕ; _+_)\nopen import Relation.Binary.PropositionalEquality using (_≡_; refl)\ntwice : ℕ → ℕ\ntwice n = \"bad\"\ntwice-3 : twice 3 ≡ 6\ntwice-3 = refl\n"
        }
    }})
    r_bad = rpc({"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {
        "name": "check_agda", "arguments": {"main_block": "main"}
    }})
    assert r_bad["result"]["isError"] is True, f"expected check_agda error: {r_bad}"
    # 2. Patch just the 1 broken line via `patch_draft`!
    rpc({"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {
        "name": "patch_draft",
        "arguments": {"name": "main", "old_text": "twice n = \"bad\"", "new_text": "twice n = n + n"}
    }})
    r_good = rpc({"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {
        "name": "check_agda", "arguments": {"main_block": "main"}
    }})
    assert r_good["result"]["isError"] is False, f"expected check_agda pass: {r_good}"
    proc.stdin.close()
    proc.wait(timeout=5)

    log_path = os.environ.get("V4_MCP_LOG", "")
    if log_path:
        with open(log_path, "a", encoding="utf-8") as lf:
            lf.write("MCP_PATCH_LOOP_VERIFIED\n")

    # Notice: return ONLY the compact `(submission ...)` envelope referencing `@main`
    # WITHOUT inline `agda main` fence — verifying `Code/AI.agda` auto-attaches saved drafts!
    reply = '```sexp\n(submission (kind plan) (why "double via addition") (main @main) (moves))\n```\n'

if out_file:
    open(out_file, "w", encoding="utf-8").write(reply)
print(json.dumps({"thread_id": tid}))
MOCK
chmod +x "$fixture/mock-mcp-codex"

CLI_HOST_C="$(pwd)/runtime/cli_host.c"
agda --compile --ghc-flag=-O0 --ghc-flag=-threaded --ghc-flag=-iruntime --ghc-flag=-iruntime/tools \
  "--ghc-flag=$CLI_HOST_C" --compile-dir=tmp/tool-build \
  -i . -i /usr/share/agda-stdlib Test/V4IntegrationTest.agda >"$fixture/compile.log" 2>&1 || {
  tail -n 100 "$fixture/compile.log" >&2
  exit 1
}

timeout 300 ./tmp/tool-build/V4IntegrationTest "$fixture/mock-mcp-codex"
