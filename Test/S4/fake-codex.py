#!/usr/bin/python3
"""Offline Codex subprocess fixture with real per-thread rollout files."""
import json
import os
import sys
import tomllib
import uuid
from pathlib import Path

args = sys.argv[1:]
prompt = sys.stdin.read()
root = Path(os.environ["LOJITA_S4_THREADS"])
ctx = Path.cwd().parent
assert ctx in (root / "ctx", root / "node-ctx")
assert Path.cwd() == ctx / "work"
expected = ["exec", "--skip-git-repo-check", "-s", "read-only", "-C", str(Path.cwd()),
            "-m", os.environ.get("CODETRANSPORT_MODEL", "gpt-6.2-sol"),
            "-c", "model_reasoning_effort=" + json.dumps(os.environ.get("CODETRANSPORT_EFFORT", "max"))]
tier = os.environ.get("CODETRANSPORT_SERVICE_TIER", "ultrafast")
if tier:
    expected += ["-c", "service_tier=" + json.dumps(tier)]
expected += ["-c", 'approval_policy="never"', "-c", "features.shell_tool=false",
             "-c", "features.unified_exec=false", "-c", "features.multi_agent=false"]
if prompt.startswith("proposal"):
    server = args[len(expected) + 1]
    repo = Path(__file__).resolve().parents[2]
    mode = "node" if ctx.name == "node-ctx" else "session"
    mcp_args = ["mcp", "--mode", mode, "--repo", str(repo), "--ctx-dir", str(ctx),
                "--narrow-log", str(root / "narrowing-events.jsonl")]
    if mode == "session":
        mcp_args += ["--workspace", str(root), "--ref-file", str(root / "ref.sexp")]
    assert tomllib.loads(server) == {"mcp_servers": {"lojita": {
        "command": str(repo / "lojita"), "startup_timeout_sec": 30, "tool_timeout_sec": 180,
        "default_tools_approval_mode": "approve", "args": mcp_args}}}
    expected += ["-c", server]
expected += ["--json", "-o", str(ctx / "last-message")]
verb = "new"
if prompt.startswith("proposal") or prompt.startswith("Accepted semantic turn:"):
    verb, source = args[len(expected):-1]
    assert verb in ("fork", "resume")
    expected += [verb, source]
assert args == expected + ["-"], args
sessions = root / "sessions"
sessions.mkdir(exist_ok=True)
if verb == "new":
    assert "READY" in prompt
    tid = str(uuid.uuid4())
else:
    assert (sessions / (source + ".jsonl")).is_file()
    tid = str(uuid.uuid4()) if verb == "fork" else source

with (root / "calls").open("a") as out:
    out.write(verb + "\n")
(sessions / (tid + ".jsonl")).write_text(prompt)
Path(args[args.index("-o") + 1]).write_text(tid)
print(json.dumps({"type": "thread.started", "thread_id": tid}))
