#!/usr/bin/python3
"""Offline Codex subprocess fixture with real per-thread rollout files."""
import fcntl
import json
import os
import sys
import time
import tomllib
import uuid
from pathlib import Path

args = sys.argv[1:]
prompt = sys.stdin.read()
root = Path(os.environ["LOJITA_S4_THREADS"])
ctx = Path.cwd().parent
assert ctx in (root / "ctx", root / "node-ctx") or root in ctx.parents
assert Path.cwd() == ctx / "work"
expected = ["exec", "--skip-git-repo-check", "-s", "read-only", "-C", str(Path.cwd()),
            "-m", os.environ.get("CODETRANSPORT_MODEL", "gpt-6.2-sol"),
            "-c", "model_reasoning_effort=" + json.dumps(os.environ.get("CODETRANSPORT_EFFORT", "max"))]
tier = os.environ.get("CODETRANSPORT_SERVICE_TIER", "ultrafast")
if tier:
    expected += ["-c", "service_tier=" + json.dumps(tier)]
expected += ["-c", 'approval_policy="never"', "-c", "features.shell_tool=false",
             "-c", "features.unified_exec=false", "-c", "features.multi_agent=false"]
verb = args[-3] if args[-3] in ("fork", "resume") else "new"
proposal = verb != "new" and not prompt.startswith("Accepted semantic turn:")
if proposal:
    server = args[len(expected) + 1]
    repo = Path(__file__).resolve().parents[2]
    mode = "session" if ctx.name in ("ctx", "SESSION_ROOT") else "node"
    mcp_args = ["mcp", "--mode", mode, "--repo", str(repo), "--ctx-dir", str(ctx),
                "--narrow-log", str(root / "narrowing-events.jsonl")]
    if mode == "session":
        mcp_args += ["--workspace", str(root), "--ref-file", str(root / "ref.sexp")]
    assert tomllib.loads(server) == {"mcp_servers": {"lojita": {
        "command": str(repo / "lojita"), "startup_timeout_sec": 30, "tool_timeout_sec": 180,
        "default_tools_approval_mode": "approve", "args": mcp_args}}}
    expected += ["-c", server]
expected += ["--json", "-o", str(ctx / "last-message")]
if verb != "new":
    source = args[-2]
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

plan_file = os.environ.get("LOJITA_FAKE_CODEX_PLAN")
owner = ctx.name
step = {}
with (root / "calls").open("a") as out:
    fcntl.flock(out, fcntl.LOCK_EX)
    if plan_file:
        phase = "propose" if proposal else "bootstrap" if verb == "new" else "accept"
        if proposal:
            # Each owner consumes its own ordered list of proposal replies, including retries.
            with (root / "calls").open() as calls:
                turn = sum(line.startswith(f"{owner} propose ") for line in calls)
            step = json.loads(Path(plan_file).read_text())[owner][turn]
        out.write(f"{owner} {phase} {verb} {tid}\n")
    else:
        out.write(verb + "\n")
    out.flush()
(sessions / (tid + ".jsonl")).write_text(prompt)
print(json.dumps({"type": "thread.started", "thread_id": tid}), flush=True)
if plan_file and proposal:
    (ctx / "drafts").mkdir(exist_ok=True)
    (ctx / "drafts" / "proposal.block").write_text(tid)
    if "pidFile" in step:
        (root / step["pidFile"]).write_text(str(os.getpid()))
    time.sleep(step.get("sleepMs", 0) / 1000)
    with (root / "calls").open("a") as out:
        fcntl.flock(out, fcntl.LOCK_EX)
        out.write(f"{owner} replied {verb} {tid}\n")
        out.flush()
Path(args[args.index("-o") + 1]).write_text(step.get("reply", tid))
