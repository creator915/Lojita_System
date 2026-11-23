"""Verify the real Codex exec event stream and the independent CLI observations."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from uuid import UUID

ws, traces, sessions = map(Path, sys.argv[1:])
durable = {p.stem: str(UUID(p.read_text())) for p in (ws / "threads").glob("*.id")}
assert "SESSION_ROOT" in durable and any(n.startswith("Gen.Trim.") for n in durable), durable
assert len(set(durable.values())) == len(durable)
rollouts = {p.name for p in sessions.rglob("*.jsonl")}
required = {"SESSION_ROOT": {"read_context", "write_draft", "run_lean_script", "check_spec", "check_entry"},
            "node": {"read_context", "write_draft", "check_lean"}}
seen = {role: set() for role in required}
scratch = set()
tool_failures = []
for owner, main in durable.items():
    role = "SESSION_ROOT" if owner == "SESSION_ROOT" else "node"
    verbs = set()
    assert any(f.endswith(main + ".jsonl") for f in rollouts), owner
    for path in sorted((traces / owner).glob("*.jsonl")):
        _, verb, *parent = path.stem.split("-", 2)
        events = [json.loads(line) for line in path.read_text().splitlines()]
        thread, = [str(UUID(e["thread_id"])) for e in events if e["type"] == "thread.started"]
        assert any(e["type"] == "turn.completed" for e in events), path
        if verb == "new":
            assert not parent and thread == main
        elif verb == "fork":
            assert parent == [main] and thread not in durable.values() and thread not in scratch
            scratch.add(thread)
        else:
            assert verb == "resume" and parent == [thread] and (thread == main or thread in scratch)
        verbs.add("accept" if verb == "resume" and thread == main else verb)
        for e in events:
            call = e.get("item", {})
            if e["type"] != "item.completed" or call.get("type") != "mcp_tool_call":
                continue
            if call["server"] != "lojita":
                continue
            result = call.get("result") or {}
            data = result.get("structured_content") or result.get("structuredContent") or {}
            if (call.get("status") != "completed" or call.get("error") or result.get("isError")
                    or result.get("is_error") or data.get("certificate") or data.get("exitCode")):
                tool_failures.append((call["tool"], call.get("error"), result.get("content")))
                continue
            assert thread in scratch, "tools ran on a durable thread"
            seen[role].add(call["tool"])
    assert {"new", "fork", "accept"} <= verbs, (owner, verbs)
    ctx = ws / "ai" / owner if role == "SESSION_ROOT" else ws / "trees" / owner.split(".")[1] / "ai" / owner
    assert (ctx / "latest-prompt").stat().st_size and (ctx / "latest-reply").stat().st_size
assert all(not any(f.endswith(t + ".jsonl") for f in rollouts) for t in scratch)
for role, names in required.items():
    assert names <= seen[role], (role, names - seen[role])
errors = [json.loads(line) for line in (ws / "narrowing-events.jsonl").read_text().splitlines()]
wrong_language = re.compile(r"\b(?:agda|haskell|ghc|agdai|synslice)\b|\bopen import\b|cross.language"
                            r"|slice.{0,16}(?:error|mismatch)|(?:error|mismatch).{0,16}slice", re.I)
violations = [e for e in [*errors, *tool_failures] if wrong_language.search(json.dumps(e, ensure_ascii=False))]
assert not violations, violations
generated = [p for p in (ws / "generated").rglob("*") if p.is_file()]
assert generated
for module in generated:
    assert module.suffix == ".lean"
    canonical = subprocess.check_output(["./lojita", "roundtrip", module])
    assert canonical == module.read_bytes(), f"source slice mismatch in {module}"
candidate = ws / "bin/candidate"
build = (ws / "bin/build.sexp").read_text()
receipt = (ws / "replay-receipt.sexp").read_text()
digest = hashlib.sha256(candidate.read_bytes()).hexdigest()
ref = Path(__file__).resolve().with_name("trim-ref.py")
assert digest in build and build in receipt and hashlib.sha256(ref.read_bytes()).hexdigest() in receipt
assert (ws / "trees/Trim/verdict").read_text() == "ok"
memory = (ws / "session-memory.sexp").read_text()
assert all(step in memory for step in ("drive-tree Trim: ok", "build-exe Gen.Trim.", "run-script "))
summary = (ws / "SUMMARY.md").read_text()
assert summary.strip() and json.dumps(summary, ensure_ascii=False) in memory
with candidate.open("rb") as binary:
    assert binary.read(4) == b"\x7fELF"
assert "INTERP" not in subprocess.check_output(["readelf", "-lW", candidate], text=True)
assert "(NEEDED)" not in subprocess.check_output(["readelf", "-dW", candidate], text=True)

cases = [
    ([], b"", 0, b""),
    ([], b"  a  b \t\n\t\n\n last\t", 0, b"  a  b\n\n\n last"),
    ([], b"\x00\xff\t \n\xc3\xa9 \r \n", 0, b"\x00\xff\n\xc3\xa9 \r\n"),
    (["--check"], b"a b\n\n", 0, b"a b\n\n"),
    (["--check"], b"dirty \nclean\n", 2, b""),
    (["--check"], b"\t", 2, b""),
    (["--check"], b"", 0, b""),
    (["--check", "extra"], b"dirty \n", 0, b"dirty\n"),
]
for args, stdin, status, stdout in cases:
    for exe in [ref, candidate]:
        p = subprocess.run([exe, *args], input=stdin, capture_output=True, timeout=10)
        assert (p.returncode, p.stdout, p.stderr) == (status, stdout, b""), (exe, args, stdin, p)
print(f"Hosted session finished with {len(durable)} durable threads, {len(scratch)} forks, "
      f"{len(generated)} byte-identical Lean roundtrips, a matching replay receipt "
      f"and {len(cases)} independent byte-stream cases.")
print("Successful MCP calls:", {k: sorted(v) for k, v in seen.items()})
