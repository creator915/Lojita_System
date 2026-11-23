"""Black-box, newline-framed MCP roundtrips against both native server modes."""
import json
import select
import statistics
import subprocess
import sys
import time
from pathlib import Path

root = Path.cwd()
scratch, ws = map(Path, sys.argv[1:])
log = scratch / "events.jsonl"
reference = scratch / "reference.sexp"
reference.write_text(f'(ref-target (local "{root}/Test/S4/mini-pandoc.py") (timeoutMs 3000))\n')


class Client:
    def __init__(self, mode, ctx=None, workspace=ws):
        self.ctx = ctx or scratch / mode
        self.ctx.mkdir(parents=True, exist_ok=True)
        self.seq = 0
        self.p = subprocess.Popen(
            [str(root / "lojita"), "mcp", "--mode", mode, "--repo", str(root),
             "--ctx-dir", str(self.ctx), "--workspace", str(workspace), "--ref-file", str(reference),
             "--narrow-log", str(log)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
        )

    def send(self, data):
        self.p.stdin.write(json.dumps(data) + "\n")
        self.p.stdin.flush()

    def rpc(self, method, params=None):
        self.seq += 1
        self.send(dict(jsonrpc="2.0", id=self.seq, method=method, params=params or {}))
        assert select.select([self.p.stdout], [], [], 45)[0], f"{method} timed out"
        reply = json.loads(self.p.stdout.readline())
        assert reply["jsonrpc"] == "2.0" and reply["id"] == self.seq, reply
        return reply["result"]

    def tool(self, tool_name, ok=True, **args):
        result = self.rpc("tools/call", {"name": tool_name, "arguments": args})
        assert result["isError"] == (not ok), (tool_name, result)
        return result

    def __enter__(self):
        result = self.rpc("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                                         "clientInfo": {"name": "gate", "version": "1"}})
        assert result["protocolVersion"] == "2025-06-18" and "tools" in result["capabilities"]
        self.send(dict(jsonrpc="2.0", method="notifications/initialized"))
        self.rpc("ping")
        return self

    def __exit__(self, *exc):
        self.p.stdin.close()
        self.p.wait(timeout=10)
        assert self.p.returncode == 0


def module(name, body, *imports):
    return "\n".join([*(f"import {i}" for i in imports), f"namespace {name}", body, f"end {name}"])


common = {"read_context", "write_draft", "patch_draft", "read_draft", "list_drafts"}
public = {".".join(p.with_suffix("").parts) for p in Path("LojitaCtx").rglob("*.lean")}


def context_source(cli, name, source):
    assert cli.tool("read_context", module=name)["content"][0]["text"] == source
    assert cli.tool("read_context", module=name, start_line=2, end_line=4)["content"][0]["text"] == (
        "\n".join(source.split("\n")[1:4]))


unpublished = scratch / "unpublished"
with Client("session", scratch / "readonly", unpublished) as cli:
    assert set(cli.tool("read_context")["structuredContent"]["modules"]) == public | {"Lojita.Session.SessionEnv"}
    assert not unpublished.exists()
    journal = unpublished / ".publication"
    journal.mkdir(parents=True)
    (unpublished / "workspace.lock").touch()
    (journal / "ready").write_text("Interrupted")
    cli.tool("read_context", ok=False)
    assert (journal / "ready").read_text() == "Interrupted"


with Client("node") as cli:
    schemas = cli.rpc("tools/list")["tools"]
    assert {t["name"] for t in schemas} == common | {"check_lean", "check_agda", "check_plan"}
    assert all(t["inputSchema"]["type"] == "object" for t in schemas)
    assert set(cli.tool("read_context")["structuredContent"]["modules"]) == public
    context_source(cli, "LojitaCtx.World", Path("LojitaCtx/World.lean").read_text())
    for denied in ["Lojita.Session.SessionEnv", "Lojita.Kernel.Driver", "../Lojita/Main", "LojitaCtx.../World"]:
        cli.tool("read_context", ok=False, module=denied)
    for bounds in [dict(start_line=0), dict(start_line=3, end_line=2), dict(end_line=-1)]:
        cli.tool("read_context", ok=False, module="LojitaCtx.World", **bounds)
    name = "Gen.Rpc.Tiny"
    (cli.ctx / "spec.lean").write_text(module(name, "axiom answer : Nat"))
    ancestor = "Gen.Rpc.Base"
    original = "-- retained preamble\n\n" + module(ancestor, "def port := 7") + "\n\n"
    (cli.ctx / "ancestors").mkdir()
    (cli.ctx / "ancestors/loose.lean").write_text(original)
    context_source(cli, ancestor, original)
    (cli.ctx / "ancestors/loose.lean").unlink()
    source = module(name, "def answer : Nat := 41")
    cli.tool("write_draft", name="main", content=source)
    cli.tool("patch_draft", name="main", old_text="41", new_text="42")
    expected = source.replace("41", "42")
    assert cli.tool("read_draft", name="main")["structuredContent"]["content"] == expected
    assert cli.tool("list_drafts")["structuredContent"]["drafts"] == ["main"]
    cli.tool("write_draft", ok=False, name="../bad", content="x")
    cli.tool("check_lean", main_block="@main")
    times = []
    for i in range(6):
        start = time.perf_counter_ns()
        cli.tool("check_lean", source=expected.replace("42", str(i + 100)))
        times.append((time.perf_counter_ns() - start) / 1e6)
    assert max(times) < 300, times
    assert statistics.median(times) < 60, times
    cli.tool("check_agda", main_block="main")
    cli.tool("check_lean", ok=False, source=module(name, "def answer := )"))
    cli.tool("check_lean", ok=False, source=module(name, "def answer := true"))
    cli.tool("check_lean", ok=False, source=module(name, "def answer := 42", "Lojita.Session.SessionEnv"))
    subspec = module(name + ".Slot", "axiom port : Nat")
    cli.tool("check_lean", source=subspec, allow_axioms=True)
    cli.tool("check_agda", source=subspec, allow_postulates=True)
    env = '(submission (kind plan) (why "birth") (main @main) (moves (move bot (unit "Gen.Rpc.Tiny.answer"))))'
    assert not cli.tool("check_plan", submission=env)["structuredContent"]["certificate"]
    bad = cli.tool("check_plan", ok=False, submission=env.replace("Tiny.answer", "Tiny.missing"))
    cert = bad["structuredContent"]["certificate"]
    assert all(cert[k] for k in ("kind", "witness", "cause", "detour"))
    assert all("[" + k.upper() + "]" in bad["content"][0]["text"] for k in cert)
    assert cli.tool("read_draft", name="main")["structuredContent"]["content"] == expected
    (cli.ctx / "spec.lean").write_text(module(name, "axiom inconsistent : False"))
    witness = module("Gen.Rpc.Witness", "theorem contradiction : False := Gen.Rpc.Tiny.inconsistent", name)
    assert "False" in cli.tool("check_lean", source=witness)["content"][0]["text"]
    cli.tool("check_entry", ok=False, entry="Gen.T1.Doc.app")
    cli.tool("run_lean_script", ok=False, source="blocked")

# The runner-produced context includes the repaired base and the routed child lift.
with Client("node", ws / "trees/T1/ai/Gen.T1.Doc.ParseLine") as cli:
    assert set(cli.tool("read_context", module="list")["structuredContent"]["modules"]) == public | {"Gen.T0.Doc"}
    context_source(cli, "Gen.T0.Doc", (ws / "generated/T0/Gen/T0/Doc.lean").read_text())
    for denied in ["Gen.T0.Root", "Gen.T1.Doc.Escape", "Lojita.Session.SessionEnv"]:
        cli.tool("read_context", ok=False, module=denied)
    parser = "Gen.T1.Doc.ParseLine"
    body = (ws / "generated/T1/Gen/T1/Doc/ParseLine.lean").read_text()
    cli.tool("write_draft", name="impl", content=body)
    cli.tool("check_lean", main_block="@impl")
    moves = " ".join(f'(move bot (unit "{parser}.{n}"))' for n in ["lookupDef", "project", "observed"])
    preview = cli.tool("check_plan", submission=f'(submission (kind plan) (why "repair") (main @impl) (moves {moves}))')
    assert "Lift" in preview["structuredContent"]["passed"]

before = {p: p.read_bytes() for p in (ws / "store/refs").rglob("*") if p.is_file()}
with Client("session") as cli:
    names = {t["name"] for t in cli.rpc("tools/list")["tools"]}
    assert names == common | {"check_spec", "check_entry", "run_lean_script", "run_agda_script"}
    sealed = {".".join(p.relative_to(tree).with_suffix("").parts)
              for tree in (ws / "generated").iterdir() for p in tree.rglob("*.lean")}
    assert set(cli.tool("read_context", module="")["structuredContent"]["modules"]) == (
        public | sealed | {"Lojita.Session.SessionEnv"})
    context_source(cli, "Lojita.Session.SessionEnv", Path("Lojita/Session/SessionEnv.lean").read_text())
    context_source(cli, "Gen.T1.Doc", (ws / "generated/T1/Gen/T1/Doc.lean").read_text())
    cli.tool("read_context", ok=False, module="Lojita.Session.Runner")
    cli.tool("read_context", ok=False, module="Gen.Unsealed.Root")
    spec = module("Gen.Rpc.Next", "axiom result : Nat")
    cli.tool("write_draft", name="spec", content=spec)
    cli.tool("check_spec", spec_block="@spec", base_trees=["T1"])
    cli.tool("check_spec", ok=False, source=spec, base_trees=["missing"])
    cli.tool("check_spec", source=spec, base_trees=["T0"],
             lift_src='(lift "Gen.T0.Doc" "Gen.Rpc.Next" () ())',
             transport_src='(poly-transport "Gen.T0.Root" "Gen.Rpc.Next" ((move ("Gen.T0.Doc") () ())) ())')
    cli.tool("check_spec", ok=False, source=spec, base_trees=["T0"],
             lift_src='(lift "Gen.T0.Doc" "Gen.Rpc.Next" () ((("missing") ("unused") "sq" ())))')
    cli.tool("check_entry", entry="Gen.T1.Doc.app")
    cli.tool("check_entry", ok=False, entry="Gen.T1.Doc.app", mode="reactive")
    cli.tool("check_entry", ok=False, entry="Gen.T1.Doc.render")
    cli.tool("check_entry", ok=False, entry="Gen.T1.Doc.unknown")
    cli.tool("check_lean", ok=False, source=spec)
    src = module("Gen.Probe.Tools", '''open Lojita.Session.SessionEnv LojitaCtx.Terminal
def probe : Probe := do
  let data := bytes "A & B\\n"
  let term ← terminal "ref" [] [.writeStdin data, .closeStdin, .sleepMs 100, .drainRaw]
  let fs ← batch "ref" [] data [.fixFile "note.md" 420 data]
  if term.stdoutOut == fs.stdoutOut && term.exitStatus == some 0 && fs.exitStatus == some 0 then
    return {stdout := text fs.stdoutOut}
  return {exitCode := 1, stderr := "terminal and batch differ"}''', "Lojita.Session.SessionEnv")
    cli.tool("write_draft", name="probe", content=src)
    result = cli.tool("run_lean_script", script_block="@probe")["structuredContent"]
    assert result["exitCode"] == 0 and result["usedRef"] and not result["usedCand"]
    assert result["stdout"] == "<p>A &amp; B</p>\n", result
    bad = module("Gen.Probe.Bad", "def probe : IO Unit := IO.println 1", "Lojita.Session.SessionEnv")
    result = cli.tool("run_agda_script", ok=False, source=bad)["structuredContent"]
    assert result["exitCode"] != 0 and "VIOLATION" in result["stderr"], result

after = {p: p.read_bytes() for p in (ws / "store/refs").rglob("*") if p.is_file()}
assert before == after, "preflight mutated tree refs"
events = [json.loads(x) for x in log.read_text().splitlines()]
assert any(e["certificate"] == cert and e["source"] == "mcp" for e in events)
print("2  Native MCP protocol and cleanroom tools passed. Warm check_lean RPCs (ms):",
      ", ".join(f"{t:.1f}" for t in times))
