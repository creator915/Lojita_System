"""Linux transport for the verified Lean fixtures. Run through test-posix-channels.sh."""
import contextlib
import fcntl
import json
import os
from pathlib import Path
import pty
import resource
import select
import signal
import subprocess
import sys
import termios
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass


@dataclass(frozen=True)
class Observation:
    tty: bytes = b""
    out: bytes = b""
    err: bytes = b""
    code: int = -1

    def deterministic(self):
        return self.out, self.err, self.code


def check(actual, expected, label):
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected!r}, observed {actual!r}")


def unhex(token):
    return b"" if token == "-" else bytes.fromhex(token)


def write(channel, data):
    return channel + " " + (data.hex() or "-")


def read_reply(relay, deadline):
    remaining = max(0, deadline - time.monotonic())
    if not select.select([relay.stdout], [], [], remaining)[0]:
        raise TimeoutError(f"{relay.args[-1]}: timed out waiting for term-relay")
    return relay.stdout.readline().decode("ascii").rstrip("\n")


def trace(probe, program, topology, commands, args=(), budget=12):
    """Observe every command before Q, measuring the stimulus budget from READY."""
    size = ["0", "0"] if topology == "stdio" else ["24", "80"]
    argv = [probe / "term-relay", topology, *size, "0", program, *args]
    with subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE) as relay:
        try:
            check(read_reply(relay, time.monotonic() + 3), "READY", str(program))
            deadline = time.monotonic() + budget
            tty, out, err = bytearray(), bytearray(), bytearray()
            checkpoints = []
            for command in commands:
                relay.stdin.write((command + "\n").encode("ascii"))
                relay.stdin.flush()
                fields = read_reply(relay, deadline).split()
                if len(fields) != 5 or fields[0] != "O":
                    raise AssertionError(f"{program} {command[:40]}: {fields!r}")
                t, o, e, code = fields[1:]
                tty.extend(unhex(t))
                out.extend(unhex(o))
                err.extend(unhex(e))
                checkpoints.append(Observation(bytes(tty), bytes(out), bytes(err), int(code)))
            if time.monotonic() > deadline:
                raise TimeoutError(f"{program}: stimulus exceeded {budget}s")
            relay.stdin.write(b"Q\n")
            relay.stdin.flush()
            final = read_reply(relay, time.monotonic() + 2).split()
            check((final[:1], final[2:]), (["O"], ["-", "-", str(checkpoints[-1].code)]),
                  f"{program}/drained at exit")
            check(relay.wait(timeout=2), 0, "term-relay exit")
            return checkpoints
        finally:
            if relay.poll() is None:
                relay.kill()


def live_pair(probe, candidate, topology, commands, args=(), budget=12):
    with ThreadPoolExecutor(2) as workers:
        jobs = [workers.submit(trace, probe, binary, topology, commands, args, budget)
                for binary in ["/workspace/executable", probe / candidate]]
        return tuple(job.result() for job in jobs)


def topology_checks(probe, model):
    data = unhex(model["input"])
    for topology, apps in model["topologies"].items():
        for app, binary in [("cli", "VerifiedCli"), ("reactive", "VerifiedReactive")]:
            commands = [write("W", data[:2]), "S 30", write("W", data[2:]), "S 120"]
            seen = trace(probe, probe / binary, topology, commands)
            check(seen[1], Observation(), f"{topology}/{app} before newline")
            expected = apps[app]
            check(seen[-1], Observation(unhex(expected["tty"]), unhex(expected["out"]),
                                        unhex(expected["err"]), expected["code"]),
                  f"{topology}/{app} vs Lean pure world before EOF")


def interrupted_read(probe):
    commands = [write("W", b"start"), "S 80", f"K {signal.SIGWINCH.value}", "S 30",
                write("W", b"\xff"), "S 80"]
    seen = trace(probe, probe / "VerifiedInterrupted", "pipe", commands)
    reading = Observation(out=b"reading\n")
    check(seen[1], reading, "blocking stdin read")
    check(seen[3], reading, "SIGWINCH during read")
    check(seen[-1], Observation(out=b"reading\n\xff", code=0), "resumed stdin read")


@contextlib.contextmanager
def controlling_pty(binary, args, stdin_on_slave):
    master_fd, slave_fd = pty.openpty()
    with os.fdopen(master_fd, "r+b", buffering=0) as master, os.fdopen(slave_fd, "r+b", buffering=0) as slave:
        before = termios.tcgetattr(slave)
        child = subprocess.Popen([binary, *args], stdin=slave if stdin_on_slave else subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, pass_fds=(slave_fd,),
                                 start_new_session=True,
                                 preexec_fn=lambda: fcntl.ioctl(slave_fd, termios.TIOCSCTTY, 0))
        try:
            yield child, master, slave, before
        finally:
            if child.poll() is None:
                child.kill()
            child.wait(timeout=2)
            for pipe in [child.stdin, child.stdout, child.stderr]:
                if pipe is not None:
                    pipe.close()


def read_exact(pipe, count, deadline):
    result = bytearray()
    while len(result) < count:
        if not select.select([pipe], [], [], max(0, deadline - time.monotonic()))[0]:
            raise AssertionError(f"timed out after reading {bytes(result)!r}")
        chunk = os.read(pipe.fileno(), count - len(result))
        if not chunk:
            raise AssertionError(f"premature EOF after {bytes(result)!r}")
        result.extend(chunk)
    return bytes(result)


def cooked_pty(probe):
    mask = termios.ECHO | termios.ICANON
    with controlling_pty(probe / "VerifiedCli", ["raw"], True) as (child, master, slave, before):
        check(before[3] & mask, mask, "openpty initially cooked")
        check(read_exact(child.stdout, 6, time.monotonic() + 2), b"ready\n", "raw-mode handshake")
        check(termios.tcgetattr(slave)[3] & mask, 0, "raw mode active")
        start = time.monotonic()
        master.write(b"beta")
        check(read_exact(child.stdout, 4, start + .100), b"beta", "four bytes without LF")
        if time.monotonic() - start >= .100:
            raise AssertionError("raw input exceeded 100 ms")
        check(child.wait(timeout=2), 0, "raw exit")
        check((child.stdout.read(), child.stderr.read()), (b"", b""), "raw pipes")
        echo = os.read(master.fileno(), 4096) if select.select([master], [], [], 0)[0] else b""
        check(echo, b"", "echo on PTY master")
        check(termios.tcgetattr(slave), before, "restored PTY termios")


def child_cpu():
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return usage.ru_utime + usage.ru_stime


def hangups(probe):
    cpu = child_cpu()
    with controlling_pty(probe / "VerifiedHangup", [], False) as (child, master, _, _before):
        child.stdin.close()
        check(read_exact(child.stdout, 10, time.monotonic() + 2), b"stdin EOF\n", "closed pipe")
        start = time.monotonic()
        master.close()
        check(read_exact(child.stdout, 8, time.monotonic() + 2), b"tty EOF\n", "closed PTY master")
        check(child.wait(timeout=2), 0, "duplicate EOF or timeout")
        if time.monotonic() - start < .190:
            raise AssertionError("poll loop skipped the post-EOF quiet interval")
        check((child.stdout.read(), child.stderr.read()), (b"", b""), "one notification per descriptor")
    # The app stays in the poll loop for another 200 ms after the second EOF.
    used = child_cpu() - cpu
    if used >= .100:
        raise AssertionError(f"poll loop consumed {used:.3f}s CPU across the hangups")


def legacy_key_resize_signals(probe):
    keys = b"\x1b[A\x1b[B\x7f\x00\xff"
    commands = [write("W", b"Aone"), "S 100", write("T", keys), "S 80",
                "R 34 95", "S 80", f"K {signal.SIGINT.value}", "S 50",
                f"K {signal.SIGQUIT.value}", "S 50", f"K {signal.SIGHUP.value}",
                "S 50", f"K {signal.SIGTERM.value}", "S 100"]
    seen = trace(probe, probe / "VerifiedInputs", "pipe", commands)
    check(seen[1].out, b"Aone", "sync stdin prefix and buffered reactive suffix")
    check(seen[3].err, keys, "raw controlling-terminal keys on a separate descriptor")
    check(seen[5].out, b"Aone34x95\n", "SIGWINCH reports actual PTY dimensions")
    check(seen[-1], Observation(out=b"Aone34x95\nINT\nQUIT\nHUP\n", err=keys, code=0),
          "legacy signal identities and SIGTERM exit")


def fzf(probe):
    for topology, tty, code in [("pipe", b"UI", 0), ("stdio", b"", 25)]:
        seen = trace(probe, probe / "VerifiedFzfTTY", topology, ["S 120"])
        check(seen[-1], Observation(tty, b"OUT", b"ERR", code), f"Issue #1/{topology}")

    small = b"alpha\nbeta\ngamma\n"
    large = b"".join(b"item_%05d\n" % i for i in range(50000))
    for label, data, close, query in [
        ("3A", small, True, b"beta"), ("3B", small, False, b"beta"),
        ("3C", large, True, b"item_42424"),
    ]:
        commands = [write("W", data[i:i + 16384]) for i in range(0, len(data), 16384)]
        if close:
            commands.append("C")
        # fzf filters asynchronously. Give the query a render turn before accepting
        # the highlighted row, and capture the alternate screen before its teardown.
        commands += ["S 80", write("T", query), "S 120", write("T", b"\r"), "S 220"]
        ref, cand = live_pair(probe, "VerifiedFzfSelect", "pipe", commands, budget=.500 if not close else 12)
        check(ref[-3].deterministic(), (b"", b"", -1), f"{label}/ref before Enter")
        check(cand[-3].deterministic(), ref[-3].deterministic(), f"{label}/cand before Enter")
        check(cand[-1].deterministic(), ref[-1].deterministic(), f"{label}/live selection")
        check(ref[-1].deterministic(), (query + b"\n", b"", 0), f"{label}/selected row")
        if label == "3A":
            # The host projects both raw traces with LojitaCtx.Terminal.stepANSI.
            print(ref[-3].tty.hex(), cand[-3].tty.hex(), sep="\n")

    # With a single highlighted row, a coalesced query/Enter has a stable
    # reference selection even when fzf accepts before its search redraw.
    ref, cand = live_pair(probe, "VerifiedFzfSelect", "pipe",
                          [write("W", b"beta\n"), "C", "S 80", write("T", b"beta\r"), "S 120"])
    check(cand[-1].deterministic(), ref[-1].deterministic(), "coalesced query and Enter")
    check(ref[-1].deterministic(), (b"beta\n", b"", 0), "coalesced selection")


def gron(probe, model):
    def observe(label, commands, args=()):
        ref, cand = live_pair(probe, "VerifiedGronStreamProbe", "stdio", commands, args)
        for observation in [*ref, *cand]:
            check(observation.tty, b"", f"{label}/pipesNoTTY")
        return ref, cand

    check(len(model["prefixes"]), 34, "probe_167 corpus plus NUL")
    for case in model["prefixes"] + model["numberLookahead"]:
        raw = unhex(case["input"])
        label = f"gron {raw!r}"
        ref, cand = observe(label, [write("W", raw), "S 120", "C", "S 80", "D"])
        check(ref[1].code != -1, case["early"], f"{label}/boundary machine")
        check(cand[1].code != -1, ref[1].code != -1, f"{label}/exited before EOF")
        for i, phase in [(1, "before EOF"), (-1, "after EOF")]:
            check(cand[i].deterministic(), ref[i].deterministic(), f"{label}/{phase}")
        if ref[-1].code not in (0, 3):
            raise AssertionError(f"{label}: unexpected final status {ref[-1].code}")

    ref, cand = observe("--stream", [write("W", b'{"a":1}\n'), "S 120", write("W", b"{}\n"),
                                    "S 120", "C", "S 80", "D"], ["--stream"])
    for i, code in [(1, -1), (3, -1), (-1, 0)]:
        check(cand[i].deterministic(), ref[i].deterministic(), f"--stream checkpoint {i}")
        check((ref[i].err, ref[i].code), (b"", code), f"--stream ref checkpoint {i}")
    # The image renders a stream as an indexed array. Check that the first
    # value (not just the array header) and then the next object flushed live.
    if b".a = 1;\n" not in ref[1].out or not ref[3].out[len(ref[1].out):].endswith(b" = {};\n"):
        raise AssertionError(f"--stream missing pre-EOF assignments: {ref[1].out!r}, {ref[3].out!r}")
    check(ref[-1].out, ref[3].out, "--stream after EOF")

    ref, cand = observe("--ungron", [write("W", b"\n"), "S 120", "C", "S 80", "D"], ["--ungron"])
    for i in (1, -1):
        check(cand[i].deterministic(), ref[i].deterministic(), "--ungron live invalid line")
    check(cand[1].code != -1, ref[1].code != -1, "--ungron exited before EOF")
    check((ref[-1].out, ref[-1].code), (b"", 5), "--ungron empty input group")
    # The open prefix can still receive a valid assignment after the blank line.
    ref, cand = observe("--ungron continuation", [write("W", b"\n"), "S 120",
                        write("W", b"json = 1;\n"), "C", "S 80", "D"], ["--ungron"])
    for i in (1, -1):
        check(cand[i].deterministic(), ref[i].deterministic(), "--ungron continuation")
    check(ref[-1].code, 0, "--ungron completed assignment")
    print("Gate 4 passed. 34 corpus prefixes, two numeric lookaheads, --stream and --ungron matched live.")


if __name__ == "__main__":
    gate, directory = sys.argv[1:]
    probe_dir = Path(directory).resolve()
    model = json.loads((probe_dir / "model.json").read_bytes())
    if gate == "linux":
        topology_checks(probe_dir, model)
        interrupted_read(probe_dir)
        cooked_pty(probe_dir)
        hangups(probe_dir)
        legacy_key_resize_signals(probe_dir)
        print("Gate 2 passed. Three topologies, interrupted reads, cooked PTY restoration and one-shot hangups matched.")
    elif gate == "fzf":
        fzf(probe_dir)
    elif gate == "gron":
        gron(probe_dir, model)
    else:
        raise ValueError(gate)
