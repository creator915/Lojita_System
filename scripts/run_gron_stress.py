#!/usr/bin/env python3
"""Offline replay of the checked-in gron sources, submissions and CAS snapshots."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
import fcntl
import hashlib
import json
import os
from multiprocessing.util import Finalize
from pathlib import Path
import re
import shutil
import signal
import shlex
import select
import subprocess
import sys
import tempfile
from types import SimpleNamespace
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Test/gron-stress"
BUILD = ROOT / "runtime/lean-prism/.lake/build"
PRISM = BUILD / "bin/agda2lean"
ENGINE = BUILD / "bin/harness-engine"
DUMP = ROOT / "dump/dump"
STD = Path("/usr/share/agda-stdlib")
COUNTERS = ("prism_bot_fallback", "prism_slow_slice", "roundtrip_ast_drift",
            "roundtrip_reparse_fail", "prism_false_rejection", "agda_scope_dumps",
            "prism_syntax_fallback", "agda_fallbacks", "native_engine_stack_fallback",
            "agda_original_confirmations", "prism_timeout_fallback")
LOCAL = SimpleNamespace()


def command(args, cwd, env, *, timeout=180):
    return subprocess.run([str(a) for a in args], cwd=cwd, env=env,
                          text=True, encoding="utf-8", stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout)


def checked(p):
    if p.returncode:
        raise RuntimeError(f"{Path(p.args[0]).name} exited {p.returncode}\n"
                           + (p.stderr + p.stdout)[-3500:])
    return p.stdout


def current_env(path):
    tmp = path / "tmp"
    cfg = path / "agda"
    tmp.mkdir(parents=True, exist_ok=True)
    cfg.mkdir(exist_ok=True)
    toolchain = (ROOT / "runtime/lean-prism/lean-toolchain").read_text().strip()
    env = dict(os.environ, LC_ALL="C.UTF-8", LANG="C.UTF-8", TMPDIR=str(tmp),
               AGDA_DIR=str(cfg), ELAN_TOOLCHAIN=toolchain)
    installed = Path(env.get("ELAN_HOME", str(Path.home() / ".elan"))) / "toolchains"
    lean_bin = installed / toolchain.replace("/", "--").replace(":", "---") / "bin"
    if (lean_bin / "lean").is_file():
        env["PATH"] = str(lean_bin) + os.pathsep + env["PATH"]
    return env


def installed_stdlib(target):
    # Some distributions ship sources with only a subset of interfaces.
    # Each compiler that can populate those missing .agdai gets its own copy.
    if not target.exists():
        shutil.copytree(STD, target)


def compile_drivers(layers):
    cache = ROOT / "tmp/gron-stress-build"
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / "build.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        env = current_env(cache)
        stdlib = cache / "stdlib"
        installed_stdlib(stdlib)
        source = cache / "source"
        dest = cache / "MAlonzo-build"
        files = list(ROOT.glob("*.agda"))
        for directory in ("Backend", "Code", "Context", "Meta", "OwnershipIO", "Store"):
            files.extend((ROOT / directory).rglob("*.agda"))
        drivers = []
        if "S3" in layers:
            drivers.append("GronReplay")
        if "S2" in layers:
            drivers.append("IndependentSession")
        files.extend(ROOT / "Test" / (name + ".agda") for name in drivers)
        if "S2" in layers:
            files.extend(ROOT / "Test" / name for name in ("IndependentPropagation.agda", "HarnessPure.agda"))
        files.extend(ROOT / "runtime" / name for name in ("cli_host.c", "cli_host.h"))
        files.extend((ROOT / "runtime").rglob("*.hs"))
        for src in files:
            target = source / src.relative_to(ROOT)
            if not target.exists() or target.read_bytes() != src.read_bytes():
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, target)
        for name in drivers:
            checked(command(["agda", "--compile", "--no-libraries", "--ghc-flag=-O0",
                             f"--ghc-flag=-i{source}/runtime", f"--ghc-flag=-i{source}/runtime/tools",
                             f"--ghc-flag={source}/runtime/cli_host.c", f"--compile-dir={dest}",
                             "-i", ".", "-i", stdlib, f"Test/{name}.agda"], source, env, timeout=900))
    return dest


def verify_inventory(manifest):
    checksums = manifest["input_sha256"]
    inputs = {p.relative_to(SUITE).as_posix() for p in (SUITE / "corpus").rglob("*")
              if p.is_file() and p.suffix != ".agdai"}
    inputs.add("curated.json")
    if inputs != set(checksums):
        changed = sorted(inputs.symmetric_difference(checksums))
        raise ValueError(f"frozen input inventory changed: {changed}")
    for name, expected in checksums.items():
        if hashlib.sha256((SUITE / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f"frozen input checksum mismatch: {name}")


def checked_input(entry):
    p = SUITE / entry["path"]
    data = p.read_bytes()
    if hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise ValueError(f"frozen source checksum mismatch: {p}")
    return data


def stage(case, work):
    src = work / "src"
    for context in case.get("context_deps", []):
        checked_input(context)
    # Reuse compiled ancestor interfaces only within the exact named closure.
    # A changed version, missing ancestor or different name gets its own root.
    closure = [(entry["module"], entry["sha256"]) for entry in case["deps"]]
    key = hashlib.sha256(json.dumps(closure).encode()).hexdigest()
    ancestors = LOCAL.path / "ancestors" / key
    ancestors.mkdir(parents=True, exist_ok=True)
    (work / "ancestors").symlink_to(ancestors, target_is_directory=True)
    paths = []
    names = set()
    for entry in [*case["deps"], case["main"]]:
        name = entry["module"]
        if name in names:
            raise ValueError(f"duplicate ancestor module {name}")
        names.add(name)
        base = src if entry is case["main"] else ancestors
        path = base.joinpath(*name.split(".")).with_suffix(".agda")
        payload = checked_input(entry)
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
        paths.append(path)
    return paths[-1], paths[:-1]


def agda_check(case, main, work, env):
    p = command(["agda", *(["--safe"] if case.get("native_safe") else []),
                 "--no-libraries", "-i", work / "src", "-i", work / "ancestors",
                 "-i", LOCAL.context, "-i", LOCAL.stdlib, main], work / "src", env)
    if p.returncode not in (0, 42):
        checked(p)
    return p


class DumpError(RuntimeError):
    """A diagnostic returned by the official scope checker."""


def close_dump(child):
    child.stdin.close()
    try:
        child.wait(timeout=5)
    except subprocess.TimeoutExpired:
        child.kill()
        child.wait()


def scope_bundle(main, deps, includes, env):
    # A pool worker handles requests serially. Its child lives across cases,
    # including the edit from the authored file to the canonical rendering.
    child = getattr(LOCAL, "dumpd", None)
    if child is None or child.poll() is not None:
        child = subprocess.Popen([DUMP, "--daemon", "-i", STD], cwd=LOCAL.path, env=env,
                                 stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                 text=True, encoding="utf-8")
        LOCAL.dumpd = child
        Finalize(child, close_dump, args=(child,), exitpriority=1)
    request = {"cmd": "dump", "main": str(main), "deps": list(map(str, deps)),
               "includes": list(map(str, includes))}
    child.stdin.write(json.dumps(request) + "\n")
    child.stdin.flush()
    if not select.select([child.stdout], [], [], 180)[0]:
        child.kill()
        child.wait()
        raise RuntimeError("agda-dumpd request timed out")
    line = child.stdout.readline()
    if not line:
        raise RuntimeError(f"agda-dumpd closed its output (exit {child.poll()})")
    response = json.loads(line)
    if not response["ok"]:
        raise DumpError(response["error"])
    if len(response["dep_sexprs"]) != len(deps) or not response["sexpr"].startswith("(module "):
        raise ValueError("invalid agda-dumpd bundle")
    return response


def frontend(case, work, env):
    main, _ = stage(case, work)
    includes = [work / "src", work / "ancestors"]
    if case.get("scope") != "session":
        includes.append(LOCAL.context)
    counters = {"agda_scope_dumps": 0}

    def dump():
        counters["agda_scope_dumps"] += 1
        # S1 consumes only the main IR. The scope checker discovers its entire
        # user import closure in the staged directories on each request.
        wire = scope_bundle(main, [], includes, env)["sexpr"]
        for root in includes[:2]:
            if any(root.rglob("*.agdai")):
                raise RuntimeError("scope dump wrote a user interface")
        return wire

    def engine(operation, path):
        return checked(command([ENGINE, operation, path], work, env))

    first = work / "before.sexp"
    first.write_text(dump())
    source = engine("roundtrip", first)
    if source.startswith("-- parse error") or "module " + case["main"]["module"] not in source:
        raise ValueError("native renderer failed to decode the scoped module")
    main.write_text(source)
    try:
        after = dump()
    except DumpError as exc:
        check_infrastructure(str(exc))
        return dict(counters, accepted=False, roundtrip_reparse_fail=1, diagnostic=str(exc)[-900:])
    second = work / "after.sexp"
    second.write_text(after)
    canonical = []
    for path in (first, second):
        output = engine("canonical", path)
        if not output.startswith("(module "):
            raise ValueError("native canonical decoder rejected a scoped module")
        canonical.append(output)
    return dict(counters, accepted=canonical[0] == canonical[1],
                roundtrip_ast_drift=int(canonical[0] != canonical[1]))


def check_infrastructure(diagnostic):
    missing = ("does not exist", "unknown module prefix", "Failed to find source of module",
               "failed to open file", "ambiguous module name", "No such file or directory")
    if any(msg.lower() in diagnostic.lower() for msg in missing):
        raise RuntimeError("missing or ambiguous dependency: " + diagnostic[-1200:])


def run_prism_check(args, work, env):
    # Match Backend.Switch's 120000 ms readProcessAt and its status 124.
    # A timed-out Lean elaborator is a child of agda2lean. Reap the whole
    # group before the private source tree disappears or another case starts.
    argv = [str(a) for a in args]
    with subprocess.Popen(argv, cwd=work, env=env, text=True, encoding="utf-8",
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          start_new_session=True) as child:
        marker = LOCAL.path.parent / f"process-group-{child.pid}"
        marker.touch()
        try:
            try:
                out, err = child.communicate(timeout=120)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                out, err = child.communicate()
                return subprocess.CompletedProcess(argv, 124, out, err + "\nprocess timeout"), True
            return subprocess.CompletedProcess(argv, child.returncode, out, err), False
        finally:
            marker.unlink(missing_ok=True)


def verify(case, work, env):
    main, deps = stage(case, work)
    start = perf_counter()
    native = agda_check(case, main, work, env)
    native_seconds = perf_counter() - start
    native_ok = native.returncode == 0
    diagnostic = native.stdout + native.stderr
    expected_ok = case["expected"] == "accept"
    prism_work = work / "prism"
    start = perf_counter()
    try:
        scoped = scope_bundle(main, deps, [work / "src", work / "ancestors", LOCAL.context], env)
        if scoped.get("check_errors"):
            raise DumpError("\n".join(scoped["check_errors"]))
    except DumpError as exc:
        scope_error = str(exc)
        check_infrastructure(scope_error)
        p = subprocess.CompletedProcess([DUMP], 10, "", scope_error)
        timed_out = False
    else:
        bundle = work / "bundle.sexp"
        bundle.write_text("(bundle " + "\n".join([*scoped["dep_sexprs"], scoped["sexpr"]]) + ")")
        args = [PRISM, "prism-check", "--lib-dir", BUILD / "lib/lean", "--work-dir", prism_work,
                "--sexpr-bundle", bundle]
        p, timed_out = run_prism_check(args, work, env)
    prism_seconds = perf_counter() - start
    if not timed_out and p.returncode not in (0, 10, 11, 20):
        checked(p)
    bot = p.returncode == 20
    fallback = bot or timed_out
    accepted = native_ok if fallback else p.returncode == 0
    # Always preserve a false acceptance, even when the oracle also disagrees.
    if expected_ok or not accepted:
        check_infrastructure(p.stderr + p.stdout + diagnostic)
        if native_ok != expected_ok:
            raise ValueError("native Agda disagrees with archive: " + diagnostic[-1200:])
        if not native_ok and not re.search(case["diagnostic"], diagnostic, re.I):
            raise ValueError("different native rejection: " + diagnostic[-1200:])
    # Session 1 freezes valid Agda bundles including known narrow Prism inputs.
    # A definitive Prism rejection is measured separately from a BOT fallback.
    return {"accepted": accepted, "prism_accepted": None if fallback else accepted,
            "prism_exit": p.returncode, "native_accepted": native_ok,
            "prism_seconds": round(prism_seconds, 6), "native_seconds": round(native_seconds, 6),
            "prism_false_rejection": int(native_ok and not accepted),
            "prism_bot_fallback": int(bot), "agda_scope_dumps": 1,
            "agda_fallbacks": int(fallback), "prism_timeout_fallback": int(timed_out),
            "prism_slow_slice": len(list(prism_work.glob("SlowSlice_*.agda"))),
            "diagnostic": (p.stderr + p.stdout) if p.returncode else ""}


def replay(case, work, env):
    before, after = case["first"], case["second"]
    plan_inputs = [before["code"], after["code"], before["spec"], after["spec"],
                   case["locked_plan"], case["plan"]]
    args = [["plan", *(SUITE / p for p in plan_inputs)]]
    if case.get("lift"):
        args.append(["lift", *[SUITE / p for p in (case["base"], after["code"],
                                                    after["spec"], case["lift"])]])
    args.append(["cas", SUITE / case["store"], case["tip"], work / "store",
                 *[SUITE / after[k] for k in ("code", "spec", "memory", "shape")]])
    for arg in args:
        checked(command([Path(env["GRON_DRIVER_DIR"]) / "GronReplay", *arg], work, env, timeout=600))
    return {"accepted": True, "checked": [a[0] for a in args]}


def native_roundtrip(case, work, env):
    path = SUITE / case["sexpr"]
    data = path.read_bytes()
    if len(data) != case["bytes"] or hashlib.sha256(data).hexdigest() != case["sha256"]:
        raise ValueError("Render wire input checksum mismatch")
    start = perf_counter()
    output = checked(command([ENGINE, "roundtrip", path], work, env))
    elapsed = perf_counter() - start
    rule = re.search(r"(?ms)^([ ]*)(?:postulate +)?reserved-rule\s*:(.*?)(?=^\1\S|\Z)", output)
    words = re.findall(r'"([a-z]+)"', rule[2]) if rule else []
    if "module Gen.T1.Render where" not in output or words != case["keywords"]:
        raise ValueError("missing Render module or altered keyword chain in native output")
    return {"accepted": elapsed < 1, "roundtrip_seconds": round(elapsed, 6),
            "input_bytes": len(data), "output_bytes": len(output.encode()),
            "keyword_count": len(words)}


def pool_worker(tmp, needs_agda):
    # Each worker and all of its ordinary compiler subprocesses share one
    # process group, allowing a false acceptance to stop pending checks.
    os.setsid()
    (Path(tmp) / f"process-group-{os.getpid()}").touch()
    setup_worker(tmp, needs_agda)


def stop_workers(tmp):
    for marker in Path(tmp).glob("process-group-*"):
        pid = int(marker.name.removeprefix("process-group-"))
        try:
            os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def setup_worker(tmp, needs_agda=True):
    worker = Path(tempfile.mkdtemp(prefix="worker-", dir=tmp))
    LOCAL.path = worker
    LOCAL.bin = worker / "bin"
    LOCAL.bin.mkdir()
    if not needs_agda:
        return
    LOCAL.stdlib = worker / "stdlib"
    installed_stdlib(LOCAL.stdlib)
    # Driver's nested compiler commands pass the distribution stdlib path.
    # Redirect that argument even for subprocesses launched inside Lean.
    for name, binary in (("agda", shutil.which("agda")), ("dump", str(DUMP))):
        if not binary:
            raise RuntimeError(f"missing {name}")
        shim = LOCAL.bin / name
        audit = ""
        if name == "agda":
            audit = ('if [[ $PWD == */agda_original_* && -n "${GRON_ORIGINAL_LOG:-}" ]]; then\n'
                     '  printf "%s\\n" "$PWD" >> "$GRON_ORIGINAL_LOG"\nfi\n')
        shim.write_text("#!/usr/bin/env bash\nset -euo pipefail\n" + audit + "args=()\n"
                        f"for arg do if [[ $arg == {shlex.quote(str(STD))} ]]; then "
                        f"arg={shlex.quote(str(LOCAL.stdlib))}; fi; args+=(\"$arg\"); done\n"
                        f"exec {shlex.quote(binary)} \"${{args[@]}}\"\n")
        shim.chmod(0o755)
    LOCAL.context = worker / "context"
    shutil.copytree(ROOT / "Context", LOCAL.context / "Context",
                    ignore=shutil.ignore_patterns("*.agdai"))
    historical = SUITE / "corpus/context/Context"
    if historical.exists():
        shutil.copytree(historical, LOCAL.context / "Context", dirs_exist_ok=True)


def run_case(case, drivers):
    layer = case["layer"]
    start = perf_counter()
    with tempfile.TemporaryDirectory(dir=LOCAL.path) as tmp:
        work = Path(tmp)
        env = current_env(LOCAL.path)
        originals = work / "original-source-checks.log"
        env["GRON_ORIGINAL_LOG"] = str(originals)
        env["PATH"] = str(LOCAL.bin) + os.pathsep + env["PATH"]
        if drivers:
            env["GRON_DRIVER_DIR"] = str(drivers)
            env["GRON_INDEPENDENT_SESSION"] = str(drivers / "IndependentSession")
        try:
            if case.get("curated"):
                from gron_stress_curated import run as run_curated
                result = run_curated(case, work, env)
            elif layer == "S1":
                result = frontend(case, work, env)
            elif layer == "S2":
                result = verify(case, work, env)
            elif layer == "S3":
                result = replay(case, work, env)
            else:
                result = native_roundtrip(case, work, env)
            result.setdefault("agda_fallbacks", result.get("prism_bot_fallback", 0))
            # A disconnected bundle may typecheck several roots in one audit.
            result["agda_original_confirmations"] = (
                len(set(originals.read_text().splitlines())) if originals.exists() else 0)
            ok = result["accepted"] == (case["expected"] == "accept")
            if result.get("native_accepted") and result.get("prism_false_rejection"):
                ok = case["expected"] == "accept"
        except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
            result = {"error": str(exc)}
            ok = False
        for field in ("diagnostic", "error"):
            if field in result:
                message = str(result[field]).replace(str(work), "<case>")
                message = message.replace(str(LOCAL.path), "<worker>").replace(str(ROOT), "<repo>")
                limit = 900 if field == "diagnostic" else 3500
                result[field] = message if len(message) <= limit else message[-limit:].partition("\n")[2] or message[-limit:]
        return {"id": case["id"], "layer": layer, "expected": case["expected"],
                "passed": ok, "seconds": round(perf_counter() - start, 6), **result}


def run_layer(cases, executor, jobs, cancel):
    start = perf_counter()
    source = iter(cases)
    records = []
    pending = set()
    while True:
        while len(pending) < jobs:
            case = next(source, None)
            if case is None:
                break
            pending.add(executor(case))
        if not pending:
            break
        done, pending = wait(pending, return_when=FIRST_COMPLETED)
        for future in done:
            r = future.result()
            records.append(r)
            false_accept = r["expected"] == "reject" and r.get("accepted") is True
            status = "FALSE ACCEPT" if false_accept else "PASS" if r["passed"] else "FAIL"
            print(f"{r['layer']} {status} {r['id']} ({r['seconds']:.3f}s)", flush=True)
            if not r["passed"]:
                print(r.get("error", r.get("diagnostic", "")), file=sys.stderr, flush=True)
            if false_accept:
                cancel()
                return sorted(records, key=lambda r: r["id"]), round(perf_counter() - start, 6)
    return sorted(records, key=lambda r: r["id"]), round(perf_counter() - start, 6)


def baseline_regressions(current, previous):
    metrics = ["roundtrip_ast_drift", "roundtrip_reparse_fail", "native_engine_stack_fallback"]
    # A production timeout or BOT records an Agda verdict. The baseline did
    # not observe a raw Prism acceptance to compare to a later rejection.
    if previous.get("prism_exit") == 0:
        metrics.append("prism_false_rejection")
    return [k for k in metrics if current.get(k, 0) > previous.get(k, 0)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--layer", choices=["S1", "S2", "S3", "S4", "all"], default="all")
    parser.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    parser.add_argument("--report-json", type=Path)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    layers = ["S1", "S2", "S3", "S4"] if args.layer == "all" else [args.layer]
    manifest_path = SUITE / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    verify_inventory(manifest)
    cases = list(manifest["cases"])
    if "S2" in layers:
        from gron_stress_curated import cases as curated_cases
        cases.extend(dict(c, layer="S2", curated=True) for c in curated_cases(manifest))
    if "S1" in layers and sum(c["layer"] == "S1" and c["expected"] == "accept" for c in cases) < 80:
        raise ValueError("S1 must exercise at least 80 positive inputs")
    if "S2" in layers and sum(c["layer"] == "S2" and c["expected"] == "reject" for c in cases) < 30:
        raise ValueError("S2 must exercise at least 30 negative inputs")
    if len(set(c["id"] for c in cases)) != len(cases):
        raise ValueError("duplicate case IDs")
    tools = []
    if {"S1", "S2"}.intersection(layers):
        tools.append(DUMP)
    if "S2" in layers:
        tools.append(PRISM)
    if {"S1", "S2", "S4"}.intersection(layers):
        tools.append(ENGINE)
    for bin_path in tools:
        if not os.access(bin_path, os.X_OK):
            parser.error(f"missing {bin_path.name}; run ./build.sh")
    (ROOT / "tmp").mkdir(exist_ok=True)
    drivers = compile_drivers(layers) if {"S2", "S3"}.intersection(layers) else None
    baseline = SUITE / "baseline-metrics.json"
    if args.report_json is None:
        if not baseline.exists() and args.layer == "all":
            args.report_json = baseline
        else:
            args.report_json = ROOT / "tmp/gron-stress-report.json"
    recorded = {}
    if baseline.exists():
        old = json.loads(baseline.read_text())
        recorded = {r["id"]: r for name, layer in old["layers"].items() if name in layers
                    for r in layer["cases"]}
        current = {c["id"]: c for c in cases}
        for key, case in recorded.items():
            if key not in current or current[key]["expected"] != case["expected"]:
                raise ValueError(f"frozen case missing or polarity changed: {key}")
    start = perf_counter()
    report = {"manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
              "jobs": args.jobs, "layers": {}, "false_positives": 0,
              "lean_toolchain": (ROOT / "runtime/lean-prism/lean-toolchain").read_text().strip(),
              "tools": {"prism": PRISM.is_file(), "agda_scope_dump": DUMP.is_file(),
                        "harness_engine": ENGINE.is_file(),
                        "ghc_gron_replay": bool(drivers and (drivers / "GronReplay").is_file())}}
    with tempfile.TemporaryDirectory(dir=ROOT / "tmp", prefix="gron-stress-") as tmp:
        needs_agda = bool({"S1", "S2"}.intersection(layers))
        with ProcessPoolExecutor(args.jobs, initializer=pool_worker, initargs=(tmp, needs_agda)) as pool:
            for layer in layers:
                inputs = [c for c in cases if c["layer"] == layer]
                if not inputs:
                    raise ValueError(f"empty layer {layer}")
                # S4 measures the native process after all other workers have drained.
                records, elapsed = run_layer(inputs, lambda c: pool.submit(run_case, c, drivers),
                                             1 if layer == "S4" else args.jobs, lambda: stop_workers(tmp))
                if baseline.exists():
                    for r in records:
                        regressions = baseline_regressions(r, recorded.get(r["id"], {}))
                        if regressions:
                            r["passed"] = False
                            r["regressions"] = regressions
                            print(f"{layer} REGRESSION {r['id']} {', '.join(regressions)}", file=sys.stderr)
                false_accepts = sum(r["expected"] == "reject" and r.get("accepted") is True
                                    for r in records)
                report["false_positives"] += false_accepts
                summary = {"seconds": elapsed, "positives": sum(r["expected"] == "accept" for r in records),
                           "negatives": sum(r["expected"] == "reject" for r in records),
                           "failures": sum(not r["passed"] for r in records),
                           "false_positives": false_accepts,
                           **{k: sum(r.get(k, 0) for r in records) for k in COUNTERS}}
                print(layer, json.dumps(summary), flush=True)
                report["layers"][layer] = dict(summary, cases=records)
                if false_accepts:
                    break
    report["seconds"] = round(perf_counter() - start, 6)
    report.update({k: sum(l[k] for l in report["layers"].values()) for k in COUNTERS})
    failed = any(l["failures"] for l in report["layers"].values())
    if args.report_json.resolve() == baseline and (failed or len(layers) != 4):
        print("Incomplete run. Writing diagnostics to tmp/gron-stress-report.json", file=sys.stderr)
        args.report_json = ROOT / "tmp/gron-stress-report.json"
    args.report_json.parent.mkdir(parents=True, exist_ok=True)
    args.report_json.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
