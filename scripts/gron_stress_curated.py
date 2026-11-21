"""Replay the frozen submission, narrowing and hybrid-slice controls for S2."""

from collections import Counter
import json
from pathlib import Path
import shutil
import subprocess
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / 'Test/gron-stress/corpus/curated'
BUILD = ROOT / 'runtime/lean-prism/.lake/build'


def cases(manifest):
    return manifest['curated']


def _exec(cmd, cwd, env, **kwargs):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True,
                          text=True, **kwargs)


def _dump(env):
    return shutil.which('dump', path=env['PATH']) or ROOT / 'dump/dump'


def _require(ok, detail):
    if not ok:
        raise RuntimeError(detail[-3000:])


def _submission(case, work, env):
    # The scripted service returns the recorded wire verbatim. It writes the next
    # prompt only if the outer harness actually asks for a corrected submission.
    ws = work / 'session'
    ws.mkdir()
    proposal = ws / 'proposal.sexp'
    shutil.copyfile(CORPUS / case['proposal'], proposal)
    # The outer runner resolves dump/dump relative to its repository argument.
    # Route that executable through the same per-worker stdlib shim as Prism.
    repo = work / 'repo'
    repo.mkdir()
    for directory in ('Context', 'runtime', 'OwnershipIO', 'Verification'):
        (repo / directory).symlink_to(ROOT / directory)
    (repo / 'dump').mkdir()
    (repo / 'dump/dump').symlink_to(_dump(env))
    args = [env['GRON_INDEPENDENT_SESSION'], repo, ws, 'T2', CORPUS / case['spec'], proposal]
    if 'recovery' in case:
        recovery = ws / 'recovery.sexp'
        shutil.copyfile(CORPUS / case['recovery'], recovery)
        args.append(recovery)
    # The first submission on a worker builds the entire sealed Context view.
    ret = _exec(args, work, dict(env, CODETRANSPORT_BACKEND='prism'), timeout=900)
    verdict = ws / 'trees/T2/verdict'
    _require(ret.returncode == 0 and verdict.exists(), ret.stdout + ret.stderr)
    retry = ws / 'recovery.sexp.prompt'
    if retry.exists():
        diagnostic = retry.read_text().rsplit('\nTRANSIENT DIAGNOSTIC\n', 1)[-1]
        _require(any(s in diagnostic for s in case['diagnostic']), diagnostic)
        _require(verdict.read_text().strip() == 'ok', ret.stdout)
        return False
    if 'verdict' in case:
        _require(verdict.read_text().strip() == case['verdict'], ret.stdout)
    return True


def _subspec(case, work, env, ledger):
    text = (CORPUS / case['main']).read_text()
    args = {'main_block': text, 'allow_postulates': True}
    rpc = {'jsonrpc': '2.0', 'id': 1, 'method': 'tools/call',
           'params': {'name': 'check_agda', 'arguments': args}}
    ctx = work / 'mcp'
    ctx.mkdir()
    ret = _exec([BUILD / 'bin/agda2lean', 'mcp', '--mode', 'node',
                 '--repo', ROOT, '--lib-dir', BUILD / 'lib/lean', '--ir-dir', BUILD / 'ir',
                 '--dump-bin', _dump(env), '--workspace', work,
                 '--ctx-dir', ctx, '--narrow-log', ledger],
                work, env, timeout=180, input=json.dumps(rpc) + '\n')
    _require(ret.returncode == 0, ret.stderr)
    return not json.loads(ret.stdout)['result']['isError']


def _slice(case, work, env):
    src = work / 'src'
    src.mkdir()
    deps = []
    for rel in [*case.get('deps', []), case['main']]:
        path = src / Path(rel).name
        shutil.copyfile(CORPUS / rel, path)
        if rel != case['main']:
            deps += ['--dep', path]
    main = src / Path(case['main']).name
    start = perf_counter()
    agda = _exec(['agda', '--no-libraries', '-i', src, '-i', '/usr/share/agda-stdlib',
                  main], src, env, timeout=180)
    native_seconds = perf_counter() - start
    expected = case['expected'] == 'accept'
    if not expected:
        _require('true' in agda.stdout and 'false' in agda.stdout, agda.stdout + agda.stderr)
    _require((agda.returncode == 0) == expected, agda.stdout + agda.stderr)
    stage = work / 'prism'
    start = perf_counter()
    checked = _exec([BUILD / 'bin/agda2lean', 'prism-check', '--lib-dir', BUILD / 'lib/lean',
                     '--work-dir', stage, '--dump-bin', _dump(env),
                     *deps, '--main', main], src, env, timeout=180)
    prism_seconds = perf_counter() - start
    msg = checked.stdout + checked.stderr
    _require(checked.returncode in (0, 10, 11, 20), msg)
    if checked.returncode == 11:
        _require('does not exist' not in msg and 'unknown module prefix' not in msg, msg)
    accepted = checked.returncode == 0 or (checked.returncode == 20 and agda.returncode == 0)
    return dict(accepted=accepted, prism_bot_fallback=int(checked.returncode == 20),
                prism_seconds=round(prism_seconds, 6), native_seconds=round(native_seconds, 6),
                prism_slow_slice=len(list(stage.glob('SlowSlice_*.agda'))),
                prism_exit=checked.returncode, agda_exit=agda.returncode)


def run(case, work, env):
    if case['driver'] == 'slice':
        return _slice(case, work, env)
    if case['driver'] == 'submission':
        accepted = _submission(case, work, env)
        ledger = work / 'session/narrowing-events.jsonl'
    else:
        ledger = work / 'narrowing-events.jsonl'
        accepted = _subspec(case, work, env, ledger)
    counts = Counter(json.loads(line)['kind'] for line in ledger.read_text().splitlines()) if ledger.exists() else Counter()
    # An unexpected acceptance must reach the runner's fatal false-positive gate
    # even when acceptance also means the expected narrowing event was absent.
    if not accepted and 'event' in case:
        _require(counts[case['event']] > 0, f"{case['id']}: expected {case['event']}, observed {dict(counts)}")
    return dict(accepted=accepted, **{name: counts[name] for name in
                                      ('prism_bot_fallback', 'prism_slow_slice', 'roundtrip_ast_drift')})
