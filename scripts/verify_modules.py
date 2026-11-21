#!/usr/bin/env python3
"""Check every repository module, normalizing historical fixture filenames.

The fixtures intentionally reuse module names (examples/out/A, stored trees,
roundtrip-Ownership). Each is checked in its own include root so neither an
original nor a stale .agdai can accidentally satisfy a rendered module.
"""
from pathlib import Path
import os, re, shutil, subprocess, sys

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
MODE = sys.argv[1]
REQUESTED = set(sys.argv[2:])
STD = '/usr/share/agda-stdlib'
ENV = dict(os.environ, LC_ALL='C.UTF-8', LANG='C.UTF-8')
WORK = ROOT / 'tmp' / ('verify-' + MODE)
if WORK.exists():
    shutil.rmtree(WORK)
WORK.mkdir(parents=True)


def run(args, cwd=ROOT):
    p = subprocess.run([str(a) for a in args], cwd=cwd, env=ENV,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if p.returncode:
        raise RuntimeError(p.stdout + p.stderr)
    return p.stdout


def module_path(path):
    m = re.search(r'^\s*module\s+([^\s()]+)', path.read_text(), re.M)
    if not m:
        raise RuntimeError(f'No module header: {path}')
    return Path(m[1].replace('.', '/') + '.agda')


files = [Path(s) for s in run(['rg', '--files', '-g', '*.agda', '-g', '!Test/prism-corpus/negative/**', '-g', '!Test/gron-stress/corpus/**', '-g', '!runtime/**', '-g', '!tmp/**']).splitlines()]
files.sort()
primary = [p for p in files if p == module_path(p)]
fixtures = [p for p in files if p not in primary]
selected = [p for p in files if not REQUESTED or str(p) in REQUESTED]
missing = REQUESTED - {str(p) for p in selected}
if missing:
    raise SystemExit(f'Unknown modules: {missing}')
source = WORK / 'source'
rendered = WORK / 'rendered'
for directory in [source, rendered]:
    directory.mkdir()
    for p in primary:
        target = directory / p
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, target)
    for p in fixtures:
        if str(p).startswith('Verification/Generated/'):
            target = directory / module_path(p)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, target)

if MODE == 'roundtrip':
    run(['ghc', '-O2', '-threaded', '-package', 'Agda', 'dump/Dump.hs', '-o', 'dump/dump'])
    log = ROOT / 'tmp/build-main.log'
    p = subprocess.run(['agda', '--compile', '--ghc-flag=-O0', '--ghc-flag=-iruntime', '--ghc-flag=-iruntime/tools', '--compile-dir=tmp/tool-build',
                        '-i', '.', '-i', STD, 'Main.agda'], env=ENV,
                       stdout=log.open('w'), stderr=subprocess.STDOUT)
    if p.returncode:
        raise SystemExit(log.read_text())


def check(directory, name):
    return run(['agda', '-i', '.', '-i', STD, name], directory)


def render(directory, name, dest):
    wire = run([ROOT / 'dump/dump', '-i', '.', '-i', STD, name], directory)
    sexp = WORK / 'current.sexp'
    sexp.write_text(wire)
    code = run([ROOT / 'tmp/tool-build/Main', 'roundtrip', sexp])
    if code.startswith('-- parse error'):
        raise RuntimeError('Code.Parse rejected Dump output')
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(code)


failures = []
if MODE == 'roundtrip':
    for f in primary:
        if f not in selected:
            continue
        try:
            check(source, f)
            render(source, f, rendered / f)
            print(f'rendered {f}', flush=True)
        except RuntimeError as e:
            failures.append(str(f))
            print(f'FAIL dump/render {f}\n{e}', flush=True)

for f in selected:
    if str(f) in failures:
        continue
    try:
        if f in primary:
            check(rendered if MODE == 'roundtrip' else source, f)
        else:
            isolated = WORK / 'fixtures' / str(f).replace('/', '_')
            shutil.copytree(rendered if MODE == 'roundtrip' else source, isolated,
                            ignore=shutil.ignore_patterns('*.agdai'))
            # Baseline examples use A/C as context. Stored-tree leaves use the
            # matching A/B snapshots; plans/out use their nearest siblings.
            deps = list((ROOT / 'examples').glob('*.agda'))
            deps = [p for p in deps if p.name != 'roundtrip-Ownership.agda']
            if 'stored-tree' in str(f):
                deps += list((ROOT / 'examples/stored-tree/P').rglob('*.agda'))
            deps += list((ROOT / f.parent).glob('*.agda'))
            deps += [ROOT / f]
            for p in deps:
                target = isolated / module_path(p)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(p, target)
            name = module_path(f)
            check(isolated, name)
            if MODE == 'roundtrip':
                render(isolated, name, isolated / name)
                for cache in isolated.rglob('*.agdai'):
                    cache.unlink()
                check(isolated, name)
        print(f'PASS {MODE} {f}', flush=True)
    except RuntimeError as e:
        failures.append(str(f))
        print(f'FAIL {MODE} {f}\n{e}', flush=True)
print(f'{len(selected) - len(failures)}/{len(selected)} modules passed {MODE}', flush=True)
raise SystemExit(bool(failures))
