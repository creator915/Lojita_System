#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"
root=$PWD
python3 scripts/embed_prompts.py --check
version=$(agda --version)
if [[ "$version" != "Agda version 2.6.3" ]]; then
  echo "Expected Agda 2.6.3, found $version" >&2
  exit 1
fi

scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
export AGDA_DIR=$scratch/agda-dir
mkdir -p "$AGDA_DIR"
repo=$scratch/repo
build=$scratch/build
mkdir -p "$repo"/{Test,Verification/Generated/{T0,T1},runtime/tools} "$build" "$scratch"/{env,ghc}
# check.sh and Agda write interfaces next to their inputs. Use the exact
# checkout sources in a private include tree, including the real FFI runtime.
cp -R Backend Code Context Meta OwnershipIO Store "$repo/"
cp runtime/*.hs runtime/*.c runtime/*.h "$repo/runtime/"
cp runtime/tools/*.hs runtime/tools/*.c "$repo/runtime/tools/"
cp Code.agda Ownership.agda OwnershipIO.agda check.sh "$repo/"
cp Test/PromptExamplesCheck.agda "$repo/Test/"
(cd "$repo" && ./check.sh Code/Prompt.agda)

quiet() {
  if ! "$@" >"$scratch/build.log" 2>&1; then
    tail -100 "$scratch/build.log" >&2
    return 1
  fi
}
echo "Building the protocol checker, dump and sandbox relays"
quiet ghc -O0 -package Agda -outputdir "$scratch/ghc" dump/Dump.hs -o "$scratch/dump"
quiet cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o "$scratch/term-relay"
quiet cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/fs-relay.c -o "$scratch/fs-relay"
quiet cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/net-relay.c -o "$scratch/net-relay"
quiet cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/git-relay.c -o "$scratch/git-relay"
quiet cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/web-relay.c -o "$scratch/web-relay"
cd "$repo"
quiet agda --compile --ghc-flag=-O0 "--ghc-flag=-i$repo/runtime" "--ghc-flag=-i$repo/runtime/tools" "--ghc-flag=$repo/runtime/cli_host.c" "--compile-dir=$build" \
  -i . -i /usr/share/agda-stdlib Test/PromptExamplesCheck.agda
"$build/PromptExamplesCheck" env "$scratch/candidate" "$scratch/term-relay" "$scratch/resources" \
  > "$scratch/env/SessionEnv.agda"

cd "$scratch"
python3 - "$root" "$scratch" <<'PY'
import collections
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

root, tmp = map(Path, sys.argv[1:])
repo, build = tmp / "repo", tmp / "build"
checker = build / "PromptExamplesCheck"
sources = {}
roles = {}
actions = {}
dumps = {}
impl = tmp / "examples"


def run(args, cwd=tmp, output=None):
    result = subprocess.run(args, cwd=cwd, text=True, stdout=output or subprocess.PIPE,
                            stderr=subprocess.PIPE)
    if result.returncode:
        sys.exit(f"{' '.join(map(str, args))}\n{(result.stdout or '')[-6000:]}\n{result.stderr[-6000:]}")
    return result.stdout


def fences(md):
    # Preserve every Agda source, including standalone, unnamed fences.
    lines = md.splitlines(keepends=True)
    pos = 0
    while pos < len(lines):
        start = pos
        tag = lines[pos].rstrip('\n')
        pos += 1
        if not tag.startswith('```'):
            continue
        end = pos
        while end < len(lines) and lines[end].rstrip('\n') != '```':
            end += 1
        if end == len(lines) or not re.fullmatch(r'```(sexp|agda(?: [\w-]+)?)', tag):
            sys.exit(f"Invalid example fence on line {start + 1}: {tag}")
        yield tag[3:], ''.join(lines[pos:end]), start, end + 1
        pos = end + 1


def remember(text, where, role=None):
    name = re.search(r'^module ([\w.]+) where$', text, re.M)
    if not name or not all(p.isidentifier() for p in name[1].split('.')):
        sys.exit(f"{where}: expected a complete named Agda module")
    key = (name[1], text.removesuffix('\n'))
    sources.setdefault(key, where)
    if role:
        roles[key] = role
    return key


embedded = (root / "Code/Prompt.agda").read_bytes()
for symbol in ("PromptHeader", "nativeHeader", "closedWorldTemplate", "sessionTemplate",
               "sessionTransportHelp", "refuteExtraText", "nodePrompt", "showProblem", "showImplProblem",
               "showLiftProblem", "showRefuteProblem"):
    if not re.search(rb'^' + symbol.encode() + rb' : ', embedded, re.M):
        sys.exit(f"Missing Code.Prompt export: {symbol}")
if b'\nnativeHeader = ""\n' not in embedded:
    sys.exit("Unexpected nativeHeader")

for prompt, symbol, kind in [
    ("node-closed-world", "closedWorldTemplate", "node"),
    ("session-open-world", "sessionTemplate", "session"),
]:
    path = root / "prompts" / (prompt + ".md")
    raw = path.read_bytes()
    literal = re.search(rb'^' + symbol.encode() + rb' = (".*")$', embedded, re.M)
    if not literal or json.loads(literal[1]).encode() != raw:
        sys.exit(f"{path}: embedded bytes differ")
    md = raw.decode()
    lines = md.splitlines(keepends=True)
    blocks = list(fences(md))
    for i, (tag, text, start, end) in enumerate(blocks):
        where = f"{path.name}:{start + 1}"
        if tag != 'sexp':
            key = remember(text, where)
            sources[key] = where
            # These standalone blocks show interfaces supplied by the harness.
            if tag == 'agda' and key[0] in ('SwitchSpec', 'Gen.U0.Root'):
                roles[key] = 'spec'
            continue

        for following, _, next_start, next_end in blocks[i + 1:]:
            if not following.startswith('agda ') or ''.join(lines[end:next_start]).strip():
                break
            end = next_end
        wire = tmp / f"{kind}-{start}.sexp"
        wire.write_text(''.join(lines[start:end]))
        fields = wire.with_suffix('.fields')
        fields.mkdir()
        run([checker, kind, fields, wire])
        for field in fields.iterdir():
            if field.name in ('entry', 'mode'):
                continue
            spec = field.name == 'specSrc' or field.name.startswith('subspec-')
            key = remember(field.read_text(), where, 'spec' if spec else 'impl')
            actions[key] = wire

# Dependencies normally see sealed implementations. Check each alternate
# specSrc in its own include tree so a same-named implementation cannot mask it.
by_module = collections.defaultdict(list)
for key in sources:
    by_module[key[0]].append(key)


def filename(key):
    return Path(*key[0].split('.')).with_suffix('.agda')


def write_module(world, key):
    dest = world / filename(key)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(key[1] + '\n')


defaults = {}
for name, variants in by_module.items():
    defaults[name] = next((v for v in variants if roles.get(v) != 'spec'), variants[0])
    write_module(impl, defaults[name])


def includes(world):
    return ['-i', world, '-i', tmp / 'env', '-i', repo, '-i', '/usr/share/agda-stdlib']


print(f"Checking {len(sources)} Agda sources from the Markdown prompts", flush=True)
for i, key in enumerate(sources):
    name, body = key
    world = impl
    if key != defaults[name]:
        world = tmp / f'variant-{i}'
        shutil.copytree(impl, world, ignore=shutil.ignore_patterns('*.agdai'))
        write_module(world, key)
    print(f"  {name}  ({sources[key]})", flush=True)
    args = [*includes(world), filename(key)]
    run(['agda', *args], cwd=world)
    ast = tmp / f'{i}.sexp'
    with ast.open('w') as output:
        run([tmp / 'dump', *args], cwd=world, output=output)
    role = roles.get(key, 'impl')
    if role != 'spec' and re.search(r'^main\s*:', body, re.M):
        role = 'io'
    run([checker, 'dump', role, ast])
    dumps[key] = ast

for name, base in [('Gen.T0.Base', 'Gen.T0.Base'), ('Gen.T1.Emph', 'Gen.T0.Base'),
                   ('Gen.B1.Root0', 'Gen.B0.Root0')]:
    spec, = [v for v in by_module[name] if v in actions and roles[v] == 'spec']
    run([checker, 'squares', actions[spec], dumps[defaults[base]], dumps[defaults[name]], dumps[spec]])
run([checker, 'refutation', dumps[defaults['SwitchSpec']], dumps[defaults['Refute']]])
print("Specifications, refutation, LiftSpec and one-to-many PolyTransport squares passed", flush=True)

if '(entry "Gen.T1.Emph.app")' not in (root / "prompts/session-open-world.md").read_text():
    sys.exit("session-open-world.md: expected (entry \"Gen.T1.Emph.app\") build-exe example")
main_body = "\n".join([
    "{-# OPTIONS --guardedness #-}",
    "module Main where",
    "open import Agda.Builtin.IO using (IO)",
    "open import Agda.Builtin.Unit using (⊤)",
    "open import OwnershipIO.WorldRunner using (runCliIO)",
    "import Gen.T1.Emph as Entry",
    "main : IO ⊤",
    "main = runCliIO Entry.app",
])
defaults['Main'] = ('Main', main_body)
write_module(impl, defaults['Main'])

for name in ['Main', 'EmphLoss', 'TerminalProbe', 'FsNetProbe', 'LocalCounter', 'FuzzProbe']:
    run(['agda', '--compile', '--ghc-flag=-O0', f'--ghc-flag=-i{repo}/runtime',
         f'--ghc-flag=-i{repo}/runtime/tools', f'--ghc-flag={repo}/runtime/cli_host.c',
         f'--compile-dir={build}', *includes(impl), filename(defaults[name])], cwd=impl)


def execute(name, expected):
    result = subprocess.run([build / name], cwd=tmp, text=True, capture_output=True, timeout=120)
    print(f"{name} [{result.returncode}] {result.stdout.strip()}", flush=True)
    if result.returncode != expected:
        sys.exit(result.stderr or f"{name}: expected exit {expected}")
    return result.stdout


candidate = tmp / 'candidate'
candidate.symlink_to(build / 'Main')
execute('TerminalProbe', 0)
execute('FsNetProbe', 0)
execute('LocalCounter', 0)
execute('FuzzProbe', 0)
candidate.unlink()
candidate.symlink_to(build / 'EmphLoss')
if 'input "*hello*" -> "*h*"' not in execute('FuzzProbe', 1):
    sys.exit("The shrinker did not report the shortest failing deletion of *hello*")
print("All prompt examples passed")
PY
