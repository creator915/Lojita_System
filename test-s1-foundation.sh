#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"

root=$(cd -- "$(dirname -- "$0")" && pwd -P)
cd "$root"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/v9-s1.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
export TMPDIR="$scratch"
export LOJITA_S1_RELAYS="$scratch/relays" LOJITA_S1_SCRATCH="$scratch/world" LOJITA_S1_ENV=session-one
mkdir -p "$LOJITA_S1_RELAYS" "$LOJITA_S1_SCRATCH"
ccflags=(-std=c11 -O2 -Wall -Wextra -Werror -static)
cc "${ccflags[@]}" runtime/term-relay.c -o "$LOJITA_S1_RELAYS/term-relay"
for tool in fs net git web; do
  cc "${ccflags[@]}" "runtime/tools/$tool-relay.c" -o "$LOJITA_S1_RELAYS/$tool-relay"
done

lake build
timeout 60s lake exe test-s1-foundation
# Compile an external client with only the object library on its search path.
export LOJITA_OBJECT_CONTEXT="$scratch/object-context"
lib="$root/.lake/build/lib/lean"
mkdir "$LOJITA_OBJECT_CONTEXT"
cp -R "$lib/LojitaCtx" "$lib"/LojitaCtx.* "$LOJITA_OBJECT_CONTEXT/"
leanbin=$(lean --print-prefix)/bin/lean
(
  cd "$scratch"
  export LEAN_PATH="$LOJITA_OBJECT_CONTEXT"
  printf '%s\n' 'import LojitaCtx' '#check LojitaCtx.Protocol.dual_involutive' > Closed.lean
  "$leanbin" Closed.lean
  printf '%s\n' 'import Lojita.WorldRunner' > Trusted.lean
  if "$leanbin" Trusted.lean >negative.log 2>&1; then
    echo "Trusted kernel is visible to a closed node" >&2
    exit 1
  fi
  grep -q 'unknown module prefix.*Lojita' negative.log
)
python3 - <<'PY'
from pathlib import Path
import os
import re

root = Path.cwd()
for f in (root / 'LojitaCtx').rglob('*.lean'):
    # The compiled Environment audit checks EIO by fully qualified name.
    # POSIX also has the unrelated, required Linux errno constructor Errno.EIO.
    if re.search(r'\b(?:IO|BaseIO|extern|implemented_by|unsafe|partial|sorry|axiom)\b', f.read_text()):
        raise SystemExit(f"unexpected effect, unchecked declaration or hole in {f}")
    # Catch a new pure module accidentally omitted from the environment audit.
    name = '.'.join(f.with_suffix('').parts[-2:])
    if not (Path(os.environ['LOJITA_OBJECT_CONTEXT']) / f.relative_to(root)).with_suffix('.olean').is_file():
        raise SystemExit(f"missing compiled object module {name}")
if re.search(r'\b(?:axiom|sorry|partial|unsafe)\b', Path('Lojita/Ownership/Core.lean').read_text()):
    raise SystemExit("unexpected unchecked definition in ownership kernel")
print("Verified the isolated object library and ownership declarations")
PY
