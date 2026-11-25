#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
lake build LojitaCtx:static Lojita:static test-io-showcase
cc -std=c11 -static -O2 -Wall -Wextra -Werror runtime/lojita-sandbox.c -o "$scratch/sandbox"
.lake/build/bin/test-io-showcase "$scratch"
mkdir "$scratch/fixtures" "$scratch/seed"
for exe in base refined argvEcho signalPoll; do
  readelf -h "$scratch/$exe" | grep -q 'Type:.*EXEC'
  if readelf -l "$scratch/$exe" | grep -q 'INTERP'; then
    echo "Expected a statically linked executable: $exe" >&2
    exit 1
  fi
done
for sample in binary empty unterminated replay; do
  case "$sample" in
    binary) printf 'ab\n\n\xff\0c\r\nlast' > "$scratch/fixtures/input" ;;
    replay) python3 -c 'import sys; sys.stdout.buffer.write(bytes(range(256)) * 2)' > "$scratch/fixtures/input" ;;
    empty) : > "$scratch/fixtures/input" ;;
    unterminated) printf '0123456789' > "$scratch/fixtures/input" ;;
  esac
  for exe in base refined; do
    out="$scratch/work-$sample-$exe"
    mkdir "$out"
    "$scratch/sandbox" "$scratch/fixtures" "$scratch/seed" "$out" - "$scratch/$exe" 5000 </dev/null 2> >(cat >&2) | cat > "$scratch/$exe.out"
    cmp "$scratch/fixtures/input" "$scratch/$exe.out"
  done
done
mkdir "$scratch/argv-work"
python3 - "$scratch" <<'PYTHON'
import subprocess
import sys
from pathlib import Path
root = Path(sys.argv[1])
arg = b"a\xffb"
completed = subprocess.run(
    [root / "sandbox", root / "fixtures", root / "seed", root / "argv-work", "-",
     root / "argvEcho", "5000", arg],
    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=7,
)
if completed.returncode or completed.stdout != arg:
    raise SystemExit(f"argvEcho status={completed.returncode} output={completed.stdout!r} stderr={completed.stderr!r}")
PYTHON
python3 Test/scripts/posix-signals.py "$scratch/signalPoll"
echo 'Gate 5 passed: T15/T16 commute, both static executables reproduced each fixture inside LinuxIso, byte-valued argv survived, and the checker rejected the wrong capabilities.'
