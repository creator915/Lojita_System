#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
mkdir "$scratch/tmp"
export TMPDIR="$scratch/tmp"
flags=(-std=c11 -static -O2 -Wall -Wextra -Werror)
cc "${flags[@]}" runtime/lojita-sandbox.c -o "$scratch/launcher"
cc "${flags[@]}" Test/scripts/sandbox-probe.c -o "$scratch/probe"
lake build Lojita.Sandbox.LinuxIso
python3 Test/scripts/sandbox-gates.py "$scratch/launcher" "$scratch/probe"
lake env lean --run Test/scripts/SandboxOwned.lean "$scratch/launcher" "$scratch/probe"
if [[ -n $(find "$TMPDIR" -mindepth 1 -print -quit) ]]; then
  echo "Sandbox staging leaked files in $TMPDIR" >&2
  exit 1
fi
echo "Gate 4 passed with no mount or staging leaks."
