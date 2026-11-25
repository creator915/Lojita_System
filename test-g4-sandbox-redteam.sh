#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if [[ $# -gt 1 || ${1:-} != "" && ${1:-} != "--with-apparmor-userns" ]]; then
  echo "Usage: $0 [--with-apparmor-userns]" >&2
  exit 2
fi
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
mkdir "$scratch/tmp"
export TMPDIR="$scratch/tmp"
flags=(-std=c11 -static -O2 -Wall -Wextra -Werror)
cc "${flags[@]}" runtime/lojita-sandbox.c -o "$scratch/launcher"
cc "${flags[@]}" Test/scripts/sandbox-probe.c -o "$scratch/probe"
lake build test-sandbox-owned treeCasNativeTest
python3 Test/scripts/sandbox-gates.py "$scratch/launcher" "$scratch/probe" .lake/build/bin/treeCasNativeTest
.lake/build/bin/test-sandbox-owned "$scratch/launcher" "$scratch/probe"
if [[ -n $(find "$TMPDIR" -mindepth 1 -print -quit) ]]; then
  echo "Sandbox staging leaked files in $TMPDIR" >&2
  exit 1
fi
if (( EUID == 0 )) || [[ ${1:-} == "--with-apparmor-userns" ]]; then
  Test/scripts/sandbox-userns.sh "$scratch/launcher" "$scratch/probe"
fi
bash Test/scripts/treecas-native.sh
echo "Gate 4 passed with no mount or staging leaks."
