#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/v9-posix.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
export TMPDIR="$scratch"
umask 022
probe="$scratch/probe"
mkdir "$probe"
lake build Lojita:static LojitaCtx:static test-posix-channels
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o "$probe/term-relay"
suite=.lake/build/bin/test-posix-channels
timeout 120s "$suite" prepare "$probe"
cp Test/Posix/conformance.py "$probe/"
python3 "$probe/conformance.py" linux "$probe"

if command -v docker >/dev/null; then
  cleanroom() {
    docker run --rm --network none --read-only -u 65534:65534 --tmpfs /tmp \
      --mount "type=bind,src=$probe,dst=/probe,readonly" "$1" \
      python3 /probe/conformance.py "$2" /probe
  }
  cleanroom programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6 fzf >"$scratch/screens"
  "$suite" screens "$scratch/screens"
  cleanroom programbench/tomnomnom_1776_gron.88a6234:task_cleanroom_v6 gron
else
  echo 'Docker is unavailable. Gates 1 and 2 passed. Cleanroom gates skipped.'
fi
