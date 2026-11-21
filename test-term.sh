#!/bin/bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"
mkdir -p tmp/term-build tmp/term-sandboxes
image=programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6
# Required, never silently skipped or pulled from the network.
docker image inspect "$image" >/dev/null
if rg -n 'postulate|\{!!\}|NON_TERMINATING' Context/Terminal.agda Test/TermConformance.agda; then
  echo 'Pure terminal modules contain a forbidden escape hatch' >&2
  exit 1
fi
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o tmp/term-build/term-relay
agda --compile --ghc-flag=-O0 --ghc-flag=-iruntime --ghc-flag=-outputdir --ghc-flag=tmp/term-build --compile-dir=tmp/term-build \
  -i . -i /usr/share/agda-stdlib Test/TermIO.agda >tmp/term-build.log 2>&1 || { cat tmp/term-build.log; exit 1; }
export HOST_SECRET_LEAK=1
timeout 180 ./tmp/term-build/TermIO
mkdir -p tmp/term-lifecycle-build
ghc -O0 -Wall -Werror -iruntime -outputdir tmp/term-lifecycle-build \
  Test/TermTransportLifecycle.hs -o tmp/term-lifecycle-build/lifecycle >tmp/term-lifecycle-build.log 2>&1 || { cat tmp/term-lifecycle-build.log; exit 1; }
timeout 60 ./tmp/term-lifecycle-build/lifecycle
if [ -n "$(find tmp/term-sandboxes -mindepth 1 -print -quit)" ]; then
  echo 'FAIL terminal workspace residue' >&2
  exit 1
fi
echo 'PASS zero terminal workspace residue'
