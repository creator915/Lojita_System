#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"
build=tmp/v3-e2e-build
mkdir -p "$build"
ghc -O0 -package Agda dump/Dump.hs -o dump/dump >"$build/dump.log" 2>&1 || { cat "$build/dump.log"; exit 1; }
agda --compile --ghc-flag=-O0 --ghc-flag=-iruntime --ghc-flag=-iruntime/tools --compile-dir="$build" \
  -i . -i /usr/share/agda-stdlib Test/EndToEndPolyTransport.agda >"$build/agda.log" 2>&1 || { tail -100 "$build/agda.log"; exit 1; }
timeout 900 "$build/EndToEndPolyTransport"
