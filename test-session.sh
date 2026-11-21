#!/bin/bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"
mkdir -p tmp/session-build
ghc -O2 -threaded -package Agda dump/Dump.hs -o dump/dump > tmp/session-build-dump.log 2>&1 || { cat tmp/session-build-dump.log; exit 1; }
agda --compile --ghc-flag=-O0 --ghc-flag=-iruntime --ghc-flag=-iruntime/tools --compile-dir=tmp/session-build -i . -i /usr/share/agda-stdlib Test/SessionIO.agda > tmp/session-build-session.log 2>&1 || { cat tmp/session-build-session.log; exit 1; }
timeout 900 ./tmp/session-build/SessionIO
