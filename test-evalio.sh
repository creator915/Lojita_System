#!/bin/bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"
mkdir -p tmp/evalio-build
agda --compile --ghc-flag=-O0 --compile-dir=tmp/evalio-build -i . -i /usr/share/agda-stdlib Test/EvalIO.agda > tmp/evalio-build-evalio.log 2>&1 || { cat tmp/evalio-build-evalio.log; exit 1; }
./tmp/evalio-build/EvalIO
