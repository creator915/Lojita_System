#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

context=Context/PolyTransport.agda
if ! grep -Eq '^[[:space:]]*\{-# *OPTIONS +([^#]* )?--safe +([^#]* )?#-\}' "$context"; then
  echo "Missing --safe OPTIONS pragma in $context" >&2
  exit 1
fi
if grep -nw -- postulate "$context"; then
  echo "Found a postulate in $context" >&2
  exit 1
fi

./check.sh Context/PolyTransport.agda
./check.sh Code/PolyTransport.agda
./check.sh Test/PolyTransportTest.agda
