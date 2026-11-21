#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

for module in HarnessPure TransportTest NegativeGates HarnessRegression; do
  ./check.sh "Test/$module.agda"
done

if grep -nF 'Root0Types' Code/Prompt.agda; then
  echo 'Closed-world prompt still references the shared task module.' >&2
  exit 1
fi

./test-evalio.sh
