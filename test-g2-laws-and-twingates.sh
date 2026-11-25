#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mapfile -t modules < <(awk '$1 == "import" {print $2}' Test/TheoremPin.lean Test/Posix/Twins.lean Test/Posix/TtyRecords.lean Test/VfsTwin.lean | sort -u)
lake build "${modules[@]}"
lake env lean Test/TheoremPin.lean
lake env lean --run Test/Posix/Twins.lean
lake env lean --run Test/Posix/TtyRecords.lean
lake env lean --run Test/VfsTwin.lean
