#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mapfile -t modules < <(awk '$1 == "import" {print $2}' Test/TheoremPin.lean Test/Posix/Twins.lean Test/Posix/TtyRecords.lean Test/Posix/DeviceCursor.lean Test/Posix/ReadMachine.lean Test/VfsTwin.lean Test/Posix/Reactive.lean Test/Posix/ConfinedRoot.lean | sort -u)
lake build "${modules[@]}" test-vfs-twin
lake env lean Test/TheoremPin.lean
lake env lean --run Test/Posix/Twins.lean
lake env lean --run Test/Posix/TtyRecords.lean
lake env lean --run Test/Posix/DeviceCursor.lean
lake env lean --run Test/Posix/ReadMachine.lean
.lake/build/bin/test-vfs-twin
lake env lean Test/Posix/ConfinedRoot.lean
lake env lean --run Test/Posix/Reactive.lean
