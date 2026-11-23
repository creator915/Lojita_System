#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/v9-s4.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
export TMPDIR="$scratch"

./test-prompts-lean4.sh
export CODETRANSPORT_CODEX_BIN="$PWD/Test/S4/fake-codex.py"
export LOJITA_S4_THREADS="$scratch/threads-default"
env -u CODETRANSPORT_MODEL -u CODETRANSPORT_EFFORT -u CODETRANSPORT_SERVICE_TIER \
  .lake/build/bin/test-s4-session threads "$LOJITA_S4_THREADS"
export LOJITA_S4_THREADS="$scratch/threads-overrides"
CODETRANSPORT_MODEL=model-for-test CODETRANSPORT_EFFORT=high CODETRANSPORT_SERVICE_TIER=priority \
  .lake/build/bin/test-s4-session threads "$LOJITA_S4_THREADS"
export LOJITA_S4_THREADS="$scratch/threads-no-tier"
CODETRANSPORT_SERVICE_TIER= .lake/build/bin/test-s4-session threads "$LOJITA_S4_THREADS"
ws="$scratch/workspace"
timeout 120s .lake/build/bin/test-s4-session tower "$ws"
file -b "$ws/bin/candidate" | grep -E '^ELF .*statically linked'
mkdir -p "$scratch/rpc"
python3 Test/S4/mcp.py "$scratch/rpc" "$ws"
./lojita session-probe "$ws" "$scratch/rpc/reference.sexp" Test/S4/relay-probe.lean

./lojita verify-self
cat >"$scratch/Base.lean" <<'LEAN'
namespace Gen.Smoke.Base
def value := 7
end Gen.Smoke.Base
LEAN
cat >"$scratch/Main.lean" <<'LEAN'
import Gen.Smoke.Base
namespace Gen.Smoke.Root
def result := Gen.Smoke.Base.value
theorem correct : result = 7 := rfl
end Gen.Smoke.Root
LEAN
./lojita check "$scratch/Main.lean" --dep "$scratch/Base.lean"
./lojita units "$scratch/Main.lean" >"$scratch/units"
grep -q 'Gen.Smoke.Root.correct' "$scratch/units"
./lojita order "$scratch/Main.lean" >"$scratch/order"
test "$(head -1 "$scratch/order")" = Gen.Smoke.Root.result
./lojita roundtrip "$scratch/Main.lean" >"$scratch/reconstructed.lean"
./lojita check "$scratch/reconstructed.lean" --dep "$scratch/Base.lean"
cat >"$scratch/edit.sexp" <<'PLAN'
(submission (kind plan) (why "increment") (main "namespace Gen.Smoke.Base\ndef value := 8\nend Gen.Smoke.Base")
 (moves (move (unit "Gen.Smoke.Base.value") (unit "Gen.Smoke.Base.value"))))
PLAN
./lojita apply "$scratch/Base.lean" "$scratch/edit.sexp" >"$scratch/edited.lean"
grep -q 'def value := 8' "$scratch/edited.lean"
./lojita check "$scratch/edited.lean"
echo '5  Unified native CLI passed'

# The S3 suite also invokes the complete S1 and S2 suites.
./test-s3-harness.sh
echo '6  All prior foundation, kernel and harness regressions passed'
