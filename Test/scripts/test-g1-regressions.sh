#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/Test/G1"
# Reuse the project's selected compiler and package search path. Writing the
# fixtures outside .lake also leaves parallel invocations independent.
lean=$(lake env which lean)
export LEAN_PATH="$work:$(lake env printenv LEAN_PATH)"
for unit in Dependencies Roots; do
  "$lean" -R . -o "$work/Test/G1/$unit.olean" "Test/G1/$unit.lean"
done
# The release verifier accepts only the pinned file inventory and hashes.
# An incomplete local prefix is a cheap negative control for that entry point.
mkdir -p "$work/prefix/bin" "$work/prefix/lib/lean"
for tool in lean leanir lake leanc; do
  printf 'fixture\n' >"$work/prefix/bin/$tool"
done
printf 'fixture\n' >"$work/prefix/lib/lean/Init.olean"
if python3 Test/scripts/g1-release.py "$work/prefix" >"$work/release.log" 2>&1; then
  echo 'G1 accepted an unpinned distribution' >&2
  exit 1
fi
grep -F 'G1 DENY [origin]' "$work/release.log" > /dev/null || { cat "$work/release.log" >&2; exit 1; }
audit() {
  "$lean" --run Test/PosixPurity.lean --module Test.G1.Roots --root "$1"
}
expect_rejection() {
  local root=$1 kind=$2 culprit=$3
  if audit "$root" >"$work/audit.log" 2>&1; then
    echo "G1 accepted forbidden fixture $root" >&2
    exit 1
  fi
  if ! grep -E "G1 DENY \\[$kind\\].*($culprit)" "$work/audit.log" > /dev/null; then
    cat "$work/audit.log" >&2
    echo "G1 did not diagnose $root as $kind ($culprit)" >&2
    exit 1
  fi
}
# A single selected root exercises only its reachable declarations even when
# the imported module also contains intentionally invalid fixtures.
audit G1Fixture.approvedBytes
audit G1Fixture.legitimateElimination
expect_rejection G1Fixture.indirectAxiom axiom hiddenAxiom
expect_rejection G1Fixture.taintedBytes axiom hiddenAxiom
expect_rejection G1Fixture.admittedTheorem sorry sorryAx
expect_rejection G1Fixture.indirectExtern extern hiddenExtern
expect_rejection G1Fixture.unsafeRoot unsafe 'G1Fixture\.(unsafeRoot|Dep\.markedUnsafe)'
expect_rejection G1Fixture.effectOnlyInType effect '(IO|EIO|RealWorld)'
expect_rejection G1Fixture.usesPartial partial partialMarker
expect_rejection G1Fixture.usesImplementedBy implemented_by 'withImpl|implTarget'
expect_rejection G1Fixture.usesCSimp rewrite 'logical|fixtureRewrite|replacement'
expect_rejection G1Fixture.outsideReviewedSet extern 'Float\.sin'
expect_rejection G1Fixture.directPanic '[a-z_]+' 'panic(Core)?'
expect_rejection G1Fixture.directPanicCore '[a-z_]+' 'panicCore'
expect_rejection lcProof '[a-z_]+' 'lcProof'
# A safe theorem depending on the compiler-only proof never reaches an olean.
"$lean" -R . Test/G1/LogicKernel.lean
echo 'G1 fixture checks passed (2 accepted, 13 rejected, 1 kernel rejection, 1 release rejection).'
