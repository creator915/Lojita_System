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
audit() {
  "$lean" --run Test/PosixPurity.lean --module Test.G1.Roots --root "G1Fixture.$1"
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
audit approvedBytes
expect_rejection indirectAxiom axiom hiddenAxiom
expect_rejection taintedBytes axiom hiddenAxiom
expect_rejection admittedTheorem sorry sorryAx
expect_rejection indirectExtern extern hiddenExtern
expect_rejection unsafeRoot unsafe 'G1Fixture\.(unsafeRoot|Dep\.markedUnsafe)'
expect_rejection effectOnlyInType effect '(IO|EIO|RealWorld)'
expect_rejection usesPartial partial partialMarker
expect_rejection usesImplementedBy implemented_by 'withImpl|implTarget'
expect_rejection usesCSimp rewrite 'logical|fixtureRewrite|replacement'
expect_rejection outsideReviewedSet extern 'Float\.sin'
echo 'G1 fixture checks passed (1 accepted, 10 rejected).'
