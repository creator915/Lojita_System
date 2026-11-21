#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"
repo=$PWD
build=$(mktemp -d "${TMPDIR:-/tmp}/test-cas-meta.XXXXXXXX")
trap 'rm -rf -- "$build"' EXIT

# Agda 2.6.3 writes .agdai next to source even with --compile-dir. Compile
# private source copies, and run the sandbox tests against the real worktree.
src=$build/src
mkdir -p "$src"/{Code,OwnershipIO,Store,Meta,Test} "$build"/{ghc,bin}
cp -- Code.agda Ownership.agda OwnershipIO.agda check.sh "$src/"
cp -- Code/*.agda "$src/Code/"
cp -- OwnershipIO/*.agda "$src/OwnershipIO/"
cp -- Store/{Object,CAS,Verify}.agda "$src/Store/"
cp -- Meta/{Boundary,Sandbox}.agda "$src/Meta/"
cp -- Test/{StoreCAS,MetaBoundary}.agda "$src/Test/"

"$src/check.sh" Store/Object.agda
"$src/check.sh" Meta/Boundary.agda

compile() {
  if ! "$@" >"$build/compiler.log" 2>&1; then
    tail -n 100 "$build/compiler.log" >&2
    return 1
  fi
}

compile ghc -O2 -threaded -package Agda -outputdir "$build/ghc" -o "$build/bin/dump" "$repo/dump/Dump.hs"
for suite in StoreCAS MetaBoundary; do
  echo "Compiling Test/$suite.agda"
  compile agda --no-libraries --compile --ghc-flag=-O0 --compile-dir="$build/bin" \
    -i "$src" -i /usr/share/agda-stdlib "$src/Test/$suite.agda"
done
"$build/bin/StoreCAS"
"$build/bin/MetaBoundary" "$build/bin/dump"
