#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
out=.lake/build/relays
mkdir -p "$out"
stage=$(mktemp -d "$out/.build.XXXXXXXX")
trap 'find "$stage" -depth -delete' EXIT
for tool in term fs net git web; do
  src="runtime/tools/$tool-relay.c"
  if [[ $tool == term ]]; then src=runtime/term-relay.c; fi
  cc -std=c11 -O2 -Wall -Wextra -Werror -static "$src" -o "$stage/$tool-relay"
  # Docker executes the mounted relay as the unprivileged cleanroom user.
  chmod 755 "$stage/$tool-relay"
done
for relay in "$stage"/*-relay; do mv -- "$relay" "$out/"; done
lake build
ln -sfn .lake/build/bin/lojita lojita
./lojita verify-self
