#!/bin/bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"

local_only=false
case "$#:$*" in
  0:) ;;
  1:--local-only) local_only=true ;;
  *) echo "Usage: $0 [--local-only]" >&2; exit 2 ;;
esac

# roundtrip.sh invokes rg from Python, including in non-interactive shells.
if ! command -v rg >/dev/null 2>&1; then
  for codex_path in /root/.codex/packages/standalone/releases/*/codex-path; do
    if [ -x "$codex_path/rg" ]; then
      export PATH="$codex_path:$PATH"
      break
    fi
  done
fi
command -v rg >/dev/null 2>&1 || { echo 'FAIL rg is required by roundtrip.sh' >&2; exit 1; }

build=tmp/ext-tools-build
image=programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6
scratch_dirs=(tmp/fs-sandboxes tmp/net-sandboxes tmp/git-sandboxes tmp/ext-sandboxes)
mkdir -p "$build" "${scratch_dirs[@]}"
if ! "$local_only"; then
  # Required by default; never pull or silently omit Docker coverage.
  docker image inspect "$image" >/dev/null
fi

assert_clean() {
  local directory residue containers
  for directory in "${scratch_dirs[@]}"; do
    residue=$(find "$directory" -mindepth 1 -print -quit)
    if [ -n "$residue" ]; then
      echo "FAIL workspace residue: $residue" >&2
      return 1
    fi
  done
  if ! "$local_only"; then
    containers=$(docker ps -a --filter name=fsrelay- --filter name=netrelay- \
      --filter name=gitrelay- --format '{{.ID}} {{.Names}}')
    if [ -n "$containers" ]; then
      echo "FAIL sandbox container residue: $containers" >&2
      return 1
    fi
  fi
}
assert_clean

reject_pattern() {
  local pattern=$1 status
  shift
  if grep -En "$pattern" "$@"; then
    echo 'FAIL static purity/decoupling audit' >&2
    exit 1
  else
    status=$?
    if [ "$status" -ne 1 ]; then
      echo 'FAIL static audit could not read its inputs' >&2
      exit "$status"
    fi
  fi
}

pure_files=(Context/Tools/*.agda Test/Tools/*Conformance.agda)
for file in "${pure_files[@]}"; do
  if ! grep -Eq '^\{-# OPTIONS --safe #-\}' "$file"; then
    echo "FAIL missing --safe pragma: $file" >&2
    exit 1
  fi
done
reject_pattern 'postulate|\{!!\}|NON_TERMINATING|TERMINATING' "${pure_files[@]}"
reject_pattern 'postulate|\{!!\}|NON_TERMINATING' Code/Tools/*.agda

tool_listing=$(rg --files -g '*.agda' Context/Tools OwnershipIO/Tools Code/Tools Test/Tools)
mapfile -t tool_files <<< "$tool_listing"
reject_pattern '(^|[[:space:]])import[[:space:]]+(Code([[:space:]]|$)|Code\.(Transport|Harness|Lift|SessionRunner|SessionTools|Prompt|AI)([.[:space:]]|$)|(ui|Store|Meta)([.[:space:]]|$)|Context\.Lang([.[:space:]]|$))' "${tool_files[@]}"

# Enforce the positive import boundary as well as the forbidden-name audit.
# Code.Driver is deliberately usable only through its registry selection API.
python3 - "${tool_files[@]}" <<'PY'
from pathlib import Path
import re
import sys

allowed = {'Ownership', 'OwnershipIO', 'OwnershipIO.FFI', 'Context.Terminal',
           'Code.TermTool', 'Code.Driver'}
prefixes = ('Context.Tools.', 'OwnershipIO.Tools.', 'Code.Tools.', 'Test.Tools.')
driver_names = {'Registry', 'Pick', 'SubT', 'select', 'all-nil', 'all-cons'}
for name in sys.argv[1:]:
    source = Path(name).read_text()
    # Imports in this tree are declarations, never executable string contents.
    imports = list(re.finditer(r'^\s*(?:open\s+)?import\s+([\w.]+)([^\n]*)', source, re.M))
    for match in imports:
        module = match[1]
        standard = (module.startswith('Agda.') or
                    (Path('/usr/share/agda-stdlib') / (module.replace('.', '/') + '.agda')).is_file())
        if module not in allowed and not module.startswith(prefixes) and not standard:
            raise SystemExit(f'FAIL forbidden import in {name}: {module}')
        if module == 'Code.Driver':
            tail = source[match.start(2):]
            using = re.match(r'\s+using\s*\(([^)]*)\)', tail)
            if not using or not {x.strip() for x in using[1].split(';')} <= driver_names:
                raise SystemExit(f'FAIL unrestricted Code.Driver import in {name}')
print('PASS static purity and decoupling audit')
PY

for tool in fs net git; do
  cc -std=c11 -O2 -Wall -Wextra -Werror -static "runtime/tools/$tool-relay.c" -o "$build/$tool-relay"
done
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o "$build/term-relay"
echo 'PASS static relay builds'

for file in "${tool_files[@]}"; do
  ./check.sh "$file"
done
# One invocation shares the isolated source/rendered tree across all modules.
# The baseline roundtrip runner rebuilds dump/dump in place. Preserve its
# original bytes/mode and any pre-existing GHC objects, even on check failure.
preserved_roundtrip() (
  backup=$(mktemp -d "$build/roundtrip-backup.XXXXXX")
  dump_outputs=(dump/dump dump/Dump.o dump/Dump.hi)
  for output in "${dump_outputs[@]}"; do
    if [ -e "$output" ]; then
      cp -p "$output" "$backup/$(basename "$output")"
    fi
  done
  restore_dump() {
    status=$?
    trap - EXIT
    for output in "${dump_outputs[@]}"; do
      saved="$backup/$(basename "$output")"
      if [ -e "$saved" ]; then
        cp -p "$saved" "$output" || status=1
      else
        rm -f "$output" || status=1
      fi
    done
    rm -rf "$backup"
    exit "$status"
  }
  trap restore_dump EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM
  ./roundtrip.sh "${tool_files[@]}"
)
preserved_roundtrip

export HOST_SECRET_LEAK=1
io_args=()
if "$local_only"; then
  io_args=(--local-only)
fi
for suite in FsIO NetIO GitIO ExtToolsIO; do
  log="$build/$suite-build.log"
  if ! agda --compile --ghc-flag=-O0 --ghc-flag=-iruntime --ghc-flag=-iruntime/tools \
    --ghc-flag=-outputdir --ghc-flag="$build/agda" --compile-dir="$build/agda" \
    -i . -i /usr/share/agda-stdlib "Test/Tools/$suite.agda" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  timeout 180 "./$build/agda/$suite" "${io_args[@]}"
done

for suite in FsLifecycle NetLifecycle GitLifecycle; do
  suite_build="$build/$suite"
  mkdir -p "$suite_build"
  log="$build/$suite-build.log"
  if ! ghc -O0 -Wall -Werror -iruntime -iruntime/tools -outputdir "$suite_build" \
    "Test/Tools/$suite.hs" -o "$suite_build/lifecycle" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  lifecycle_args=()
  if ! "$local_only" && [ "$suite" = NetLifecycle ]; then
    lifecycle_args=(--docker)
  fi
  timeout 60 "./$suite_build/lifecycle" "${lifecycle_args[@]}"
done

assert_clean
echo 'PASS zero external tool workspace residue'
if "$local_only"; then
  echo 'PASS local-only run created no Docker containers'
else
  echo 'PASS zero external tool container residue'
fi
echo 'PASS ALL EXT TOOLS CONFORMANCE AND LIFECYCLE TESTS'
