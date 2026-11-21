#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"

protected=(Ownership.agda OwnershipIO.agda Context Meta/Boundary.agda Store
  runtime/lean-prism/AgdaMirror runtime/lean-prism/Prism/Conservativity.lean)
V6_BASE="${V6_BASE:-7ebd4e9}"
if git rev-parse --verify "${V6_BASE}^{commit}" >/dev/null 2>&1; then
  git diff --exit-code "${V6_BASE}..HEAD" -- "${protected[@]}"
  git diff --exit-code "${V6_BASE}" -- "${protected[@]}"
fi
python3 scripts/embed_prompts.py --check

# Some regressions also compile the project in place. Wait for each script
# and all of its children before allowing the next writer to start.
gate() (
  set -eu
  export AGDA_DIR
  AGDA_DIR=$(mktemp -d /tmp/v7-suite.XXXXXX) || exit 1
  export TMPDIR="$AGDA_DIR"
  trap 'rm -r -- "$AGDA_DIR"' EXIT
  echo "Running $*"
  "$@"
)

gate ./build.sh
gate ./runtime/lean-prism/.lake/build/bin/harness-engine verify-self
failed=()
for script in test-v7-lift test-v7-obstruction test-v7-2d-e2e test-lean-prism \
              test-whitebox-gates test-independent-gates test-gron-stress \
              test-world-conformance test-step4-protocol test-prompts test-replay-gate; do
  if ! gate "./$script.sh"; then
    failed+=("$script")
  fi
done

if (( ${#failed[@]} )); then
  printf 'Failed gate: %s\n' "${failed[@]}" >&2
  exit 1
fi
status=$(git status --porcelain)
if [[ -n "$status" ]]; then
  echo "$status" >&2
  exit 1
fi
echo "PASS v7 acceptance suite and clean worktree"
