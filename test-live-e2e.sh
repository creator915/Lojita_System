#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8 PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lojita-live.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
mkdir "$scratch/tmp"
export TMPDIR="$scratch/tmp"
./build.sh
image=programbench/tomnomnom_1776_gron.88a6234:task_cleanroom_v6
if ! command -v docker >/dev/null; then
  echo 'Docker gron skipped. Docker CLI is absent.'
elif docker image inspect "$image" >/dev/null 2>"$scratch/docker-inspect"; then
  printf '(ref-target (docker "%s" "/workspace/executable") (timeoutMs 30000))\n' "$image" >"$scratch/gron.sexp"
  ./lojita session-probe "$scratch/gron-ws" "$scratch/gron.sexp" Test/S5/gron-probe.lean >"$scratch/gron.out"
  printf 'json = {};\njson.a = 1;\n' >"$scratch/gron.expected"
  cmp "$scratch/gron.expected" "$scratch/gron.out"
  echo 'Docker gron matched both cleanroom executions.'
elif grep -qiE 'no such (image|object)' "$scratch/docker-inspect"; then
  echo "Docker gron skipped. Image $image is absent."
else
  cat "$scratch/docker-inspect" >&2
  exit 1
fi

# Keep Codex settings, durable sessions, fork rollouts and caches private to this run.
# Import the credential into the disposable home so a client refresh also stays there.
auth_dir=${CODEX_HOME:-$HOME/.codex}
install -d -m 700 "$scratch/codex"
if [[ -r "$auth_dir/auth.json" ]]; then
  install -m 600 "$auth_dir/auth.json" "$scratch/codex/auth.json"
fi
export CODEX_HOME="$scratch/codex" XDG_CACHE_HOME="$scratch/cache" XDG_STATE_HOME="$scratch/state"
export CODETRANSPORT_CODEX_BIN=/root/.local/bin/codex CODETRANSPORT_MODEL=gpt-6.2-astra
export CODETRANSPORT_EFFORT=medium CODETRANSPORT_SERVICE_TIER=fast
export CODETRANSPORT_CODEX_TRACE_DIR="$scratch/exec-events"
"$CODETRANSPORT_CODEX_BIN" --version
install -m 755 Test/S5/trim-ref.py "$scratch/trim-ref.py"
printf '%s\n' '(ref-target (local "trim-ref.py") (timeoutMs 30000))' >"$scratch/trim.sexp"
ws="$scratch/session"
timeout -k 15s 45m ./lojita session "$ws" Test/S5/trim-goal.md "$scratch/trim.sexp"
python3 Test/S5/verify-live.py "$ws" "$CODETRANSPORT_CODEX_TRACE_DIR" "$CODEX_HOME/sessions"
