#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd -- "$(dirname -- "$0")"

for module in Code/Driver.agda Code/CLI.agda Code/AI.agda Main.agda; do
  ./check.sh "$module"
done
./build.sh
test -x ./Main

fixture=$(mktemp -d "${TMPDIR:-/tmp}/test-cli-sandbox.XXXXXXXX")
trap 'rm -rf -- "$fixture"' EXIT
cat >"$fixture/codex" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
mode=new
parent=
while (( $# )); do
  case $1 in
    -o) output=$2; shift 2 ;;
    fork|resume) mode=$1; parent=$2; shift 2 ;;
    *) shift ;;
  esac
done
fixture=$CLI_SANDBOX_FIXTURE
archive=$CODEX_HOME/sessions/2026/11/19
rollout() { printf '%s/rollout-2026-11-19T08-00-00-%s.jsonl' "$archive" "$1"; }
mkdir -p "$archive" "$fixture/threads"
if [[ $mode != new ]]; then
  test -f "$(rollout "$parent")"
fi
if [[ $mode == fork && -f $fixture/reported-id ]]; then
  cat >/dev/null
  printf 'draft' >"$output"
  printf '{"thread_id":"%s"}\n' "$(<"$fixture/reported-id")"
  rm -- "$fixture/reported-id"
  exit 0
fi
if [[ $mode == resume ]]; then
  if [[ -f $fixture/fail-resume ]]; then
    rm -- "$fixture/fail-resume"
    exit 1
  fi
  tid=$parent
else
  serial=0
  if [[ -f $fixture/serial ]]; then serial=$(<"$fixture/serial"); fi
  serial=$((serial + 1))
  printf '%s' "$serial" >"$fixture/serial"
  printf -v tid '00000000-0000-4000-a000-%012d' "$serial"
  printf '%s' "$tid" >"$fixture/threads/$tid.thread"
  printf '%s' "$tid" >"$fixture/threads/$tid.jsonl"
fi
printf '%s' "$tid" >"$fixture/$mode.id"
cat >>"$(rollout "$tid")"
printf '\n' >>"$(rollout "$tid")"
if [[ -f $fixture/reply ]]; then cat "$fixture/reply" >"$output"; else printf 'READY' >"$output"; fi
printf '{"thread_id":"%s"}\n' "$tid"
MOCK
chmod +x "$fixture/codex"

build=tmp/tool-build
if ! agda --compile --ghc-flag=-O0 --ghc-flag=-iruntime --ghc-flag=-iruntime/tools --compile-dir="$build" \
    -i . -i /usr/share/agda-stdlib Test/CLISandboxTest.agda >"$fixture/compile.log" 2>&1; then
  tail -n 100 "$fixture/compile.log" >&2
  exit 1
fi
"$build/CLISandboxTest" "$fixture/codex"
