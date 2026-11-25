#!/usr/bin/env bash
set -uo pipefail
cd -- "$(dirname -- "$0")"
if [[ ${1:-} != --run-gates ]]; then
  exec timeout --foreground 180s bash "$0" --run-gates "$@"
fi
shift
if (( $# > 1 )) || [[ -n ${1:-} && $1 != --with-apparmor-userns ]]; then
  echo "Usage: $0 [--with-apparmor-userns]" >&2
  exit 2
fi
gates=(g1-purity-and-size g2-laws-and-twingates g3-ubuntu-fuzz-conformance g4-sandbox-redteam g5-lift-showcase)
failed=()
for gate in "${gates[@]}"; do
  start=$SECONDS
  args=()
  if [[ $gate == g4-sandbox-redteam ]]; then args=("$@"); fi
  if "./test-$gate.sh" "${args[@]}"; then
    printf 'PASS %s (%ds)\n' "$gate" "$((SECONDS-start))"
  else
    code=$?
    failed+=("$gate")
    printf 'FAIL %s (exit %d, %ds)\n' "$gate" "$code" "$((SECONDS-start))" >&2
  fi
done
printf 'Completed %d gates in %ds, failures=%d\n' "${#gates[@]}" "$SECONDS" "${#failed[@]}"
(( ${#failed[@]} == 0 ))
