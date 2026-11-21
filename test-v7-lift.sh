#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
cd -- "$(dirname -- "$0")"
engine="$PWD/runtime/lean-prism/.lake/build/bin/harness-engine"

scratch=$(mktemp -d /tmp/v7-lift.XXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
export AGDA_DIR="$scratch"
mkdir "$scratch/src"

# Agda 2.6.3 writes project interfaces beside their sources.
tar --exclude='*.agdai' -cf - Backend Code Context Meta OwnershipIO Store \
  Code.agda Ownership.agda OwnershipIO.agda Test/{BlueprintLift,FunctorialLiftTest}.agda |
  tar -xf - -C "$scratch/src"
cd "$scratch/src"
for fixture in Test/{BlueprintLift,FunctorialLiftTest}.agda; do
  if ! agda --no-libraries -i . -i /usr/share/agda-stdlib "$fixture" >"$scratch/check.log" 2>&1; then
    tail -60 "$scratch/check.log" >&2
    exit 1
  fi
  echo "PASS $fixture"
done

# Export the checked Agda fixtures so the native engine reads the same wire data.
python3 - "$engine" <<'PY'
import json
import subprocess
import sys
from pathlib import Path

module = '"Test/FunctorialLiftTest.agda"'
expressions = ["fusionContext", "previewRequest (fusion [ subB ])", "previewRequest unimportedTarget"]
commands = [f'Cmd_load {module} ["--no-libraries","-i",".","-i","/usr/share/agda-stdlib"]']
commands += [f"Cmd_compute_toplevel DefaultCompute {json.dumps(expr)}" for expr in expressions]
wire = "".join(f"IOTCM {module} None Direct ({cmd})\n" for cmd in commands)
output = subprocess.check_output(["agda", "--interaction-json"], input=wire, text=True)

fixtures = []
for line in output.splitlines():
    message = line.removeprefix("JSON> ").strip()
    if message:
        info = json.loads(message).get("info", {})
        if info.get("kind") == "NormalForm":
            fixtures.append(json.loads(info["expr"]))
if len(fixtures) != len(expressions):
    sys.exit("Agda did not produce all three serialized check-plan fixtures")

ctx, accepted, rejected = fixtures
Path("context.sexp").write_text(ctx)
for request, expected in [(accepted, []), (rejected, ['(missingChildImport "Missing")'])]:
    Path("request.sexp").write_text(request)
    report = json.loads(subprocess.check_output([sys.argv[1], "check-plan", "context.sexp", "request.sexp"], text=True))
    if report["ok"] != (not expected) or report["diagnostics"] != expected:
        sys.exit(f"Unexpected native check-plan result: {report}")
print("PASS native check-plan accepted fusion and diagnosed the missing second target")
PY
