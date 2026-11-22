#!/bin/bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")"
mkdir -p tmp/tool-build tmp/term-build tmp/harness-engine-build
ghc -O2 -threaded -with-rtsopts=-A32m -package Agda dump/Dump.hs -o dump/dump >tmp/build-dump.log 2>&1 || { cat tmp/build-dump.log; exit 1; }
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/term-relay.c -o tmp/term-build/term-relay
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/fs-relay.c -o tmp/term-build/fs-relay
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/net-relay.c -o tmp/term-build/net-relay
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/git-relay.c -o tmp/term-build/git-relay
cc -std=c11 -O2 -Wall -Wextra -Werror -static runtime/tools/web-relay.c -o tmp/term-build/web-relay
(cd runtime/lean-prism && lake build liblean_cli_host AgdaMirror:static agda2lean) >tmp/build-lean-prism.log 2>&1 || { cat tmp/build-lean-prism.log; exit 1; }
# Readers may be using the current binary while the compiler links a new one.
engine_bin=runtime/lean-prism/.lake/build/bin
engine_stage=$(mktemp "$engine_bin/.harness-engine.XXXXXXXX")
trap 'rm -f -- "$engine_stage"' EXIT
"$engine_bin/agda2lean" prism-build \
  --lib-dir runtime/lean-prism/.lake/build/lib/lean \
  --ir-dir runtime/lean-prism/.lake/build/ir \
  --work-dir tmp/harness-engine-build \
  --trusted-codegen \
  --dep Context/Terminal.agda \
  --dep Context/Filter.agda \
  --dep Backend/Mode.agda \
  --dep Code.agda \
  --dep Code/SExpr.agda \
  --dep Code/Shape.agda \
  --dep Code/Transport.agda \
  --dep Code/Lift.agda \
  --dep Code/Protocol.agda \
  --dep Code/Encode.agda \
  --dep Code/Parse.agda \
  --dep Code/Render.agda \
  --dep Code/Namespace.agda \
  --dep Code/Countermodel/Wire.agda \
  --dep Code/Countermodel.agda \
  --dep Code/PolyTransport.agda \
  --dep Code/NodeTransport.agda \
  --dep Code/Submission.agda \
  --dep Code/SessionProtocol.agda \
  --dep Code/Prompt.agda \
  --dep Code/HarnessCore.agda \
  --dep Code/PlanPreview.agda \
  --dep Code/PureCLI.agda \
  --main Code/HarnessEngineMain.agda \
  --out "$engine_stage" >tmp/build-harness-engine.log 2>&1 || { cat tmp/build-harness-engine.log; exit 1; }
"$engine_stage" verify-self >/dev/null
mv -f -- "$engine_stage" "$engine_bin/harness-engine"
CLI_HOST_C="$(pwd)/runtime/cli_host.c"
agda --compile --ghc-flag=-O0 --ghc-flag=-threaded --ghc-flag=-iruntime --ghc-flag=-iruntime/tools \
  "--ghc-flag=$CLI_HOST_C" --compile-dir=tmp/tool-build \
  -i . -i /usr/share/agda-stdlib Main.agda >tmp/build-main.log 2>&1 || { cat tmp/build-main.log; exit 1; }
cp tmp/tool-build/Main Main
