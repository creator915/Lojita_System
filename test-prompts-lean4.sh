#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
cd -- "$(dirname -- "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/v9-s4.XXXXXXXX")
trap 'find "$scratch" -depth -delete' EXIT
export TMPDIR="$scratch"
python3 scripts/embed_prompts_lean.py --check
python3 - "$scratch/drafts" <<'PY'
import re
import sys
from pathlib import Path

dest = Path(sys.argv[1]) / "drafts"
dest.mkdir(parents=True)
for filename in ["node-closed-world.md", "session-open-world.md"]:
    source = Path("prompts", filename)
    block = None
    for n, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
        if block is None:
            match = re.fullmatch(r"\s*(`{3,}|~{3,})\s*(.*?)\s*", line)
            if match:
                fence, info = match.groups()
                words = info.split()
                capture = words and words[0].lstrip(".") in ("lean", "sexp")
                if capture and (len(words) != 2 or not re.fullmatch(r"[\w.-]+", words[1])):
                    raise SystemExit(f"{source}:{n} example needs a unique test name")
                block = (fence, words[1] if capture else None, [])
        else:
            fence, name, lines = block
            if line.strip().startswith(fence) and set(line.strip()) == {fence[0]}:
                if name is not None:
                    with (dest / (name + ".block")).open("x", encoding="utf-8") as out:
                        out.write("\n".join(lines) + "\n")
                block = None
            else:
                lines.append(line)
    if block:
        raise SystemExit(f"{source} has an unclosed fence")
PY
./build.sh
lake build test-s4-session
timeout 120s .lake/build/bin/test-s4-session prompts "$scratch/drafts" "$scratch/workspace"
