#!/usr/bin/env python3
"""Embed the authoritative prompt files verbatim; --check detects drift."""
import json, re, sys
from pathlib import Path
root = Path(__file__).resolve().parent.parent
file = root / 'Code/Prompt.agda'
old = file.read_text()
new = old
for name, source in [('closedWorldTemplate', 'prompts/node-closed-world.md'),
                     ('sessionTemplate', 'prompts/session-open-world.md')]:
    value = json.dumps((root / source).read_text(), ensure_ascii=False)
    new = re.sub(r'^' + name + r' = .*$', lambda _: name + ' = ' + value, new, flags=re.M)
if '--check' in sys.argv:
    if new != old:
        raise SystemExit('Code/Prompt.agda differs from authoritative prompt files')
else:
    file.write_text(new)
