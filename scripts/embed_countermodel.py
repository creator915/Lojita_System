#!/usr/bin/env python3
"""Compile prompts/Countermodel.agda via dump/dump into Code/Countermodel/Wire.agda; --check detects drift."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
source = root / "prompts/Countermodel.agda"
target = root / "Code/Countermodel/Wire.agda"
dump_bin = Path(os.environ.get("DUMP_BIN") or (root / "dump/dump"))

with tempfile.TemporaryDirectory(prefix="cm-embed-") as tmp:
    staged = Path(tmp) / "Countermodel.agda"
    shutil.copyfile(source, staged)
    proc = subprocess.run(
        [str(dump_bin), "--require-complete", "-i", tmp, "-i", "/usr/share/agda-stdlib", str(staged)],
        capture_output=True, text=True, check=True,
    )
    wire = " ".join(proc.stdout.split())

rendered = (
    "module Code.Countermodel.Wire where\n\n"
    "open import Data.String using (String)\n\n"
    "countermodelWire : String\n"
    f"countermodelWire = {json.dumps(wire, ensure_ascii=False)}\n"
)

if "--check" in sys.argv:
    if not target.is_file() or target.read_text() != rendered:
        raise SystemExit("Code/Countermodel/Wire.agda differs from prompts/Countermodel.agda")
else:
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(rendered)
