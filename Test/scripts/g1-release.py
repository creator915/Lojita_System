"""Check the actual Lean distribution used by G1, including executable, native and module artifacts."""
import hashlib
import os
import platform
import sys
from pathlib import Path

release = Path(sys.argv[1]).resolve()
catalog = Path(__file__).resolve().parents[1] / "audit" / "lean-4.36.0-release.tsv"
key = platform.system() + "-" + platform.machine()
modules = []
for pkg in ("Init", "Std", "Lean", "Lake"):
    root = release / "lib" / "lean"
    for path in [*root.glob(pkg + ".*"), *(root / pkg).rglob("*")]:
        if path.is_file() and any(path.name.endswith(s) for s in (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")):
            modules.append(path)
native = [release / "bin" / n for n in ("lean", "leanir", "lake", "leanc")]
native += list((release / "include" / "lean").rglob("*.h"))
native += [p for p in (release / "lib" / "lean").iterdir() if p.is_file() and
           (p.suffix in (".a", ".so", ".dylib") or ".so." in p.name)]
def digest(files):
    result = hashlib.sha256()
    for path in sorted(files):
        result.update(os.fsencode(path.relative_to(release).as_posix()) + b"\0")
        with path.open("rb") as stream:
            item = hashlib.sha256()
            while block := stream.read(1 << 20):
                item.update(block)
        result.update(item.digest())
    return result.hexdigest()
found = [key, digest(modules), digest(native)]
if found not in [line.split("\t") for line in catalog.read_text().splitlines()]:
    sys.exit("G1 DENY [origin] unpinned Lean distribution: " + "\t".join(found))
print("G1 pinned release " + " ".join(found))
