"""Count physical source lines with non-comment tokens; handle nested Lean comments."""
import pathlib
import sys

def count(path):
    depth = lines = 0
    lean = path.suffix == ".lean"
    opening, closing, line_comment = ("/-", "-/", "--") if lean else ("/*", "*/", "//")
    for line in path.read_text().splitlines():
        idx, has_code, quoted = 0, False, False
        while idx < len(line):
            if depth:
                if line.startswith(closing, idx):
                    depth -= 1
                    idx += 2
                elif lean and line.startswith(opening, idx):
                    depth += 1
                    idx += 2
                else:
                    idx += 1
            elif quoted:
                if line[idx] == "\\":
                    idx += 2
                else:
                    quoted = line[idx] != '"'
                    idx += 1
            elif line.startswith(line_comment, idx):
                break
            elif line.startswith(opening, idx):
                depth, idx = 1, idx + 2
            else:
                has_code |= not line[idx].isspace()
                quoted = line[idx] == '"'
                idx += 1
        lines += int(has_code)
    return lines

limits = {"runtime/posix_host.c": 250, "runtime/lojita-sandbox.c": 300,
          "Lojita/Runtime/WorldRunner.lean": 180}
for root in ["LojitaCtx/Posix", "LojitaCtx/Io"]:
    limits.update({str(p): 350 for p in pathlib.Path(root).rglob("*.lean")})
limits.update({"LojitaCtx/Posix/Types.lean": 150, "LojitaCtx/Posix/Stream.lean": 180,
               "LojitaCtx/Posix/Tty.lean": 220, "LojitaCtx/Posix/Vfs.lean": 300,
               "LojitaCtx/Posix/Kernel.lean": 320, "LojitaCtx/Io/Buf.lean": 280,
               "LojitaCtx/Io/FsLib.lean": 200, "LojitaCtx/Io/Reactive.lean": 180,
               "Lojita/Store/TreeCAS.lean": 240, "Lojita/Sandbox/LinuxIso.lean": 260})
failed = False
for name, maximum in limits.items():
    path = pathlib.Path(name)
    n = count(path) if path.exists() else -1
    print(f"{name}: {n}/{maximum}")
    failed |= not 0 <= n <= maximum
sys.exit(int(failed))
