"""Exercise native namespace isolation using bounded payloads and private fixtures."""
import hashlib
import os
from pathlib import Path
import selectors
import shutil
import subprocess
import sys
import tempfile
import time
import uuid

launcher, probe = map(lambda value: Path(value).resolve(), sys.argv[1:])
def mount_table():
    return set(Path("/proc/self/mountinfo").read_text().splitlines())

with tempfile.TemporaryDirectory() as directory:
    top = Path(directory)
    fixtures, seed, base = [top / name for name in ("fixtures", "seed", "base")]
    for path in (fixtures, seed, base):
        path.mkdir(mode=0o755)
    marker = top / "private-marker"
    marker.write_text("unmounted sentinel")
    (fixtures / "host-marker").symlink_to(marker)
    immutable = fixtures / "immutable"
    immutable.write_text("Immutable")
    immutable.chmod(0o666)
    (seed / "seed").write_text("Seed")
    (base / "base-marker").write_text("Base")
    initial_digest = hashlib.sha256(immutable.read_bytes()).hexdigest()
    mounts = mount_table()
    def run(mode, *args, timeout_ms=2000, expected=0):
        out = top / ("out-" + mode)
        out.mkdir()
        start = time.monotonic()
        p = subprocess.run([launcher, fixtures, seed, out, base, probe, str(timeout_ms), mode, *args],
                           cwd=top, stdin=subprocess.DEVNULL, capture_output=True,
                           env={**os.environ, "LOJITA_PRIVATE_MARKER": "private"}, timeout=5)
        elapsed = time.monotonic() - start
        if p.returncode != expected:
            raise RuntimeError(f"{mode}: {p.returncode}, stdout={p.stdout!r}, stderr={p.stderr!r}")
        return out, elapsed
    out, _ = run("normal", marker)
    assert (out / "new").read_bytes() == b"X"
    assert os.readlink(out / "link-out") == "/outside"
    assert (seed / "seed").read_text() == "Seed" and not (seed / "new").exists()
    assert initial_digest == hashlib.sha256(immutable.read_bytes()).hexdigest()
    assert marker.read_text() == "unmounted sentinel"
    _, elapsed = run("limits")
    assert elapsed < .5, f"limit enforcement took {elapsed:.3f}s"
    tag = "lji-" + uuid.uuid4().hex[:10]
    run("orphan", tag)
    start = time.monotonic()
    for path in Path("/proc").glob("[0-9]*/comm"):
        try:
            assert path.read_text().strip() != tag, f"orphan found: {path}"
        except (ProcessLookupError, FileNotFoundError):
            pass
    assert time.monotonic() - start < .05, "descendant census exceeded 50 ms"
    _, elapsed = run("wait", timeout_ms=100, expected=124)
    assert elapsed < .5, f"timeout reaping took {elapsed:.3f}s"
    # Kill our own launcher after an explicit child handshake, simulating caller death.
    abort = top / "abandoned"
    abort.mkdir()
    tag = "lja-" + uuid.uuid4().hex[:10]
    with subprocess.Popen([launcher,fixtures,seed,abort,"-",probe,"2000","abort",tag],
                          stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE) as lab:
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(lab.stdout,selectors.EVENT_READ)
                assert selector.select(2) and lab.stdout.read(1)==b"R", "abnormal-exit handshake"
            lab.kill()
            lab.communicate(timeout=2)
        finally:
            lab.kill()
    deadline=time.monotonic()+.05
    while True:
        marked=False
        for file in Path("/proc").glob("[0-9]*/comm"):
            try:
                marked |= file.read_text().strip()==tag
            except (ProcessLookupError,FileNotFoundError):
                pass
        if not marked: break
        assert time.monotonic()<deadline, "caller death left a marked child"
    assert list(abort.iterdir())==[], "abnormal exit published incomplete data"

    # A dynamic reference can use a curated base with its loader and libraries.
    printf = Path("/usr/bin/printf")
    libs = subprocess.check_output(["ldd", printf], text=True)
    for line in libs.splitlines():
        words = line.split()
        paths = [Path(w) for w in words if w.startswith("/")]
        for lib in paths:
            target = base / lib.relative_to("/")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(lib, target)
    dyn = top / "dynamic"
    dyn.mkdir()
    dynamic = subprocess.run([launcher, fixtures, seed, dyn, base, printf, "1000", "%s", "dynamic"],
                             stdin=subprocess.DEVNULL, capture_output=True, timeout=3)
    assert dynamic.returncode == 0 and dynamic.stdout == b"dynamic", dynamic.stderr

    # Corrupt one byte in a disposable store. The immutable mounted source stays intact.
    objects = Path(__file__).resolve().parents[2] / "Lojita/Store/TreeCAS/objects.py"
    store = top / "cas"
    cli = [sys.executable, "-I", objects]
    tree = subprocess.check_output([*cli, "capture", store, fixtures], text=True).strip()
    subprocess.run([*cli, "verify", store, tree], check=True, capture_output=True)
    blob = store / "blob" / initial_digest
    blob.chmod(0o600)
    with blob.open("r+b") as f:
        f.write(b"!")
    bad = subprocess.run([*cli, "verify", store, tree], capture_output=True)
    assert bad.returncode != 0 and b"CAS_HASH_MISMATCH" in bad.stderr, bad
    broken = top / "bad-materialization"
    bad = subprocess.run([*cli, "materialize", store, tree, broken], capture_output=True)
    assert bad.returncode != 0 and b"CAS_HASH_MISMATCH" in bad.stderr and not broken.exists(), bad

    if os.geteuid() == 0:
        # Run from an already-open cwd, even if TMPDIR itself belongs to root.
        fallback = top / "userns"
        fallback.mkdir()
        for name in ("in", "seed", "out"):
            path = fallback / name
            path.mkdir()
            os.chown(path, 65534, 65534)
        shutil.copy2(launcher, fallback / "launcher")
        shutil.copy2(probe, fallback / "probe")
        def unprivileged():
            os.setgroups([])
            os.setgid(65534)
            os.setuid(65534)
        user = subprocess.run(["./launcher", "in", "seed", "out", "-", "./probe", "1000", "cas"],
                              cwd=fallback, preexec_fn=unprivileged, input=b"userns",
                              capture_output=True, timeout=3)
        if user.returncode == 125 and user.stdout == b"userns" and user.stderr == b"abcdef":
            print("Unprivileged user namespace worked.")
        else:
            assert user.returncode == 125 and b"Operation not permitted" in user.stderr, user
            assert user.stderr.startswith((b"unshare ", b"/proc/self/uid_map:")), user.stderr
            print("Host user namespace policy refused the unprivileged path:", user.stderr.decode().strip())

    assert mounts == mount_table(), "host mount table changed"
print("Namespace confinement, immutable input, work export, bounded limits, orphan teardown and timeout passed.")
