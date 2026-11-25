"""Independent fixtures for the published LJT1 format. No Python in the runtime."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import os
from pathlib import Path
import stat
import shutil
import statistics
import struct
import subprocess
import sys
import tempfile

EXE = str(Path(sys.argv[1]).resolve())
KINDS = {b"b": "blob", b"s": "symlink", b"t": "tree"}


def run(*args, ok=True):
    proc = subprocess.run([EXE, *map(str, args)], capture_output=True, text=True,
                          env={**os.environ, "PATH": ""}, timeout=20)
    assert (proc.returncode == 0) == ok, (args, proc.returncode, proc.stderr)
    return proc.stdout.strip() if ok else proc.stderr


def entry(name, kind, mode, digest):
    return struct.pack(">HcH", len(name), kind, mode) + name + bytes.fromhex(digest)


def tree(mode, *entries):
    return b"LJT1" + struct.pack(">H", mode) + b"".join(entries)


def put(store, kind, data):
    digest = sha256(data).hexdigest()
    folder = store / KINDS[kind]
    folder.mkdir(parents=True, exist_ok=True)
    (folder / digest).write_bytes(data)
    return digest


def fixtures(tmp):
    store = tmp / "reference"
    payload = b"\x80\x00\xff\n"
    raw = b"a\xff"
    blob = put(store, b"b", payload)
    link = put(store, b"s", raw)
    sub = put(store, b"t", tree(0o555, entry(b"alias", b"s", 0o777, link)))
    root = put(store, b"t", tree(0o751, entry(raw, b"b", 0o604, blob),
                                entry(b"b", b"t", 0o555, sub), entry(b"z", b"b", 0o640, blob)))
    run("verify", store, root)
    if shutil.which("strace"):
        trace = tmp / "execs"
        subprocess.run(["strace", "-f", "-qq", "-e", "trace=execve,execveat", "-o", trace,
                        EXE, "load-save", str(store), root, str(tmp / "traced")],
                       check=True, stdout=subprocess.DEVNULL, timeout=20)
        execs = trace.read_text().splitlines()
        assert len(execs) == 1 and EXE in execs[0], execs
    dst = tmp / "mat"
    run("materialize", store, root, dst)
    assert stat.S_IMODE(dst.stat().st_mode) == 0o751
    assert stat.S_IMODE(os.stat(os.fsencode(dst) + b"/" + raw).st_mode) == 0o604
    with open(os.fsencode(dst) + b"/" + raw, "rb") as opened:
        assert opened.read() == payload
    assert os.readlink(os.fsencode(dst / "b" / "alias")) == raw
    assert stat.S_IMODE((dst / "b").stat().st_mode) == 0o555
    assert (dst / "z").stat().st_ino != os.stat(os.fsencode(dst) + b"/" + raw).st_ino
    dest_store = tmp / "captured"
    assert run("capture", dest_store, dst) == root
    assert run("load-save", store, root, tmp / "from-image") == root
    for path in store.rglob("*"):
        if path.is_file():
            rel = path.relative_to(store)
            for copy in [dest_store, tmp / "from-image"]:
                assert path.read_bytes() == (copy / rel).read_bytes(), rel
    run("materialize", store, root, dst, ok=False)
    assert run("capture", dest_store, dst) == root
    nested = dst / "nested-cas"
    run("capture", nested, dst, ok=False)
    assert not nested.exists()
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda _: run("capture", tmp / "parallel", dst), range(8)))
    assert results == [root] * len(results)
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda _: subprocess.run(
            [EXE, "materialize", str(store), root, str(tmp / "published")],
            capture_output=True, timeout=20).returncode, range(8)))
    assert results.count(0) == 1
    assert run("capture", dest_store, tmp / "published") == root
    assert not list(tmp.glob(".lojita-*"))
    print("LJT1 old-format read/write, raw names and targets, modes, repeated digests and publication OK")
    return store, root, blob


def malformed(tmp, store, root, blob):
    normal = entry(b"a", b"b", 0o600, blob)
    wrong = [
        b"XJT1\0\0", b"LJT1\0", tree(0o1000), tree(0, normal[:-1]),
        tree(0, *(entry(name, b"b", 0o600, blob) for name in [b"z", b"a"])),
        tree(0, normal, normal), tree(0, entry(b"a", b"x", 0, blob)),
        tree(0, entry(b"a", b"b", 0o1000, blob)),
        tree(0, entry(b"a", b"s", 0o755, blob)),
        tree(0, entry(b"a", b"t", 0o600, root)),
        tree(0, entry(b"missing", b"b", 0o444, "00"*32)),
        *(tree(0, entry(name, b"b", 0, blob)) for name in
          [b"", b".", b"..", b"a/b", b"a\0b", b"x"*256]),
        *(tree(0, entry(b"target", b"s", 0o777, put(store, b"s", body)))
          for body in [b"", b"a\0b", b"x"*4096]),
    ]
    dest = tmp / "invalid-materialization"
    bad_ids = [put(store, b"t", data) for data in wrong] + [root[:-1], root.upper(), "../" + root]
    for oid in bad_ids:
        run("verify", store, oid, ok=False)
        run("load", store, oid, ok=False)
        run("materialize", store, oid, dest, ok=False)
        assert not dest.exists() and not list(tmp.glob(".lojita-*"))
    # A later failing entry must remove an already-restored mode-000 directory.
    locked = put(store, b"t", tree(0))
    late = put(store, b"t", tree(0o700, entry(b"a", b"t", 0, locked),
                                entry(b"z", b"b", 0o600, "00"*32)))
    run("materialize", store, late, dest, ok=False)
    assert not dest.exists() and not list(tmp.glob(".lojita-*"))
    path = store / "blob" / blob
    payload = path.read_bytes()
    path.write_bytes(b"changed")
    assert "CAS_HASH_MISMATCH" in run("verify", store, root, ok=False)
    run("load", store, root, ok=False)
    run("materialize", store, root, dest, ok=False)
    run("load-save", tmp / "captured", root, store, ok=False)
    assert path.read_bytes() == b"changed" and not dest.exists()
    path.unlink()
    sentinel = tmp / "untouched"
    sentinel.write_bytes(payload)
    path.symlink_to(sentinel)
    run("verify", store, root, ok=False)
    run("load-save", tmp / "captured", root, store, ok=False)
    assert path.is_symlink() and sentinel.read_bytes() == payload
    print(f"{len(bad_ids)} malformed trees/digests rejected by verify, load and materialize; corruption isolated")


def unsupported(tmp):
    src = tmp / "unsupported"
    src.mkdir()
    data = src / "file"
    data.write_bytes(b"x")
    os.link(data, src / "hardlink")
    run("capture", tmp / "obj", src, ok=False)
    (src / "hardlink").unlink()
    os.mkfifo(src / "pipe")
    run("capture", tmp / "obj", src, ok=False)
    (src / "pipe").unlink()
    data.chmod(0o4755)
    run("capture", tmp / "obj", src, ok=False)
    data.chmod(0o600)
    sentinel = tmp / "keep"
    sentinel.mkdir()
    (sentinel / "file").write_bytes(b"untouched")
    os.symlink(sentinel, os.fsencode(src) + b"/\xff")
    src.chmod(0)
    run("remove", src)
    assert not src.exists() and (sentinel / "file").read_bytes() == b"untouched"
    print("Unsupported captures and byte-preserving cleanup OK")


with tempfile.TemporaryDirectory() as tmpdir:
    tmp = Path(tmpdir)
    store, root, blob = fixtures(tmp)
    malformed(tmp, store, root, blob)
    unsupported(tmp)

timings = [tuple(map(int, run("bench").split())) for _ in range(5)]
median = statistics.median(t[2] for t in timings)
print(f"4 MiB fresh-store save/load in microseconds {timings}, median {median} us")
assert median < 50_000, "4 MiB native saveTree + loadTree exceeds 50ms"
