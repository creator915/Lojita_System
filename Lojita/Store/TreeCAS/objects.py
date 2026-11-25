"""Byte-preserving, content-addressed filesystem trees used by the Linux runner."""
import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import stat
import struct
import tempfile

KINDS = {b"b": "blob", b"s": "symlink", b"t": "tree"}
MAGIC = b"LJT1"
DIR = os.O_DIRECTORY | os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked_id(value):
    if len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise ValueError("invalid TreeCAS digest")
    return value


def load(store, kind, oid):
    data = (store / KINDS[kind] / checked_id(oid)).read_bytes()
    if digest(data) != oid:
        raise ValueError("CAS_HASH_MISMATCH " + oid)
    return data


def save(store, kind, data):
    oid = digest(data)
    folder = store / KINDS[kind]
    folder.mkdir(parents=True, exist_ok=True)
    final = folder / oid
    if final.exists():
        load(store, kind, oid)
        return oid
    with tempfile.NamedTemporaryFile(dir=folder, delete=False) as f:
        temp = Path(f.name)
        try:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
            if digest(temp.read_bytes()) != oid:
                raise ValueError("CAS_HASH_MISMATCH " + oid)
            os.chmod(temp, 0o444)
            os.replace(temp, final)
            with opening(folder, DIR) as directory:
                os.fsync(directory)
        finally:
            temp.unlink(missing_ok=True)
    return oid


@contextlib.contextmanager
def opening(path, flags, *, parent=None):
    fd = os.open(path, flags, dir_fd=parent)
    try:
        yield fd
    finally:
        os.close(fd)


def valid_name(name):
    return bool(name) and name not in (b".", b"..") and b"/" not in name and b"\0" not in name and len(name) <= 255


def encode_tree(mode, entries):
    out = bytearray(MAGIC + struct.pack(">H", mode))
    for name, kind, entry_mode, oid in entries:
        out.extend(struct.pack(">HcH", len(name), kind, entry_mode))
        out.extend(name)
        out.extend(bytes.fromhex(oid))
    return bytes(out)


def decode_tree(data):
    if len(data) < 6 or data[:4] != MAGIC:
        raise ValueError("invalid TreeCAS tree header")
    mode = int.from_bytes(data[4:6], "big")
    pos, last, entries = 6, b"", []
    if mode > 0o777:
        raise ValueError("invalid TreeCAS directory mode")
    while pos < len(data):
        if pos + 5 > len(data):
            raise ValueError("truncated TreeCAS entry")
        length, kind, perms = struct.unpack_from(">HcH", data, pos)
        pos += 5
        end = pos + length
        if end + 32 > len(data):
            raise ValueError("truncated TreeCAS digest")
        name, oid = data[pos:end], data[end:end + 32].hex()
        if (kind == b"s" and perms != 0o777) or kind not in KINDS or not valid_name(name) or name <= last or perms > 0o777:
            raise ValueError("invalid or unsorted TreeCAS entry")
        entries.append((name, kind, perms, oid))
        pos, last = end + 32, name
    return mode, entries


def capture(store, directory):
    before = os.fstat(directory)
    if before.st_mode & 0o7000:
        raise ValueError("unsupported special directory permission bits")
    entries = []
    for name in sorted(os.fsencode(s) for s in os.listdir(directory)):
        info = os.stat(name, dir_fd=directory, follow_symlinks=False)
        if not stat.S_ISDIR(info.st_mode) and info.st_nlink != 1:
            raise ValueError("hard links cannot be represented by a TreeCAS tree")
        if info.st_mode & 0o7000:
            raise ValueError("special permission bits cannot be represented by a TreeCAS tree")
        if stat.S_ISLNK(info.st_mode):
            kind = b"s"
            oid = save(store, kind, os.readlink(name, dir_fd=directory))
        elif stat.S_ISDIR(info.st_mode):
            kind = b"t"
            with opening(name, DIR, parent=directory) as child:
                if not os.path.samestat(info, os.fstat(child)):
                    raise ValueError("TreeCAS source changed during capture")
                oid = capture(store, child)
        elif stat.S_ISREG(info.st_mode):
            kind = b"b"
            flags = os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW | os.O_CLOEXEC
            with opening(name, flags, parent=directory) as child:
                if not os.path.samestat(info, os.fstat(child)):
                    raise ValueError("TreeCAS source changed during capture")
                with os.fdopen(child, "rb", closefd=False) as f:
                    oid = save(store, kind, f.read())
                after = os.fstat(child)
                if (info.st_mtime_ns, info.st_ctime_ns) != (after.st_mtime_ns, after.st_ctime_ns):
                    raise ValueError("TreeCAS file changed during capture")
        else:
            raise ValueError("unsupported TreeCAS node type")
        entries.append((name, kind, info.st_mode & 0o777, oid))
    after = os.fstat(directory)
    if (before.st_mtime_ns, before.st_ctime_ns) != (after.st_mtime_ns, after.st_ctime_ns):
        raise ValueError("TreeCAS directory changed during capture")
    return save(store, b"t", encode_tree(before.st_mode & 0o777, entries))


def walk(store, oid, target=None, mode=None, active=None):
    active = set() if active is None else active
    if oid in active:
        raise ValueError("cyclic TreeCAS graph")
    actual, entries = decode_tree(load(store, b"t", oid))
    if mode is not None and actual != mode:
        raise ValueError("inconsistent TreeCAS directory mode")
    active.add(oid)
    for name, kind, perms, ref in entries:
        if kind == b"t":
            if target is None:
                walk(store, ref, mode=perms, active=active)
            else:
                os.mkdir(name, 0o700, dir_fd=target)
                with opening(name, DIR, parent=target) as child:
                    walk(store, ref, child, perms, active)
        else:
            content = load(store, kind, ref)
            if kind == b"s" and (not content or len(content) >= 4096 or b"\0" in content):
                raise ValueError("invalid TreeCAS symlink body")
            if target is None:
                continue
            if kind == b"s":
                os.symlink(content, name, dir_fd=target)
            else:
                fd = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=target)
                with os.fdopen(fd, "wb") as f:
                    f.write(content)
                    os.fchmod(fd, perms)
    active.remove(oid)
    if target is not None:
        os.fchmod(target, actual)


def read_image(store, root):
    rows = []

    def visit(kind, oid, mode, parent, visiting):
        ident = len(rows) + 1
        row = dict(ident=ident, mode=mode, parent=parent, kind=kind.decode(), data=[], entries=[])
        rows.append(row)
        data = load(store, kind, oid)
        if kind != b"t":
            row["data"] = list(data)
            return ident
        actual, items = decode_tree(data)
        if (mode is not None and mode != actual) or oid in visiting:
            raise ValueError("inconsistent directory in TreeCAS")
        row["mode"] = actual
        for name, child_kind, perms, digest_id in items:
            child = visit(child_kind, digest_id, perms, ident, visiting | {oid})
            row["entries"].append([list(name), child])
        return ident

    visit(b"t", root, None, 1, set())
    return rows


def save_image(store, rows):
    # Input comes from the Lean canonicalTree projection. Check the external
    # framing as well before writing any directory reference into a tree.
    nodes = {r["ident"]: r for r in rows}
    used = set()

    def visit(i, parent):
        if i in used:
            raise ValueError("cyclic tree or multiple incoming links")
        used.add(i)
        row = nodes[i]
        kind, mode = row["kind"].encode(), row["mode"]
        if kind not in KINDS or not 0 <= mode <= 0o777:
            raise ValueError("bad image row")
        if kind == b"t":
            if row["parent"] != parent:
                raise ValueError("bad parent pointer")
            entries = [(bytes(name), *visit(ref, i)) for name, ref in row["entries"]]
            data = encode_tree(mode, entries)
            decode_tree(data)
        else:
            data = bytes(row["data"])
            if kind == b"s" and (mode != 0o777 or not data or len(data) >= 4096 or b"\0" in data):
                raise ValueError("bad symlink")
        return kind, mode, save(store, kind, data)

    kind, _, oid = visit(1, 1)
    if kind != b"t" or len(used) != len(rows):
        raise ValueError("invalid image root or unreachable node")
    return oid


def main():
    p = argparse.ArgumentParser()
    p.add_argument("command", choices=["capture", "materialize", "verify", "read-image", "save-image"])
    p.add_argument("store", type=Path)
    p.add_argument("value")
    p.add_argument("destination", type=Path, nargs="?")
    a = p.parse_args()
    if a.command == "capture":
        source = Path(a.value).resolve(strict=True)
        if a.store.resolve().is_relative_to(source):
            p.error("TreeCAS store must be outside the captured directory")
        with opening(source, DIR) as src:
            print(capture(a.store, src))
    elif a.command == "read-image":
        print(json.dumps(read_image(a.store, a.value), separators=(",", ":")))
    elif a.command == "save-image":
        with open(a.value) as manifest:
            print(save_image(a.store, json.load(manifest)))
    elif a.command == "verify":
        walk(a.store, a.value)
    else:
        if a.destination is None:
            p.error("materialize requires a destination")
        # Build privately; a failed hash check never publishes a partial tree.
        with tempfile.TemporaryDirectory(dir=a.destination.parent) as tmp:
            tree = Path(tmp) / "root"
            tree.mkdir(mode=0o700)
            with opening(tree, DIR) as root:
                walk(a.store, a.value, root)
            # renameat2 RENAME_NOREPLACE prevents races with another publisher.
            import ctypes
            libc = ctypes.CDLL(None, use_errno=True)
            if libc.renameat2(-100, os.fsencode(tree), -100, os.fsencode(a.destination), 1):
                e = ctypes.get_errno()
                raise OSError(e, os.strerror(e), a.destination)


if __name__ == "__main__":
    main()
