"""Check request isolation and scope-only imports on one resident frontend."""
import json
from pathlib import Path
import subprocess
import sys


def main(binary, work):
    work.mkdir()
    other = work / "other"
    other.mkdir()
    leaf, bridge, top = [work / f"{name}.agda" for name in ("Leaf", "Bridge", "Top")]
    original = "module Leaf where\ndata A : Set where a : A\npoison : A\npoison = A\n"
    leaf.write_text(original)
    bridge.write_text("module Bridge where\nopen import {- gap -} Leaf public\n")
    top.write_text("module Top where\nopen import Bridge\npick : A\npick = a\n")
    with subprocess.Popen([binary, "--daemon", "-i", "/usr/share/agda-stdlib"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          text=True, encoding="utf-8") as worker:
        def call(cmd):
            worker.stdin.write(json.dumps(cmd) + "\n")
            worker.stdin.flush()
            return json.loads(worker.stdout.readline())

        def dump(main_file=top, deps=(), expect=True):
            result = call({"cmd": "dump", "main": str(main_file), "deps": list(map(str, deps)),
                           "includes": [str(work), str(other)]})
            assert result["ok"] == expect, result
            assert not list(work.rglob("*.agdai")), "scope-only request wrote an interface"
            return result

        try:
            headers = call({"cmd": "headers", "sources": [
                "module\n Foo.Bar\n where\n private\n  import {- gap -} Leaf\n"]})
            assert headers["headers"] == [{"name": "Foo.Bar", "imports": ["Leaf"]}], headers

            # Leaf.poison is ill-typed. Even a dependency that imports the
            # nominated main must see only its in-memory scope interface.
            backwards = dump(leaf, [bridge])
            assert len(backwards["dep_sexprs"]) == 1 and '"poison"' in backwards["sexpr"]
            before = dump()
            assert before == dump()
            leaf.write_text(original.replace("where a : A", "where b : A"))
            dump(expect=False)
            leaf.write_text(original)
            assert before == dump()

            shadow = other / "Leaf.agda"
            shadow.write_text(original)
            dump(expect=False)
            shadow.unlink()
            leaf.write_text("{-# OPTIONS --guardedness #-}\n" + original)
            dump(expect=False)
            leaf.write_text(original.replace("poison : A\npoison = A", "postulate poison : A"))
            dump()
            (work / "local.agda-lib").write_text("name: local\ninclude: .\nflags: --safe\n")
            dump(expect=False)
            (work / "local.agda-lib").unlink()

            top.write_text("module Top where\nmissing : Set\n")
            spec = dump()
            assert spec["check_errors"] and '"missing"' in spec["sexpr"], spec
            top.write_text("module Top where\npostulate missing : Set\n")
            assert dump()["check_errors"] == []

            # A re-export carries the name in its scope. Expansion also needs
            # the defining module's pattern table from its compiled interface.
            top.write_text("module Top where\nopen import Data.Integer using (+[1+_])\n"
                           "pattern positive n = +[1+ n ]\n")
            assert '(patsyn "positive"' in dump()["sexpr"]
        finally:
            worker.terminate()


if __name__ == "__main__":
    main(sys.argv[1], Path(sys.argv[2]))
