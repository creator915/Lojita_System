"""Replayable Linux / PosixCore differential gate. No third-party packages."""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import random
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("treecas", ROOT / "Lojita/Store/TreeCAS/objects.py")
cas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cas)
NAMES = ["openat", "close", "read", "write", "dup2", "lseek", "mkdirat", "unlinkat",
         "renameat", "symlinkat", "readlinkat", "pipe2", "ppoll", "openpty", "tcsetattr",
         "SIGWINCH/ppoll", "pread", "pwrite", "writeAll", "readLine+readAll",
         "one-page pipe", "page write", "page read"]
def command(op, a=0, b=0, c=0):
    return [op, a, b, c]

def generate(seed, ident):
    rng = random.Random((seed << 32) + ident)
    n = rng.randint(15, 40)
    C = command
    filename, content = rng.choice([0,1,2,11]), rng.randrange(256)
    length = rng.randint(1,23)
    target = rng.choice([0,12])
    templates = [
        [C(0,filename,6,0o664), C(3,3,length,content), C(4,3,9), C(5,9,8,0),
         C(2,3,rng.randrange(length+1)), C(2,9,24), C(7,filename), C(0,filename),
         C(5,3,8,0), C(2,9,length), C(1,3), C(1,9)],
        [C(6,4,0o755), C(6,3,0o755), C(6,3,0o755), C(0,0,6,0o640),
         C(9,target,6), C(9,rng.choice([6,13]),7), C(0,7), C(0,7,128),
         C(10,7), C(8,0,4), C(0,7), C(7,3,1), C(8,4,5), C(7,5)],
        [C(11), C(2,3,4), C(3,4,length,content), C(12,3,4), C(2,3,rng.randint(1,23)),
         C(4,4,9), C(1,4), C(3,9,3,content), C(1,3), C(12,3,9),
         C(3,9,1,content), C(1,9), C(15)],
        [C(13), C(3,3,length,content), C(2,4,length), C(14,4,1),
         C(3,3,1,97), C(2,4,9), C(3,3,1,10), C(2,4,23), C(14,4,0),
         C(3,4,length,content), C(2,3,length), C(1,4), C(1,3)],
        [C(0,filename,6,0o600), C(18,3,rng.randint(0,38),rng.randint(256,350)),
         C(5,3,8), C(19,3,rng.randint(1,9)), C(0,filename,34,0o600),
         C(17,4,length,content), C(5,3,8), C(19,3,rng.randint(1,6))],
        [C(0,filename,6,0o664), C(11), C(3,5,length,content), C(4,3,8),
         C(16,8,4,2), C(12,4,5), C(1,5), C(2,4,23), C(2,4,23), C(15)]]
    steps = templates[ident % len(templates)]
    if ident%100 == 99:
        steps=[C(20), C(21,4,rng.randint(1,23),content), C(12,3,4), C(2,3,1),
               C(3,4,1,content), C(12,3,4), C(22,3), C(12,3,4),
               C(21,4,0,content), C(12,3,4), C(3,4,2,content), C(3,4,1,content),
               C(22,3), C(1,3), C(3,4,1,content)]
    while len(steps) < n:
        op = rng.choice([0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,15,16,17,18])
        fd = rng.choice([3,4,5,6,9,10,63])
        p = rng.randrange(16)
        if op==0:
            access = rng.choice([0,1,2])
            fl = access | rng.choice([0,4,12,16,20,32,36,64,128,192])
            args=(p, fl, rng.choice([0o644,0o664,0o600,0o666]))
        elif op in (1,): args=(fd,)
        elif op in (2,): args=(fd,rng.randrange(24))
        elif op in (3,17,18): args=(fd,rng.randrange(24),rng.randrange(256))
        elif op in (4,12): args=(fd,rng.choice([3,4,5,9,10,63]))
        elif op==5: args=(fd,rng.randrange(25),rng.randrange(3))
        elif op==6: args=(p,rng.choice([0o755,0o775,0o777]))
        elif op==7: args=(p,rng.randrange(2))
        elif op in (8,9): args=(p,rng.randrange(16))
        elif op==10: args=(p,)
        elif op==16: args=(fd,rng.randrange(24),rng.randrange(12))
        else: args=()
        steps.append(C(op,*args))
    return {"ident":ident,"steps":steps}

def digest(kind, mode, contents):
    if kind == "t":
        entries = [(name, k.encode(), m, h) for name, (k,m,h) in sorted(contents)]
        data = cas.encode_tree(mode, entries)
    else:
        data = contents
    return kind, mode, hashlib.sha256(data).hexdigest()

def physical(path):
    info = os.lstat(path)
    mode = stat.S_IMODE(info.st_mode)
    if stat.S_ISLNK(info.st_mode):
        return digest("s", mode, os.readlink(path))
    if stat.S_ISREG(info.st_mode):
        with open(path,"rb") as f: return digest("b", mode, f.read())
    if stat.S_ISDIR(info.st_mode):
        return digest("t", mode, [(n,physical(os.path.join(path,n))) for n in os.listdir(path)])
    raise AssertionError(f"unexpected native node {path!r}")

def predicted(node):
    kind, (mode, body) = node
    if kind == "t":
        return digest(kind, mode, [(bytes.fromhex(n),predicted(child)) for n,child in body])
    return digest(kind, mode, bytes.fromhex(body))

class Runner:
    def __init__(self, args):
        self.seen = Counter()
        self.errors = Counter()
        self.short_read = 0
        self.short_write = 0
        self.launcher, self.probe, self.model = [Path(p).resolve() for p in (args.launcher,args.probe,args.model)]
    def batch(self, cases):
        with tempfile.TemporaryDirectory() as tmp:
            top = Path(tmp)
            fixtures, seed, export = [top/n for n in ("fixtures","seed","export")]
            for p in (fixtures,seed,export): p.mkdir()
            commands = []
            for case in cases:
                commands += [f"{case['ident']} {len(case['steps'])}"]
                commands += [" ".join(map(str,r)) for r in case["steps"]]
            native = subprocess.run([self.launcher,fixtures,seed,export,"-",self.probe,"10000"],
                                    input="\n".join(commands)+"\n", text=True, capture_output=True, timeout=15)
            if native.returncode:
                raise RuntimeError(f"native observer exited {native.returncode}: {native.stderr}")
            replies = native.stdout.splitlines()
            rows = []
            start = 0
            for case in cases:
                end = start+len(case["steps"])
                rows.append({**case,"linux":replies[start:end]})
                start = end
            assert start==len(replies), "wrong number of Linux observations"
            shadows = subprocess.run([self.model],input="\n".join(map(json.dumps,rows))+"\n",
                                     text=True,capture_output=True,timeout=30,check=True)
            predictions = list(map(json.loads,shadows.stdout.splitlines()))
            assert len(rows)==len(predictions), "wrong number of model results"
            for case,(answers,tree) in zip(rows,predictions):
                assert len(answers)==len(case["steps"])
                for i,(actual,expected) in enumerate(zip(case["linux"],answers)):
                    op, _, want, _ = case["steps"][i]
                    self.seen[NAMES[op]] += 1
                    if actual.startswith("E"):
                        self.errors[int(actual[1:])] += 1
                    if op == 2 and actual.startswith("B") and 0 < (len(actual)-1)//2 < want:
                        self.short_read += 1
                    if op == 21 and want and actual.startswith("N") and 0<int(actual[1:])<4096+want:
                        self.short_write+=1
                    if actual != expected:
                        op = case["steps"][i][0]
                        return case, (NAMES[op],actual,expected), f"step {i+1} {case['steps'][i]} Linux {actual} Lean {expected}"
                live = physical(os.fsencode(export / f"D{case['ident']}"))
                model = predicted(tree)
                if live != model:
                    return case, ("TreeCAS",), f"TreeCAS Linux {live[2]} Lean {model[2]}"
            return None

def shrink(runner, case, failure):
    original = case["steps"]
    steps, n = original[:], 2
    while steps:
        width = (len(steps)+n-1)//n
        for i in range(0,len(steps),width):
            trial = steps[:i]+steps[i+width:]
            found = runner.batch([{**case,"steps":trial}])
            if found and found[1] == failure:
                steps, n = trial, max(2,n-1)
                break
        else:
            if n >= len(steps): break
            n = min(len(steps), n*2)
    return {"ident":case["ident"],"steps":steps}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("launcher","probe","model"): parser.add_argument(name)
    parser.add_argument("--seed",type=int,default=680024)
    parser.add_argument("--count",type=int,default=2000)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--replay",type=Path)
    parser.add_argument("--artifact",type=Path,default=ROOT/".lake/build/io-diff-counterexample.json")
    args=parser.parse_args()
    if args.count < 1 or args.start < 0 or args.seed < 0:
        parser.error("count must be positive, start and seed must be nonnegative")
    distro=platform.freedesktop_os_release()
    identity=(distro.get("ID"),distro.get("VERSION_ID"),platform.machine())
    if identity != ("ubuntu","24.04","x86_64") or not platform.release().startswith("6.8."):
        parser.error(f"this conformance profile requires Ubuntu 24.04 x86-64 Linux 6.8, got {identity} {platform.release()}")
    print(f"Linux oracle: {distro['PRETTY_NAME']}, {platform.release()}, {platform.machine()}.", flush=True)
    cases = [json.loads(args.replay.read_text())] if args.replay else [generate(args.seed,i) for i in range(args.start,args.start+args.count)]
    runner = Runner(args)
    total = 0
    for i in range(0,len(cases),40):
        batch=cases[i:i+40]
        mismatch = runner.batch(batch)
        if mismatch:
            bad,signature,why=mismatch
            print(f"Gate 3 counterexample seed {args.seed} case {bad['ident']}: {why}",file=sys.stderr,flush=True)
            minimized=shrink(runner,bad,signature)
            args.artifact.parent.mkdir(parents=True, exist_ok=True)
            args.artifact.write_text(json.dumps(minimized)+"\n")
            print(f"Minimized {len(bad['steps'])} to {len(minimized['steps'])} steps. Replay with --replay {args.artifact}",file=sys.stderr)
            return 1
        total += sum(len(t["steps"]) for t in batch)
    if not args.replay and args.count >= 2000:
        assert set(runner.seen) == set(NAMES)
        assert runner.errors[4] and runner.errors[11] and runner.errors[32] and runner.short_read and runner.short_write
    print(f"Linux coverage: EINTR={runner.errors[4]}, EAGAIN={runner.errors[11]}, EPIPE={runner.errors[32]}, "
          f"short reads={runner.short_read}, short writes={runner.short_write}, openpty={runner.seen['openpty']}, "
          f"writeAll={runner.seen['writeAll']}, readLine+readAll={runner.seen['readLine+readAll']}.")
    label = "Gate 3" if len(cases) >= 2000 else "Diagnostic replay"
    print(f"{label} seed {args.seed}: {len(cases)} traces, {total} steps, {len(cases)} matching TreeCAS roots, zero counterexamples.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
