#!/usr/bin/env python3
"""Re-extract the checked-in gron inputs. No compiler or network required."""
import argparse
from collections import defaultdict
from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "Test/gron-stress"
RUNS = {
    "v3-first": ("v3-gron-sol62", "gron-run1-c0bdc08"),
    "v3": ("v3-gron-sol62", "gron"),
    "v4": ("v4-dialectica-lean", "gron"),
    "v4-v2": ("v4-dialectica-lean", "gron-v2"),
    "v4-v3": ("v4-dialectica-lean", "gron-v3"),
}
MODULE = re.compile(r"^module ([\w.]+) where\b", re.M)
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+(Gen\.[\w.]+)", re.M)
FENCE = re.compile(r"^```agda(?:[ \t]+([^\n]*))?\n(.*?)^```[ \t]*$", re.S | re.M)
PROMPT_SECTION = re.compile(
    r"^(CURRENT CODE|ORIGINAL SPECIFICATION SOURCE[^\n]*|SPECIFICATION|"
    r"PENDING DRAFT \(add-moves extends this plan\):)\n(.*?)"
    r"(?=\n(?:ORIGINAL SPECIFICATION SOURCE|SPECIFICATION|REFUTATION EXTRA POSTULATES|"
    r"PARENT FLAGS|LOCKED SEEDS|PENDING PLAN|\(plan|TRANSIENT DIAGNOSTIC)(?:\b|:)|\Z)", re.S | re.M
)
# Agda 2.6.3 outcomes for historical broken sources are pinned independently
# of the current verifier. A changed implementation must reproduce the outcome.
NEGATIVE = {
    "005707a12071": r"Could not parse the application Fast\._≟_",
    "356cee9592b6": r"primStringEquality s s != true",
    "46c72817ee94": r"does not construct an element of Path",
    "59ca982a9cf0": r"primStringEquality s s != true",
    "7d61ff352872": r"pattern 34 has type ℕ",
    "722ca9ecab16": r"primCharEquality c d !=",
    "7931daca13d1": r"primStringEquality s t !=",
    "88b7e92639be": r"!= primStringEquality s t",
    "945c092d8fe7": r"primCharEquality c c != true",
    "9e11a7effb58": r"primCharEquality c c != true",
    "a249566de826": r"Agda\.Builtin\.String\.primStringAppend",
    "cb5a19f467c6": r"when scope checking Fast\.≟",
    "e866e76a5c2d": r"when checking the constructor permutation-keep",
    "eaf7a36798cc": r"when checking the constructor permutation-keep",
    "fb831b6a9696": r"when checking the constructor permutation-keep",
    "d8dff0c111b6": r"primCharEquality c d ≟ true",
    "de65816becb8": r"pattern 39 has type ℕ",
    "df29cd5773aa": r"primStringEquality s s != true",
}


@dataclass
class Source:
    run: str
    module: str
    text: str
    digest: str
    origins: list[str] = field(default_factory=list)
    original_file: str | None = None

    @property
    def key(self):
        return self.run + "-" + self.digest[:12]

    @property
    def path(self):
        ext = ".block" if any(p.endswith(".block") for p in self.origins) else ".agda"
        return f"corpus/modules/{self.run}/{self.module}-{self.digest[:12]}{ext}"

    @property
    def payload(self):
        return self.original_file if self.original_file is not None else self.text

    def ref(self):
        checksum = hashlib.sha256(self.payload.encode()).hexdigest()
        return {"module": self.module, "path": self.path, "sha256": checksum}


def candidates(run):
    """Retain sources in files, submissions and *live* prompt sections only."""
    for p in sorted(run.rglob("*")):
        if not p.is_file():
            continue
        where = p.relative_to(run).as_posix()
        if p.suffix in (".agda", ".block"):
            if "agda_ctx_view/" not in where:
                yield where, p.read_text()
        elif p.suffix == ".latest-reply":
            for m in FENCE.finditer(p.read_text()):
                yield f"{where}#agda:{m[1] or 'source'}", m[2]
        elif p.suffix == ".accepted":
            s = p.read_text()
            m = MODULE.search(s)
            if m:
                yield where + "#accepted", s[m.start():]
        elif p.suffix == ".latest-prompt" or p.name == "node-prompt.txt":
            for m in PROMPT_SECTION.finditer(p.read_text()):
                yield where + "#" + m[1].split(" (")[0], m[2]


def inventory(runs):
    sources = {}
    for name, directory in runs.items():
        for origin, raw in candidates(directory):
            m = MODULE.search(raw)
            if not m or m[1] == "Main":
                continue
            if m[1].startswith(("Context.", "Agda.")):
                continue
            # Uniform final newline for code embedded inside textual envelopes.
            source = raw.rstrip("\n") + "\n"
            digest = hashlib.sha256(source.encode()).hexdigest()
            obj = sources.setdefault((name, digest), Source(name, m[1], source, digest))
            obj.origins.append(origin)
            if origin.endswith((".block", ".agda")) and obj.original_file is None:
                obj.original_file = raw
    return list(sources.values())


def link_sources(sources):
    providers = defaultdict(list)
    for obj in sources:
        providers[obj.run, obj.module].append(obj)

    def provider(obj, module):
        options = providers[obj.run, module]
        # A conditional plan is checked against its *own* child interfaces.
        # Never satisfy the parent by substituting a later child's body.
        for a in obj.origins:
            for b in options:
                if "#agda:" in a and any(x.split("#")[0] == a.split("#")[0] and "#agda:" in x for x in b.origins):
                    return b
                if "/drafts/" in a and any(x.rpartition("/")[0] == a.rpartition("/")[0] and "/drafts/" in x for x in b.origins):
                    return b
        if obj.run == "v3":
            # Concurrent open trees in gron shared the first sealed bases until
            # revision 199 replaced T0, then revision 224 replaced T1.
            early = any(re.search(r"4124219-(?:67|98)/", a) for a in obj.origins)
            version = ("33" if early else "199") if module == "Gen.T0.Gron" else ("67" if early else "224")
            for b in options:
                if any("4124219-" + version + "/code.agda" in x for x in b.origins):
                    return b
        for b in options:
            if any(x.startswith("generated/") for x in b.origins):
                return b
        raise ValueError(f"no exact provider for {obj.key} {obj.module} import {module}")

    def closure(obj):
        result = {}
        def visit(parent):
            for name in dict.fromkeys(IMPORT.findall(parent.text)):
                dep = provider(parent, name)
                if name in result:
                    if result[name] != dep:
                        raise ValueError(f"inconsistent ancestor {name} in {obj.key}")
                    continue
                result[name] = dep
                visit(dep)
        visit(obj)
        return [result[k].ref() for k in sorted(result)]
    return closure


def session_dependencies(write, v4):
    """Recreate the original session prelude with inert local executable paths.

    No archived SessionEnv.agda survived the scratch cleanups. Its checked-in
    generator supplies all static lines verbatim. Only path-valued arguments to
    the generated reference, candidate, relay and scratch directory are fixed.
    """
    template = (v4 / "Code/SessionRunner.agda").read_text().split("sessionEnvSource ref candidate relay scratch = unlines", 1)[1].split("∷ [])", 1)[0]
    lines = []
    for line in template.splitlines():
        if '("reference = decode' in line:
            lines.append('reference = decode (parseRefSpec "(ref-target (local \\"/bin/false\\") (args) (timeoutMs 30000))")')
        elif '("sessionEnv = sessionTools' in line:
            lines.append('sessionEnv = sessionTools reference "/bin/false" "/bin/false" "."')
        else:
            lines.extend(json.loads(x) for x in re.findall(r'"(?:[^"\\]|\\.)*"', line))
    generated = "\n".join(lines) + "\n"
    modules = {}
    def add(module, data):
        dest = "corpus/session-deps/" + module.replace(".", "/") + ".agda"
        modules[module] = {"module": module, "path": write(dest, data),
                           "sha256": hashlib.sha256(data.encode()).hexdigest()}
        for name in re.findall(r"^\s*(?:open\s+)?import\s+([\w.]+)", data, re.M):
            path = v4 / (name.replace(".", "/") + ".agda")
            if path.is_file() and name not in modules:
                add(name, path.read_text())
    add("SessionEnv", generated)
    return [modules[name] for name in sorted(modules)]


def reconstructed_syntax(write, sources):
    # v4's sealed mergeEntries eta-expands the section from the bug report.
    # Record that single edit explicitly and keep the archived file alongside it.
    sealed = next(s for s in sources if s.run == "v4" and
                  "generated/T0/Gen/T0/Gron.agda" in s.origins)
    before, after = "(λ vs → old ∷ vs)", "(old ∷_)"
    if sealed.text.count(before) != 1:
        raise ValueError("unexpected mergeEntries source")
    items = [
        ("operator-section", sealed.module, sealed.text.replace(before, after),
         f"{sealed.path}, replacing {before} by {after}"),
        ("overloaded-cons", "OverloadedCons", """module OverloadedCons where

open import Data.Bool using (Bool; true)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)

flags : List Bool
flags = List._∷_ true List.[]

evidence : All (λ _ → ⊤) flags
evidence = All._∷_ tt All.[]

moreFlags : List Bool
moreFlags = true ∷ flags

moreEvidence : All (λ _ → ⊤) moreFlags
moreEvidence = tt ∷ evidence
""", "Reconstruction of the List._∷_ and All._∷_ overloads used together in Code.SessionTools"),
    ]
    cases = []
    for name, module, source, provenance in items:
        path = write("corpus/syntax/" + name + ".agda", source)
        cases.append({"id": name, "layer": "S1", "expected": "accept", "deps": [],
                      "main": {"module": module, "path": path, "sha256": hashlib.sha256(source.encode()).hexdigest()},
                      "derived_from": provenance})
    path = "corpus/curated/hybrid/M0.agda"
    source = (FIXTURES / path).read_bytes()
    cases.append({"id": "surrogate-bound", "layer": "S1", "expected": "accept", "deps": [],
                  "main": {"module": "M0", "path": path, "sha256": hashlib.sha256(source).hexdigest()},
                  "derived_from": "56319 <ᵇ n in Gen.T1.Gron.Codec.unicodeStep, lifted to an order proof"})
    return cases


def multi_turn(write, directory):
    cases = []
    target = Path("corpus/history/v3")
    store = str(target / "store")
    for p in sorted((directory / "store").rglob("*")):
        if p.is_file():
            write(str(target / p.relative_to(directory)), p.read_bytes())
    second = {}
    for tree in ("T0", "T1", "T2"):
        base = directory / "trees" / tree
        versions = sorted((base / "versions").iterdir(), key=lambda v: int(v.name.split("-")[-1]))
        first, last = [{k: write(str(target / tree / v.name / (k + ".sexp")), (v / (k + ".sexp")).read_bytes())
                        for k in ("code", "spec", "memory", "shape")} for v in versions]
        second[tree] = last
        prompt = next((base / "ai").glob("*.latest-prompt")).read_text().splitlines()
        prefix = str(target / tree)
        case = {"id": f"v3-{tree}-replay", "layer": "S3", "expected": "accept", "tree": tree,
                "first": first, "second": last, "store": store,
                "tip": (directory / "store/refs/trees" / tree).read_text().strip(),
                "plan": write(prefix + "/submission.reply", next((base / "ai").glob("*.latest-reply")).read_bytes()),
                "locked_plan": write(prefix + "/locked-plan.sexp", next(l for l in prompt if l.startswith("(plan ")))}
        for line in prompt:
            if line.startswith("(lift "):
                case["lift"] = write(prefix + "/lift.sexp", line)
                case["base"] = second["T0"]["code"]
        cases.append(case)
    return cases


def render_inputs(write, run):
    render = next(p for p in sorted(run.rglob("cand_rt.sexp"))
                  if p.read_text().startswith('(module (q "Gen.T1.Render"'))
    wire = render.read_text()
    rule = next(line for line in wire.splitlines() if line.lstrip().startswith('(sig (mods) "reserved-rule"'))
    words = re.findall(r'\(lit \(str "([a-z]+)"\)\)', rule)
    cons = '(con "Agda.Builtin.List.List._∷_")'
    nil = '(con "Agda.Builtin.List.List.[]")'
    if len(words) != 36 or words[0] != "break" or words[-1] != "yield" or rule.count(cons) != 36 or rule.count(nil) != 1:
        raise ValueError("unexpected archived reserved-rule keyword chain")

    # The archive eta-normalizes other syntax but preserves this 36-cell chain.
    # Extend only its tail to exercise the requested 50-cell nesting depth.
    extra = ["await", "enum", "implements", "interface", "let", "package", "private",
             "protected", "public", "static", "async", "as", "from", "of"]
    tail = nil
    for word in reversed(extra):
        tail = f'(app (app {cons} (arg vis _ (lit (str "{word}")))) (arg vis _ {tail}))'
    deeper = wire.replace(rule, rule.replace(nil, tail))
    if len(set(words + extra)) != 50:
        raise ValueError("derived keyword table must contain 50 distinct entries")
    cases = []
    for name, data, stem, table in (("v4-v2-render-roundtrip", wire, "Gen.T1.Render", words),
                                    ("render-50-roundtrip", deeper, "Gen.T1.Render-50", words + extra)):
        body = data.encode()
        case = {"id": name, "layer": "S4", "expected": "accept",
                "sexpr": write("corpus/native/" + stem + ".sexp", body),
                "bytes": len(body), "sha256": hashlib.sha256(body).hexdigest(),
                "origin": str(render.relative_to(run)), "keywords": table}
        if data != wire:
            case["derived_from"] = "v4-v2-render-roundtrip; append 14 JS reserved/contextual names to reserved-rule"
        cases.append(case)
    return cases


def extract(worktrees, out):
    inputs = {}

    def write(path, data):
        if isinstance(data, str):
            data = data.encode()
        destination = out / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists() or destination.read_bytes() != data:
            destination.write_bytes(data)
        inputs[path] = hashlib.sha256(data).hexdigest()
        return path

    runs = {k: worktrees / repo / "tmp/runs" / name for k, (repo, name) in RUNS.items()}
    for archive in runs.values():
        if not (archive / "trees").is_dir():
            raise FileNotFoundError(f"gron tree archive missing: {archive}")
    sources = inventory(runs)
    closure = link_sources(sources)
    cases = []
    session = session_dependencies(write, worktrees / RUNS["v4"][0])
    blueprint = (worktrees / RUNS["v3"][0] / "Context/Blueprint.agda").read_bytes()
    if blueprint != (worktrees / RUNS["v4"][0] / "Context/Blueprint.agda").read_bytes():
        raise ValueError("gron runs used different Blueprint preludes")
    prelude = {"module": "Context.Blueprint", "sha256": hashlib.sha256(blueprint).hexdigest(),
               "path": write("corpus/context/Context/Blueprint.agda", blueprint)}
    by_path = {s.path: s for s in sources}
    for obj in sources:
        # An empty pre-plan tree adds no syntax or scope coverage.
        if not obj.text.split("where", 1)[1].strip():
            continue
        write(obj.path, obj.payload)
        case = {"id": obj.key, "layer": "S1", "expected": "accept", "main": obj.ref(),
                "deps": closure(obj), "origins": sorted(set(obj.origins))}
        ancestors = [by_path[dep["path"]] for dep in case["deps"]]
        if any("import Context.Blueprint" in s.text for s in [obj, *ancestors]):
            case["context_deps"] = [prelude]
        if "import SessionEnv" in obj.text:
            case.update(scope="session", deps=session)
        if obj.module == "PrimitiveImportProbe":
            case.update(layer="S2", expected="reject", native_safe=True, diagnostic="--safe")
        if obj.digest[:12] in NEGATIVE:
            case.update(layer="S2", expected="reject", diagnostic=NEGATIVE[obj.digest[:12]])
        cases.append(case)
        sealed = any(re.search(r"trees/T[0-9]+/versions/[^/]+/code\.agda$", p) for p in obj.origins)
        child = obj.module in {"Gen.T2.JsonInput.Grammar", "Gen.T2.JsonInput.Glyphs"} and any(
            p.startswith("threads/T2/") and p.endswith("#accepted") for p in obj.origins)
        backend_fixture = obj.module == "Gen.T1.Gron.Codec" and any(
            "/agda_src/" in p for p in obj.origins)
        render_body = obj.run == "v4-v2" and obj.module == "Gen.T1.Render" and any(
            p.endswith("/drafts/main.block") for p in obj.origins)
        if case["layer"] == "S1" and (sealed or child or backend_fixture or render_body):
            cases.append({**case, "id": obj.key + "-verify", "layer": "S2"})
    cases.extend(reconstructed_syntax(write, sources))
    cases.extend(multi_turn(write, runs["v3"]))
    cases.extend(render_inputs(write, runs["v4-v2"]))
    raw = (FIXTURES / "curated.json").read_bytes()
    curated = json.loads(raw)
    write("curated.json", raw)
    for case in curated:
        names = [case[k] for k in ("main", "spec", "proposal", "recovery") if k in case]
        for name in names + case.get("deps", []):
            path = "corpus/curated/" + name
            if path not in inputs:
                write(path, (FIXTURES / path).read_bytes())
    # Keep the original (often multi-module) replies as well as the extracted
    # Agda. Their byte counts include envelopes, moves and child specifications.
    archival = []
    for run in ("v4", "v4-v2", "v4-v3"):
        for reply in sorted(runs[run].glob("trees/*/ai/*.latest-reply")):
            envelope = reply.read_bytes()
            path = write(f"corpus/replies/{run}/{reply.name}", envelope)
            archival.append({"run": run, "origin": str(reply.relative_to(runs[run])),
                             "path": path, "bytes": len(envelope), "sha256": hashlib.sha256(envelope).hexdigest()})
    manifest = {"version": 1, "input_sha256": dict(sorted(inputs.items())), "archived_replies": archival, "runs": RUNS, "cases": sorted(cases, key=lambda c: (c["layer"], c["id"])),
                "curated": curated}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worktrees", type=Path, default=ROOT.parent)
    parser.add_argument("--output-dir", type=Path, default=FIXTURES)
    args = parser.parse_args()
    extract(args.worktrees, args.output_dir)
