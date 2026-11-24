#!/usr/bin/env python3
"""Reconstruct the four sealed gron stages from completed MCP calls, offline."""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re


RUN = Path("/root/Documents/Codex/handoffs/CodeTransport-730010e3/worktrees/"
           "v9-pure-lean4/tmp/runs/gron-v9-posix")
FIXTURE = Path(__file__).resolve().parents[1] / "Test/Concurrent/gron_t0_t3_fixture.json"
TIPS = {
    "T0": "34d4cbdbeb94c5ace6a7d7b59fcd9e0b9fac4eee6fd0d78d1a8df05c22f3fb6a",
    "T1": "f5bd513cc00039f46e9430453463c6a4b4a806ea4967175feaad77409836751b",
    "T2": "558fb87c63503e6ab1121925b242d3dbd1bb041141013c357354e6f30971f58b",
    "T3": "fae14ba50a9de8631acddd83ce56b2c0e4a38242f8f596ffef50070c11aba202",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Atom(str):
    """Unquoted wire token (distinct from a quoted source or name)."""


TOKEN = re.compile(r'\s+|[()]|"(?:[^"\\]|\\.)*"|[^()"\s]+')
ESCAPES = str.maketrans({'\\': '\\\\', '"': '\\"', '\n': '\\n', '\r': '\\r', '\t': '\\t'})


def parse(text):
    stack = [[]]
    pos = 0
    for match in TOKEN.finditer(text):
        require(match.start() == pos, f"invalid S-expression at {pos}")
        token = match[0]
        pos = match.end()
        if token == '(':
            stack.append([])
        elif token == ')':
            require(len(stack) > 1, "unmatched closing parenthesis")
            value = stack.pop()
            stack[-1].append(value)
        elif token.startswith('"'):
            stack[-1].append(json.loads(token, strict=False))
        elif not token.isspace():
            stack[-1].append(Atom(token))
    require(pos == len(text) and len(stack) == 1 and len(stack[0]) == 1,
            "expected one complete S-expression")
    return stack[0][0]


def canonical(expr):
    if isinstance(expr, list):
        return '(' + ' '.join(map(canonical, expr)) + ')'
    if isinstance(expr, Atom):
        return str(expr)
    return '"' + expr.translate(ESCAPES) + '"'


def object_at(kind, key):
    require(re.fullmatch('[0-9a-f]{64}', key), f"invalid {kind} address")
    data = (RUN / "store/objects" / kind / (key + ".sexp")).read_bytes()
    require(hashlib.sha256(data).hexdigest() == key, f"{kind}/{key} digest mismatch")
    return parse(data.decode())


def items(path):
    with path.open(encoding="utf-8") as trace:
        for line in trace:
            event = json.loads(line)
            if event["type"] == "item.completed":
                yield event["item"]


def last_reply(path):
    reply = ""
    for item in items(path):
        if item["type"] == "agent_message":
            reply = item["text"]
    return reply


def resolve_reply(reply, drafts):
    envelope = []
    lines = []
    fence = None
    for line in reply.split('\n'):
        words = line.strip().split()
        if fence is not None:
            if words == ['```']:
                if fence:
                    drafts[fence] = '\n'.join(lines)
                else:
                    envelope.extend(lines)
                fence = None
                lines = []
            else:
                lines.append(line)
        elif words == ['```sexp']:
            fence = ''
        elif len(words) == 2 and words[0] in ('```lean', '```sexp'):
            fence = words[1]
        else:
            envelope.append(line)
    require(fence is None, "unterminated reply fence")

    def resolve(value):
        if isinstance(value, list):
            return list(map(resolve, value))
        if isinstance(value, Atom) and value.startswith('@'):
            return drafts[value[1:]]
        return value

    return resolve(parse('\n'.join(envelope)))


def replay(path, owner=None):
    drafts = {}
    checks = []
    reply = None
    for item in items(path):
        if item["type"] == "agent_message":
            reply = item["text"]
            continue
        if item.get("server") != "lojita":
            continue
        tool = item["tool"]
        args = item["arguments"]
        result = item.get("result") or {}
        ok = result.get("structured_content", {}).get("ok") is True
        if ok and tool == "write_draft":
            drafts[args["name"]] = args["content"]
        elif ok and tool == "patch_draft":
            name, old = args["name"], args["old_text"]
            require(old and drafts[name].count(old) == 1, f"{path.name}: ambiguous patch of {name}")
            drafts[name] = drafts[name].replace(old, args["new_text"], 1)
        elif owner and tool == "check_lean":
            message = result["content"][0]["text"]
            outcome = "ok" if ok else message.split('\n', 1)[0].removeprefix("[KIND] ")
            if outcome not in ("ok", "ELABORATION_ERROR", "INTERFACE_MISSING", "INTERFACE_MISMATCH"):
                continue
            def source(text):
                if text.startswith('@'):
                    return drafts[text[1:]]
                return drafts.get(text, text)
            main = source(args.get("main_block") or args["source"])
            checks.append(dict(owner=owner, trace=path.name, item=item["id"], source=main,
                               depBlocks=[source(s) for s in args.get("dep_blocks", [])],
                               allowAxioms=args.get("allow_axioms", False), outcome=outcome))
    return resolve_reply(reply, drafts), checks


def fields(expr, tag):
    require(expr[0] == tag, f"expected {tag}")
    result = {field: values for field, *values in expr[1:]}
    require(len(result) == len(expr) - 1, f"duplicate field in {tag}")
    return result


def accepted_action(name, why, replies):
    candidates = []
    for path, message in replies:
        if why not in message:
            continue
        expr, _ = replay(path)
        f = fields(expr, "session-action")
        if f["kind"] == ["drive-tree"] and f["treeName"] == [name] and f["why"] == [why]:
            def optional(key):
                value, = f.get(key, [Atom("nothing")])
                if value == Atom("nothing"):
                    return None
                require(isinstance(value, list) and value[0] == "just" and len(value) == 2, key)
                return value[1]
            candidates.append(dict(treeName=name, why=why, specSrc=f["specSrc"][0],
                                   baseTrees=f["baseTrees"], maybeLiftSrc=optional("maybeLiftSrc"),
                                   maybeTransportSrc=optional("maybeTransportSrc"), trace=path.name))
    require(len(candidates) == 1, f"{name}: expected one fork matching the sealed commit")
    return candidates[0]


def check_module(source, header, units):
    # CAS stores exact Lean command slices. The gaps between these slices are
    # layout and comments. Check every byte of every command, including opens.
    name = '.'.join(header[1])
    commands = (['import ' + '.'.join(i[0]) for i in header[2]] + ['namespace ' + name] +
                header[3] + [u[3] for u in units] + ['end ' + name])
    pos = 0
    for command in commands:
        while True:
            pos = re.compile(r'\s*').match(source, pos).end()
            if source.startswith(command, pos):
                break
            if source.startswith('--', pos):
                pos = source.index('\n', pos)
            elif source.startswith('/-', pos):
                pos = source.index('-/', pos + 2) + 2
            else:
                raise ValueError(f"{name} at {pos}: expected {command[:90]!r}, found {source[pos:pos+90]!r}")
        pos += len(command)
    require(not source[pos:].strip(), f"{name}: extra commands after namespace")


def extract_node(tree, owner, key, spec_src, nodes, checks):
    home = object_at("home", key)
    code = object_at("code", home[1])
    iface = object_at("iface", home[2])[1:]
    memory = object_at("mem", home[3])
    links = home[4:]
    header = object_at("code", links[0][1]) if links and links[0][0] == "scope" else code
    require('.'.join(code[1]) == owner == '.'.join(header[1]), f"{owner}: wrong CAS module")
    check_module(spec_src, header, iface)

    ctx = RUN / "trees" / tree / "ai" / owner
    frozen_spec = canonical([*header[:4], iface])
    require(json.loads((ctx / "context.json").read_bytes())["spec"] == frozen_spec,
            f"{owner}: assigned canonical spec differs from sealed scope/iface")
    reply = (ctx / "latest-reply").read_text(encoding="utf-8").strip()
    paths = [p for p in sorted((RUN / "codex-traces" / owner).glob("*-fork-*.jsonl"))
             if last_reply(p).strip() == reply]
    require(len(paths) == 1, f"{owner}: cannot identify accepted fork")
    expr, samples = replay(paths[0], owner)
    plan = fields(expr, "submission")
    require(plan["kind"] == ["plan"], f"{owner}: expected plan")
    targets = []
    for tag, src, target in plan["moves"]:
        require(tag == "move" and src == Atom("bot"), f"{owner}: expected a fresh-node move")
        if target not in targets:
            targets.append(target)
    expected = [Atom("memory")] + [[Atom("note"), target, *plan["why"]] for target in targets]
    require(canonical(memory) == canonical(expected), f"{owner}: memory differs from accepted moves/why")
    units = [u for u in code[4] if [Atom("unit"), '.'.join(u[0])] in targets]
    require(len(units) == sum(t[0] == 'unit' for t in targets), f"{owner}: missing move target")
    # withTests may append a theorem copied from the assigned spec.
    require(all(u in units or (u[2] == "4" and u in iface) for u in code[4]), f"{owner}: unaccounted sealed declaration")
    # Plan.apply topologically orders interdependent units before sealing.
    main = plan["main"][0]
    check_module(main, code, sorted(units, key=lambda u: main.find(u[3])))
    children = {link[1]: link[2] for link in links if link[0] == "kid"}
    subs = {(slot if slot.startswith("Gen.") else owner + '.' + slot): src
            for slot, src in plan.get("subspecs", [])}
    require(subs.keys() == children.keys(), f"{owner}: sealed child slots differ")
    nodes.append(dict(owner=owner, trace=paths[0].name, submission=canonical(expr)))
    for draft in samples:
        draft["matchesSubmittedMain"] = draft["source"].strip() == main.strip()
    checks.extend(samples)
    assigned = {'.'.join(name): units for name, units in code[2] if units}
    require(assigned.keys() == children.keys(), f"{owner}: wrong imported child interfaces")
    for child, child_key in children.items():
        child_iface = extract_node(tree, child, child_key, subs[child], nodes, checks)
        require(assigned[child] == child_iface, f"{child}: parent and sealed child interfaces differ")
    return iface


def sample_checks(checks):
    # Round-robin across owners and diagnostic kinds. Retain complete inputs
    # at call time, including staged dependencies that were edited later.
    groups = defaultdict(list)
    seen = set()
    for draft in checks:
        key = (draft["source"], tuple(draft["depBlocks"]), draft["allowAxioms"], draft["owner"])
        if key not in seen:
            groups[draft["owner"], draft["outcome"]].append(draft)
            seen.add(key)
    selected = []
    for batch in range(max(map(len, groups.values()))):
        for group in groups.values():
            if batch < len(group):
                selected.append(group[batch])
        if len(selected) >= 84:
            break
    require(len(selected) >= 84, "too few distinct trace checks")
    selected = selected[:84]
    earlier = {d["source"].strip() for d in selected if not d["matchesSubmittedMain"]}
    require(len(earlier) > 60, "expected over sixty distinct main drafts preceding their submitted versions")
    return selected


def extract():
    stages, checks = [], []
    forks = sorted((RUN / "codex-traces/SESSION_ROOT").glob("*-fork-*.jsonl"))
    replies = [(path, last_reply(path)) for path in forks]
    for tree, golden in TIPS.items():
        tip = (RUN / "store/refs/trees" / tree).read_text()
        require(tip == golden, f"{tree}: serial ref changed")
        _, parents, root, epoch, why = object_at("commit", tip)
        action = accepted_action(tree, why, replies)
        owner = f"Gen.{tree}.Gron"
        ctx = json.loads((RUN / "trees" / tree / "ai" / owner / "context.json").read_bytes())
        for records, key in [("lifts", "maybeLiftSrc"), ("transports", "maybeTransportSrc")]:
            desc = action[key]
            expected = [] if desc is None else [canonical(parse(desc))]
            require([item[1] for item in ctx[records]] == expected, f"{tree}: wrong {key}")
        require(epoch == tree and parents == ['parents', *[TIPS[b] for b in action['baseTrees']]],
                f"{tree}: wrong epoch or parents")
        nodes = []
        extract_node(tree, owner, root, action["specSrc"], nodes, checks)
        require(len(nodes) == [1, 4, 11, 11][len(stages)], f"{tree}: wrong ownership tree")
        stages.append(dict(**action, commit=tip, rootHome=root, nodes=nodes))
    return dict(stages=stages, drafts=sample_checks(checks))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare without writing any files')
    args = parser.parse_args()
    fixture = extract()
    data = (json.dumps(fixture, ensure_ascii=False, indent=2) + '\n').encode()
    if args.check:
        require(FIXTURE.read_bytes() == data, "checked-in fixture differs from the sealed traces")
    else:
        FIXTURE.parent.mkdir(parents=True, exist_ok=True)
        FIXTURE.write_bytes(data)
    print(f"Verified four gron commits, 27 submissions and {len(fixture['drafts'])} distinct check_lean drafts.")


if __name__ == "__main__":
    main()
