#!/usr/bin/env python3
"""Render or lint a UTF-8 CodeTransport v5 goal.txt without a checkout."""

import argparse
from pathlib import Path
import re
from string import Template
import subprocess
import sys
import tempfile
import unicodedata


TOOLS = ("procExec", "pty", "fsbox", "netbox", "gitbox", "FuzzGen")
BUILD = '(session-action (kind build-exe) (why "...") (entry "<VerifiedMod>.<app>"))'

# Domain hints describe observations. The same discovery and proof protocol
# applies to every combination, including targets that span several domains.
DOMAINS = {
    "cli-filter": {
        "en": "Check flags, empty and multiline inputs, trailing newlines, byte streams and exit status.",
        "zh": "探测标志、空输入、多行输入、末行换行、各字节流与退出码。",
    },
    "fs-symlink": {
        "en": "Compare path and permission errors, file snapshots and argv[0] dispatch through symlink aliases.",
        "zh": "比对路径与权限错误、文件快照及符号链接别名触发的 argv[0] 分发。",
    },
    "net-http": {
        "en": "Exercise HTTP URL inputs on loopback. Compare captured requests, responses, connection failures and timeout boundaries.",
        "zh": "在回环地址探测 HTTP URL 输入，比对请求抓包、响应、连接失败与超时边界。",
    },
    "git-repo": {
        "en": "Compare repository observations before and after each operation, including worktree, index, commits, branches and tags.",
        "zh": "比对每步操作前后的仓库状态，包括工作区、暂存区、提交、分支与标签。",
    },
    "tui-reactive": {
        "en": "Replay keystrokes, resizes and timer events. Compare terminal frames, application state and exit behavior over the same trace.",
        "zh": "回放按键、窗口缩放与定时事件，比对同一事件轨迹上的终端画面、应用状态与退出行为。",
    },
    "web-canvas": {
        "en": "Probe viewport changes, input coordinates and event order. Compare the observable canvas output after each relevant event.",
        "zh": "探测视口变化、输入坐标与事件顺序，比对相关事件发生后的可观察画布输出。",
    },
    "multi-service": {
        "en": "Trace messages across service endpoints. Compare reply order, failure propagation and resulting state. Use Context.Protocol where applicable.",
        "zh": "跟踪服务端点间的消息，比对回复顺序、错误传播与最终状态。协议组合适用时可采用 Context.Protocol。",
    },
}

GOALS = {
    "en": Template('''Reconstruct a cleanroom, statically linked, formally verified replacement ("cand") for the reference binary ("ref") of $target.

Scope and observable behavior
$scope

Discovery and replay
SESSION_ROOT must first inspect "ref" for help, version, usage, errors and I/O channels. Autonomously select and combine any SessionEnv tools appropriate to the observations and differential replay.
- "procExec" exposes batch arguments, stdin, stdout, stderr and exit codes.
- "pty" exposes isatty-dependent ANSI output, resizeTTY, keystrokes, timers and signals.
- "fsbox" exposes files, directories, snapshots, path and permission errors, and argv[0] dispatch. With fixSymlink, point the same alias at "ref" and "cand" in their respective runs.
- "netbox" provides loopback HTTP/TCP/UDP/proxy fixtures, httpStubMode / tcpStubMode, delayed responses via httpDelayedStubMode / tcpDelayedStubMode, {{PORT}}/{{ADDR}}/{{URL}} substitution and capturedReqs.
- "gitbox" exposes worktree, index, commit, branch and tag transitions.
- Context.Tools.FuzzGen provides deterministic inputs and counterexample shrinking.

Closed-world specification and build
1. Progress from the finite T0 blueprint through T1/T2 concrete ports to the root specification Σ_root. Keep specSrc behavioral, with minimal PortLift projections, named laws and boundary equations observed on "ref". Place parsers and internal algorithms in the implementation.
2. At Σ_root, model every host effect in --safe Context.World as a CliApp Δ = WorldProg Δ ExitCode or a ReactiveApp Δ S for an event-driven target. Prove universal ∀ (w : SimWorld) contracts over runCliPure or runReactivePure for every relevant observation, including argv[0], flags, environment, isTTYStdout, file and network errors, timeouts and exit status. Use Context.WorldLaws and relevant FsLaws, NetLaws, TermLaws, ClockLaws and GitLaws. Lift child capabilities with Δ_child ⊆ Δ_parent and liftWorld.
3. Build bin/candidate exclusively via $build through the single thin interpreter OwnershipIO.WorldRunner. Supply a reason and a qualified entry exported by a proof tree with verdict = ok. For a reactive entry include (mode reactive) in that action. The harness supplies the IO wrapper and statically links the executable.
4. Before (kind finish), run "ref" and "cand" symmetrically with equivalent initial worlds. Compare all relevant output bytes, exit status, terminal state, filesystem snapshots and symlinks, captured requests, timeouts and Git state. Shrink counterexamples with FuzzGen and exit 0 only on exact agreement.
'''),
    "zh": Template('''为 $target 的参考程序 "ref" 构建洁净室、静态链接且经形式化验证的等价替代程序 "cand"。

任务范围与可观察行为
$scope

开放世界观测与回放
SESSION_ROOT 必须先探测 "ref" 的帮助、版本、用法、报错和 I/O 通道，再从 SessionEnv 的全套工具中按需自主选择和组合探针与差分回放工具。
- "procExec" 可观测批处理参数、标准输入、输出、错误流及退出码。
- "pty" 可观测 isatty 相关的 ANSI 输出、resizeTTY 窗口变化、按键、定时与信号。
- "fsbox" 可观测文件、目录、快照、路径和权限错误，以及 argv[0] 分发。用 fixSymlink 在两次运行中将同一别名分别指向 "ref" 和 "cand"。
- "netbox" 提供本地回环 HTTP/TCP/UDP/代理桩、httpStubMode / tcpStubMode、httpDelayedStubMode / tcpDelayedStubMode 慢响应、{{PORT}}/{{ADDR}}/{{URL}} 替换以及 capturedReqs 请求抓包。
- "gitbox" 可观测工作区、暂存区、提交、分支与标签的状态演进。
- Context.Tools.FuzzGen 提供确定性输入生成与反例收缩。

封闭世界规约与构建
1. 从 T0 有限蓝图推进到 T1/T2 具体端口与根规约 Σ_root。specSrc 只描述行为，给出最小 PortLift 投影、具名定律及从 "ref" 观测到的边界方程。解析器与内部算法放在实现中。
2. 在 Σ_root 将全部宿主副作用纳入 --safe 的 Context.World，建模为 CliApp Δ = WorldProg Δ ExitCode 或事件驱动目标的 ReactiveApp Δ S。证明关于 runCliPure 或 runReactivePure 的全称 ∀ (w : SimWorld) 定律，覆盖目标涉及的 argv[0]、标志、环境变量、isTTYStdout、文件和网络错误、超时与退出码。使用 Context.WorldLaws 及相关的 FsLaws、NetLaws、TermLaws、ClockLaws、GitLaws，以 Δ_child ⊆ Δ_parent 和 liftWorld 提升子能力。
3. 必须经 $build 由单一薄解释器 OwnershipIO.WorldRunner 静态编译 bin/candidate。填写构建理由，入口须为 verdict = ok 的证明树导出的限定名。对于响应式入口，在同一动作中加入 (mode reactive)。IO 胶水由评测框架生成。
4. 在 (kind finish) 前，从等价的初始世界分别实际运行 "ref" 与 "cand"，对称比对全部相关的输出字节、退出码、终端状态、文件快照与软链、请求抓包、超时和 Git 状态。用 FuzzGen 收缩反例，全部吻合才以 0 退出。
'''),
}


def render(target, summary, domains, lang, extra):
    default = {
        "en": 'Reproduce the observable behavior of "ref" within the stated scope in the cleanroom.',
        "zh": '在洁净室内复现 "ref" 在任务范围内的可观察行为。',
    }
    scope = [summary, default[lang]]
    scope.extend(DOMAINS[domain][lang] for domain in dict.fromkeys(domains))
    scope.extend(extra)
    return GOALS[lang].substitute(
        target=target, scope="\n".join("- " + item for item in scope if item), build=BUILD,
    )


def phrase(pattern):
    # ASCII word boundaries separate API identifiers from adjacent Chinese text.
    return re.compile(pattern, re.IGNORECASE | re.ASCII)


TOOL = r"\b(?:Context\.Tools\.)?(?:" + "|".join(TOOLS) + r")\b"
JOIN = r"\s*(?:\band\b|&|\+|以及|和|与|、)\s*"
PAIR = rf"(?:\bprocExec\b{JOIN}\bpty\b|\bpty\b{JOIN}\bprocExec\b)"
LOCK = phrase(
    rf"(?:\b(?:only|solely|exclusively)\s+(?:(?:use|using|with|via|the)\s+)*"
    rf"|\b(?:limited|restricted|confined)\s+to\s+(?:using\s+)?(?:the\s+)?"
    rf"|\b(?:limit|restrict|confine)\s+(?:yourself|discovery|probes?|replay)\s+to\s+(?:the\s+)?"
    rf"|\b(?:no|(?:do not|dont|never)\s+use\s+(?:any\s+)?)\s*(?:other\s+)?tools?\s+"
    rf"(?:except|besides|other than)\s+(?:the\s+)?"
    rf"|(?:只能|只可|仅能|仅可|仅限于?|只允许|仅允许|只|仅)\s*(?:使用|调用|用)?\s*){TOOL}"
    rf"|{TOOL}\s+(?:(?:is the (?:sole|only)\s+(?:allowed\s+)?tool)\b"
    rf"|(?:only|exclusively)\b(?!\s+(?:if|when|where|for|after|on)\b))"
)
REQUIRED_PAIR = phrase(
    rf"(?:\b(?:us(?:e|ing)|with|requires?)\s+(?:both\s+)?"
    rf"|(?:必须|务必|须|应当)\s*(?:同时|一并)?\s*(?:使用|调用|用)\s*"
    rf"|(?:同时|一并)\s*(?:使用|调用|用)\s*){PAIR}"
    rf"|\b(?:both\s+)?{PAIR}\s+(?:are (?:required|mandatory)|must be used)\b"
)
DENIED_TOOL = phrase(
    rf"(?:\b(?:do not|dont|never|must not|cannot)\s+(?:use|invoke|call)\s+"
    rf"|\b(?:all|any)\s+(?:tools?|sandboxes|sandbox)\s+(?:except|but|other than)\s+"
    rf"|(?:禁止|禁用|不得|不准|不能|不可)\s*(?:使用|调用|用)?\s*){TOOL}"
    rf"|{TOOL}\s+(?:is\s+(?:forbidden|unavailable|off.limits)|must not be used)\b"
)
MANUAL_MAIN = phrase(
    r"\bmodule\s+Main\s+where\b"
    r"|(?:\b(?:write|hand[- ]?write|supply|create|provide|implement|edit|submit|author)\s+"
    r"(?:(?:a|the|new|your|own|custom|file|named)\s+)*"
    r"|\bhand[- ]?(?:written|rolled)\s+"
    r"|(?:手写|编写|创建|提交|提供|自行写)\s*(?:(?:一个|自己的)\s*)?)Main\.agda\b"
)
SOURCE_FIELD = phrase(r"\(\s*source\b[^)\n]*\)?")
CLI_HOST = phrase(r"\bCLIHost\b")

# A goal may explicitly prohibit legacy instructions, or give an optional pair
# as an example. A mention of the retired CLIHost is itself a v5 violation.
CLAUSE_BREAK = phrase(r"[;；。!?！？]|\.(?=\s)|\n\s*\n|\n\s*[-*]\s+|\b(?:but|instead|then)\b|但是|改为")
PROHIBITION = phrase(
    r"\b(?:not|don['’]?t|never|without|no need to|avoid|reject(?:s|ed)?|forbid(?:s|den)?|prohibit(?:s|ed)?)\b"
    r"|严禁|禁止|不得|切勿|不要|不能|无需|不应|不可|不允许|不必"
)
POST_PROHIBITION = phrase(
    r"\s*(?:(?:field|form|clause)s?\s+)?"
    r"(?:(?:is|are)\s+(?:forbidden|disallowed|prohibited|rejected|not (?:allowed|required))\b"
    r"|must not be used\b|(?:字段|写法)?\s*(?:已废除|已禁用|不允许|被禁止))"
)
OPTIONAL = phrase(r"\b(?:may|can|could|optionally|optional|for example|free to)\b|例如|比如|按需|可以|可选|可\s*$")
POST_OPTIONAL = phrase(r"\s*(?:(?:when|if|as) (?:appropriate|needed|useful|relevant)|are (?:available|optional))\b")
FORGO = (r"(?:\b(?:skip|omit|bypass|disable|avoid)\s+|\b(?:do not|dont|never|must not)\s+"
         r"(?:use|enable|require|build (?:via|through))\s+|(?:跳过|禁用|绕过|不用|禁止使用|不得使用)\s*)")

TOOL_MESSAGE = "Leave discovery and replay open to all SessionEnv tools."
ANTI_PATTERNS = (
    ("tool-lock", LOCK, TOOL_MESSAGE),
    ("tool-lock", REQUIRED_PAIR, TOOL_MESSAGE),
    ("tool-lock", DENIED_TOOL, TOOL_MESSAGE),
    ("manual-main", MANUAL_MAIN, "The harness must generate the IO wrapper for the verified entry."),
    ("source-field", SOURCE_FIELD, 'Use the verified (entry "...") field for build-exe.'),
    ("obsolete-cli-host", CLI_HOST, "CLIHost is retired. Use OwnershipIO.WorldRunner."),
    ("safe-option", phrase(FORGO + r"--safe\b"), "Require --safe for the root specification."),
    ("world-module", phrase(FORGO + r"\bContext\.World\b"), "Model host effects in Context.World."),
    ("world-runner", phrase(FORGO + r"\bOwnershipIO\.WorldRunner\b"), "Use the single OwnershipIO.WorldRunner."),
)


def qualified_mention(text, match, optional_pair=False):
    """Is this example explicitly prohibited, or is the pair a free choice?"""
    before = CLAUSE_BREAK.split(text[max(0, match.start() - 180):match.start()])[-1]
    after = text[match.end():match.end() + 90].lstrip("\x60*")
    return (PROHIBITION.search(before) or POST_PROHIBITION.match(after)
            or optional_pair and (OPTIONAL.search(before) or POST_OPTIONAL.match(after)))


FREE_CHOICE = phrase(
    r"\b(?:autonom\w*|freely|free to (?:use|choose|explore)|as needed|as appropriate|as applicable|"
    r"at your discretion|appropriate tools?|relevant tools?|any (?:combination|subset|tools?|of the tools)|"
    r"(?:choose|select|combine|pick)\b.{0,50}\btools?)\b|自主|按需|自由|酌情|任意组合|自行选"
)
REQUIREMENTS = (
    ("safe-option", r"(?<![\w-])--safe(?![\w-])", "Require Agda --safe for the root specification."),
    ("world-module", r"\bContext\.World\b", "Model all host effects in Context.World."),
    ("world-root", r"Σ[_ ]?root\b|\broot\b|根(?:规约|模块|规范|规格|契约)", "Locate the world contract at the root (Σ_root)."),
    ("world-law", r"(?:∀|\bforall\b)\s*\(\s*[^\s:()]+\s*:\s*(?:Context\.World\.)?SimWorld\s*\)",
     "Quantify the contract over every world, e.g. ∀ (w : SimWorld)."),
    ("world-runner", r"\bOwnershipIO\.WorldRunner\b", "Build through the single interpreter OwnershipIO.WorldRunner."),
)

# The protocol action contains flat (name value) fields. Quoted values may
# contain whitespace, parentheses or escaped quotes. An entry in another
# action or inside the reason string cannot satisfy this build.
QUOTED = r'"(?:[^"\\]|\\.)*"'
FIELD = re.compile(r'\(\s*([A-Za-z][\w-]*)\s+(' + QUOTED + r'|[^\s()"]+)\s*\)', re.ASCII)
ACTION = re.compile(r"\(\s*session-action\b\s*((?:" + FIELD.pattern + r"\s*)+)\)", re.ASCII)
BUILD_START = re.compile(r"\(\s*session-action\s*\(\s*kind\s+build-exe\s*\)")
ENTRY_NAME = r'(?:<[^.\s<>/\\()"]+>|[^.\s<>/\\()"]+)'
ENTRY = re.compile(r'"' + ENTRY_NAME + r'(?:\.' + ENTRY_NAME + r')+"')
PROSE_ENTRY = re.compile(r"\bbuild-exe\s*(?:指定|须指定|with|requires?)\s*\(\s*entry\s+" + ENTRY.pattern + r"\s*\)", re.ASCII)


def template_build_clause(text):
    # The published Chinese template specifies the entry and the single static
    # WorldRunner build in prose. Require that binding in one clause. A loose
    # (entry ...) elsewhere cannot repair an incomplete session-action.
    prose = text.replace("\x60", "").replace("**", "")
    for clause in CLAUSE_BREAK.split(prose):
        entry = PROSE_ENTRY.search(clause)
        if entry and not qualified_mention(clause, entry):
            if (re.search(r"\bOwnershipIO\.WorldRunner\b", clause, re.ASCII)
                    and "bin/candidate" in clause and re.search(r"\b(?:sole|single)\b|单一|唯一", clause)
                    and re.search(r"\bstatic(?:ally)?\b|静态", clause)):
                return True
    return False


def lint_build(text, report):
    parsed = set()
    required = False
    for action in ACTION.finditer(text):
        fields = list(FIELD.finditer(text, action.start(1), action.end(1)))
        if not any(field[1] == "kind" and field[2] == "build-exe" for field in fields):
            continue
        parsed.add(action.start())
        if qualified_mention(text, action):
            continue
        required = True
        line = text.count("\n", 0, action.start()) + 1
        values = {field[1]: field[2] for field in fields}
        for field in fields:
            if field[1] == "source":
                report("source-field", "build-exe cannot accept a source field.", text.count("\n", 0, field.start()) + 1)
        if len(values) != len(fields):
            report("build-action", "Duplicate field in the build-exe action.", line)
        if set(values) - {"kind", "why", "entry", "mode", "source"}:
            report("build-action", "Only kind, why, entry and optional mode belong in build-exe.", line)
        reason = values.get("why", "")
        if not re.fullmatch(QUOTED, reason) or not reason[1:-1].strip():
            report("build-why", 'Include a nonempty quoted (why "...") in build-exe.', line)
        if not ENTRY.fullmatch(values.get("entry", "")):
            report("build-entry", 'Include (entry "<VerifiedMod>.<app>") in the same build-exe action.', line)
        if values.get("mode", "cli") not in ("cli", "reactive"):
            report("build-mode", "The optional build mode must be cli or reactive.", line)
    for start in BUILD_START.finditer(text):
        if start.start() in parsed or qualified_mention(text, start):
            continue
        required = True
        report("build-action", "Malformed build-exe action. Expected " + BUILD, text.count("\n", 0, start.start()) + 1)
    if not required and not template_build_clause(text):
        report("build-action", "Require the verified-entry build action " + BUILD)


def lint(goal):
    """Return (line or None, rule, diagnostic) for textual v5 violations."""
    issues = {}

    def report(rule, message, line=None):
        issues.setdefault((line, rule), message)

    text = unicodedata.normalize("NFKC", goal)
    plain = text.replace(r'\"', '"').translate(str.maketrans("", "", "\"'\x60*“”‘’"))
    for rule, pattern, message in ANTI_PATTERNS:
        for match in pattern.finditer(plain):
            if pattern is not CLI_HOST and qualified_mention(plain, match, pattern is REQUIRED_PAIR):
                continue
            excerpt = " ".join(match.group().split())[:90]
            report(rule, f"{excerpt!r}. {message}", plain.count("\n", 0, match.start()) + 1)

    missing = [name for name in ("SessionEnv", *TOOLS)
               if not re.search(r"\b" + name + r"\b", plain, re.ASCII)]
    if missing:
        report("tool-palette", "Expose the full SessionEnv palette. Missing " + ", ".join(missing) + ".")
    if not FREE_CHOICE.search(plain):
        report("tool-choice", "Explicitly allow autonomous, target-appropriate tool selection.")
    for rule, pattern, message in REQUIREMENTS:
        if not re.search(pattern, plain, re.ASCII):
            report(rule, message)
    evaluators = [runner for app, runner in (("CliApp", "runCliPure"), ("ReactiveApp", "runReactivePure"))
                  if re.search(r"\b" + app + r"\b", plain, re.ASCII)]
    if not evaluators:
        report("world-app", "Model the entry as CliApp Δ or ReactiveApp Δ S.")
    elif not any(re.search(r"\b" + runner + r"\b", plain, re.ASCII) for runner in evaluators):
        report("pure-run", "State the contract over " + " or ".join(evaluators) + ".")
    lint_build(text, report)
    return [(line, rule, message) for (line, rule), message in issues.items()]


def check_goal(goal, label):
    issues = lint(goal)
    for line, rule, message in issues:
        location = f"{label}:{line}" if line is not None else label
        print(f"{location}: [{rule}] {message}", file=sys.stderr)
    return not issues


def write_goal(name, goal):
    # Stage a regular file on the same filesystem so readers see a complete
    # goal on replacement. Follow user-supplied output symlinks as open() does.
    path = Path(name).resolve()
    if path.exists() and not path.is_file():
        path.write_text(goal, encoding="utf-8")
        return
    with tempfile.TemporaryDirectory(dir=path.parent) as staging:
        staged = Path(staging) / "goal.txt"
        staged.write_text(goal, encoding="utf-8")
        if path.is_file():
            staged.chmod(path.stat().st_mode & 0o777)
        staged.replace(path)


def self_test():
    """Exercise the public CLI, including exit status, from an empty directory."""
    script = str(Path(__file__).resolve())
    with tempfile.TemporaryDirectory(prefix="render-task-goal-") as workspace:
        goal = Path(workspace) / "goal.txt"

        def cli(*args, status=0):
            run = subprocess.run([sys.executable, script, *args], cwd=workspace,
                                 capture_output=True, encoding="utf-8")
            if run.returncode != status:
                raise RuntimeError(f"{args!r} returned {run.returncode}, expected {status}\n{run.stderr}")
            return run

        def expect(text, *parts):
            for part in parts:
                if part not in text:
                    raise RuntimeError(f"expected output to contain {part!r}")

        def lint_file(contents, *rules):
            goal.write_text(contents, encoding="utf-8")
            result = cli("--lint", goal.name, status=1 if rules else 0)
            found = set(re.findall(r"\[([a-z-]+)\]", result.stderr))
            if found != set(rules):
                raise RuntimeError(f"expected {rules!r}, got {sorted(found)!r}\n{result.stderr}")
            return result.stderr

        for lang in GOALS:
            for domain, hints in DOMAINS.items():
                cli("--target", "demo", "--summary", "UTF-8 λ", "--domain", domain,
                    "--lang", lang, "--out", goal.name)
                body = goal.read_text(encoding="utf-8")
                expect(body, "demo", "UTF-8 λ", hints[lang], BUILD, "∀ (w : SimWorld)", *TOOLS)
                cli("--lint", goal.name)
        print(f"PASS {len(GOALS) * len(DOMAINS)} bilingual/domain render + lint cases")

        gron = {
            "en": ("Flatten and reconstruct JSON.", 'Invoke "ungron" as a symlink and compare argv[0] dispatch.',
                   'Exercise HTTP URL input with {{URL}}, delayed replies and capturedReqs.'),
            "zh": ("展开 JSON 并还原。", '通过软链 "ungron" 触发并比对 argv[0] 分发。',
                   '用 {{URL}} 探测 HTTP URL 输入、延时响应与 capturedReqs。'),
        }
        for lang, (summary, symlink, http) in gron.items():
            args = ("--target", "gron", "--summary", summary, "--lang", lang,
                    "--domain", "cli-filter", "--domain", "fs-symlink", "--domain", "net-http",
                    "--extra-req", symlink, "--extra-req", http)
            cli(*args, "--out", goal.name)
            body = goal.read_text(encoding="utf-8")
            expect(body, "gron", summary, symlink, http, DOMAINS["fs-symlink"][lang],
                   DOMAINS["net-http"][lang], "fixSymlink", "httpDelayedStubMode")
            if cli(*args).stdout != body:
                raise RuntimeError("stdout and --out rendered different goals")
            cli("--lint", goal.name)
        print("PASS gron / ungron symlink + HTTP URL render and lint in en and zh")

        good = cli("--target", "example").stdout
        legacy = '''Reconstruct gron. Observe ref using both "procExec" and "pty".
Replay using only procExec.
Write Main.agda containing module Main where and import OwnershipIO.CLIHost.
(session-action (kind build-exe) (why "compile gron") (source "main"))
'''
        diagnostics = lint_file(legacy, "tool-lock", "manual-main", "obsolete-cli-host", "source-field",
                                "tool-palette", "tool-choice", "safe-option", "world-root", "world-module",
                                "world-law", "world-runner", "world-app", "build-entry")
        expect(diagnostics, ":1: [tool-lock]", ":2: [tool-lock]", ":3: [manual-main]",
               ":3: [obsolete-cli-host]", ":4: [source-field]", ":4: [build-entry]")
        print("PASS legacy gron rejected with line-specific tool, Main, CLIHost and source diagnostics")

        # Mutate a compliant goal one rule at a time. A generic failure on a
        # different missing requirement must not masquerade as a detection.
        detached = '(session-action (kind replay) (why "...") (entry "Gen.Root.app"))'
        mutations = [
            ("tool-lock", good + 'Observe ref using both "procExec" and "pty".'),
            ("tool-lock", good + "Use only procExec."),
            ("tool-lock", good + "Do not use any tool other than procExec."),
            ("tool-lock", good + "You are restricted to the procExec tool."),
            ("tool-lock", good + "Use any sandbox except netbox."),
            ("tool-lock", good + "必须同时使用“pty”和“procExec”。"),
            ("tool-lock", good + "仅允许使用 procExec。"),
            ("tool-lock", good + "禁止使用 netbox。"),
            ("manual-main", good + "Create Main.agda for the executable."),
            ("manual-main", good + "Build with your own hand-written Main.agda."),
            ("manual-main", good + "自行编写 module Main where。"),
            ("source-field", good + 'Pass (source "run IO") to the build action.'),
            ("obsolete-cli-host", good + "Avoid OwnershipIO/CLIHost.agda."),
            ("tool-palette", good.replace("FuzzGen", "generators")),
            ("tool-choice", good.replace("Autonomously select and combine any SessionEnv tools appropriate",
                                         "Use the SessionEnv palette relevant")),
            ("world-module", good.replace("Context.World ", "Context.WorldLaws ")),
            ("world-module", good + "Bypass Context.World."),
            ("safe-option", good.replace("--safe", "--unsafe")),
            ("safe-option", good + "Skip --safe for the candidate root."),
            ("world-root", good.replace("Σ_root", "Σ").replace("root specification", "specification")),
            ("world-law", good.replace("∀ (w : SimWorld)", "∀ (n : Nat)")),
            ("world-app", good.replace("CliApp", "Filter").replace("ReactiveApp", "UI")),
            ("pure-run", good.replace("runCliPure", "runCliIO").replace("runReactivePure", "runReactiveIO")),
            ("world-runner", good.replace("OwnershipIO.WorldRunner", "WorldRunner")),
            ("world-runner", good + "Do not use OwnershipIO.WorldRunner."),
            ("build-action", good.replace("(kind build-exe)", "(kind replay)")),
            ("build-why", good.replace('(why "...")', '(why "")')),
            ("source-field", good.replace('(why "...")', '(why "do not discard diagnostics") (source "IO")')),
            ("build-entry", good.replace(' (entry "<VerifiedMod>.<app>")', "") + detached),
            ("build-entry", good.replace("<VerifiedMod>.<app>", "app")),
            ("build-action", good.replace(BUILD, BUILD[:-1])),
            ("build-mode", good.replace(BUILD, BUILD[:-1] + " (mode raw))")),
        ]
        for rule, contents in mutations:
            lint_file(contents, rule)

        real_entry = r'''(session-action (kind build-exe)
    (why "compile (checked) \"root\"") (entry "Gen.M0.Root.cliEntry") (mode reactive))'''
        lint_file(good.replace(BUILD, real_entry) + '''
You may use both procExec and pty when appropriate. Use pty only for interactive cases.
Both procExec and pty are part of the palette. Use both procExec and pty as needed.
Do not limit discovery to using both "procExec" and "pty".
Never write module Main where or pass (source "...").
Never use (session-action (kind build-exe) (why "old") (source "main")).
禁止手写 Main.agda 或使用 (source "...")。可同时使用 procExec 和 pty。
''')
        zh = cli("--target", "示例", "--lang", "zh").stdout
        compact = 'build-exe 指定 (entry "<RootMod>.<app>")（可选 (mode reactive)）'
        lint_file(zh.replace(BUILD, compact))
        lint_file(zh.replace(BUILD, compact.replace("build-exe 指定 ", "")), "build-action")
        goal.write_text(good, encoding="utf-8")
        result = cli("--target", "gron", "--extra-req", "only procExec", "--out", goal.name, status=1)
        expect(result.stderr, "[tool-lock]")
        if goal.read_text(encoding="utf-8") != good:
            raise RuntimeError("a rejected render changed an existing goal")
        print(f"PASS {len(mutations)} isolated lint violations, valid protocol variants and output protection")
    print("self-test: PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--lint", metavar="GOAL", help="check a UTF-8 goal and its verified-entry build rule (- for stdin)")
    mode.add_argument("--self-test", action="store_true", help="run isolated CLI acceptance tests")
    parser.add_argument("--target", help="reference program name (required for rendering)")
    parser.add_argument("--summary", help="observable behavior to reproduce")
    parser.add_argument("--domain", action="append", choices=DOMAINS, help="add domain observations (repeatable)")
    parser.add_argument("--lang", choices=GOALS, help="goal language (default: en)")
    parser.add_argument("--extra-req", action="append", help="add a scope requirement (repeatable)")
    parser.add_argument("--out", metavar="PATH", help="write a UTF-8 goal file (default: stdout)")
    args = parser.parse_args()
    render_args = (args.target, args.summary, args.domain, args.lang, args.extra_req, args.out)
    if (args.lint is not None or args.self_test) and any(value is not None for value in render_args):
        parser.error("rendering options cannot be combined with --lint or --self-test")

    try:
        if args.self_test:
            try:
                self_test()
            except RuntimeError as exc:
                print(f"self-test: FAIL\n{exc}", file=sys.stderr)
                return 1
            return 0
        if args.lint is not None:
            if args.lint == "-":
                goal = sys.stdin.buffer.read().decode("utf-8-sig")
            else:
                goal = Path(args.lint).read_text(encoding="utf-8-sig")
            if not check_goal(goal, args.lint):
                return 1
            print(f"{args.lint}: OK")
            return 0
        if not args.target or not args.target.strip():
            parser.error("rendering needs a nonempty --target")
        goal = render(args.target.strip(), (args.summary or "").strip(), args.domain or [],
                      args.lang or "en", [req.strip() for req in args.extra_req or []])
        if not check_goal(goal, args.out or "<rendered goal>"):
            return 1
        if args.out in (None, "-"):
            sys.stdout.buffer.write(goal.encode("utf-8"))
        else:
            write_goal(args.out, goal)
        return 0
    except (OSError, UnicodeError) as exc:
        print(f"{parser.prog}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
