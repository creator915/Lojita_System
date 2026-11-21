# 任务级 `goal.txt` 权威模板与编写规范（Tool-Neutral & World-Coupled）

本文件为评测基准（benchmark harness）与任务启动脚本提供权威的 `goal.txt` 生成模板及编写准则，确保每个开放世界会话既能**按目标领域自主调度全套 `SessionEnv` 沙箱工具**，又能将全部宿主副作用耦合进 `--safe` 的 `Context.World` 封闭世界规约与 `OwnershipIO.WorldRunner` 单一薄解释器。

---

## 1. 严禁出现的两条历史反模式

1. **严禁把观测或回放工具硬编码锁死为 `"using both procExec and pty"`（或仅提 `procExec`）**
   - 早期评测脚本在 `goal.txt` 中写死 `"Observe ref using both procExec and pty"`，导致模型在处理 `gron` / `ungron`（依赖 `argv[0]` 符号链接别名分发与文件读写）、`curl` / HTTP 客户端（依赖本地回环 HTTP/TCP/代理桩、慢响应超时 `httpDelayedStubMode` 与 `capturedReqs` 报文抓包）或版本控制工具（依赖 Git 仓库状态演进）时不敢调用 `"fsbox"`、`"netbox"` 与 `"gitbox"`。
   - **正确做法**：`goal.txt` 必须列出完整的开放世界工具调色板（`"procExec"`、`"pty"`、`"fsbox"`、`"netbox"`、`"gitbox"` 与 `Context.Tools.FuzzGen`），要求 `SESSION_ROOT` 先探测 `"ref"` 的真实行为边界，再自主组合匹配该目标领域的沙箱工具完成探针与回放。

2. **严禁允许手写 `Main.agda` 或把宿主副作用留给未验证 IO 胶水**
   - `build-exe` 已彻底废除 `source` 字段，只接受 `(entry "<RootMod>.<app>")`（及可选 `(mode cli | reactive)`）并由 `OwnershipIO.WorldRunner` 静态编译 `bin/candidate`。
   - **正确做法**：`goal.txt` 必须明确要求上层根规约 `Σ_root` 在 `--safe` 的 `Context.World` 中将目标程序建模为 `CliApp Δ = WorldProg Δ ExitCode`（或交互式 TUI / 守护进程的 `ReactiveApp Δ S`），把 `argv[0]` 符号链接分发、CLI 标志、环境变量、`isTTYStdout` ANSI 着色、文件/网络错误分支、毫秒级超时与退出码全部纳入 `runCliPure` / `runReactivePure` 的全称 `∀ (w : SimWorld)` 定律（配合 `Context.WorldLaws` 及 `FsLaws`、`NetLaws`、`TermLaws`、`ClockLaws`、`GitLaws`）。

---

## 2. 标准 `goal.txt` 权威模板（英文通用版，推荐评测脚本直接渲染）

评测脚本只需替换 `{{TARGET_DESC}}` 与可选的 `{{SCOPE_CONSTRAINTS}}`（若全功能黑盒复刻可留空或填 `Full observable behavior of "ref" within the cleanroom sandbox.`）：

```text
Reconstruct a cleanroom, statically linked, formally verified replacement ("cand") for the reference binary ("ref"): {{TARGET_DESC}}

Scope & Observable Surface:
- {{SCOPE_CONSTRAINTS}}

Mandatory Open-World Discovery & Replay Protocol (Tool-Neutral Palette):
1. Do NOT hardcode your probes to a single tool. First inspect "ref" (--help, version/usage, error paths, and I/O channels), then autonomously select and combine the appropriate tools from the SessionEnv palette:
   - "procExec": batch CLI flags, stdin/stdout/stderr byte streams, and exit codes;
   - "pty": isatty-dependent ANSI coloring/formatting, terminal dimensions (resizeTTY), interactive keystrokes, timers, and signals;
   - "fsbox": file/directory reads and mutations, permission/directory error handling, and argv[0] symlink dispatch (e.g., fixSymlink "<alias>" "ref" / "cand");
   - "netbox": loopback HTTP/TCP/UDP/proxy endpoints (httpStubMode / tcpStubMode), slow-response timeout boundaries (httpDelayedStubMode / tcpDelayedStubMode), {{PORT}}/{{ADDR}}/{{URL}} substitution, and wire-level request capture (capturedReqs);
   - "gitbox": repository worktree, index, commit, branch, and tag transitions;
   - Context.Tools.FuzzGen: deterministic generators and counterexample shrinkers.

Mandatory Closed-World Specification & Build Protocol (World-Coupling):
2. Drive progressive Dialectica trees (T0 finite blueprint -> T1/T2... concrete ports and world-coupled root Σ_root). Keep every specSrc purely behavioral (ports, minimal PortLift projections, named postulates with universal ∀ laws, and "ref"-verified boundary equations — never pre-write parsers or internal algorithms in specSrc).
3. Model ALL target host side-effects inside --safe Context.World as `CliApp Δ = WorldProg Δ ExitCode` (or `ReactiveApp Δ S` for interactive TUI / daemons) at Σ_root, proving universal `∀ (w : SimWorld)` contracts over `runCliPure` / `runReactivePure` with `Context.WorldLaws`, `FsLaws`, `NetLaws`, `TermLaws`, `ClockLaws`, and `GitLaws` (decomposing child capabilities via `Δ_child ⊆ Δ_parent` and `liftWorld`).
4. Build `bin/candidate` exclusively via `(session-action (kind build-exe) (why "...") (entry "<RootMod>.<app>"))` (with optional `(mode reactive)`) through `OwnershipIO.WorldRunner` — never write hand-rolled IO glue.
5. Before `(kind finish)`, execute differential replay scripts comparing "ref" and "cand" symmetrically across every relevant channel (stdout, stderr, exit status, TTY output, filesystem snapshots & symlinks, captured network requests & timeouts, or Git state) with FuzzGen shrinking, exiting 0 only on exact agreement.
```

---

## 3. 标准 `goal.txt` 权威模板（中文版）

```text
为参考程序 `"ref"` 构建洁净室、静态链接且经形式化验证的等价替代程序 `"cand"`：{{TARGET_DESC}}

任务范围与可观察边界：
- {{SCOPE_CONSTRAINTS}}

强制执行准则：
1. 开放世界自主选型观测（严禁局限于单一工具）：先探测 `"ref"` 的帮助信息、参数语法、报错分支与 I/O 通道，再从 `SessionEnv` 全套工具表中按目标领域自主组合探针：
   - `"procExec"`：批处理命令行参数、标准输入/输出/错误流与退出码；
   - `"pty"`：`isatty` 敏感的 ANSI 着色与排版、终端尺寸变更、交互按键时序与信号；
   - `"fsbox"`：文件/目录读写快照、路径与权限报错、以及 `argv[0]` 符号链接别名分发（如 `fixSymlink "<别名>" "ref"` / `"cand"`）；
   - `"netbox"`：本地回环 HTTP/TCP/UDP/代理桩（`httpStubMode` / `tcpStubMode`）、慢响应超时边界（`httpDelayedStubMode` / `tcpDelayedStubMode`）、`{{PORT}}`/`{{ADDR}}`/`{{URL}}` 注入与 `capturedReqs` 请求抓包；
   - `"gitbox"`：Git 工作区、暂存区、分支、标签与提交状态演进；
   - `Context.Tools.FuzzGen`：纯 Agda 随机输入生成与最小反例收缩。
2. 封闭世界耦合规约（`Context.World` + `*Laws`）：按 T0 有限蓝图 -> T1/T2 具体端口与根模块 `Σ_root` 逐级演进；所有宿主副作用（`argv[0]`、标志、环境变量、TTY 着色、文件/网络错误、超时与退出码）必须在 `--safe` 的 `Context.World` 中建模为 `CliApp Δ`（或 `ReactiveApp Δ S`），并用 `Context.WorldLaws`、`FsLaws`、`NetLaws`、`TermLaws`、`ClockLaws`、`GitLaws` 证明关于 `runCliPure` / `runReactivePure` 的全称 `∀ (w : SimWorld)` 定律。
3. 零手写胶水编译与对称回放门禁：通过 `build-exe` 指定 `(entry "<RootMod>.<app>")`（可选 `(mode reactive)`）交由单一薄解释器 `OwnershipIO.WorldRunner` 静态编译 `bin/candidate`；`finish` 前必须在实际调用 `"ref"` 与 `"cand"` 的全部相关通道上完成生成式对拍与自动收缩。
```

---

## 4. 目标领域与工具 / 能力映射检查表（供评测作者核对，切勿裁剪调色板）

编写具体任务的 `{{SCOPE_CONSTRAINTS}}` 时，可描述业务边界（如“仅要求 HTTP/1.1 明文与本地代理，不要求 HTTP/3”），但**保留上方完整的 `SessionEnv` 调色板说明**，由会话根自主决策：

| 目标程序类型 | 典型开放世界探针组合 (`SessionEnv`) | 典型封闭世界能力集 (`Context.World`) 与定律库 |
| --- | --- | --- |
| 结构化文本 / JSON 转换器（如 `gron`、`jq`） | `"procExec"` + `"fsbox"`（文件输入与 `fixSymlink "ungron"` 测 `argv[0]`）+ `"pty"`（测 TTY 彩色输出 vs 管道纯文本）+ `FuzzGen` | `envCap ∷ ttyCap ∷ fsCap ∷ []`；`WorldLaws` + `FsLaws` + `TermLaws` |
| 文件检索 / 归档 / 补丁工具 | `"fsbox"`（目录树、符号链接、权限报错与 `diffSnapshot`）+ `"procExec"` + `"pty"` + `FuzzGen` | `envCap ∷ ttyCap ∷ fsCap ∷ []`；`WorldLaws` + `FsLaws` |
| 网络客户端 / 协议探针（如 `curl` 子集） | `"netbox"`（`httpStubMode`、`httpDelayedStubMode` 超时、`capturedReqs` 抓包）+ `"fsbox"`（`-o` 落盘与配置）+ `"procExec"` + `FuzzGen` | `CliCaps`（含 `clockCap`、`netCap`、`fsCap`、`envCap`、`ttyCap`）；`WorldLaws` + `NetLaws` + `ClockLaws` + `FsLaws` |
| 交互式终端应用 / 编辑器 / 监控器 | `"pty"`（`allTTY` / `pipeStdioWithTTY`、按键序列、`resizeTTY`、`sleepMs` 定时器与 `stepANSI`）+ `"fsbox"` + `FuzzGen` | `ReactiveApp (clockCap ∷ envCap ∷ ttyCap ∷ fsCap ∷ []) S`；`WorldLaws` (`runReactiveSteps-++`) + `TermLaws` + `ClockLaws` |
| 版本控制辅助工具 | `"gitbox"`（`gitWriteFile`、`gitStageAll`、`gitCommit`、`gitRunTarget`）+ `"fsbox"` + `FuzzGen` | `envCap ∷ ttyCap ∷ fsCap ∷ gitCap ∷ []`；`WorldLaws` + `GitLaws` + `FsLaws` |
