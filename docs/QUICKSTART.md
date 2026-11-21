# Lojita System / CodeTransport (v7) 构建与使用指南

Lojita System（底层核心引擎代号 `CodeTransport`）是一个基于 **Agda 2.6.3 (`--safe`) + Lean 4 (Prism)** 的范畴式编程形式化操作系统与所有权树 Harness。本文档汇总环境配置、构建、AI 后端配置与离线验收回归命令。

---

## 环境要求

当前开发与验收环境（Linux x86_64）：

- **OS**：Linux x86_64（实测 Ubuntu 24.04）
- **Agda**：`2.6.3`
- **agda-stdlib**：`1.7.3`（默认路径 `/usr/share/agda-stdlib`）
- **GHC**：`9.4.7`（需安装带 `Agda` 库包的 GHC，供 `dump/Dump.hs` 与 Agda `--compile` 使用）
- **Lean 4 / Lake**：`leanprover/lean4:v4.36.0`（见 `runtime/lean-prism/lean-toolchain`，通过 `elan` 安装并确保 `$HOME/.elan/bin` 在 `PATH` 中）
- **C 编译器**：`gcc` / `cc`（C11，且需带静态链接库如 `libc6-dev`，用于 `build.sh` 的 `-static` relay 编译）
- **Python**：`3.12+`（仅标准库，用于脚本与 `goal.txt` 生成器）
- **可选依赖**：
  - **Codex CLI** / **Claude Code**（或其他 HTTP LLM 接口，仅在运行 live AI 会话时需要）
  - **Docker**（仅在使用 `(ref-target (docker ...))` 洁净室目标或运行 `test-v4-integration.sh` 时需要）
  - **curl**（仅在使用 `RawHTTPBackend` 时需要）

构建与运行前建议先设置环境变量：

```bash
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$PATH"
```

---

## 构建

```bash
./build.sh
```

`build.sh` 会依次编译：
1. `dump/dump`（Agda AST 导出器）
2. 5 个静态 C 沙箱中继（`tmp/term-build/{term,fs,net,git,web}-relay`）
3. Lean 4 `liblean_cli_host`、`AgdaMirror`（含零公理校验）与 `agda2lean`
4. Lean 4 原生编译版 `runtime/lean-prism/.lake/build/bin/harness-engine` 并执行 `verify-self`
5. 顶层命令行入口 `./Main`

---

## 在哪里设置 AI

所有 AI 后端与默认模型配置都在 **`Code/AI.agda`** 中：

- **默认 Codex CLI 配置**（`Code/AI.agda` 中的 `defaultCodex`）：
  - **环境变量覆盖（免重编）**：
    - `CODETRANSPORT_MODEL`：覆盖默认模型名
    - `CODETRANSPORT_EFFORT`：覆盖推理强度
    - `CODETRANSPORT_SERVICE_TIER`：覆盖服务档位
    - `CODEX_HOME`：覆盖 Codex 会话 rollout 目录（默认 `$HOME/.codex/sessions`）
  - **修改 CLI 可执行文件路径**：请根据你本机的 `codex` 路径（例如 `"codex"` 或 `"/usr/local/bin/codex"`）按需修改 `Code/AI.agda` 中的 `executable` 字段后重新运行 `./build.sh`。
- **其他后端接口**（`Code/AI.agda` 中的 `Backend` 数据类型）：
  - `CodexCLIBackend`：默认命令行入口使用的 Codex CLI + 内置 `agda2lean mcp` 后端。
  - `RawHTTPBackend`：通过 `curl` 调用自定义 HTTP 接口。
  - `ScriptedBackend` / `ServiceBackend` / `ParallelServiceBackend`：用于离线脚本化测试或自定义接入。

---

## 如何使用

### 1. 离线快速自检（无需 AI / API Key）

构建完成后，可直接跑以下离线测试验证本机环境是否正常：

```bash
# 检查 goal.txt 生成器与提示词同步
python3 scripts/render_task_goal.py --self-test
python3 scripts/embed_prompts.py --check

# v7 新增二维提升、: ⊥ 反驳与跨层零轮次复用门禁
./test-v7-lift.sh
./test-v7-obstruction.sh
./test-v7-2d-e2e.sh

# v6/v5 核心门禁（双核 Prism、白盒与独立性门禁、世界模型与协议组合）
./test-lean-prism.sh
./test-whitebox-gates.sh
./test-independent-gates.sh
./test-gron-stress.sh
./test-world-conformance.sh
./test-step4-protocol.sh
./test-prompts.sh
./test-replay-gate.sh

# 或一键运行 v7 全量验收套件
./test-v7-all.sh
```

> 提示：Agda 2.6.3 并发写同一目录的 `.agdai` 会导致接口文件损坏，上述脚本请**串行执行**，或在独立目录副本中设置不同 `AGDA_DIR` 后再并发运行。

### 2. 运行开放世界自主会话（`session`）

1. 生成符合协议的 `goal.txt`：
   ```bash
   python3 scripts/render_task_goal.py \
     --target mytool \
     --domain cli-filter \
     --lang zh \
     --out /tmp/work/goal.txt
   ```
2. 准备参考目标描述文件 `ref.sexp`（二选一）：
   - 本地可执行文件：
     ```scheme
     (ref-target (local "/bin/cat"))
     ```
   - Docker 洁净室镜像内可执行文件：
     ```scheme
     (ref-target (docker "your-image:tag" "/usr/local/bin/target"))
     ```
3. 启动会话：
   ```bash
   ./Main session /tmp/work /tmp/work/goal.txt /tmp/work/ref.sexp
   ```

### 3. 其他常用子命令

```bash
# 运行单个封闭世界节点（由 Spec.agda 驱动）
./Main node Spec.agda ./state-dir

# 基于已有状态树执行 Lift
./Main lift Spec.agda ./new-state ./base-state Lift.sexp

# 离线运行单个会话探针脚本（不需要 AI）
./Main session-probe /tmp/work /tmp/work/ref.sexp probe.agda

# 运行普通 Agda 脚本
./Main script Script.agda

# AST / S-Expr 底层工具
./Main roundtrip File.sexp
./Main units File.sexp
./Main order File.sexp
./Main apply Code.sexp Plan.sexp
```

### 4. 编译后端热切换（环境变量）

- 默认（或 `CODETRANSPORT_BACKEND=prism`）：启用 Lean 4 Prism 与原生 `harness-engine`（遇到未覆盖特性自动回退到 Agda）。
- `CODETRANSPORT_BACKEND=legacy`：全程走传统 `dump/dump` + Agda + MAlonzo 管线。
- `CODETRANSPORT_BACKEND=audit`：双后端同时运行并逐字节对拍。

---

## 本机默认路径说明

部署到其他机器时请留意以下默认配置：

1. **`Code/AI.agda`**：默认 Codex CLI 可执行文件路径与模型参数按开发机预设，跨机部署请调整该行或配合 `CODETRANSPORT_MODEL` / `CODETRANSPORT_EFFORT` / `CODETRANSPORT_SERVICE_TIER` 覆盖。
2. **`agda-stdlib` 路径**：`build.sh`、`Code/CLI.agda`、`check.sh`、`scripts/verify_modules.py` 等处默认引用 `/usr/share/agda-stdlib`。如果你的标准库安装在其他位置，请建软链到 `/usr/share/agda-stdlib` 或按需调整 `-i` 参数。
3. **静态编译参数**：`build.sh` 使用 `cc ... -static` 构建 5 个 C relay，需系统提供静态 C 库（Ubuntu/Debian 可安装 `libc6-dev`）；非 Linux 或缺少静态库的环境需去掉 `-static` 或在 Linux 容器中构建。
