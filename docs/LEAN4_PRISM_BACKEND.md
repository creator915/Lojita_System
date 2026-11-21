# Lean 4 Prism 偏计算器、v2 单元级 Optic Lens 切片与 Harness 原生编译架构规范

> **单一权威源码**：全仓 `.agda` 源码保持为唯一权威真相源（Authoritative Source of Truth）。  
> **双层落地架构**：
> 1. **Layer 1（任务期全链路默认接入）**：`Code/CLI.agda`、`Code/SessionRunner.agda`、`Main.agda` 默认启用 `leanPrism`，通过环境变量 `CODETRANSPORT_BACKEND=prism|legacy|audit` 支持零重编热切换；原生修复原版 Agda 在大 `ℕ` 字面量模式（如 `39`、`8232`）上的 `suc` 链展开缺陷。
> 2. **Layer 2（Harness 自身纯模块转译 Lean 4 原生二进制）**：将 Harness、语境与后端协议中全部 23 个纯计算/协议/门禁模块由 `.agda` 直接转译编译为单个 Lean 4 原生 C 二进制 `runtime/lean-prism/.lake/build/bin/harness-engine`，而余归纳线性资源编排（`Ownership.agda` 的 `ServerI`/`Proc`/`Prog` 与 `SessionRunner` IO 调度）继续保留在 `--guardedness` Agda 层。

---

## 一、核心设计演进：从整文件 Prism 到单元级 Optic Lens（`Whole ≅ FastFocus ×_∂ SlowResidual`）

依赖类型系统的**开放数学表达力**（余归纳 `coinductive` / copattern、多参字典序与互递归 Foetus、`with` 抽象、`--without-K` 等）与**极致系统工程优化**（Lean 4 C++ 内核、`.olean` 内存映射、LCNF + Perceus 精确引用计数 C 后端）存在天然张力。

**v2 单元级 Optic Lens 架构**将截流粒度下沉至**声明强连通分量（`Unit` SCC）**，实现**证明检查按车道切片、原生二进制统一拼装**：

$$\text{Whole} \;\cong\; \text{FastFocus }(F_1, F_2) \;\times_{\partial}\; \text{SlowResidual }(S)$$

1. **`Lens.get`：声明级 SCC 依赖切片与去传染（`Prism/LensSlice.lean` + `Prism/LoweringContext.lean`）**
   - **去传染（De-Infection）**：剥离文件头 `{-# OPTIONS --guardedness #-}` 的跨单元与跨模块传染——只要某个单元自身未构造余归纳值，即使所在模块或上游依赖带有 `--guardedness`，该单元依然 100% 留在 Lean 4 快车道（`SLOW_UNITS = 0`，零次 Agda 调用）。
   - **原生 `ℕ` 与 `String` 字面量模式**：Lean 4 快车道与 C 代码生成原生支持任意大小 `ℕ`（如 `39`、`8232`）与 `String` 字面量模式匹配（$O(1)$ 整数/字符串判等与内核 `rfl` 归约），彻底消除原版 Agda 2.6.3 将 `n > 20` 暴力展开为一元 `suc` 链并报错的实现缺陷。
   - **非依赖积 `AgdaPair` 自动特化**：当编译包未使用依赖和 `Σ` 时，自动将 `_×_` / `_,_` / `proj₁` / `proj₂` 特化为非依赖 `AgdaPair` 结构，使 Lean 4 内核原生支持任意嵌套与互归纳数据类型（如 `Code.agda` 的 8 路互归纳语法树与 `Frozen`、`JSON` 等）。
   - **三段拓扑分解（$F_1 \to S \to F_2$）**：
     - **$F_1$（底层甜区焦点）**：纯代数数据类型（含多类型 `mutual inductive`）、非余归纳记录、模式同义词 `pattern`、高阶多态函数、单参结构递归与内涵等式证明 $\longrightarrow$ 交由 Lean 4 极速核验。
     - **$S$（极小慢残差）**：仅包含真正用到 `coinductive` 记录、前后缀 copattern、多参字典序/互递归、`with` 子句、扩展 λ 的 SCC，以及类型签名中需要展开 $S$ 定义归约的少量证明单元。
     - **$F_2$（下游甜区调用者）**：所有仅在项位置消费 $S$ 的下游单元直接留在 Lean 4 快车道。

2. **`Lens.put` 第一层：双车道证明拼接（Sequent Cut 消去，100% 兼容 `--safe`）**
   $$\frac{\vdash_{\text{Lean}} F_1 : \partial_{F_1} \qquad \partial_{F_1} \vdash_{\text{Agda (`--safe`)}} S : \partial_S \qquad \partial_{F_1}, \partial_S \vdash_{\text{Lean}} F_2 : \tau}{\vdash F_1 \,;\, S \,;\, F_2 : \tau}$$

3. **`Lens.put` 第二层：统一原生 C 代码生成与单二进制链接**
   - `Prism/TranscodeExec.lean` 与检查器共用声明表和 `TSyntax` 降级。证明通过 `Prop` 擦除，延迟端口用 `Thunk.mk` 构造并按需读取，严格标量直接传值。驻留的 Lean elaborator 编译每个模块，`Lean.Compiler.LCNF.emitC` 从环境直接生成 C。各模块以 `gcc -O3 -c` 并行编译，再与镜像和 WorldRunner 静态链接。
   - 默认的 `prism-build` 先用 `checkSlicedBundle` 核验输入。需要 Agda 核验且尚未取得检查结果的残差返回退出码 20。在构建进程外完成 `prism-check` 或 Agda 核验后可对同一输入使用 `--trusted-codegen`，包括使用 `--prop` 的模块。执行环境中无法为 `partial def` 构造 `Nonempty` 见证时使用 Lean 的 `unsafe def` 原生递归。
   - 检查与执行共用数据和记录的声明表。执行端根据全包内的消费方式选择字段布局；依赖索引、有限归纳类型的递归字段和深层构造子模式保留严格视图，余归纳记录按投影强制相应字段。
   - 遇到未覆盖的长尾表层语法时，`--dump-bin` 自动通过 `dump/dump` S-表达式解码衔接后续 Lens 切片；仅当整模块使用 `--without-K` 或未镜像外部模块（如 `Ownership`）时触发退出码 `20`（$\bot$）无损回退至 `legacyAgda`。

---

## 二、双层工程落地清单

### 1. Layer 1：主干运行管线全接入（默认 `leanPrism`）

| 接入点 | 路由函数 | 行为说明 |
| --- | --- | --- |
| `Code/CLI.agda` (`runTaskIn`) | `switchDumpTool` / `switchAgdaTool` / `switchNodeEnvironment` | 单节点任务与提升任务默认走 `leanPrism` |
| `Code/SessionRunner.agda` (`driveTreeWith`) | `switchDump` / `switchCheck`（支持非空 `ancestors` 封存视图） | 会话树 `specSrc` 解析、规约类型检查与节点内工具调用全走 `leanPrism` |
| `Code/SessionRunner.agda` (`buildExe`) | `switchSessionCompileExe` | 通过 `prism-dump` 校验 `closedImplOK` 并由 `prism-build` (`gcc -O3 -static`) 直接产出 `bin/candidate`，仅在 `exitBot` 时回退 `legacyBuild` |
| `Code/SessionRunner.agda` (`auditTrees`) | `switchCheck` | `finish` 门禁复核全量导出模块时走同一后端，杜绝大 `ℕ` 字面量模式冲突 |
| `Main.agda` (`roundtrip` \| `units` \| `apply` \| `order`) | `runHarnessEngine` | 纯 CLI 命令直接路由至原生 Lean 4 `harness-engine` 二进制 |

### 2. Layer 2：转译为原生 Lean 4 的 23 个 Harness / 语境 / 后端模块

构建脚本 `./build.sh` 自动将以下权威 `.agda` 源码转译并静态链接为 `runtime/lean-prism/.lake/build/bin/harness-engine`（自检 `harness-engine verify-self` 输出 `HARNESS_ENGINE_OK`）：

- **不可变语境与后端契约（5 个）**：`Context/Blueprint.agda`、`Context/PolyTransport.agda`、`Context/Terminal.agda`、`Context/Filter.agda`、`Backend/Mode.agda`
- **AST、范畴搬运、自由提升与多范畴校验核心（11 个）**：`Code.agda`、`Code/SExpr.agda`、`Code/Shape.agda`、`Code/Transport.agda`、`Code/Lift.agda`、`Code/Protocol.agda`、`Code/Encode.agda`、`Code/Parse.agda`、`Code/Render.agda`、`Code/Namespace.agda`、`Code/PolyTransport.agda`
- **节点协议、提示词渲染、门禁核心与宿主入口（7 个）**：`Code/NodeTransport.agda`、`Code/Submission.agda`、`Code/SessionProtocol.agda`、`Code/Prompt.agda`、`Code/HarnessCore.agda`、`Code/PureCLI.agda`、`Code/HarnessEngineMain.agda`
- **保留在 Agda `--guardedness` 层的模块**：`Ownership.agda`、`OwnershipIO.agda`、`OwnershipIO/*`、`Store/*`、`Meta/*`、`Code/Harness.agda`（余归纳 `ServerI` 状态机外壳，纯门禁委托 `Code/HarnessCore.agda`）、`Code/SessionWorkspace.agda`、`Code/SessionRunner.agda`。

### 3. 热切换方式（无需重编代码）
- 默认（或 `CODETRANSPORT_BACKEND=prism`）：启用 Lean 4 Prism v2 + `harness-engine` + 模块级 $\bot$ 自动回退；
- `CODETRANSPORT_BACKEND=legacy`：100% 走原版 `dump/dump` + `agda` + MAlonzo 管线；
- `CODETRANSPORT_BACKEND=audit`：双跑对拍审计模式，实时交叉核验 `encodeCanonical`、`pass`/`fail` 及 `harness-engine` 输出逐字节全等。

---

## 三、验收与构建命令

```bash
./build.sh
./test-lean-prism.sh
```
