# 二维多对多函子化提升、`: ⊥` 反驳门禁与无辜子树零轮次复用（v7 架构规范）

> **设计原理（单向下降函子 $p : E \to B$ 的两条推论）**：
> 1. **下降是保复合结构的函子**：上层多步函数或子包的复合 $g_1 \circ f_1$ 下降后等于底范畴的单步粗函数/子包 $h_0$（反之融合亦然）。因此静态提升门禁 `Code/Lift.agda` 必须像横向的 `Code/PolyTransport.agda` 一样支持 `List QName` 多对多单元/子包映射，并在关系白名单中放行 `Context.PolyTransport`。
> 2. **下降是单向蕴含（$E \implies B$，但 $B \not\implies E$）**：把程序看作命题的证明，上层证明的命题严格强于底范畴证明的命题。因此底范畴 $T_0$ 编译通过（证出了弱命题的一个特解 $c_0$），不代表 $c_0$ 落在 $p$ 的像里（可能是偷用了沙盘简化条件的死胡同，无法提升）。系统必须给上层节点提供零启发式的形式化 `: ⊥` 反驳出口（证明 `(δ + T₀) ⊢ ⊥`，提取底范畴闯祸单元 `culprits` 打回重构 $T_0 \leadsto T_0'$），同时把上层树 $T_1$ 中**已验证完成的无辜兄弟子树**封存起来，供下一轮 $T_1'$ 通过 `keepChild` **0 轮 AI 调用直接复用**。

---

## 一、核心健全性约束

1. **窄腰底座、全部 `Context/*` 与全部 `AgdaMirror/*` 严格零改动**：
   `Ownership.agda`、`OwnershipIO.agda`、`Context/*`、`Meta/Boundary.agda`、`Store/*`、`runtime/lean-prism/AgdaMirror/*`、`runtime/lean-prism/Prism/Conservativity.lean` 保持原封不动。
2. **`refute-lift` 严格导出 `: ⊥`（不混入 `SafeTaboo`）**：
   构造性禁忌 `Context.Taboo.SafeTaboo` 继续专走既有的 `(submission (kind independent) ...)` 双核审计通道（`independenceCheck`）；新增的 `(submission (kind refute-lift) ...)` 严格要求导出闭合的 `Data.Empty.⊥` 或 `Agda.Builtin.Empty.⊥`，走 `ordinaryCheck`（`switchCheck`），天然复用 `Driver.lean` 的 `guardAxiomsAssuming` 白名单公理守卫，保证 `prism`、`legacy`、`audit` 三模式逐字节一致。
3. **MCP 预检与原生自举同步对齐**：
   对 `LiftSpec`、`NodeTask`、`Submission` 与反驳门禁的扩展同步接入 `Code/PlanPreview.agda`、`Code/HarnessEngineMain.agda` 与 `runtime/lean-prism/Prism/MCPServer.lean`，并编译进原生 `harness-engine`。
4. **零新增假设漏洞**：
   子节点绝不允许声明任何 `postulate`（`closedImplOK == []`），只能引用父节点/`SESSION_ROOT` 给定的 `refuteStubOf (δ t)` 与已闭合验证的 `baseModules t`（$T_0$）。只要存在满足 `δ` 的合法上层实现，由 `--safe` Agda 与零公理 Lean 内核的健全性，子节点在数学上绝无可能伪造出 `: ⊥`。

---

## 二、模块技术契约

### 2.1 `Code/Lift.agda` 多对多函子化升级与全链路对齐

1. **`EndpointLift` 升级为多单元列表（100% 向后兼容旧构造子）**：
   - 支持 `baseUnits : List QName`、`upperUnits : List QName`、`squareUnit : QName`、`requiredRefs : List QName`，提供 `polyEndpointLiftRefs` 与 `polyEndpointLift`；
   - 保留 `endpointLiftRefs` 与 `endpointLift` 兼容单对单写法；
   - `checkLift` 端点核验对齐 `Code/PolyTransport.agda`：检查非空端点（`emptyLiftEndpoints`）、底单元存在性（`missingBaseUnit`）、上层单元存在性（`missingUpperUnit`，允许引用子包导出步骤函数）、`square` 签名完整引用全部 `baseUnits ++ upperUnits ++ requiredRefs` 且余域非平凡并命中关系白名单。
2. **`ChildLift` 支持一拆多 / 多合一子包映射**：
   - 支持同一 `baseChild` 多次映射（一拆多：`Parser₀` 拆为 `Lex₁` 与 `Resolve₁`），并新增 `moveChildLifts : List QName → List QName → List LiftSpec → ChildLift`（多对多/多合一：`Pass1₀, Pass2₀` 融合为 `Fused₁`）；
   - `checkLift` 全量核验所有带假设的底子包 `required` 均被覆盖（`missingChildMap`），且 `ChildLift` 声明的每一个上层目标子包均出现在 `imports (withTests upper upperSpec)` 中（`missingChildImport`）。
3. **`relation` 白名单放行 `Context.PolyTransport`**：
   - 在 `Code/Lift.agda` 的 `relation` 中加入 `Context.PolyTransport` 前缀，使纵向提升可直接使用 `PortRel`、`TransportsPoly`、`Transports₁`、`Transports₂`、`cut₁`。
4. **S-表达式向后兼容编解码与下游对齐**：
   - `Code/Encode.agda` 与 `Code/Parse.agda` 保持单对单编码逐字符兼容，并扩展多单元列表及 `(move (B1 B2) (U1 U2) (sub...))` 编码；
   - 同步对齐 `Code/HarnessCore.agda`、`Code/NodeTransport.agda`、`Code/PlanPreview.agda` 与 `Code/SessionRunner.agda`。

### 2.2 节点形式化 `: ⊥` 提升反驳出口与已完成无辜子树保活

1. **协议与提交扩展（`Code/Transport.agda`、`Code/Submission.agda`）**：
   - `Verdict` 新增 `liftObstruction : (why : String) → (culprits : List QName) → Code → Verdict`；
   - `Submission` 新增 `refuteLift : (why : String) → (src : String) → Submission`，对应 S-表达式 `(submission (kind refute-lift) (why "...") (refute @refute))`。
2. **纯静态门禁 `validLiftRefutation` 与罪魁单元提取 `extractCulpritBaseUnits`**：
   - `extractCulpritBaseUnits` 静态扫描 `refsDecls (decls c)`，收集所有命中 `bases` 各模块定义单元的规范 `QName`（去重保序）；
   - `validLiftRefutation` 强制要求 `closedImplOK allowedFlags c == []`、无顶层模块参数、存在公开导出 `⊥`、全部引用严格限定在 `modName c` / `specMod` / `bases` / `--safe` `contextModule` 内，且**必须实际引用底范畴模块**（未触碰底范畴的纯规约冲突应交 `contradiction`）；
   - 同步在 `Code/HarnessEngineMain.agda` 新增 `check-lift-refute` CLI 分支，并在 `runtime/lean-prism/Prism/MCPServer.lean` 支持草稿级提升反驳预检。
3. **`Code/Harness.agda` 状态机流转与 `freezeVerifiedKids` 保活**：
   - `Planning` 收到 `refuteLift` 后经 `dumpSubmission` $\to$ `validLiftRefutation` $\to$ `checkAgda` 核验并提取 `culprits` 进入 `Done (liftObstruction why culprits c)`；
   - `WaitingKids` 收到子包 `liftObstruction` 时仅停止受阻孩子，**保持其余 `finished` 与 `sleeping _ true` 兄弟槽位不动**，并将诊断带回父节点 `Planning`；
   - `shutdownState` 在 `liftObstruction` 停机时通过类型安全的 `freezeVerifiedKids` 保留全部已完成兄弟子包，写入零 `postulate` 的干净壳模块后归还给 `SessionRunner`。

### 2.3 会话层二维回流（`T₀ → T₀′`）与跨层 `keepChild` 零轮次复用

1. **部分封存树缓存（`Code/SessionWorkspace.agda`、`Code/SessionRunner.agda`）**：
   - 当 `runNode` 返回 `(liftObstruction why culprits c , partialResult)` 时，写入 `trees/<name>/verdict = "lift-obstruction"`；若 `partialResult` 包含已验证子包，则存入 CAS 并绑定 `refs/partial/<name>`（经 `verifyCommitDAG` 校验），向 `SESSION_ROOT` 返回 `CULPRIT_BASE_UNITS` 与 `PRESERVED_CHILDREN`。
2. **`chooseTransport` 跨层挂载 `refs/partial/*` 实现零轮次 `keepChild`**：
   - `SessionWorkspace.loadPartialBases` 加载经校验且满足 `closedImplOK [] == []` 的部分封存快照；
   - 新上层树 `T₁′` 中凡通过 `(keep oldChild newChild)` 声明复用的无辜子包，直接植回已验证实现并静态复核 `retainedLift`，**AI 调用次数严格为 `0`**。
3. **防原地空转护栏**：
   - 记录最近一次 `lift-obstruction` 的 `(baseTips, specCanonicalHash)`；若底范畴未重构且上层规约/提升原封不动重交，`driveTreeWith` 直接拒绝并提示先重构 `CULPRIT_BASE_UNITS` 或修订提升规约。

---

## 三、验收测试入口

- `./test-v7-lift.sh`：多对多单元/子包函子化提升、`Context.PolyTransport` 纵向方块与 `PlanPreview` 预检；
- `./test-v7-obstruction.sh`：`prism` / `legacy` / `audit` 三模式 `: ⊥` 提升反驳门禁与 `freezeVerifiedKids` 抢救；
- `./test-v7-2d-e2e.sh`：迷你 Pandoc 端到端二维恢复（`T₀` $\to$ `T₁` `Escape₁` 完成 + `refute-lift` $\to$ 空转拒绝 $\to$ 重构 `T₀′` $\to$ `T₁′` 以 **0 轮 AI 调用** `keepChild` 复用 `Escape₁`）；
- `./test-v7-all.sh`：v7 全量验收与 v5/v6 核心门禁回归。
