<p align="center">
  <img src="./docs/assets/logo.svg" width="112" height="112" alt="*⋉ Lojita System Icon" />
</p>

<h1 align="center">Lojita System &nbsp;<code>*⋉</code></h1>

<p align="center">
  <strong>Categorical Programming for the Post-Agent Era.</strong><br/>
  <em>Files are the ontology. Types are the rails. LLMs are just replaceable oracles.</em>
</p>

<p align="center">
  <strong>以范畴式编程驱动的形式化许愿机</strong> —— <em>Vibe Coding 只适合玩具；范畴式编程才能托起巨型系统。</em>
</p>

<p align="center">
  <a href="./README.md"><strong>简体中文</strong></a> ·
  <a href="./docs/README_EN.md">English</a> ·
  <a href="./docs/MANIFESTO.md"><strong>📖 完整理论与架构白皮书 (Manifesto)</strong></a>
</p>

<p align="center">
  <img src="https://img.shields.io/badge/Kernel-Agda_2.6.3_(--safe)-0F172A?style=flat-square" alt="Agda 2.6.3 --safe" />
  <img src="https://img.shields.io/badge/Fast_Backend-Lean_4_C%2B%2B_%2F_LCNF-2563EB?style=flat-square" alt="Lean 4 Backend" />
  <img src="https://img.shields.io/badge/Soundness-Zero--Axiom_Guard_(0_False_Positives)-10B981?style=flat-square" alt="Zero Axiom Guard" />
  <img src="https://img.shields.io/badge/Intelligence-Zero--Cost_API_%26_Agent_Plug--in-D83139?style=flat-square" alt="Zero-Cost API & Agent Plug-in" />
</p>

<!-- 录屏完成后可将下方 ./docs/assets/hero-loop.svg 直接替换为 15~30 秒实录 ./docs/assets/demo.gif -->
<p align="center">
  <img src="./docs/assets/hero-loop.svg" width="960" alt="Lojita System: Structure-Preserving Closed Loop" />
</p>

---

## ⚡ 告别“拟人化 Agent”与“Vibe Coding”

市面上的主流 AI 编程产品把大模型拟人化成“坐在终端前聊天的数字实习生（Humanoid Agent）”——当项目膨胀到数万行时，上下文雪崩、偷改测试、分包走样接踵而至。

**Lojita System 不是另一个 Agent 编排框架，而是一台以类型化文件树为本体的操作系统。** 一会话对应一愿望；在这里，连系统调度自身的探测脚本与状态机都是经过机器检验的 Agda 代码，而大模型只是轨道上随用随换的局部推理算子。

| 维度 | Vibe Coding / 拟人化 Agent | Lojita System（范畴式编程） |
| :--- | :--- | :--- |
| **记忆与规模** | 单一长会话堆积全部探索与报错，工程越大越健忘 | **文件本体局部记忆**：平时零常驻进程；编译试错关在临时槽过关即焚，盘上只留纯净语义因果 |
| **权限与操作** | 对着未知目录盲敲 `bash` / `sed`，随时误删越权 | **线性所有权树（无 `write` 原语）**：`文件 = 资源 ⊗ !数据`，越权路径在类型层连名字都算不出来 |
| **模块分包** | 自然语言层层传话，3 层之后边界条件漏成筛子 | **Dialectica 先验条件粘合**：唤醒子包前必须先编译证明“子规约合取 $\implies$ 父规约”，分包只强不弱 |
| **排错与重构** | 测试挂了靠人工救火，AI 硬塞脏特判或推倒重写 | **`: ⊥` 红牌反驳 + 零重算复用**：死胡同交 `: ⊥` 精准打回，窄口弹 `DETOUR` 绕路，无辜子树 **0 次 AI 调用**直接复用 |

---

## 🧩 什么是「范畴式编程」？—— 在每一次变换中保持结构

范畴论的核心思想只有一句话：**在变换中保持结构**。

软件工程的全生命周期，本质上就是一连串**变换**：从抽象规约到代码实现、从极简原型到完整系统、从旧架构到新架构、从高层逻辑到原生机器码。传统编程与 Vibe Coding 之所以一扩就乱、一改就崩，根本原因在于**每一次变换都在丢失原有的组合结构与隐含契约**。

**范畴式编程先用有色端口接线（`cut`）钉死系统的组合骨架，再强制生命周期中的每一种变换都严格保持这套结构：**

<table>
  <tr>
    <td width="33%" valign="top">
      <h3>1. 实现与编译变换<br/><sub>保接线的函子</sub></h3>
      <p><strong>从“规约”变换到“代码与机器码”，外部组合关系不走样。</strong></p>
      <p>一步高层操作在实现时可以展开为底层一段复杂的多模块复合接线图，但<strong>函子</strong>强制变换前后的端口边界与部分复合严格守恒；拆分子包前必须先编译证明“局部合取蕴含整体”，分包变换绝不弱化设计。</p>
    </td>
    <td width="33%" valign="top">
      <h3>2. 纵向精化变换<br/><sub>保骨架的吹胀与投影</sub></h3>
      <p><strong>从“极简沙盘”变换到“完整系统”，粗粒度控制流不坍塌。</strong></p>
      <p>先忘却细节投影到几个点的有限蓝图（<code>T0</code>）跑通骨架，再用 <code>El</code> 把底下的<strong>单个值</strong>吹胀成带完整状态与规则的局部范畴（<code>T1</code>）。无论上层长出多少细节，向下投影回底蓝图时必须保持交换方块；若沙盘捷径破坏了可提升性，直接交 <code>: ⊥</code> 打回修正蓝图。</p>
    </td>
    <td width="33%" valign="top">
      <h3>3. 横向重构变换<br/><sub>两端对等的保结构搬运</sub></h3>
      <p><strong>从“旧架构”变换到“新架构”，依赖闭合与历史因果不断裂。</strong></p>
      <p>改代码不是覆盖文本，而是新旧系统间<strong>两端地位对等的保结构关系（多异函子）</strong>。无论一拆多、多合一还是增删模块，变换必须保持全图接线闭合——设计记忆顺着变换精准继承，未受波及的子树 <strong>0 次 AI 调用</strong>原封不动复用。</p>
    </td>
  </tr>
</table>

---

## 🔌 零成本无缝衔接：API 与现成 Agent 皆可即插即用

在 Lojita 的文件本体论架构下，记忆驻留在文件树上、权限收敛在类型系统里，智能层被彻底解耦为标准的无状态推理算子。因此，**无论接入裸大模型 API（直连协议接口后续补齐），还是直接挂载你手头现成的商用 Agent，都能零成本无缝衔接**：

- **零迁移成本，零合规风险**：许多大模型厂商将主力推理额度绑定在自家订阅制 Agent 客户端内；你既无需为跑形式化工程额外承担高昂的按量 API 账单，也无需冒着封号与违约风险逆向“破壳”——现有订阅即插即用。
- **自动剥离越权外壳**：接入外部 Agent 时，Lojita 自动关闭其多余的宿主 Shell、任意文件改写与自治多智能体派发权限，将其无缝收编进只读形式化预检沙箱（MCP：`check_agda`、`check_plan`）。
- **增信息、绝不增权限（0 假阳性）**：内核门禁寸步不让，错证明与隐藏公理 0 放行；当 AI 触碰保守静态窄口（假阴性）时，系统即时弹出结构化 **`DETOUR` 绕路证书**（精确给出期望 vs 实际 AST 见证与等价改写路径），引导 AI 在草稿箱内改几行代码丝滑绕过。

---

## 🌌 同一台机器：从超大型软件直通经典数学定理

为什么业务软件工程显得**“庞杂但平庸”**，而著名数学定理显得**“简洁但深奥”**？

因为业务软件一开始就把跨系统架构（IO、文件树、终端协议、Canvas 视图）摊在了明面上；而初等数学命题只给出了单一离散整数世界里的最终验收规约，**隐藏了通往答案所需的跨世界有色复范畴结构**！一旦找对范畴结构，开发工业级软件与证明菲尔兹奖级经典数学定理，在 Lojita 中运行的是**完全同一套保结构状态机**：

| 统一二维范畴状态机 | 超大型软件开发（例：Markdown 转换器） | 经典数学定理证明（例：Roth 三项等差数列定理） |
| :--- | :--- | :--- |
| **根世界强规约 $E$** | 端到端完整文档转换、安全属性与全系统世界耦合定律 | 离散整数算术 $(\mathbb{Z}, +)$ 上正密度子集必含三项等差数列 $x, x+d, x+2d$ |
| **底范畴弱沙盘 $T_0$** | 忘却具体字符串正文，投影为有限块标签枚举跑通分包骨架 | 退化到特征 $3$ 有限域 $\mathbb{F}_3^n$（Meshulam 沙盘，子空间零边缘泄漏，小维数毫秒穷举） |
| **单点吹胀为范畴（`El`）** | 标题单点标签吹胀为带 `1..6` 级深度与降级约束的小范畴；单步粗函数拆为解析与渲染串联 | 精确线性子空间单点 $H$（在 $\mathbb{Z}$ 中无有限子群对应）吹胀为带半径尺度参数的 **Bohr 集小范畴** |
| **`: ⊥` 反驳驱动重构与零轮次复用** | $T_0$ 单遍流式扫描丢弃尾注引用导致上层导出 `: ⊥` $\to$ 打回重构两遍扫描 $T_0'$，**0 轮 AI 调用直接复用转义子包 `Escape₁`** | $T_0$ 偷用子空间全局平移不变性导致整数层导出 `: ⊥` $\to$ 打回重构“宽母盒 + 窄子盒”双尺度蓝图 $T_0'$，**0 轮直接复用 Parseval 傅里叶能量旁支** |

---

## ⚙️ Agda + Lean 4 双核引擎与全栈能力

- **Agda 承接开放前沿，Lean 4 承载工业算力**：全仓以 `.agda` 为唯一权威源码，用 Agda 表达余归纳会话编排与开放范畴结构；通过声明级**安全推出粘合（$\mathrm{SweetMod} \sqcup_{M_0} \mathrm{ExoMod}$）**与保求值色编译，将成熟纯函数及自身 23 个核心调度模块透明转译为 **Lean 4 C++ 内核校验与 `gcc -O3` 静态原生二进制**，严格拦截 `Classical.choice`、`propext`、`sorryAx` 等一切公理走私。
- **外部世界的纯粹数学提炼（脑手分离）**：
  - **交互式 Web Canvas（`WebOperad`）**：业务侧 **0 手写 JS**——用有色平面 Operad 建模双向布局、用精确有理仿射变换群取代浮点误差，机器证明**“画家算法可见像素归属 $\equiv$ 逆变换点击命中路由”**，彻底根绝热区错位与模态弹窗点击穿透；
  - **操作系统世界耦合（`Context.World`）**：终端逻辑时钟（`pty`）、文件系统（`fsbox`）、回环网络（`netbox`）与 Git 沙箱组成正交乘积世界 `SimWorld`（单步跨能力互不干扰 Frame Law 直接化简为 `refl`），全系统仅经**唯一 8 行受审计薄解释器 `WorldRunner`** 静态链接落地，并在洁净室容器中完成字节级真实回放。

---

## 🚀 Quick Start

> 完整的 Linux 环境要求、`./build.sh` 全栈编译、AI 后端配置（`Code/AI.agda`）、CLI 子命令与 v7 离线回归门禁请参阅：**[构建与使用指南 (docs/QUICKSTART.md)](./docs/QUICKSTART.md)**。  
> *一键体验脚本与交互式 `WebOperad` 离线画布演示正在持续整理完善中。*

---

## 📚 深度入坑：阅读完整白皮书与专题规范

如果你希望深入理解 Lojita System 背后的线性逻辑文件树、有色复范畴函子/异函子方程、Cruttwell–Shulman 虚装备免商集机制、多模态类型论（Monadic vs Comonadic）跨语言边界以及双核保守性证明，请直接进入完整架构宣言：

👉 **[阅读《Lojita System 架构宣言与理论白皮书》(docs/MANIFESTO.md)](./docs/MANIFESTO.md)**

**专题技术文档导览：**
- [范畴式编程与机器数学的统一理论纲要](./docs/THEORY_UNIFIED.md) · [类型化拼接范畴与保类型函子](./docs/TYPED_COLLAGE_FUNCTORS.md) · [范畴式找点、复函子数据库与 Roth 定理推演](./docs/CATEGORICAL_POINT_FINDING.md)
- [Ownership.agda：线性逻辑类型化 Shell（`文件 = 资源 ⊗ !数据`）](./docs/OWNERSHIP.md)
- [Lean 4 Prism 双核推出切片、求值着色与原生自举架构](./docs/LEAN4_PRISM_BACKEND.md)
- [二维多对多函子化提升、`: ⊥` 反驳门禁与无辜子树零轮次复用规范](./docs/V7_2D_LIFT_RECOVERY.md)
- [WebOperad 有色算子代数画布工作台](./docs/WEB_OPERAD.md) · [参数化外部工具对拍](./docs/EXT_TOOLS.md) · [终端逻辑时钟语义](./docs/TERMINAL.md) · [开放世界会话协议](./docs/SESSIONS.md)

---

## License

本项目采用 [Apache License 2.0](./LICENSE) 开源协议。
