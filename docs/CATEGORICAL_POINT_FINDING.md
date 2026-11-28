# 从 `[C, D]` 到 `[1, C]` / `[2, C]`：范畴式找点、Lean 4 实测证明与双向数据库构想

本报告汇总本次会话的核心推演脉络，并将讨论涉及的 **6 个代表性找点定理**全部落地为通过 **Lean 4.36.0** 内核零 `sorry` 实测校验的源码（见 [CategoricalPointFinding.lean](./examples/CategoricalPointFinding.lean)），最后探讨 **Lean 4 $\leftrightarrow$ 范畴式证明的双向转化**与**范畴式数学数据库**设计。

---

## 一、核心理论底座：`[1, C]` 范式反转与超穷不动点标尺

### 1.1 用 `[1, C]` 与 `[2, C]` 统摄一般范畴找点

最初从软件工程进入数学证明时，直觉容易默认“命题是规约 $Q$，证明是写函子 $F : \mathcal{C} \to \mathcal{D}$”。遇到形如 $\exists x.\, Q(x)$ 或 $\exists x \forall y.\, Q(x,y)$ 的“找孤点”命题时，表面上似乎失去了输入端 $\mathcal{C}$ 的结构扶手。

破局的关键在于**反转伴随同构 $\mathrm{Hom}(\mathbf{1}, [C, D]) \cong \mathrm{Hom}(C, D)$ 的阅读方向**：
- **错误方向**：把函子范畴 `[C, D]` 退化理解为散点集 $D^C$（拆毁结构）；
- **正确方向**：反过来**把一般空间 `C` 中的找点看作函子空间 `[1, C]`（或耦合点对 `[2, C]`、有色复范畴 `[1_poly, E]`）中的找点**（注入函子动力学，见 [`UnitGoalPoly` 与 `evalPointFunctor`](./examples/CategoricalPointFinding.lean#L57-L91)）！

> [!IMPORTANT]
> **为什么 `1 -> C` 绝不是文字游戏？**
> 1. **Dialectica 内部长出函数网**：外层边界虽是零输入 `1 -> C`，但放在大宇宙 $\mathcal{U}$ 中切开后，内部子块照样是非贯通、非横截的真函数 `A -> B`、`(A, B) -> C` 与极小种子 `1 -> A`。
> 2. **源端蓝图提升 = 挖掘数学理论**：对 `1 -> C` 或 `2 -> C` 的**源端 `1`、`2`** 做蓝图吹胀，孤立找点题会自动升格为参数化归纳族 $\mathcal{A} \to C$ 或双侧对偶拼接范畴 $\mathcal{E}_0 \oplus_P \mathcal{E}_1 \to C$（顺手挖出递推律、戴德金分割或原始-对偶理论）。
> 3. **多出口复范畴 `m -> n` = 经典排中律的几何真身**：直觉主义找点限制在多范畴（`m -> 1`）；经典排中律找点则对应复范畴（允许 `2 -> 2` 右端分岔 + 右缩并合流）。

### 1.2 沿靶范畴内部箭头找点：从幂等不动点 $f^{n+1} = f^n$ 到超穷序数 `colim` / `lim`

许多深奥证明并非一步猜中目标点，而是**顺着范畴内部的演化箭头一步步走到目标点**。只要约定“抵达目标态后原地保持不动（吸收态）”，整个搜索动力学就与**自映射/自函子的不动点理论（Adámek 超穷构造）**严格合一：

1. **有限步必停机递归（序数 $< \omega$）$\Longleftrightarrow$ 幂等稳定化 $f^{n+1} = f^n$**：
   设单步演化为 $f : A \to A$，满足规约的目标点即不动点 $\mathrm{Fix}(f) = \{x \mid f(x) = x\}$。存在有界停机燃料 $n$ 在代数上字面等价于第 $n$ 步已卡进不动点：
   $$f^{n+1}(x_0) = f^n(x_0)$$
   若 $n$ 对全空间一致有界，则高次幂 $E := f^n$ 成为**幂等算子（$E \circ E = E$）**，相当于做了一次 Karoubi 幂等分裂，把任意粗糙初值一把投影到不动点子空间 $\mathrm{Fix}(f)$ 上！
2. **超穷序数收敛（序数 $\ge \omega$）$\Longleftrightarrow$ 后继步跑函子，极限步求 `colim` / `lim`**：
   当任意有限步都停不下来（$F^{n+1} \neq F^n$）时，全体序数 $(\mathbf{Ord}, \le)$ 本身就是一个偏序小范畴（$0 \to 1 \to \dots \to \omega \to \omega+1 \to \dots$），超穷归纳就是构造链函子 $X_\bullet : \mathbf{Ord} \to \mathcal{C}$：
   - **后继序数 $\alpha + 1$**：走一步单步函子 $X_{\alpha+1} := F(X_\alpha)$；
   - **极限序数 $\lambda$（一次超穷跨越）**：协变生长（从初始对象 `0` 搭自由闭包 / 最小不动点 $\mu F$）时求一次**余极限 `colim`**（$X_\lambda := \mathrm{colim}_{\beta < \lambda} X_\beta$）；逆变提纯（从终对象 `1` 筛完备空间 / 最大不动点 $\nu F$）时求一次**极限 `lim`**（$X_\lambda := \mathrm{lim}_{\beta < \lambda} X_\beta$）。
   - 若 $F$ 保 $\omega$-极限/余极限，做 **1 次 `colim`/`lim`** 即满足 $F(X_\omega) \cong X_\omega$ 停机；若不保，则穿过 $\omega$ 继续走 $\omega+1, \dots, \omega\cdot 2$ 反复交替“函子步进 + 极限收敛”，直到某个正则基数 $\kappa$ 处满足 $F(X_\kappa) \cong X_\kappa$。**不同数学公理系统对“什么叫找到点”的证明论序数强弱，本质上就是允许交替跑多少轮“函子迭代 + `colim/lim` 过极限”！**

---

## 二、六个代表性定理：Lean 4 签名与范畴式编程证明对照

### 定理 1：反例博弈与幂等不动点稳定化 —— `f : Nat → Nat` 全局最小值点
*(源码见 [CategoricalPointFinding.lean](./examples/CategoricalPointFinding.lean#L93-L190))*

面对无穷黑盒 `f : Nat → Nat`，构造性算法无法一步算出全局最小值点 `x`；但经 **Gödel–Shoenfield / 无反例解释**，问题转化为吃进反例预言机 `adv : Nat → Nat` 的单步吸收算子 `stepMin(x) := if f x ≤ f (adv x) then x else adv x`。此时：
- **获胜点就是不动点**：`f x ≤ f (adv x)` 当且仅当 `stepMin x = x`；
- **良基燃料就是幂等稳定阶 $f^{n+1} = f^n$**：自然数下界 `0` 保证初值燃料 $n = f(0)$ 步内必撞入不动点，满足 `stepMin^(n+1)(0) = stepMin^n(0)`（若换成 `f : Nat → Int`，$f(x) = -x$ 无下界导致对一切有限 $n$ 都有 $\mathrm{step}^{n+1}(0) \neq \mathrm{step}^n(0)$，编译期直接拦截）。

```lean
-- 【标准经典 Lean 4 签名】（依赖 Classical.choice）
theorem thm1_classical_min (f : Nat → Nat) : ∃ x : Nat, ∀ y : Nat, f x ≤ f y

-- 【吸收单步算子与幂等不动点稳定化 step^(n+1)(0) = step^n(0)】（零经典公理！）
def stepMin (f adv : Nat → Nat) (x : Nat) : Nat :=
  if f x ≤ f (adv x) then x else adv x

theorem thm1_stepMin_stabilizes (f adv : Nat → Nat) :
    iterStep (stepMin f adv) (f 0 + 1) 0 = iterStep (stepMin f adv) (f 0) 0

theorem thm1_shoenfield_min (f : Nat → Nat) (adv : Nat → Nat) :
    ∃ x : Nat, f x ≤ f (adv x)
```

---

### 定理 2：蓝图提升塔 + `: ⊥` 反驳回流 —— 模同余寻点 $x^2 \equiv 41 \pmod{64}$
*(源码见 [CategoricalPointFinding.lean](./examples/CategoricalPointFinding.lean#L192-L239))*

沿着商投影塔 $\mathbb{Z}/64 \to \mathbb{Z}/32 \to \mathbb{Z}/16 \to \mathbb{Z}/8 \to \mathbb{Z}/4 \to \mathbb{Z}/2$ 由粗到精每次只展开 2 个点的纤维 `[x₀, x₀ + m]`。低阶沙盘偷懒选出的 `x₀ ≡ 1 (mod 8)` 在升到模 16 时整条纤维 `{1, 9}` 全军覆没，触发闭合 `: ⊥` 反驳，打回模 8 切到兄弟分支 `3` 并最终锁定 `19`。

```lean
-- 【Lean 4 签名】
theorem thm2_hensel_sqrt41_mod64 : ∃ x : Fin 64, (x.val * x.val) % 64 = 41

-- 【范畴式蓝图下降保真 + 闭合 `: ⊥` 提升阻塞 + 纤维递进】
theorem proj_quadMod_sound {m x : Nat} (hm : 0 < m) (h : QuadModSpec (2 * m) x) :
    QuadModSpec m (x % m)

-- 模 8 特解 `1` 在模 16 触发 `refute-lift (: ⊥)`：
theorem refute_lift_mod8_one : ¬ ∃ x : Nat, QuadModSpec 16 x ∧ x % 8 = 1

def henselFiberStep (m : Nat) (cands : List Nat) : List Nat :=
  (cands.flatMap fun x₀ => [x₀, x₀ + m]).filter fun x =>
    decide ((x * x) % (2 * m) = 41 % (2 * m))
```

---

### 定理 3：`1 -> ℕ⁺` 非贯通、非横截异构 DAG 分包 —— 找大于 1000 的完全数 `8128`
*(源码见 [CategoricalPointFinding.lean](./examples/CategoricalPointFinding.lean#L241-L503))*

虽然顶层签名 `1 -> ℕ⁺` 是纯找点，但拆开大盒子后形成一张异构有向无环图（种子 `a : 1 -> ℕ⁺` 一路跨层直连二元函数 `mul`，另一路经一元函数 `f(x) = 2x - 1` 进 `mul`）。父节点**先只写接口规约并完成粘合证明 `perfect_dag_glue`**；当窄上限 `a ≤ 50` 触发 `: ⊥` 反驳时，放宽种子范围**零修改直接复用两个函数子包 `implF_spec` 与 `implMul_spec`**。

```mermaid
flowchart TD
  Unit["1 (零输入边界)"] --> SeedA["子包 A: a : 1 -> Nat (σ(a) = 2a - 1 且 2a - 1 为素数)"]
  SeedA -->|"左路跨层直连"| Mul["子包 M: mul : (Nat, Nat) -> Nat (互素乘积因数和定律)"]
  SeedA --> FuncF["子包 F: f : Nat -> Nat (f(x) = 2x - 1, 证 gcd(x, f(x)) = 1)"]
  FuncF -->|"右路加工"| Mul
  Mul --> OutN["目标点 N = 8128 : Nat"]
```

```lean
-- 【Lean 4 签名】
theorem thm3_perfect_gt_1000 : ∃ N : Nat, N > 1000 ∧ divisorSum N = 2 * N

-- 【范畴式先验粘合门禁（在填任何具体数字或实现前先行证毕！）】
theorem perfect_dag_glue {bound a : Nat} {f : Nat → Nat} {mul : Nat → Nat → Nat}
    (hA : SpecSeedA bound a) (hF : SpecFuncF f) (hM : SpecCombMul mul) :
    mul a (f a) > 1000 ∧ divisorSum (mul a (f a)) = 2 * mul a (f a)

-- 窄上限 `a ≤ 50` 导出闭合 `: ⊥` 证书；放宽至 `100` 后零重算复用 `implF_spec`, `implMul_spec`：
theorem refute_seed_bound_50 : ¬ ∃ a : Nat, SpecSeedA 50 a
theorem thm3_perfect_gt_1000 :=
  ⟨implMul 64 (implF 64), perfect_dag_glue implSeedA_64 implF_spec implMul_spec⟩
```

---

### 定理 4：`1 -> Graph -> Graph` 拆出升阶函数子包 —— 无三角形非 3-可染图（Grötzsch 图）
*(源码见 [CategoricalPointFinding.lean](./examples/CategoricalPointFinding.lean#L505-L746))*

在 $2^{55}$ 张 11 阶图里盲搜无三角形 4 色图近乎绝望。通过把 `1 -> Graph` 拆成 `1 --S--> Graph --M--> Graph`，硬生生从纯组合找点题里切出了一个纯函数开发包 `mycielski : SimpleGraph n → SimpleGraph (2n + 1)`；不仅拼出 11 点 Grötzsch 图，把源端 `1` 吹胀成 `(ℕ, succ)` 后还顺手零公理挖出了**任意高色数无三角形图定理**。

```lean
-- 【Lean 4 签名】
theorem thm4_grotzsch_triangleFree_not_3colorable :
    ∃ (n : Nat) (G : SimpleGraph n), TriangleFree G ∧ ¬ Colorable 3 G

-- 【先验粘合门禁 + 源端 `1` 吹胀为 `ℕ` 挖出的任意色数族定理】
theorem mycielski_dialectica_glue {n₀ : Nat} (S : SimpleGraph n₀)
    (MSize : Nat → Nat) (M : {n : Nat} → SimpleGraph n → SimpleGraph (MSize n))
    (hS : TriangleFree S ∧ ¬ Colorable 2 S)
    (hM_tf  : ∀ {n} (H : SimpleGraph n), TriangleFree H → TriangleFree (M H))
    (hM_chr : ∀ {n k} (H : SimpleGraph n), ¬ Colorable k H → ¬ Colorable (k + 1) (M H)) :
    TriangleFree (M S) ∧ ¬ Colorable 3 (M S)

theorem thm4_arbitrary_chromatic_triangleFree (k : Nat) :
    ∃ (n : Nat) (G : SimpleGraph n), TriangleFree G ∧ ¬ Colorable k G
```

---

### 定理 5：`2 -> ℚ⁺` 双侧对偶拼接范畴提升 —— 纯正有理数夹逼 $\sqrt{2}$ 到 $10^{-5}$
*(源码见 [CategoricalPointFinding.lean](./examples/CategoricalPointFinding.lean#L748-L803))*

在完全不引入实数 $\mathbb{R}$ 的正有理分数范畴 `PosRat` 中，单点无法自证逼近误差界；改用 `2 -> ℚ⁺` 找上下界配对 `(l, u)`，并将行走序对 `{0 -> 1}` 吹胀为左协变递增链 $\mathcal{E}_0$（调和均值反射）与右逆变递减链 $\mathcal{E}_1$（算术均值收缩）的 Collage 拼接范畴，从 `(1, 2)` 迭代 3 步即得 `(816/577, 577/408)`（顺手挖出戴德金分割函子）。

```lean
-- 【Lean 4 签名（纯正整数分子分母 PosRat，零实数公理）】
theorem thm5_dedekind_sqrt2_clamp :
    ∃ p : PosRat × PosRat, SqLtTwo p.1 ∧ TwoLtSq p.2 ∧ GapLtInv p.1 p.2 100000

-- 【双侧对偶演化步算子：3 步二次收敛至误差 1/235416 < 10⁻⁵】
def clampStep (p : PosRat × PosRat) : PosRat × PosRat -- (l, u) ↦ (2lu/(l+u), (l+u)/2)
def step3Pair : PosRat × PosRat := clampStep (clampStep (clampStep initPair))
```

---

### 定理 6：`2 -> 2` 经典复范畴切消 + 蓝图下降复函子 —— 无理数幂 $a^b \in \mathbb{Q}$
*(源码见 [CategoricalPointFinding.lean](./examples/CategoricalPointFinding.lean#L805-L991))*

底复范畴 `CoarsePolyB` 含 `{I, Q, W}` 三色；提升复范畴 `RefinedPolyE` 按实数项索引锁死坐标，配备纵向下降复函子 `piBlueprint : PolyFunctor RefinedPolyE CoarsePolyB`。利用 `2 -> 2` 分岔箭头 `genDelta`、三元叠幂 `3 -> 1` 坍缩箭头 `genTau` 经三次严格单线 `cut` 与一次右缩并合流，构造出严格点函子 `irrPowPointFunctor : PolyFunctor UnitGoalPoly RefinedPolyE`，一行 `evalPointFunctor` 机械还原出标准 Lean 4 证明。

```mermaid
flowchart LR
  Eta["genEta (0 -> 1): [] -> [Irr √2]"] --> Delta["genDelta (2 -> 2): [Irr √2, Irr √2] -> [Irr c, Rat c]"]
  Delta -->|"右出口 Rat c (2 -> 1 直通)"| Pack1["genPack (√2, √2)"]
  Delta -->|"左出口 Irr c (单线 cut)"| Pack2["genPack (c, √2)"]
  Tau["genTau (3 -> 1): [Irr √2 × 3] -> [Rat c^√2]"] --> Pack2
  Pack1 --> Merge["右缩并合流 [Win, Win] -> [Win]"]
  Pack2 --> Merge
```

```lean
-- 【Lean 4 签名】
theorem thm6_irrational_pow_rational (M : RealPowModel) :
    ∃ a b : M.R, M.Irr a ∧ M.Irr b ∧ M.Rat (M.pow a b)

-- 【纵向蓝图下降复函子 & 横向点复函子】
def piBlueprint (M : RealPowModel) : PolyFunctor (RefinedPolyE M) CoarsePolyB
def irrPowPointFunctor (M : RealPowModel) : PolyFunctor UnitGoalPoly (RefinedPolyE M)

-- 机械求值一键对接 Lean 4 签名：
have hArrow := (evalPointFunctor (irrPowPointFunctor M)).down trivial
```

---

## 三、Lean 4 签名/证明 $\leftrightarrow$ 范畴式证明的双向转换

### 1. 正向转换：范畴式证明 $\longrightarrow$ Lean 4 签名与证明项（100% 机械编译）

正向之所以完全机械、零启发式，是因为 **Lean 4 的类型论内核本身就是有色复范畴与虚装备的一个语义目标代数（Target Semantic Algebra）**。转换器只是在执行多对一的遗忘求值函子 `eval`：

| 范畴式构件 | 机械编译出的 Lean 4 目标代码 |
| :--- | :--- |
| **数据颜色 `c` / 精化颜色 `P(x)`** | 子类型 `{x : T // Inv x}` 或命题类型 `: Prop` |
| **直觉主义多箭头 `[c₁..cₘ] ⟶ [d]`** | 多参函数 / 蕴含链 `⟦c₁⟧ → ... → ⟦cₘ⟧ → ⟦d⟧` |
| **经典析取复箭头 `[c₁..cₘ] ⟶ [d₁..dₙ]`** | `⟦c₁⟧ ∧ ... ∧ ⟦cₘ⟧ → ⟦d₁⟧ ∨ ... ∨ ⟦dₙ⟧`（如定理 6 的 `RefinedPolyE`） |
| **同时输出复箭头 `[c₁..cₘ] ⟶ [d₁..dₙ]`** | 存在 / Sigma 元组 `⟦c₁⟧ → ... → ∃ y₁ ... yₙ, ...`（如定理 5 的 `PosRat × PosRat`） |
| **单端口 `cut` + Dialectica 先验粘合** | `let` 局部绑定、`Or.elim` 分支消去及参数化粘合定理 `parent_glue` |
| **蓝图投影塔 $\mathcal{E} \xrightarrow{\pi} \mathcal{B}$** | 粗沙盘 $\mathcal{B}$ 编译期零开销擦除（或留作静态断言），仅将顶层 `evalPointFunctor F` 交给内核校验 |

> [!TIP]
> **防作弊闭环是机械转换的一部分**：正向编译时，固定求值器 `evalPointFunctor` 直接从函子产出目标 `: P`（禁止手写旁路 `sound` 函数偷换证明），并配合静态 `cutCount ≥ 1` 审计与 `#print axioms` 公理指纹提取，确保范畴结构真实参与了推理。

---

### 2. 反向转换：Lean 4 签名 / 现成证明 $\leadsto$ 范畴式证明（为何是一对多？）

反向之所以**天然是一对多（甚至无穷对多）**，是因为 Lean 4 签名只规定了最外层黑盒的**边界端口**（如 `[] ⟶ [Win]`），却抹平了所有**内部切颜色（中间概念）**与**纵向沙盘层级**：

1. **只有 Lean 4 签名时（正向探索的一题多解）**：
   - 同一个 `∃ a b, Irr a ∧ Irr b ∧ Rat (a^b)`，在允许经典 `2 -> 2` 复范畴时走 $\sqrt{2}^{\sqrt{2}}$ 分岔（零超越数论前置）；若限制在直觉主义 `m -> 1` 多范畴，则必须切换为 Gelfond–Schneider 定理构造 $(\sqrt{2}, 2\log_2 3)$。
   - 同一个同余寻点，既可走纵向 Hensel $2$-进提升塔（定理 2），也可走横向中国剩余定理正交基粘合。
2. **已有 Mathlib 扁平战术证明（`by rw ...; cases ...`）时（逆向反编译 / Proof Mining）**：
   虽然源码里的 tactic 脚本是一维按键流水账，但编译成 Lean 4 内核 `Expr`（纯 $\lambda$-项）后，可以按语法特征做**半自动范畴反编译（Decompilation）**：
   - **局部 `let` / 引理应用 DAG** $\leadsto$ 还原为 Dialectica / 复范畴的单端口 `cut` 接线图，中间引理类型自动成为**切颜色**；
   - **`Or.elim` / `Classical.byCases`** $\leadsto$ 识别为 `1 -> 2` 或 `2 -> 2` 分岔复箭头 + 右缩并合流；
   - **`Nat.rec` / `WellFounded.fix`** $\leadsto$ 识别为源端 `1` 吹胀出的归纳链函子或带良基燃料的 CEGIS 状态机（定理 1、定理 4B）；
   - **沿商同态（如 `Nat.cast : ℕ → ZMod m`）导出 `False`** $\leadsto$ 识别为向粗蓝图 `T₀` 的下降函子投影与 `: ⊥` 提升阻塞（定理 2）。

---

## 四、Grothendieck 式范畴与函子数据库：确定性规范化与三级检索漏斗

传统定理库（如 Mathlib）按表层概念或类型名字建索引，存在两个根本错位：
1. **同词不同范畴**：同样写着 `Nat`，在归纳题里是皮亚诺自由一元范畴 `(0, succ)`，在完全数（定理 3）里是互素乘性整除范畴 `(ℕ⁺, ×, ∣)`，在同余寻点（定理 2）里是 $2$-进射影环塔——表层类型相同，底下的范畴与解题函子毫无关系。
2. **异词同一范畴**：实数幂分岔 $\sqrt{2}^{\sqrt{2}}$（定理 6）与图染色分岔 `[红, 红] -> [红, 蓝]`、`[红, 红, 红] -> [蓝]` 字面词汇零交集，底下的复范畴与切消函子却严格同构。

因此，数据库的**一等公民必须是去名化的“范畴（理论草图）”与“函子”本身**；而**检索的定义不是点对点判等 $\mathcal{T} \cong \mathcal{C}$，更不是模糊 RAG，而是确定性求解“是否存在保结构复函子 $F : \mathcal{T}_{\text{库}} \to \overline{\mathcal{C}}_{\text{当前}}$”**！

### 1. 为什么“找函子”天然克服了“点对点检索”的三大死穴？

- **死穴 A（同构冗余点与张量包装差异）$\implies$ 入库前 Morita / 原子色规范化**：
  合并同构点取骨架（Skeleton），并将一切可由张量积、积、余积表出的复合对象沿泛性质拆回**不可约原子色多端口列表** `[c₁, …, cₖ]`（正如正整数乘法范畴规范化为纯质数导线对称复范畴 $\mathbf{Sym}(\mathbb{P})$）。
- **死穴 B（对象个数不同：特例折叠与无关旁支）$\implies$ 草图同态代替双射**：
  受数据库 **Chandra–Merlin 定理**启发，查询本身是一张抽象小草图 $\mathcal{T}$。函子 $F : \mathcal{T} \to \mathcal{C}$ 允许**非单射**（$\mathcal{T}$ 的不同角色色折叠到 $\mathcal{C}$ 的同一点，自动命中自对偶特例）与**非满射**（自动忽略 $\mathcal{C}$ 中几十个无关旁支对象）。
- **死穴 C（生成元粒度不同：1 步原语 vs 3 步复合）$\implies$ 向切闭包 $\overline{\mathcal{C}}$ 找函子**：
  从自由展示草图 $\mathcal{T}$ 到 $\overline{\mathcal{C}}$ 的复函子，天然允许把 $\mathcal{T}$ 的单条生成箭头映为 $\mathcal{C}$ 中任意有界深度的 `cut` 复合树，彻底抹平原语选法差异。

### 2. 零模糊、零假阴性的“三级确定性检索漏斗”与库表结构

```mermaid
flowchart LR
  Cur["当前问题局部范畴 C"] --> L1["第 1 级: 内在公理概念格 FCA (位掩码偏序 Props(T) ⊆ Props(C))"]
  L1 --> L2["第 2 级: 米田试金石探针谱 + E-Graph 等式饱和 (范畴等价不变量剪枝)"]
  L2 --> L3["第 3 级: 有界深度复函子合一器 (精确算出桥接函子 F : T -> C̅)"]
  L3 --> Out["检索即证明: 复合库内点函子 F ∘ P : 1_poly -> C̅"]
```

1. **第 1 级（毫秒级位运算过滤 · 0 假阴性）：内在范畴公理格（FCA Concept Lattice）**
   只索引严格范畴等价不变的布尔属性：左右端口结构律（纯线性 / 交换 / 笛卡尔 / 经典右缩并）、薄度（偏序 / 群胚 / 真范畴）、泛性质完备谱（初始终零对象、积与余积分配律、对偶自反性、到 $(\mathbb{N}, >)$ 的良基减度量）。仅保留满足 $\mathrm{Props}(\mathcal{T}) \subseteq \mathrm{Props}(\mathcal{C})$ 的库理论 $\mathcal{T}$。
2. **第 2 级（代数不变量剪枝）：米田小探针谱（Yoneda Probe Profile）+ E-Graph 规范化**
   对交换图方程跑有界步 **E-graph 等式饱和**消除写法差异，再用一族固定极小试金石范畴 $\{\mathcal{K}_1, \dots, \mathcal{K}_m\}$（行走幂等元、`2 -> 2` 分岔元、伴随对等）探测 $\mathrm{Hom}(\mathcal{K}_i, -)$ 存在谱。凡违反函子单调保持律的候选直接淘汰。
3. **第 3 级（精确锁定并吐出编译器）：有界深度复函子合一（Polyfunctor Unification）**
   用确定性约束求解器算出颜色映射 `mapColor` 与生成元接线树 `mapGen`。**检索器的返回值本身就是验证完毕的函子 $F : \mathcal{T} \to \overline{\mathcal{C}}$——直接与库中已有的解题函子复合，检索命中的瞬间证明已自动过半！**

据此，数据库核心关系不再绑死具体类型名，而是围绕**范畴理论节点、函子超边、`: ⊥` 提升阻塞与双模搬运桥**组织：

```mermaid
erDiagram
  THEORY_CATS ||--o{ FUNCTOR_EDGES : "作为源/靶范畴"
  THEORY_CATS ||--o{ LIFT_OBSTRUCTIONS : "暴露提升死路"
  LIFT_OBSTRUCTIONS ||--o| BIMODULE_TRANSPORTS : "触发范畴吹胀 T0 ~> T0'"
  THEORY_CATS ||--o{ LEAN4_ANCHORS : "多对多语义落点"

  THEORY_CATS {
    hash cat_id PK "Morita原子色 + E-Graph规范化指纹"
    bitmask fca_props "内在结构律与泛性质布尔格掩码"
    vector yoneda_spec "小试金石范畴 Hom 探针谱"
    sketch presentation "抽象颜色、生成复箭头与交换图"
  }
  FUNCTOR_EDGES {
    hash functor_id PK "已校验的复函子 / Dialectica粘合超边"
    string role "PointProof_1toT | Subcontract_DAG | Projection_EtoB"
    hash dom_cat_id FK "源范畴 (含 1_poly / 2_walk)"
    hash cod_cat_id FK "靶范畴切闭包"
    olean kernel_cert "Lean4 内核校验二进制证书"
  }
  LIFT_OBSTRUCTIONS {
    hash obs_id PK "闭合 :⊥ 反驳证书 (c0 ∉ Im(p))"
    hash coarse_cat_id FK "底沙盘范畴 B"
    hash fine_cat_id FK "目标精细范畴 E"
    list culprit_gens "静态揪出的闯祸生成箭头"
  }
  BIMODULE_TRANSPORTS {
    hash trans_id PK "横向多异函子重构桥 T0 ~> T0'"
    hash from_cat_id FK "受阻旧范畴 (如单尺度盒)"
    hash to_cat_id FK "吹胀后新范畴 (如 2->C 双尺度盒)"
    list invariant_subtrees "0次重算直接继承的正交子函子"
  }
  LEAN4_ANCHORS {
    hash anchor_id PK "具体数学类型/定理锚点"
    hash cat_id FK "所挂载的底层范畴结构"
    expr eval_bridge "向标准 Lean4 签名的机械求值投影"
  }
```

---

## 五、压轴全流程模拟：用范畴式编程与函子数据库证明 Roth 定理

作为全篇讨论的总汇演，我们模拟系统如何面对加性组合经典难题——**Roth 三项等差数列定理**，不靠人类灵光一现盲搜不等式，而是靠 **外层函子范畴 `[C, D]` 找点 + 吸收态幂等不动点 $T^{N_0+1} = T^{N_0}$ + 范畴数据库确定性检索 + 内层环境从 `1` 吹胀到 `2` 的 `: ⊥` 反驳重构** 一步步生长出完整证明（核心机器骨架、幂等稳定化与 `: ⊥` 阻塞均已在 [CategoricalPointFinding.lean 第 7 节](./examples/CategoricalPointFinding.lean#L993-L1133) 通过 Lean 4.36 零 `sorry` 验证）。

### 第 0 步：问题建模 —— 外层是标准的函子范畴 `[C_Stage, D_AP3]` 找点

- **目标 Lean 4 签名语义**（典型的 $\forall \dots \exists \dots$ 全称存在命题）：
  $$\forall \delta_0 > 0,\; \exists N_0,\; \forall N \ge N_0,\; \forall A \subseteq \{1, \dots, N\}\; (|A| \ge \delta_0 N),\; \exists x, d \in \mathbb{N}^+,\; \{x,\, x + d,\, x + 2d\} \subseteq A$$
- **范畴定位**：因为外层带着全称量词 $\forall (N, A)$（在机器骨架中即 `∀ s₀ : A.Stage, A.Has3AP s₀`），**这首先是一个货真价实的函子范畴 $[\mathcal{C}_{\mathrm{Stage}}, \mathcal{D}_{\mathrm{AP3}}]$ 找点问题**！
  - 如果把输入 $(N, A)$ 当成毫无关联的散点集，对每个固定 $A$ 暴力搜 $(x, d)$ 是孤立黑盒；
  - 一旦把源端看作**状态范畴 $\mathcal{C}_{\mathrm{Stage}}$**：点是正密度子集构型 $s = (B, A)$，**箭头 $s' \hookrightarrow s$ 是保三项等差结构的仿射子结构嵌入（Zoom-in 态射）**，靶范畴 $\mathcal{D}_{\mathrm{AP3}}$ 沿嵌入箭头逆变拉回三项等差见证（`Has3AP s' → Has3AP s`）——密度递增法才有了跨尺度递归演化的轨道！

---

### 第 1 步：纵向退化探路 —— 沿公理格进入有限域沙盘 $\mathcal{C}_{\mathbb{F}_3}$（`T₀`）

在根世界离散整数 $(\mathbb{Z}, +)$ 中，“加法进位”与“有限区间边缘泄漏”纠缠在一起。系统先向范畴数据库发起**纵向投影查询**，附加简化公理 `x + x + x = 0` 消去挠率与边界，进入特征 3 有限域向量空间沙盘 $\mathbb{F}_3^n$（Meshulam 模型）：
- 在 $\mathbb{F}_3^n$ 中，三项等差条件 $x, x+d, x+2d$ 对称化为纯净的线性方程 $x + y + z = 0$；
- 局部环境对象简化为单个颜色 `Subspace H`，自带完美的加法自封闭多箭头 `closedAdd : [H, H] ⟶ [H]`（零边缘泄漏！）。

---

### 第 2 步：三级确定性范畴检索 —— 跨领域拼出“吸收态幂等不动点主引擎 $T^{N_0+1} = T^{N_0}$”

将当前沙盘状态范畴 $\mathcal{C}_{\mathbb{F}_3}$（对象是带正密度子集的环境框 `Stage`）送入**三级确定性检索漏斗**：

1. **FCA 公理格命中**：`Stage` 具备经典排中律 `m -> n` 分岔位，且子集密度 $\delta(s) \in (0, 1]$ 有严格天花板 `1`——每次密度固定跃升 $\Delta = c\delta_0^2$ 时，剩余空间 `densityGap(s) = ⌈(1 - δ(s)) / Δ⌉` 构成射向 $(\mathbb{N}, >)$ 的**良基燃料函子**！
2. **米田探针与复函子合一命中“二分分岔 + 吸收不动点稳定化”复合骨架**：
   - **命中骨架 #6（`1 -> 2` 二分排中分岔，同构于定理 6 的 `genDelta`）**：对任意 `Stage`，按傅里叶最大非平凡系数阈值劈出双出口复箭头 `[Stage] ⟶ [IsUniform, ¬IsUniform]`；
   - **命中骨架 #1（幂等不动点投影 $T^{n+1} = T^n$，同构于定理 1 的 `stepMin`）**：把状态空间扩充为吸收和类型 `RothState = active(s) ⊕ win`（在 `win` 上恒等，在伪随机 `s` 上跳入 `win`，在非一致 `s` 上跳入高密子盒 `s'`）。由密度天花板锁死步数 $n = \mathrm{densityGap}(s_0) + 1$，单步自映射 `T = rothStepEndo` 严格满足幂等稳定化（见 [`rothStepEndo_stabilizes`](./examples/CategoricalPointFinding.lean#L1080-L1133)）：
     $$T^{n+1}(s_0) = T^n(s_0) \in \mathrm{Fix}(T) = \mathrm{win}$$
     即高次幂 $T^n$ 直接作为 Karoubi 幂等投影算子，把任意初始构型一步投进获胜不动点！

检索器当场合成并编译通过**先验粘合主定理** [`roth_master_categorical_glue`](./examples/CategoricalPointFinding.lean#L1051-L1076)，将未知细节精准切分为两个隔离的 Dialectica 子包：
- **子包 1（`CountingModule`）**：`IsUniform s → Has3AP s`（伪随机分布下，三项等差计数逼近 $\delta^3 |H|^2 > 0$）；
- **子包 2（`CorrelationBumpModule`）**：`¬IsUniform s → Σ' s', densityGap s' < densityGap s ∧ (Has3AP s' → Has3AP s)`（大傅里叶系数经 Parseval 能量守恒与抽屉原理，在余维 1 子空间平移陪集上把密度推高 $c\delta^2$）。

在 $\mathbb{F}_3^n$ 沙盘 `T₀` 中，两个子包轻松填入闭合实现，蓝图全绿跑通！

---

### 第 3 步：向整数根世界提升 —— 撞上 4 行闭合 `: ⊥` 阻塞（`c₀ ∉ Im(p)`）

现在系统沿下降函子逆向把 `T₀` 提升回无挠整数世界 $(\mathbb{Z}, +)$（对应有界自然数区间 `{1..N}`）：
- 若生搬硬套 `T₀` 的单点概念 `Subspace H`，要求整数有界候选集 `H` 同样满足单尺度加法封闭箭头 `hClosed : ∀ x d, H x → H d → H (x + d)` 且含非零公差 $d_0 > 0$；
- 子节点无需任何高深分析，**4 行初等算术直接向父节点拍出闭合 `: ⊥` 反驳证书** [`refute_single_scale_closed_nat`](./examples/CategoricalPointFinding.lean#L1007-L1026)：把正步长 $d_0$ 自加 $(\mathrm{bound}+1)$ 次仍在 $H$ 内，却严格大于上界 $\mathrm{bound}$，矛盾！
- 系统静态扫描依赖图，精准定位闯祸原语：`hClosed : [H, H] ⟶ [H]`。同时发现：**旁边的 `CorrelationBumpModule`（Parseval $L^2$ 能量恒等式与大谱相关性提取）根本没有引用 `hClosed`！**

---

### 第 4 步：检索搬运桥 `T₀ ⇝ T₀'` —— 单点吹胀为 `2 -> C` 双尺度拼接范畴 + 零轮次复用

拿着 `refute_single_scale_closed_nat` 的阻塞特征查询数据库的 `LIFT_OBSTRUCTIONS -> BIMODULE_TRANSPORTS` 表，确定性命中经典重构桥（与**定理 5** 的 `2 -> C` 拼接范畴同源）：

```mermaid
flowchart TD
  T0["沙盘 T0: 单点颜色 Subspace H (偷用伪封闭箭头 [H, H] -> [H])"] -->|"整数层触发 refute_single_scale_closed_nat (: ⊥)"| Trans["横向双模搬运桥 T0 ~> T0'"]
  Trans -->|"用 El 将单点 H 吹胀为 2 = {Wide -> Narrow}"| T0Prime["新蓝图 T0': Bourgain 正则双尺度 Bohr 集对 (B(Ξ, ρ), B(Ξ, ερ))"]
  T0Prime --> CountNew["仅重做 CountingModule: 跨尺度多箭头 [Wide, Narrow] -> [WideOut] (x ∈ 宽盒, d ∈ 窄盒, 边缘泄漏 ≪ δ³)"]
  T0 -->|"0 次重算原样继承!"| BumpKeep["CorrelationBumpModule + 吸收态幂等引擎 T^(n+1) = T^n"]
  CountNew --> Final["整数根世界 Roth 定理完整闭合证明"]
  BumpKeep --> Final
```

1. **单点升范畴（`1` 吹胀为 `2`）**：
   抛弃整数中不存在的有限子群单点 `H`，将其沿 `El` 吹胀为带频率集 $\Xi$ 与半径参数的 **Bohr 集范畴**，并进一步拆成**双色拼接范畴 `{Wide, Narrow}`**：
   - 基点 $x$ 住在**宽母盒** $B(\Xi, \rho)$，公差 $d$ 限制在**窄步长子盒** $B(\Xi, \varepsilon\rho)$；
   - 原先报错的自封闭箭头 `[H, H] ⟶ [H]` 被合法改写为跨色异函子箭头 `[Wide, Narrow] ⟶ [WideOut]`——只要挑选满足 Bourgain 正则性尺度的 $\rho$，绝大部分 $x + d, x + 2d$ 稳稳落在宽盒内部，边界泄漏被严格压制在 $\ll \delta^3$ 以内！
2. **无辜子树零轮次复用**：
   沿着这条多异函子搬运桥，先前已经验证完毕的**吸收态幂等粘合引擎 `roth_master_categorical_glue` / `rothStepEndo_stabilizes`** 与 **Parseval 傅里叶能量相关性旁支**连一个字符都不用重算，直接平移挂载到新蓝图 `T₀'` 上；系统只需局部补完双尺度 Bohr 集的边缘计数引理，整座菲尔兹奖级定理的证明即告合龙。
3. **顺着 `1.2` 超穷不动点视角再看一步（从 Roth 定理升维到任意 $k$ 项 Szemerédi 定理）**：
   - 在 $3$ 项等差数列的 Roth 定理中，密度每次涨固定常数 $c\delta_0^2$，因此单步算子 $T$ 在有限步 $n < \omega$ 内就满足幂等稳定 $T^{n+1} = T^n$，连一次 `lim/colim` 都无需动用；
   - 而当目标升级为任意 $k$ 项等差数列（Szemerédi 定理）时，Furstenberg 的遍历论证明恰恰就是把同一个单步算子 $T$ 延拓到了**可数序数范畴 $(\mathbf{Ord}, \le)$** 上（Furstenberg–Zimmer 结构塔）：从平凡因子 $Z_0 = \mathbf{1}$ 出发，若未达相对伪随机不动点，**后继序数步**扩出一层紧致群扩张 $Z_{\alpha+1} \twoheadrightarrow Z_\alpha$；走了无穷步仍未停机，则在**极限序数 $\lambda$ 处求一次逆向极限 $Z_\lambda = \lim_{\beta < \lambda} Z_\beta$** 跨过无穷继续扩！最终靠可分性在某个可数序数 $\alpha < \omega_1$ 处命中不动点 $T(Z_\alpha) \cong Z_\alpha$，一举证出任意长度等差数列。

> [!NOTE]
> **全景收束**：回看 Roth 定理的整个证明轨迹——外层因全称量词 $\forall (N, A)$ 天然落在**函子范畴 $[\mathcal{C}_{\mathrm{Stage}}, \mathcal{D}_{\mathrm{AP3}}]$ 找点**，主循环是**吸收态幂等不动点 $T^{n+1} = T^n$（定理 1）**与**`2 -> 2` 排中分岔切消（定理 6）**在范畴数据库里的**确定性函子复合**（升维至 $k$ 项则平滑延拓为序数塔上的 `lim` 不动点），跨世界架桥是**沙盘投影与 `: ⊥` 提升反驳（定理 2）**，而内层局部环境对象则从单点 `1 -> Env` 经 `: ⊥` 吹胀为 **`2 -> Env` 双侧拼接范畴（定理 5）**外加 **Dialectica 无辜子树零重算复用**。所谓“深奥莫测的纯数学神来之笔”，在范畴式编程的显微镜下，完全还原成了有迹可循、可检索、可局部自愈的保结构函子工程。
