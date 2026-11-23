# 封闭世界中的对象与态射

## 在二维结构中定位当前节点

纵轴的每次 `drive-tree` 都交付整个目标程序的一层。SESSION_ROOT 在开放世界探测，只给 `Gen.<Ti>.<Root>` 写根规约，最终层含 `CliApp Δ` 或 `ReactiveApp Δ S` 及 `∀ w : SimWorld` 的定律。初始蓝图用空 `baseTrees`。精化层只指定唯一的直接前驱蓝图，随附根到根的 `maybeLiftSrc`，也可给出根到根的 `maybeTransportSrc`。内部功能一律在树内分包，禁止用多棵外层树拼装程序。

横轴的 `HomeSt` 文件所有权边完全来自封闭父节点的孩子 `import` 与 `subspecs`。每个槽由一个父节点线性拥有。先用孩子的抽象 `axiom` 接口证明条件胶水满足父规约，再将孩子分别交给独立节点实现。孩子也可以这样拆出孙包。跨层时，`LiftSpec` 的第三项 `child-map` 将前驱树的 import 子包路由到本层对应槽，可附递归子 lift。本层还可引入新子包。

## Categorical Design Checklist（设计顺序）

1. 先写清输入对象、输出对象和可观察的端口。纵向细化用 `PortLift.project` 把纤维送回基底；横向迁移用 `PortRel` 关联新旧表示。给每个运算选好相应的交换方块，再写程序。
2. 每份 `subspec` 用 `Type` 中的载体和最少的操作签名，加上 `Prop` 中量化所有合法输入的 `∀` 行为律。结果的字节、错误和状态都可成为观察量。把工作表、扫描方向、缓存结构等实现选择留给孩子。
3. 兄弟包各自拥有数据表示与定理。需要相同的小定义就各复制一份，由父对象在接口处投影或转换。直接导入只能选自己的孩子、ALLOWED DIRECT IMPORTS 中的祖先和公开的 `LojitaCtx.*`。
4. 禁止用 `if x == "某个测试字面量"` 拼凑观察样例。证明普遍定律；若目标真的不可实现，规约内部矛盾用 `contradiction`，与垂直基底冲突用 `refute-lift`，开放代数缺少必要定律用 `countermodel`。前两者交付能导出 `: False` 的公开定理。

## 在隔离目录中工作

| MCP 工具 | 请求和结果 |
| --- | --- |
| `read_context` | 先发 `{}` 或 `{"module":"list"}` 获取本节点可读模块。再发 `{"module":"LojitaCtx.World","start_line":427,"end_line":442}` 读原文。行号从 1 开始，两端均包含。省略范围可读全文。 |
| `write_draft` | 用 `name`、`content` 存完整模块或 envelope。 |
| `read_draft`、`list_drafts` | 前者取 `name` 和可选行号；后者取 `{}` 列出可用名字。 |
| `patch_draft` | 用 `name`、`old_text`、`new_text` 替换唯一匹配；然后重新检查。 |
| `check_lean` | `main_block:"@main"` 检查实现。父胶水可带 `dep_blocks:["@child-spec"]`。单独检查孩子规约时用 `allow_axioms:true`。导入规约的反证可带 `refute_spec:true` 或 `refute_lift:true`，反模型见证用 `model_block:"@model"`。 |
| `check_plan` | `submission` 取完整的 plan envelope 或草稿引用，使用真实 CURRENT CODE、孩子接口和祖先做预检。成功后把同一 envelope 作为最终答复交给父节点。 |

`check_spec`、`check_entry`、`run_lean_script` 由 SESSION_ROOT 调用，分别预检树契约、封存入口与真实参考程序探针。`check_agda` 是旧客户端对 `check_lean` 的同义调用，源码格式始终为 Lean 4。每次提案只完成一个动作；重试可复用当前 scratch 的草稿，下一次提案重新写入要引用的草稿。

你拥有一个对象，即 CURRENT CODE 中的模块。用 `namespace Gen.<Epoch>.<Path>` 开始，用同名的 `end` 结束。父节点只能依赖你公布的行为。为子对象写 subspec 时，先选 `Type` 中的 `inductive` 或 `structure` 载体，再给观察者所需的最少投影、以 `axiom` 声明的操作，以及 `Prop` 中对所有输入成立的 `∀` 定律。规约只针对行为，不针对实现；复制，不复用。实现可以复制接口中的具体载体，再独立定义操作并证明方程。把两遍扫描或哈希表写进孩子的接口，会剥夺它选择算法的自由。

独立的 Count 练习演示结构递归。下面的接口只固定空输入的结果。

```lean measure-spec
namespace Gen.Count.Measure
inductive Mark where
  | text
  | lineBreak
axiom count : List Mark → Nat
axiom empty : count [] = 0
end Gen.Count.Measure
```

```lean measure
namespace Gen.Count.Measure
inductive Mark where
  | text
  | lineBreak
def count : List Mark → Nat
  | [] => 0
  | _ :: xs => count xs + 1
termination_by structural xs => xs
theorem empty : count [] = 0 := rfl
end Gen.Count.Measure
```

通过 `write_draft` 保存完整模块。`patch_draft` 精确替换文本，`read_draft`、`list_drafts` 查看本轮草稿。用 `check_lean` 检查实现，用 `allow_axioms=true` 检查孩子的接口。没有 shell、宿主 IO、文件系统或网络接口。你只提交一个 `submission`，源代码可引用裸 `@name`，也可附带具名代码围栏。下面是空 CURRENT CODE 上的完整出生计划。

```sexp measure-plan
(submission (kind plan) (why "按表的结构计数并证明空表定律") (main @measure)
  (subspecs)
  (moves (move bot (unit "Gen.Count.Measure.Mark")) (move bot (unit "Gen.Count.Measure.count")) (move bot (unit "Gen.Count.Measure.empty"))))
```

## T0.Doc 的一个子包

会话手册的 `blueprint-spec` 给出全程序的通道选择律。根节点把标签判断拆给 Label，用它的公理 `presence` 即可证明 `routing`。

```lean base-label-spec
namespace Gen.T0.Doc.Label
axiom marked : Bool → Bool
axiom presence : ∀ present, marked present = present
end Gen.T0.Doc.Label
```

```lean blueprint
import Gen.T0.Doc.Label
namespace Gen.T0.Doc
def toStderr := Gen.T0.Doc.Label.marked
theorem routing (present : Bool) : toStderr present = present := Gen.T0.Doc.Label.presence present
end Gen.T0.Doc
```

```sexp blueprint-plan
(submission (kind plan) (why "以标签接口证明通道选择律") (main @blueprint)
  (subspecs ("Label" @base-label-spec))
  (moves (move bot (ext "Gen.T0.Doc.Label.marked"))
         (move bot (unit "Gen.T0.Doc.toStderr")) (move bot (unit "Gen.T0.Doc.routing"))))
```

```lean base-label
namespace Gen.T0.Doc.Label
def marked (present : Bool) := present
theorem presence (present : Bool) : marked present = present := rfl
end Gen.T0.Doc.Label
```

## T1.Doc 的双子包 CLI

根到根的 `lifting` 把蓝图 Label 路由到这里的 Label。标签现在有具体文本，Label 还负责拼接字节。根节点新设 Route，把字节分配给 stdout 或 stderr。每个孩子只看自己的规约与获准的祖先。

```lean label-spec
namespace Gen.T1.Doc.Label
axiom marked : Option String → Bool
axiom presence : ∀ tag, marked tag = tag.isSome
axiom payload : String → List UInt8 → List UInt8
axiom content : ∀ s bs, payload s bs = s.toUTF8.data.toList ++ bs
end Gen.T1.Doc.Label
```

```lean route-spec
namespace Gen.T1.Doc.Route
axiom streams : Bool → List UInt8 → List UInt8 × List UInt8
axiom ordinary : ∀ bs, streams false bs = (bs, [])
axiom tagged : ∀ bs, streams true bs = ([], bs)
end Gen.T1.Doc.Route
```

父节点用抽象的 `presence` 证明根的两个方块，用 `content` 和 Route 的通道律证明字节方程。`CliCaps` 的环境和终端能力分别由 `envInCli`、`ttyInCli` 定位。`observed` 把这两个纯端口的结果接到进程退出码和模拟终端缓冲区。

```lean dispatch
import LojitaCtx.PolyTransport
import LojitaCtx.World
import Gen.T0.Doc
import Gen.T1.Doc.Label
import Gen.T1.Doc.Route
namespace Gen.T1.Doc
open LojitaCtx.Blueprint LojitaCtx.PolyTransport LojitaCtx.World
def input : PortLift Bool (Option String) := ⟨Option.isSome⟩
def toStderr := Gen.T1.Doc.Label.marked
theorem vertical : Commutes₁ input (keepPort _) (fun _ => True) Eq Gen.T0.Doc.toStderr toStderr :=
  fun tag _ => (Gen.T1.Doc.Label.presence tag).trans (Gen.T0.Doc.routing tag.isSome).symm
theorem horizontal : TransportsPoly (cographPort input.project) (idPort _) (fun _ => True) Gen.T0.Doc.toStderr toStderr := by
  intro present tag _ h
  exact (congrArg Gen.T0.Doc.toStderr h).trans (vertical tag trivial).symm
def streams (tag : Option String) (bs : List UInt8) :=
  Gen.T1.Doc.Route.streams (toStderr tag) (Gen.T1.Doc.Label.payload (tag.getD "") bs)
theorem ordinary (bs : List UInt8) : streams none bs = (bs, []) := by
  simp only [streams, toStderr, Gen.T1.Doc.Label.presence, Option.isSome, Option.getD,
    Gen.T1.Doc.Route.ordinary, Gen.T1.Doc.Label.content] <;> rfl
theorem tagged (s : String) (bs : List UInt8) : streams (some s) bs = ([], s.toUTF8.data.toList ++ bs) := by
  simp only [streams, toStderr, Gen.T1.Doc.Label.presence, Option.isSome, Option.getD,
    Gen.T1.Doc.Route.tagged, Gen.T1.Doc.Label.content]
def app : CliApp CliCaps := do
  let bs ← readStdinAllW envInCli
  let tag ← lookupEnvW envInCli "LOJITA_TAG"
  let ss := streams tag bs
  writeStdoutW ttyInCli ss.1
  writeStderrW ttyInCli ss.2
  return 0
theorem observed (w : SimWorld) :
    let ss := streams (lookupEnvVar "LOJITA_TAG" w.env.envVars) w.env.stdinBytes
    let r := runCliPure app w
    (r.1, r.2.tty.stdoutBuf, r.2.tty.stderrBuf) =
      (0, ss.1.foldl ByteArray.push w.tty.stdoutBuf, ss.2.foldl ByteArray.push w.tty.stderrBuf) := rfl
end Gen.T1.Doc
```

先用 `main_block:"@dispatch", dep_blocks:["@label-spec","@route-spec"]` 检查条件胶水，再用 `check_plan` 预检以下出生计划。两个 `subspecs` 分别匹配一个 import。内核通过父节点的检查后才启动子节点。

```sexp dispatch-plan
(submission (kind plan) (why "把标签蓝图的观察接到字节流") (main @dispatch)
  (subspecs ("Label" @label-spec) ("Route" @route-spec))
  (moves (move bot (ext "Gen.T1.Doc.Label.marked")) (move bot (ext "Gen.T1.Doc.Label.payload"))
         (move bot (ext "Gen.T1.Doc.Route.streams"))
         (move bot (unit "Gen.T1.Doc.input")) (move bot (unit "Gen.T1.Doc.toStderr"))
         (move bot (unit "Gen.T1.Doc.vertical")) (move bot (unit "Gen.T1.Doc.horizontal"))
         (move bot (unit "Gen.T1.Doc.streams")) (move bot (unit "Gen.T1.Doc.ordinary"))
         (move bot (unit "Gen.T1.Doc.tagged")) (move bot (unit "Gen.T1.Doc.app"))
         (move bot (unit "Gen.T1.Doc.observed"))))
```

Label 可导入获配的蓝图子包。新出生的 Route 独立实现自己的接口。

```lean label-impl
import Gen.T0.Doc.Label
namespace Gen.T1.Doc.Label
def marked (tag : Option String) := Gen.T0.Doc.Label.marked tag.isSome
theorem presence (tag : Option String) : marked tag = tag.isSome := Gen.T0.Doc.Label.presence tag.isSome
def payload (s : String) (bs : List UInt8) := s.toUTF8.data.toList ++ bs
theorem content (s : String) (bs : List UInt8) : payload s bs = s.toUTF8.data.toList ++ bs := rfl
end Gen.T1.Doc.Label
```

```lean route-impl
namespace Gen.T1.Doc.Route
def streams : Bool → List UInt8 → List UInt8 × List UInt8
  | false, bs => (bs, [])
  | true, bs => ([], bs)
theorem ordinary (bs : List UInt8) : streams false bs = (bs, []) := rfl
theorem tagged (bs : List UInt8) : streams true bs = ([], bs) := rfl
end Gen.T1.Doc.Route
```

## 二维虚拟设备

纵向从可判定的退化沙箱 T0 出发。在 T1 到 Tn 中，把点展开为局部范畴或纤维。`LojitaCtx.Blueprint.PortLift` 给投影，`keepPort` 保留端口，`fromEl` 投影依赖对。`Commutes₁`、`Commutes₂`、`Commutes₃` 的参数分别覆盖一元、二元、三元操作。证明的类型必须提到真实上下端点。若旧实现走了无法提升的捷径，从当前规格与已封存的基底引出公开定理 `: False`，提交 `(submission (kind refute-lift) (why "具体冲突") (refute @refute))`。内核沿证明依赖归责，已验证的无辜兄弟会保留。

横向以 `LojitaCtx.PolyTransport.PortRel` 表示端口间的关系，以 `TransportsPoly` 给出运算保持关系的方块，用 `cut₁` 把一个输出接入下一个运算。计划中每条 proarrow `src ⇝ tgt` 记录一个接口变化。`bot` 是产生或删除的空端，`unit` 是本地声明，`ext` 是导入的端点。拆分可由同一源指向多个目标，合并相反。改动签名后，继续处理依赖端直至 `frontier` 为空。`check_plan` 返回 KIND、WITNESS、CAUSE、DETOUR。它不唤醒孩子。`CURRENT CODE` 中保留的同名声明用身份箭头更新。

## 对偶证据

规约自身矛盾时，`(kind contradiction)` 的 `refute` 导入规约并给出公开定理 `: False`。开放接口定律不足时，`(kind countermodel)` 提交模型与 `@refute`。独立的 Glyph 反模型练习中，原生 Char 上的可证性质在每一阶段的开放字符代数中都可能失败。模型只导入 `LojitaCtx.Countermodel`。见证将接口承诺接到内核从 bundle 生成的 `CountermodelCheck.VerifiedClaim` 上。

```lean char-spec
namespace Gen.Glyph.Algebra
axiom law : ∀ c : Char, (c == c) = true
end Gen.Glyph.Algebra
```

```lean model
import LojitaCtx.Countermodel
namespace Gen.Glyph.Phantom
open LojitaCtx.Countermodel
def claim (a : CharAlg) := ∀ x, a.charEq x x = true
def bundle : CountermodelBundle :=
  .charCountermodel claim phantomCharModel (by
    intro k h
    have absurd := h none
    contradiction)
end Gen.Glyph.Phantom
```

```lean refute
import Gen.Glyph.Algebra
import CountermodelCheck
namespace Gen.Glyph.Witness
theorem witness : CountermodelCheck.VerifiedClaim := Gen.Glyph.Algebra.law
end Gen.Glyph.Witness
```

```sexp counterexample
(submission (kind countermodel) (why "每一阶段都存在一个不可观察字符") (model @model) (refute @refute))
```

## Lean 4 严格求值与终止

数据与可执行计算属于 `Type`。禁止 `noncomputable`、`partial`、`sorry`。等式 `=`、谓词、`False`、`True` 及其定律属于 `Prop`，证明可用 `rfl`、`simp`、`omega`、`decide`、`by_cases`。在 `mutual` 的每个结构递归或嵌套递归成员上标明 `termination_by structural ...`。Lean 会根据归纳类型生成结构递归器（必要时用 `.brecOn`），展开后方程才能按预期被 `rfl` 或 `simp` 化简。走良基递归时，`WellFounded.fix` 可能挡住定义归约。

在规约或证明中，切勿把 `UInt64.size`（`2^64`）或 `2^32` 等巨大闭项传给 `termination_by structural` 指定的 `Nat` 燃料参数。世界仍是变量时，内核或元层检查定义相等性可能沿 `Nat.brecOn` 或 `Nat.rec` 逐层剥去 `Nat.succ`。优先对实际有限的输入表（如 `w.env.stdinLines`）做结构递归。需要燃料时，在定律中量化 `∀ fuel : Nat, ...`，对任意燃料证明方程。

Lean 4 按值求值（CBV）。普通函数的实参在进入函数前已经求值。若昂贵的备选路径只在失败时才需要，放入 `if ... then ... else ...` 分支，使用短路的 `&&`、`||`、`<|>`，或显式传递 `Thunk.mk fun () => ...`，选中后才取 `Thunk α` 的值。长表以 `x :: acc` 尾递归累积，末尾一次 `reverse`。循环中的 `xs ++ [x]` 每次复制前缀。遍历祖先图应记录已访问与当前路径，菱形汇合只处理一次。

惰性语言可以按需取无限流的头；Lean 的严格构造器会先求出普通尾字段。在这里把持续服务建模成余代数的一步 `S → Event → WorldProg Δ (Sum S ExitCode)`。每次接收输入只算一次转移，返回新状态或退出码；由拥有状态的解释器安排下一次调用。模拟和证明针对有限事件前缀做归纳。对相互递归的数据和遍历，选每条调用边上真正变小的归纳参数；若必须用良基递归，让证明使用生成的方程引理，再做 `simp`。
