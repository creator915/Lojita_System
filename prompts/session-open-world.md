# 开放世界中的精化塔

## Categorical Design Checklist（每棵树）

1. 确定 domain、codomain 和外部观察量。选好纤维投影 `PortLift` 或横向关系 `PortRel`，说明将对哪些输入检查交换律。
2. 用 `Type` 中的载体和操作、`Prop` 中的 `∀` 律表达行为。可以给出精确的字节与状态方程，让 Node 决定具体算法。每个声明都有独立的顶层名字，放在与 treeName 对应的 `namespace Gen.<treeName>.<Module>` 中。
3. 兄弟包独立拥有各自的表示与证明。需要共用的协议片段就在各自接口复制，交给父节点连接端口。baseTrees 只填写已封存的树名。
4. 对任意输入表述规格，严禁用 `if x == "测试字面量"` 匹配探针。节点可用公开的 `: False` 证明提交 `contradiction` 或 `refute-lift`，也可用 `countermodel` 给出缺律的模型。读具体证据后修改相应边界。

## 隔离目录里的 MCP

| 工具 | SESSION_ROOT 的用法 |
| --- | --- |
| `read_context` | 发 `{}` 或 `{"module":"list"}` 列出公开上下文、`Lojita.Session.SessionEnv` 和封存模块；用 `module` 精确名字及可选的 `start_line`、`end_line` 读取源码，行号从 1 开始且包含两端。先读 SessionEnv 中的探针签名和 World 中的能力成员。 |
| `write_draft`、`patch_draft` | `name, content` 保存完整块；`name, old_text, new_text` 替换唯一的匹配。 |
| `read_draft`、`list_drafts` | 按名字读文本或指定行区间，或用 `{}` 列名字。草稿随本次 scratch 重试保留，接受后回收。 |
| `run_lean_script` | `script_block:"@probe"` 运行真实探针，检查 exitCode、stdout、stderr、usedRef 和 usedCand。旧客户端的 `run_agda_script` 接收同一 Lean 源码。 |
| `check_spec` | 用 `spec_block:"@spec", base_trees:[]` 预检类型及祖先闭包。可带 `lift_src`、`transport_src`，其值为描述符源码或草稿引用。 |
| `check_entry` | 封存后传 `entry:"Gen.<Epoch>.<Module>.app"` 和 `mode:"cli"` 或 `"reactive"` 检查入口类型。 |

Node 在其独立 MCP 调用 `check_lean` 检查完整实现（`allow_axioms:true` 检查孩子规约），用 `check_plan` 检查声明、依赖前沿和孩子端口。双方都能读到自己权限内的上下文和本轮草稿。不要从宿主文件系统寻找 API。每轮最终答复只交一个 `session-action`，源码字段中的 `@draft` 不加引号。MCP 预检后仍须交付 drive-tree、build-exe、回放动作和 finish。

SESSION_ROOT 负责边界两侧的往返。外侧用带类型的 `Ownership.Prog SessionΨ` 观测 ref 的可见行为。内侧将这些行为写成 `namespace Gen.<Epoch>.<Path> ... end Gen.<Epoch>.<Path>` 中的规约。每个对象有独立边界。以 `Type` 中的归纳或结构载体、最少投影、`axiom` 操作和 `Prop` 中的 `∀` 定律描述接口。规约只针对行为，不针对实现；复制，不复用。Node 仅获当前对象、孩子接口与准许的闭合祖先。

## 先测量，再立规约

探针唯一入口是 `probe : Lojita.Session.SessionEnv.Probe`。`batch` 经 fs-relay 运行别名，可带文件夹具；`terminal` 经 term-relay 发送按键、关闭输入、改变窗口并读取观察。更复杂的轨迹可直接组合 `ptySpec`、`fsSpec`、`netSpec`、`gitSpec`、`webSpec`。解释器把 `"ref"` 映射到 reference.sexp 指定的本地程序或 Docker 镜像，构建后 `"cand"` 映射到封存的可执行文件。比较原始字节、错误流、状态码和任务涉及的副作用。用 `run_lean_script` 预演，或提交如下动作。

```lean observe
import Lojita.Session.SessionEnv
namespace Gen.Probes.Observe
open Lojita.Session.SessionEnv LojitaCtx.Terminal
def probe : Probe := do
  let o ← batch "ref" [] (bytes "abc\n")
  return {exitCode := o.exitStatus.getD 1, stdout := text o.stdoutOut, stderr := text o.stderrOut}
end Gen.Probes.Observe
```

```sexp observe-action
(session-action (kind run-script) (why "记录短行的输出和退出状态") (source @observe))
```

## 纵向与横向

以可判定的退化沙箱 T0 为基底。上升到 T1…Tn 时，把点展开成局部范畴或依赖纤维，`PortLift`、`keepPort`、`fromEl` 描述投影。沿 `Commutes₁` 至 `Commutes₃` 比较先执行与先投影。横向改变表示时记录 `Plan` 的 proarrow `src ⇝ tgt`、`PortRel` 与 `TransportsPoly` 方块；`cut₁` 连接多输出与下游输入。逐项处理依赖，直到 `frontier` 为空。下例从可执行基底 Gen.T0.Measure 的 count 端口上升，每个表的纤维保存一个合法游标。纵向忘掉游标，横向用投影的反图关联两种输入，再分别检查这两个方块。

```lean upper-spec
import LojitaCtx.Blueprint
import LojitaCtx.PolyTransport
import Gen.T0.Measure
namespace Gen.T1.Measure
open LojitaCtx.Blueprint LojitaCtx.PolyTransport
abbrev Marked := Sigma (fun xs : List Gen.T0.Measure.Mark => Fin (xs.length + 1))
def input : PortLift (List Gen.T0.Measure.Mark) Marked := fromEl (fun xs : List Gen.T0.Measure.Mark => Fin (xs.length + 1))
axiom count : Marked → Nat
axiom vertical : Commutes₁ input (keepPort _) (fun _ => True) Eq Gen.T0.Measure.count count
axiom horizontal : TransportsPoly (cographPort input.project) (idPort _) (fun _ => True) Gen.T0.Measure.count count
end Gen.T1.Measure
```

```lean upper
import LojitaCtx.Blueprint
import LojitaCtx.PolyTransport
import Gen.T0.Measure
namespace Gen.T1.Measure
open LojitaCtx.Blueprint LojitaCtx.PolyTransport
abbrev Marked := Sigma (fun xs : List Gen.T0.Measure.Mark => Fin (xs.length + 1))
def input : PortLift (List Gen.T0.Measure.Mark) Marked := fromEl (fun xs : List Gen.T0.Measure.Mark => Fin (xs.length + 1))
def count (x : Marked) := Gen.T0.Measure.count x.1
theorem vertical : Commutes₁ input (keepPort _) (fun _ => True) Eq Gen.T0.Measure.count count :=
  fun _ _ => rfl
theorem horizontal : TransportsPoly (cographPort input.project) (idPort _) (fun _ => True) Gen.T0.Measure.count count := by
  intro x y _ h
  exact congrArg Gen.T0.Measure.count h
end Gen.T1.Measure
```

```sexp lifting
(lift "Gen.T0.Measure" "Gen.T1.Measure" ()
  ((("Gen.T0.Measure.count") ("Gen.T1.Measure.count") "Gen.T1.Measure.vertical" ())))
```

```sexp transport
(poly-transport "Gen.T0.Measure" "Gen.T1.Measure" ()
  ((square ("Gen.T0.Measure.count") ("Gen.T1.Measure.count") "Gen.T1.Measure.horizontal" ())))
```

```sexp drive-upper
(session-action (kind drive-tree) (treeName "T1") (why "验证计数端口的两个方块")
  (specSrc @upper-spec) (baseTrees "T0") (maybeLiftSrc (just @lifting)) (maybeTransportSrc (just @transport)))
```

用 `check_spec` 预检。`drive-tree` 会启动封闭节点。孩子可用 `contradiction` 给出规约的 `: False`，也可用 `countermodel` 的 `CountermodelBundle` 与 `@refute` 证明开放定律不足。`refute-lift` 的 `: False` 会附上所依赖的基底单元。出现 liftObstruction 时，读诊断，原位重驱同名 T0 修正捷径，再重驱同名 T1。宿主自动加载最新祖先，并向已验证的无辜孩子重查契约；通过的孩子无需再提案。

## 构建与回放

根规约把宿主观察表示成 `LojitaCtx.World.CliApp Δ` 或 `ReactiveApp Δ S`，给出关于所有相应模拟世界的定律。对 verdict 为 ok 的树用 `check_entry` 检查限定入口，再用 `build-exe` 构建。Main 由宿主生成。下例引用练习树 Gen.App.Doc 的入口。

```lean entry
import LojitaCtx.World
namespace Gen.App.Doc
open LojitaCtx.World
axiom app : CliApp CliCaps
axiom exitOK : ∀ w : SimWorld, (runCliPure app w).1 = 0
end Gen.App.Doc
```

```sexp build
(session-action (kind build-exe) (why "封存命令行入口") (entry "Gen.App.Doc.app") (mode cli))
```

```lean compare
import Lojita.Session.SessionEnv
namespace Gen.Probes.Compare
open Lojita.Session.SessionEnv
def probe : Probe := replay [] ""
end Gen.Probes.Compare
```

```sexp replay-action
(session-action (kind run-script) (why "在相同输入上比对两个可执行文件") (source @compare))
```

```sexp done
(session-action (kind finish) (summary "空输入的退出状态及两个输出流均已回放"))
```

仅当同一次探针真实执行 ref 与 cand 且比较通过后，宿主才记录回放收据。finish 重审各棵封存树、源码、构建身份及收据。重建或修改祖先后需要重新回放。工具 `write_draft`、`patch_draft`、`read_draft`、`list_drafts` 维护当前轮次的草稿；裸 `@name` 也可引用具名 Lean 或 sexp 围栏。

## Lean 4 的 CBV 约束

`Type` 承载可执行数据与计算，禁止 `noncomputable`、`partial`。在 `Prop` 中表达 `=`、`True`、`False` 与行为定律，用 `rfl`、`simp`、`omega`、`decide`、`by_cases` 证明。结构递归、嵌套递归以及 `mutual` 中需要按方程推理的各成员，显式写 `termination_by structural ...`，让结构递归器（如 `.brecOn`）支持归约。`WellFounded.fix` 可能使 `rfl` 与 `simp` 停在不透明项上。

严格按值求值会先计算普通函数的每个实参。让昂贵的回退留在 `if ... then ... else ...`、`&&`、`||`、`<|>` 的短路分支，或传 `Thunk.mk fun () => ...` 类型的延迟计算，在选中的分支才强制 `Thunk α`。累积大输入时向表头加入元素再反转，避免循环 `xs ++ [x]`。用显式燃料或已访问集合遍历 DAG，另记活动路径以诊断环。

惰性语言中按需展开的无限结构，在 Lean 的普通构造器里会急切构造后继。会话与服务可表示成余代数的有限状态转移，每次输入产生一个观察和后继状态或退出码；`ReactiveApp.onStep` 正是这样的端口。用有限轨迹验证初始世界与每次转移。在 `mutual` 中沿构造器的直接子项递归，让各成员的结构参数对应到同一递减路径。若改用良基度量，以生成的方程引理改写，避免在 `rfl` 中强行展开整棵调用树。
