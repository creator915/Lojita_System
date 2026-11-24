# 开放世界中的精化塔

## 二维分工

**纵轴 Lift · 跨抽象层级的整树精化。** 一棵树表示整个目标程序在一个抽象层级的完整所有权树。SESSION_ROOT 负责开放世界探测，每层只编写根模块规约 `Gen.<Ti>.<Root>`。例如 T0 是有限可判定的蓝图，T1/T2 把它提升到流与世界规约，最终层公开 `CliApp Δ` 或 `ReactiveApp Δ S` 及其 `∀ w : SimWorld` 观察定律。初始树和它的原位修复用 `(baseTrees)`。精化层只填唯一已封存的直接前驱，如 `(baseTrees "T0")`，宿主自动跟随更早各层的当前封存版本。给出根到根的 `maybeLiftSrc`，可附加 `maybeTransportSrc`。以关系方块表达精化时，根到根的 transport 也可单独满足此门槛。严禁把 CLI、解析、压缩等内部功能各建一棵外层树再自底向上拼装。

**横轴 Transport · 同一抽象层级的修补与重构。** 修复回放偏差时保持原 `baseTrees`，生成新版本、销毁旧版本。严禁为局部 bug 把旧可执行树塞进 `baseTrees`，盲目叠出 T3 → T4 → T5。

- **同名原位重驱。** 对同一 `treeName` 再次 `drive-tree`，保留原 `baseTrees` 及对底树的 `maybeLiftSrc`。接口未变且复验通过的子包自动零轮复用。若需证明新旧版本的 `TransportsPoly`，用同名源和目标提交 `maybeTransportSrc`，在临时方块中引用只读快照 `Old.Gen.<Ti>.<Mod>.*`。封存后只交付新实现。
- **换名同层替换。** 例如把 T1.Doc 换成 T1b.Doc，仍用 `(baseTrees "T0")`，将底树 lift 的目标改为 T1b.Doc。在 `maybeTransportSrc` 中写 `(poly-transport "Gen.T1.Doc" "Gen.T1b.Doc" ((keep "Gen.T1.Doc.Label" "Gen.T1b.Doc.Label") (move ("Gen.T1.Doc.Route") ("Gen.T1b.Doc.Route") ())) ())`。Label 连同孙包零轮搬迁，Route 交给新槽。在 `drive-tree` 中加 `(replaces "T1")`，新树封存成功时原子撤下旧树的引用和生成目录。若其他封存树仍以 T1 为直接底树，须先处理其依赖。

**树内分包与 import 所有权。** 收到根规约后，封闭根节点决定怎样分包。每条父子边来自父实现的孩子 `import` 和对应的 `subspecs`，每个孩子槽只有一个父所有者。内核先仅凭孩子的抽象 `axiom` 接口检查父胶水能推出根规约，再唤醒孩子独立实现；孩子也可用同样方式拆出孙包。提升整树时，`LiftSpec` 第三项 `child-map` 把底树的这些 import 子包路由到上层子包，可递归给出子 lift。上层还可增设自己的 import 子包。

## Categorical Design Checklist（每棵树）

1. 确定 domain、codomain 和外部观察量。选好纤维投影 `PortLift` 或横向关系 `PortRel`，说明将对哪些输入检查交换律。
2. 用 `Type` 中的载体和操作、`Prop` 中的 `∀` 律表达行为。可以给出精确的字节与状态方程，让 Node 决定具体算法。每个声明都有独立的顶层名字，放在与 treeName 对应的 `namespace Gen.<treeName>.<Module>` 中。
3. 兄弟包独立拥有各自的表示与证明。需要共用的协议片段就在各自接口复制，交给父节点连接端口。用前驱根的封存源码识别需要路由的子包。
4. 对任意输入表述规格，严禁用 `if x == "测试字面量"` 匹配探针。节点可用公开的 `: False` 证明提交 `contradiction` 或 `refute-lift`，也可用 `countermodel` 给出缺律的模型。读具体证据后修改相应边界。

## 隔离目录里的 MCP

| 工具 | SESSION_ROOT 的用法 |
| --- | --- |
| `read_context` | 发 `{}` 或 `{"module":"list"}` 列出公开上下文、`Lojita.Session.SessionEnv` 和封存模块；用 `module` 精确名字及可选的 `start_line`、`end_line` 读取源码，行号从 1 开始且包含两端。先读 SessionEnv 中的探针签名和 World 中的能力成员。 |
| `write_draft`、`patch_draft` | `name, content` 保存完整块；`name, old_text, new_text` 替换唯一的匹配。 |
| `read_draft`、`list_drafts` | 按名字读文本或指定行区间，或用 `{}` 列名字。草稿随本次 scratch 重试保留，接受后回收。 |
| `run_lean_script` | `script_block:"@probe"` 运行真实探针。SessionEnv 已导入 `LojitaCtx.FuzzGen`，可在立规约前生成样本、对拍纯规格与 ref、收缩反例。检查 exitCode、stdout、stderr、usedRef 和 usedCand。旧客户端的 `run_agda_script` 接收同一 Lean 源码。 |
| `check_spec` | 用 `spec_block:"@spec", base_trees:[]` 预检类型及祖先闭包。可带 `lift_src`、`transport_src` 描述符及同层替换列表 `replaces`。 |
| `check_entry` | 封存后传 `entry:"Gen.<Epoch>.<Module>.app"` 和 `mode:"cli"` 或 `"reactive"` 检查入口类型。 |

Node 在其独立 MCP 调用 `check_lean` 检查完整实现（`allow_axioms:true` 检查孩子规约），用 `check_plan` 检查声明、依赖前沿和孩子端口。双方都能读到自己权限内的上下文和本轮草稿。不要从宿主文件系统寻找 API。每轮最终答复只交一个 `session-action`，源码字段中的 `@draft` 不加引号。MCP 预检后仍须交付 drive-tree、build-exe、回放动作和 finish。

SESSION_ROOT 负责边界两侧的往返。外侧用带类型的 `Ownership.Prog SessionΨ` 观测 ref 的可见行为。内侧将这些行为写成 `namespace Gen.<Epoch>.<Path> ... end Gen.<Epoch>.<Path>` 中的规约。规约限定整棵树的外部行为。以 `Type` 中的归纳或结构载体、最少投影、`axiom` 操作和 `Prop` 中的 `∀` 定律描述接口。规约只针对行为，不针对实现；复制，不复用。Node 仅获当前对象、孩子接口与准许的闭合祖先。

## 先测量与 Fuzz 预对拍，再立规约（Spec-vs-Ref 预演铁律）

**阶段一（立规约前 · 秒级「纯规格预言机 vs `ref`」Fuzz 预对拍）。** 提交语义层 `drive-tree`、唤醒子节点做重型证明之前，SESSION_ROOT 必须先在 `run_lean_script` 里写出可执行的纯规格草稿。比如用分类谓词描述词法字符表，用纯函数预测数值和字符串格式化、路径错误的输出与状态码，用二分搜索定位长度或超时阈值，并复测阈值两侧。`Lojita.Session.SessionEnv` 已内置导入 `LojitaCtx.FuzzGen`。以 `mkSeed` 固定种子，组合 `genBytes`、`genList`、`genChoose`，用 `sampleMany` 批量取样。对每个输入实际运行 `"ref"`，比较预言机给出的观察；用 `shrinkBytes` 或 `shrinkList` 生成更小的输入，复测后用 `minimize` 保留仍有分歧的反例。改一行猜错的规格只需 2～3 秒即可再测。**唯有可执行规格模型在 Fuzz 样本集与边界二分上与 `"ref"` 100% 吻合后，才准将其锁定进 `specSrc` 下发 `drive-tree`！**

**阶段二（`build-exe` 后 · 终审差分回放验签）。** 阶段一已用 ref 校准规格，封闭树再用定理证明 cand 满足该规格。用同样的种子、夹具和边界轨迹对称回放 `"ref"` 与 `"cand"`，核验宿主胶水层，取得本次构建的回放收据后再 `finish`。若发现宿主边界偏差，沿同层横轴 Transport 原位重驱，或用 `(replaces ...)` 加 `(keep ...)` 保留已验证子包。严禁为此叠出 T4、T5、T6。

探针唯一入口是 `probe : Lojita.Session.SessionEnv.Probe`。`batch` 经 fs-relay 运行别名，可带文件夹具；`terminal` 经 term-relay 发送按键、关闭输入、改变窗口并读取观察。更复杂的轨迹可直接组合 `ptySpec`、`fsSpec`、`netSpec`、`gitSpec`、`webSpec`。解释器把 `"ref"` 映射到 reference.sexp 指定的本地程序或 Docker 镜像，构建后 `"cand"` 映射到封存的可执行文件。比较原始字节、错误流、状态码和任务涉及的副作用。用 `run_lean_script` 预演，或提交如下动作。

`SessionEnv.stdio` 以 `pipesNoTTY` 拓扑运行纯管道探针。先发送 `writeStdin`，用 `sleepMs` 与 `drainRaw` 观察关闭输入前的输出和退出状态，再发送 `closeStdin`。在相同轨迹上比较 ref 与 cand。`stdioCap` 管理 fd 0/1/2；对象可用 `readStdinByteW`、`LojitaCtx.Cli.scanStdinFuelW` 或 `LojitaCtx.Cli.streamScannerApp` 逐步消费输入。`ttyCap` 管理独立的 `/dev/tty`；`LojitaCtx.Cli.tuiReactiveApp` 使用 `setTTYRawW` 与 `writeTTYW` 处理按键和绘制界面。用 `Terminal.stepANSI` 投影终端字节，再比较可见内容。

下面先校准未设置 `LOJITA_TAG` 时的字节流规格。随机原始字节覆盖非 UTF-8 输入，另一组样本从行片段构造空行、制表符及换行组合。失败时对后缀和单步收缩候选重跑 ref，纯函数 `minimize` 只选取已确认失败的输入。

```lean observe
import Lojita.Session.SessionEnv
import LojitaCtx.FuzzGen
namespace Gen.Probes.Observe
open Lojita.Session.SessionEnv LojitaCtx.Terminal LojitaCtx.FuzzGen
def oracle (input : Bytes) : Nat × Bytes × Bytes := (0, input, [])
def agrees (input : Bytes) : Script Bool := do
  let o ← batch "ref" [] input
  return !o.timedOut && o.exitStatus.isSome &&
    (o.exitStatus.getD 1, o.stdoutOut, o.stderrOut) == oracle input
def counterexample (input : Bytes) : Script Bytes := do
  let suffixes := (List.range (input.length + 1)).map fun n => input.drop n
  let candidates := (suffixes ++ shrinkBytes input).eraseDups
  let failed ← candidates.filterM fun bs => return !(← agrees bs)
  return minimize (input.length + 1) shrinkBytes (fun bs => !failed.contains bs) input
def probe : Probe := do
  let raw := sampleMany 16 (genBytes 24) (mkSeed 17)
  let line := genMap (fun parts => bytes (String.join parts))
    (genList 5 (genChoose "" ["word", "\t", "\n", "\r\n", "尾"]))
  let samples := raw ++ sampleMany 16 line (mkSeed 41)
  for input in samples do
    unless ← agrees input do
      let small ← counterexample input
      return {exitCode := 1, stderr := s!"Spec-vs-Ref mismatch: {input} -> {small}"}
  return {exitCode := 0, stdout := s!"Spec-vs-Ref: {samples.length} samples agree"}
end Gen.Probes.Observe
```

```sexp observe-action
(session-action (kind run-script) (why "立规约前逐样本核对纯规格与 ref 的两条输出流和退出状态") (source @observe))
```

## 从有限的 Doc 蓝图到字节流 CLI

T0 把标签抽象成一个 Bool，整个程序的观察是输出流选择。上例覆盖未设置标签的分支；还须在设置空标签和非空标签的夹具下对拍 stderr 前缀与原始输入，所有分支吻合后再提交根规约。封闭根的计划会导入 `Gen.T0.Doc.Label` 并给它 subspec，见节点手册的 `blueprint-plan`。SESSION_ROOT 可以从封存结果读到这条边。

```lean blueprint-spec
namespace Gen.T0.Doc
axiom toStderr : Bool → Bool
axiom routing : ∀ present, toStderr present = present
end Gen.T0.Doc
```

```sexp drive-base
(session-action (kind drive-tree) (treeName "T0") (why "验证标签存在与输出通道的有限蓝图")
  (specSrc @blueprint-spec) (baseTrees))
```

T1 用可选字符串和实际字节实现同一个程序。投影 `input` 忘掉标签文本，只保留存在性。`vertical` 比较先选通道与先投影的结果；`horizontal` 用投影的反图关联两种输入。根规约还把两个流和退出码连到每个模拟世界，具体分包留给封闭节点。

```lean upper-spec
import LojitaCtx.PolyTransport
import LojitaCtx.World
import Gen.T0.Doc
namespace Gen.T1.Doc
open LojitaCtx.Blueprint LojitaCtx.PolyTransport LojitaCtx.World
def input : PortLift Bool (Option String) := ⟨Option.isSome⟩
axiom toStderr : Option String → Bool
axiom vertical : Commutes₁ input (keepPort _) (fun _ => True) Eq Gen.T0.Doc.toStderr toStderr
axiom horizontal : TransportsPoly (cographPort input.project) (idPort _) (fun _ => True) Gen.T0.Doc.toStderr toStderr
axiom streams : Option String → List UInt8 → List UInt8 × List UInt8
axiom ordinary : ∀ bs, streams none bs = (bs, [])
axiom tagged : ∀ s bs, streams (some s) bs = ([], s.toUTF8.data.toList ++ bs)
axiom app : CliApp CliCaps
axiom observed : ∀ w : SimWorld,
  let ss := streams (lookupEnvVar "LOJITA_TAG" w.env.envVars) w.stdio.stdin.pending
  let r := runCliPure app w
  (r.1, r.2.stdio.stdout.written, r.2.stdio.stderr.written) =
    (0, ss.1.foldl ByteArray.push w.stdio.stdout.written, ss.2.foldl ByteArray.push w.stdio.stderr.written)
end Gen.T1.Doc
```

根到根的 lift 把 T0.Doc 的 Label 路由给 T1.Doc 的 Label。T1.Doc 的封闭节点另增 Route，在自己的计划中导入两个孩子，分别提供 subspec。新出生的 Route 没有底树来源。第四项指定根端口及其交换方块。

```sexp lifting
(lift "Gen.T0.Doc" "Gen.T1.Doc"
  (("Gen.T0.Doc.Label" "Gen.T1.Doc.Label"))
  ((("Gen.T0.Doc.toStderr") ("Gen.T1.Doc.toStderr") "Gen.T1.Doc.vertical" ())))
```

```sexp transport
(poly-transport "Gen.T0.Doc" "Gen.T1.Doc"
  ((move ("Gen.T0.Doc.Label") ("Gen.T1.Doc.Label") ()))
  ((square ("Gen.T0.Doc.toStderr") ("Gen.T1.Doc.toStderr") "Gen.T1.Doc.horizontal" ())))
```

```sexp drive-upper
(session-action (kind drive-tree) (treeName "T1") (why "把整棵标签蓝图提升到字节流 CLI")
  (specSrc @upper-spec) (baseTrees "T0") (maybeLiftSrc (just @lifting)) (maybeTransportSrc (just @transport)))
```

用 `check_spec` 预检。`drive-tree` 会启动封闭节点。孩子可用 `contradiction` 给出规约的 `: False`，也可用 `countermodel` 的 `CountermodelBundle` 与 `@refute` 证明开放定律不足。`refute-lift` 的 `: False` 会附上所依赖的基底单元。出现 liftObstruction 时，读诊断，原位重驱同名 T0 修正捷径，再重驱同名 T1。宿主自动加载最新祖先，并重查 `PRESERVED_CHILDREN` 中无辜孩子的契约；通过的孩子无需再提案。

## 构建与回放

T1 封存后，用 `check_entry` 检查根规约的入口，再用 `build-exe` 生成 Main 并链接 T1 与其直接前驱链上的模块。工作区的其他封存树仍参加完整性重审和构建指纹计算。

```sexp build
(session-action (kind build-exe) (why "封存命令行入口") (entry "Gen.T1.Doc.app") (mode cli))
```

```lean compare
import Lojita.Session.SessionEnv
namespace Gen.Probes.Compare
open Lojita.Session.SessionEnv
def probe : Probe := do
  let empty ← replay [] ""
  if empty.exitCode != 0 then return empty
  replay [] "abc\n"
end Gen.Probes.Compare
```

```sexp replay-action
(session-action (kind run-script) (why "在相同输入上比对两个可执行文件") (source @compare))
```

```sexp done
(session-action (kind finish) (summary "空输入和短行的退出状态及两个输出流均已回放"))
```

仅当同一次探针真实执行 ref 与 cand 且比较通过后，宿主才记录回放收据。finish 重审各棵封存树、源码、构建身份及收据。重建或修改祖先后需要重新回放。工具 `write_draft`、`patch_draft`、`read_draft`、`list_drafts` 维护当前轮次的草稿；裸 `@name` 也可引用具名 Lean 或 sexp 围栏。

## Lean 4 的 CBV 约束

`Type` 承载可执行数据与计算，禁止 `noncomputable`、`partial`。在 `Prop` 中表达 `=`、`True`、`False` 与行为定律，用 `rfl`、`simp`、`omega`、`decide`、`by_cases` 证明。结构递归、嵌套递归以及 `mutual` 中需要按方程推理的各成员，显式写 `termination_by structural ...`，让结构递归器（如 `.brecOn`）支持归约。`WellFounded.fix` 可能使 `rfl` 与 `simp` 停在不透明项上。

编写树规约和证明时，切勿用 `UInt64.size`（`2^64`）或 `2^32` 等巨大闭项实例化 `termination_by structural` 的 `Nat` 燃料。若世界仍是符号变量，内核或元层的定义相等性检查可能沿 `Nat.brecOn` 或 `Nat.rec` 逐个展开 `Nat.succ`。让树按实际有限的世界输入（如 `w.stdio.stdin.pending`）做结构递归，或让定律量化抽象的 `fuel : Nat`。

严格按值求值会先计算普通函数的每个实参。让昂贵的回退留在 `if ... then ... else ...`、`&&`、`||`、`<|>` 的短路分支，或传 `Thunk.mk fun () => ...` 类型的延迟计算，在选中的分支才强制 `Thunk α`。累积大输入时向表头加入元素再反转，避免循环 `xs ++ [x]`。用显式燃料或已访问集合遍历 DAG，另记活动路径以诊断环。

惰性语言中按需展开的无限结构，在 Lean 的普通构造器里会急切构造后继。会话与服务可表示成余代数的有限状态转移，每次输入产生一个观察和后继状态或退出码；`ReactiveApp.onStep` 正是这样的端口。用有限轨迹验证初始世界与每次转移。在 `mutual` 中沿构造器的直接子项递归，让各成员的结构参数对应到同一递减路径。若改用良基度量，以生成的方程引理改写，避免在 `rfl` 中强行展开整棵调用树。
