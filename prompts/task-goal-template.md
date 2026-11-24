# 任务目标

为「目标程序」实现纯 Lean 4 替代程序。填写输入域、输出、错误、可见副作用及必须覆盖的边界情形。以 reference.sexp 指定的参考程序为观察对象，交付经内核验证的静态 bin/candidate。

立规约前，SESSION_ROOT 必须先在 `run_lean_script` 中写出可执行的纯规格预言机。用 SessionEnv 内置的 `LojitaCtx.FuzzGen` 固定种子、批量生成字节、行或操作序列，逐样本做 Spec-vs-Ref 预对拍。按任务组合终端、文件系统、网络、Git 与 Web 工具，记录夹具、输入、超时、输出字节、错误流、退出状态及副作用。复测并收缩反例，修正规格，再用相同种子重跑并二分核对边界。只有样本集与边界观察全部吻合，才把规格写入 `specSrc` 并提交语义层 `drive-tree`。

纵轴用 `drive-tree` 从有限可判定的 T0 蓝图开始，每一层都是整个目标程序的完整所有权树。SESSION_ROOT 只编写各层根模块规约 `Gen.<Ti>.<Root>`，给出端口投影与行为定律。最终根公开 `CliApp Δ` 或 `ReactiveApp Δ S` 以及 `∀ w : SimWorld` 的观察律。T0 的 `baseTrees` 为空。每个精化层只指定唯一的直接前驱，并附根到根的 `maybeLiftSrc`，可补充关系方块 `maybeTransportSrc`，也可由根到根的 transport 单独承担精化。禁止将内部子系统拆成外层树再自底向上拼装。

横轴由封闭节点在自己的 `HomeSt` 中按孩子 `import` 自顶向下分包。父节点给每个独占槽提交 `subspecs`，内核先用孩子的抽象 `axiom` 检查条件胶水，再让各孩子独立选算法、实现或继续拆出孙包。跨层时用 `LiftSpec` 第三项 `child-map` 将底树的 import 子包路由到上层对应槽，上层可自由增加新子包。

列明最终入口与回放用例。用 `build-exe` 从入口所属封存树及其前驱链生成候选程序，在相同种子、输入和初始条件下对称回放 `ref` 与 `cand`，核验宿主胶水层。宿主边界偏差走同层 Transport 原位重驱或 `(replaces ...)` 加 `(keep ...)`。取得本次构建的回放收据后再提交 `finish`，由宿主重审整树和收据。
