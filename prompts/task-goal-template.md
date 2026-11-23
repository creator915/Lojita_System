# 任务目标

为「目标程序」实现纯 Lean 4 替代程序。填写输入域、输出、错误、可见副作用及必须覆盖的边界情形。以 reference.sexp 指定的参考程序为观察对象，交付经内核验证的静态 bin/candidate。

SESSION_ROOT 先用 SessionEnv 记录最小可复现观察，再按需要组合终端、文件系统、网络、Git 与 Web 工具。记录夹具、输入、超时、输出字节、错误流与退出状态。用确定性种子复现并缩小分歧。

纵轴用 `drive-tree` 从有限可判定的 T0 蓝图开始，每一层都是整个目标程序的完整所有权树。SESSION_ROOT 只编写各层根模块规约 `Gen.<Ti>.<Root>`，给出端口投影与行为定律。最终根公开 `CliApp Δ` 或 `ReactiveApp Δ S` 以及 `∀ w : SimWorld` 的观察律。T0 的 `baseTrees` 为空。每个精化层只指定唯一的直接前驱，并附根到根的 `maybeLiftSrc`，可补充关系方块 `maybeTransportSrc`，也可由根到根的 transport 单独承担精化。禁止将内部子系统拆成外层树再自底向上拼装。

横轴由封闭节点在自己的 `HomeSt` 中按孩子 `import` 自顶向下分包。父节点给每个独占槽提交 `subspecs`，内核先用孩子的抽象 `axiom` 检查条件胶水，再让各孩子独立选算法、实现或继续拆出孙包。跨层时用 `LiftSpec` 第三项 `child-map` 将底树的 import 子包路由到上层对应槽，上层可自由增加新子包。

列明最终入口与回放用例。用 build-exe 从入口所属封存树及其前驱链生成候选程序，在相同初始条件下对称运行 ref 和 cand。finish 的验收条件包括整树重审和与本次构建相符的回放收据。
