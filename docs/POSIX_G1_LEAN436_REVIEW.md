# G1 附录 · Lean 4.36.0 官方运行时依赖

本次审查使用项目提交 `1244b3989fb556be1a3c998268394721e4353039`。审查单位是**有来源模块、具体符号、具体用途的一项声明或替换**。同模块的其他声明、不同版本的同名声明、同一符号的新原生绑定都需要重新审查。[逐项清单](../Test/audit/lean-4.36.0-trust.tsv) · [受限调用的直接入边](../Test/audit/lean-4.36.0-parents.tsv)

## 版本和来源

`lean-toolchain` 指定 `leanprover/lean4:v4.36.0`。官方 Git 标签及 47 服务器 `lean --githash` 均返回 `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`。Linux x86_64 的官方发布资产 `lean-4.36.0-linux.tar.zst` 长 607,649,028 字节，发布页的 SHA-256 是 `2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb`。本轮独立比对了 38 个涉及声明、实现、替换证明或受限入边的官方源模块。服务器发行包中的这些源文件与该提交逐字节一致，发行包的 `include/lean/lean.h` 也与提交中的 `src/include/lean/lean.h` 一致，SHA-256 是 `dbccdab3a0036f41494f22762adce633875e34cf8f6f7cfa2186175b0e964aa4`。原生符号的实现定位使用固定提交中的 C/C++ 文件和头文件。软件版本字符串单独不能验证二进制来源。[官方发布](https://github.com/leanprover/lean4/releases/tag/v4.36.0) · [固定源码](https://github.com/leanprover/lean4/tree/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src)

## 清单如何阅读

| 核查范围 | extern | unsafe 实现 | lcProof 编译标记 | implemented_by 边 | csimp 等式边 |
|---|---:|---:|---:|---:|---:|
| 类型和定义依赖，加上注册的 implemented_by | 77 | 13 | 1 | 12 | 0 |
| 再跟踪注册的 csimp 目标和证明 | 91 | 17 | 1 | 14 | 28 |

第二行包含第一行。每个 TSV 行的 `scope` 表示所在范围，`module` 给出原声明真正的来源模块。`extern` 行给出完整外部绑定以及原生实现的源码位置。`implemented_by` 行固定实现名。`rewrite` 行固定目标及内核校验过的等式证明，并在说明列分别记录目标与证明的源模块。此处具体的 151 行只适用于本次输入。检查器仍需从实际环境枚举，拒绝缺项、错项以及新依赖。

另以全部受审声明为根，只递归跟踪常量类型与内核定义的原始依赖，得到的逻辑公理为 `propext`、`Quot.sound` 和 `Classical.choice`。该遍历没有抵达 `lcProof`、`unsafeCast` 或其他 unsafe 声明。直接依赖第三方或项目自定义公理仍应失败。表中 `artifact` 仅用于下述固定编译器路径，绝不扩充可用于证明的公理集合。

## 纯语义与原生信任点

| 家族 | 已核对的语义或约束 | 原生信任点 |
|---|---|---|
| Nat、Int | 加减乘、比较、按位运算，除法和余数的零除数约定，带符号 Euclidean 商余，幅值和构造器 | 小整数标记、越界后大整数表示和 GMP/运行时的算术正确性。超大输入可能触发资源诊断 |
| UInt、USize、Char | 对应位宽上的无符号运算，窄化及扩展，`Char.ofNatAux` 的合法标量前提，`UInt32.shiftRight` 按 32 约简位移量 | 运行时标量 ABI、截断和装箱。`System.Platform.getNumBits` 由 `sizeof(void*)` 决定，47 上为 64，不查询环境或设备 |
| Array、ByteArray | 列表顺序、长度、追加、空数组、已证明的边界和切片。字节缓冲与装箱数组间按元素转换 | 原生实现分配内存，利用引用计数复用独占缓冲。带证明的索引和 UTF-8 构造器依赖擦除前的类型前提 |
| String、hash、Repr | 分开核对 UTF-8 字节数、标量数、追加及遍历顺序。字符串使用长度传递，数据中的 NUL 可保留。`String.Internal.foldl` 对应固定 Lean 导出 `String.Internal.foldlImpl` | `String.hash`、`mixHash` 的精确值属于原生信任点；`lean_string_hash` 使用编码字节与固定种子 11。十进制 USize 格式化与缓存布局也是发行版实现 |
| List、递归与 Bool 的 csimp | 逐项核对函数、方向与等式证明。列表保留顺序、截断和短路行为；`Acc.recC`、`WellFounded.fixC` 等通过注册等式连接原语义 | 内核检查等式；编译器和机器码执行这些实现的正确性仍属可信计算基。大列表的右折叠可能转经数组 |
| 构造器编号、Lean.Name | 六个具体 `ctorIdx._impl` 只读取对应归纳类型的标签。五个 `Lean.Name` 覆盖分别处理 anonymous、str、num、casesOn 与已缓存 hash，模式分派跳过实现新增的 hash 字段 | 通用取标签和类型转换必须受直接调用边约束。Native Name 的字段顺序、缓存计算和 proof erasure 为原生假设 |

发行版原生代码可以分配、释放内存，并在内存不足时失败。`lean_nat_pow` 对超出本实现指数范围且底数至少为 2 的输入使用固定的内部诊断。`lean_nat_big_shiftr` 对超出实现范围且仍不足以移空数值的位移也保留固定的失败分支。它们的成功值仅由参数和固定 ABI 决定。这些边界不提供用户选择文件、网络地址、时钟、环境变量名或诊断正文的接口。[整数与平台原语](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/runtime/object.cpp) · [平台位宽](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/runtime/platform.cpp) · [容器与标量 ABI](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/include/lean/lean.h) · [UTF-8 遍历导出](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Init/Data/String/Iterate.lean)

## lcProof 和受限的诊断路径

`lcProof : {p : Prop} → p` 是发行版标记为 unsafe 的编译器公理。清单仅容许三条已复核的直接入边，并区分两种用途。

- `Lean.Name.{anonymous,str,num,casesOn,hash}._override → unsafeCast → unsafeCast._proof_1 → lcProof`。最后的声明为编译后无操作的表示转换构造一个擦除的类型等式。原始 `Name` 的逻辑表示可单独检查。一个实测入口是 `vfsSymlinkat.eq_1` 中的 `instLinearOrderPackageUInt8` 默认参数，经 `Std.Packages.PreorderOfLEArgs.le_refl._autoParam` 到 `Lean.Name.anonymous` 的原生覆盖。
- `Array.foldlM → Array.foldlMUnsafe → …fold → lcProof` 和对应的右折叠路径。两种内部循环先把端点限制在数组长度以内，分别递增至停止索引或递减后读取，再向 `Array.uget` 传入擦除的证明。检查了保留边界证明的参考 Lean 实现和两个 USize 循环的分支；`implemented_by` 本身不生成两者等价的内核定理。回调的行为取决于传入的函数和 monad；数组遍历不凭空赋予宿主 IO 能力。[核心标记及 Name 定义](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Init/Prelude.lean) · [前向和反向循环](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Init/Data/Array/Basic.lean)

`panicCore` 的 Lean 定义返回 `default`，其原生实现却可以写 stderr、读取回溯诊断开关，并按进程设置退出或中止。这项真实副作用单独审查。固定的向下链为 `panicWithPosWithDecl → panic → panicCore → lean_panic_fn_borrowed`。直接调用表还限制 `Option.get!`、`List.get!Internal`、树内部的不完全查询和不带平衡证明的旋转。普通受审项目定义不能把动态诊断文本送进这些入口。当前项目对 `balanceL!`、`balanceR!` 的直接引用均来自固定的 `Kernel.InsertMapping` 定理与方程证明；21 个被列作父项的项目声明全部是内核识别的定理。其中六个声明直接引用 `panicWithPosWithDecl`，包括两个 `map_bal` 证明及左右旋转各两个不平衡分支方程。工具链的旋转失败消息来自固定源码，正常树操作使用其不变量。这个审查不声称崩溃、资源用尽或破坏了运行时不变量后的宿主进程没有可观测副作用。[不平衡输入的定义](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Std/Data/DTreeMap/Internal/Balancing.lean) · [运行时诊断实现](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/runtime/object.cpp#L128-L207)

## 原生数据操作实验

附带的探针从运行时参数生成输入，核对跨 `2^64` 的算术、负整数商余、Unicode 和 NUL、数组装箱、树的插查删和含零洞的文件读写。驱动程序只在纯计算两侧打印标记。47 的 Linux x86_64 上，用 `strace -f` 观察所有线程，输入 `0`、`127`、`255`、`256`、`9223372036854775808` 全部通过；每次两个标记之间的系统调用数均为 0。这是对这些路径和输入的动态见证；通用行为仍依赖上述源码、证明与固定运行时。[探针源码](../Test/audit/Lean436DataProbe.lean)

在仓库根目录执行以下命令可复查对应的原生二进制和完整跟踪。

```sh
scratch=$(mktemp -d)
lake build LojitaCtx
lake env lean -c "$scratch/probe.c" Test/audit/Lean436DataProbe.lean
lake env leanc -O3 -o "$scratch/probe" "$scratch/probe.c" .lake/build/lib/liblojita_LojitaCtx.a
for n in 0 127 255 256 9223372036854775808; do
  strace -f -qq -o "$scratch/$n.trace" "$scratch/probe" "$n"
done
awk '/write\(1, "G1_REVIEW_BEGIN/{p=1;next}
     /write\(1, "G1_REVIEW_PASS/{p=0;next}
     p' "$scratch"/*.trace
```
