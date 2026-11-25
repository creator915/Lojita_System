# POSIX IO 分支验收记录

验证平台为 Ubuntu 24.04.5 LTS x86-64、Linux 6.8.0-147-generic、Lean 4.36.0。开发基线为 `feat/v9-pure-lean4` 的 `d0a052c3a3b0`。

| 门禁 | 在 47 服务器上的结果 |
| --- | --- |
| G1 严格纯度与代码体量 | 失败。2,643 个项目声明可达 8,204 个常量，含 83 个带 extern 的常量、17 个 unsafe 常量及编译器公理 lcProof。体量检查通过，系统调用桥 178/250 行，隔离器 300/300 行。 |
| G2 定理与回归 | T1–T17 的签名逐项通过 Lean 检查。另测半行继续读、软链局部性和环、mkdir 错误、打开后删除、共享与独立偏移、只读层、FD 耗尽、管道页槽、终端规范行与 VEOF。 |
| G3 Ubuntu 差分 | 种子 680024，2,000 条序列、54,790 步、2,000 个最终目录树哈希一致。共观察到 2,290 次 EINTR、773 次 EAGAIN、367 次 EPIPE、1,111 次短读、20 次短写。原生 ABI 另有直接的读写、路径、别名、轮询和时钟回归。 |
| G4 TreeCAS 与 LinuxIso | 在具备 CAP_SYS_ADMIN 的路径验证夹具只读、工作树导出、资源限额、孤儿和超时回收、CAS 篡改拒绝及挂载清理。资源限额使用有界申请验证。服务器对非特权 UID 映射返回 EPERM，该路径已验证会退出。 |
| G5 Lift | 对整读和 3 字节逐行读的精化关系进行了证明。经封存入口检查与静态链接，在 LinuxIso 中逐字节比较二进制、空、未以换行结尾及跨观察深度的输入。另验证非 UTF-8 命令行参数和错误能力集。 |

运行 `./test-io-all.sh` 可复验全部五项。脚本会继续运行后续门禁，并在任一门禁失败时返回非零。在无构建缓存的工作目录实测耗时 58 秒，在已有缓存的工作目录复测耗时 14 秒，两次退出码均为 1。单独复跑差分可用 `./test-g3-ubuntu-fuzz-conformance.sh --seed 680024`。发现偏差时，脚本会缩减序列并打印重放命令。

## G1 的具体依赖

检查器按定义模块枚举编译后环境，包括私有常量、自动生成的辅助定义、声明类型和实现，沿常量依赖以及 `implemented_by` 边遍历。输出列出各类别的命中名称及代表性链路。例如，`inodeWrite.eq_1` 可达带 extern 的 `ByteArray.mk`，`streamRead_eof_iff` 经 `List.ctorIdx` 可达 unsafe 的 `List.ctorIdx._impl`，`read_replaced` 经 `Array.foldlMUnsafe` 可达 `lcProof`。这些是锁定工具链的依赖。验收保留原文，所有命中均计入失败。

## Linux 行为与契约

- 长度不超过 4,096 字节的管道写入有原子性。仅剩 1 字节空间时，非阻塞写 2 字节得到 EAGAIN。先写满再读走 1 字节也可能仍占用全部页槽。差分覆盖部分读、短写、页尾追加以及 POLLOUT。
- T13 对所有仍有链接的 inode 比较目录结构、模式、链接数、软链目标及文件字节。关闭只读描述符会调整引用计数，最后一次关闭无名文件会回收 inode。
- T16 的成功条件包括成功打开、进展性读取和成功关闭。完成后逐个 FD 检查映射。FD 耗尽直接返回 EMFILE。T14 的两个行片段都不含换行；T15 允许有限次中断，并要求调度最终能读到 EOF 或写完。
- 只读挂载上，以 O_RDONLY | O_CREAT 打开既有文件可成功。创建缺失文件或截断既有文件会返回 EROFS。模型还按 Linux 的错误优先级处理 EEXIST、EBUSY 及管道定位 IO 的 ESPIPE。

## 入口与边界

新入口的类型是 `LojitaCtx.Posix.PosixProg LojitaCtx.Posix.CoreCaps UInt32`。会话可通过 `(build-exe ... (mode posix))` 构建，MCP `check_entry` 的 `mode` 填 `posix`。原有 cli 和 reactive 模式继续服务既有 World 类型的封存入口。

纯程序和解释器共用 `LojitaCtx.Io` 缓冲逻辑。宿主侧可信组件包含固定版 Lean 运行时、Linux 内核、libc、原生系统调用桥、静态启动包装、namespace/Landlock 启动器及以 Python 标准库实现的 TreeCAS 磁盘读写。TreeCAS 按字节处理文件名、链接目标与内容，拒绝无法保真表示的硬链接、特殊权限位与特殊节点。运行时保留 Linux 未命名的错误码。差分结论仅覆盖已执行的序列。
