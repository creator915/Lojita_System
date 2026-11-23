# Lojita · 纯 Lean 4 范畴程序设计系统

Lojita 从参考程序的可观察行为出发，在 Lean 4 中建立规约、验证实现，并交付静态可执行文件。一个会话可以先观察「输入哪些字节、退出码是什么」，再把观测写成所有输入都应满足的定律。孩子节点各自实现其规约。根节点只有在构建、差分回放和整树重审通过后才能结束会话。[English](docs/README_EN.md)

## 构建与验收

在 Linux 上使用 `lean-toolchain` 指定的 Lean 4.36.0、Lake、C 工具链以及支持静态链接的系统库（含 OpenSSL）。测试使用 Python 3.11+ 和 Git。运行下面的命令即可构建 Lean 宿主和五个静态 C relay，并检查内核、证明及导入边界。

```sh
export LC_ALL=C.UTF-8 LANG=C.UTF-8
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
./build.sh
./test-all.sh
```

`./test-all.sh` 在白名单 PATH 上运行基础库、内核、Harness、提示词和会话测试。提示词中的多子包示例也会编译成真正的 CLI 并核对字节输出。`./test-live-e2e.sh` 使用已登录的 Codex 和本地 Docker。它对已安装的 gron 镜像核对两次真实运行，随后让托管模型独立完成字节流过滤器的规约、实现、构建与差分回放。[会话指南](docs/SESSIONS.md)

## 模块边界

| 层 | 职责 |
| --- | --- |
| `LojitaCtx` | 对象语言的纯函数、行为模型与定律。用 `CliApp` 和 `SimWorld` 描述同一入口的原生执行和可证明的观察量。 |
| `Lojita.Ownership` | 通过资源状态索引的 `Prog` 和会话类型约束目录、通道与线性资源。服务按请求推进状态，并显式归还所有权。 |
| `Lojita.Kernel` | 用 Lean 自己的解析器从源码切片，经内核得到 `SemGraph`。驻留模块映像供下一次检查复用。LCNF 后端从已验证环境生成 C。 |
| `Lojita.Transport` 和 `Lojita.Harness` | 用二维虚拟设备组织纵向提升与横向重构。每个节点检查端点、依赖前沿、孩子接口和交换方块。 |
| `Lojita.Session`、`Lojita.MCP` 和 `Lojita.Store` | 探测参考程序，管理 durable/scratch 线程、驻留检查、封存树和回放收据。热态 MCP 的小模块检查以中位延迟低于 60 ms 为验收指标。 |

架构文档从源码声明跟踪到静态 ELF，设计原则说明何种行为应当成为孩子的公开定律。[架构](docs/PURE_LEAN4_ARCHITECTURE.md) · [设计原则](docs/MANIFESTO.md)
