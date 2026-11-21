# 模型原生 Harness 提示头目录（`prompts/headers/`）

说明：
1. **接入原生 CLI Agent（如 `codex cli`）时**：CLI 工具自身已内置与该模型版本精确匹配的官方 Harness 系统头。此时 `PromptHeader` 置空，只发送 `prompts/session-open-world.md` 或 `prompts/node-closed-world.md` 组装出的角色任务提示词，避免双重系统提示头冲突。
2. **通过 `RawHTTPBackend` 直连裸大模型 API 时**：按模型标识在此目录下放置对应厂商同版本的原生 Harness 头部模板（与通用角色任务提示词解耦维护），自动前置拼接以对齐模型的强化学习分布。
