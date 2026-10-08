# 来源与版本

本仓库于 2026-10-08 从 `KataDavidXD/AAMAS27` 的当前 Windows 工作目录建立独立副本。原仓库 HEAD 为 `a61cf0957aa7cf74feff4e1258c732f872879445`；工作目录存在尚未提交的 Lean、导读与论文修改，因此该 HEAD 只标识来源基线，完整归档内容由本仓库首次提交保存。

| 内容 | 来源 / 版本 |
| --- | --- |
| Lean 数学源码、导读与审计入口 | AAMAS27 `theory/lean`，2026-10-08 工作目录 |
| 英文单文件生成器、源码扫描器、MCP batch 客户端 | AAMAS27 `theory/scripts` |
| 原始证明任务陈述 | AAMAS27 `theory/claims` |
| 证明背景 | AAMAS27 README 第 6 节，2026-10-08 快照 |
| 两份英文阅读 PDF | AAMAS27 `Agentic_Optimization/output/pdf/proof-reading-20261004`；2026-10-04 交付版，8 / 40 页；按用户要求省略中文 PDF |
| LaTeX 数学证明及相关输入 | AAMAS27 当前论文源，2026-10-08 工作目录；归档 PDF 保留其历史版 |
| 历史验证证据 | AAMAS27 `proof-guide-20261004`, `proof-guide-en-20261004`, `vscode-native-20261004`, `standalone-readers-20261004`，原始日志/JSON |
| 本仓库验证 | `evidence/verification-20261008`；实际编译输出及逐定理公理检查 |
| GitHub Linux CI | 2026-10-08，run `37733656335`，测试首次归档提交 `96e1206`；`evidence/ci-linux-20261008` 保存完整构建、公理与 PDF 检查证据 |
| Lean / Lake | `leanprover/lean4:v4.24.0` |
| mathlib | `v4.24.0`，Lake 锁定 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |
| Aesop | mathlib 的传递依赖，Lake 锁定 `725ac8cd67acd70a7beaf47c3725e23484c1ef50` |
| lean4-skills | 原项目已使用的 4.11.3，commit `b6243b85b9b0a0ddff5bb6773889044daf687f8e`；`vendor/lean4-skills` |
| lean-lsp-mcp | 原工作流使用的 0.30.0 / tag `v0.30.0`，commit `bb176c58a4f895061561685318e92b8db446f1b5`；`vendor/lean-lsp-mcp`，保留 `uv.lock` |

上述提交号是普通依赖和来源版本记录。运行不增加实验 fingerprint、SHA 或源字节准入检查。

历史 JSON/log 中的原 Windows / WSL 路径属于当时执行记录；本仓库复现入口见 `WORKFLOW.md`。旧 build target 数与旧图表不覆盖新验证结果。lean4-skills 的历史 `plugins/lean4/scripts` 符号链接保留在 Git 中；Windows 下运行使用上游 canonical `lib/scripts`。第三方源码保留其文件头、原许可证与引用信息，见 [第三方说明](THIRD_PARTY_NOTICES.md)。原研究材料未新增公共授权。
