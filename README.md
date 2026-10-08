# AgentUCT Lean Proofs

AgentUCT 的数学证明、Lean 源码和可复现证明工作流。仓库为 **GitHub 私密仓库**。

现有核心结果是：在固定有限终局树、固定训练奖励、成功持久发布和有界冷费用估计下，AgentUCT 的累计训练质量 regret 有 $O(\log T)$ 界；最佳已观察训练工作流的 simple gap 有 $O(\log T/T)$ 界。这里 $T$ 是完整评估次数，包括零新增冷费用的 cache replay。假设、常数与结论范围见 [证明背景与结果](BACKGROUND_AND_RESULTS.md)。

## 阅读入口

| 材料 | 内容 |
| --- | --- |
| [英文数学证明与形式验证 PDF](materials/pdf/AgentUCT_Proof_Sections_EN.pdf) | 8 页，独立编号的证明阅读版 |
| [英文完整补充材料 PDF](materials/pdf/AgentUCT_Supplement_Only_EN.pdf) | 40 页，含数学证明、附加推导及当时的实验材料 |
| [中文 Lean 导读](theory/lean/AgentUCTProofGuide.lean) / [英文导读](theory/lean/AgentUCTProofGuideEN.lean) | 每份 96 个声明引用，编译器显示完整类型 |
| [英文完整证明单文件](theory/lean/AgentUCTCompleteProofsEN.lean) | 全部 45 个数学源码模块的定义与证明体，按依赖顺序组织 |
| [模块化证明入口](theory/lean/AgentUCTPaper.lean) | 维护与编辑入口；原模块保留 |
| [证明工作流](WORKFLOW.md) | 安装、Lean 技能、LSP、tactics、编译、公理检查及 CI |
| [验证记录](evidence/verification-20261008/verification.json) | 本仓库副本的实际构建与公理检查结果 |
| [来源与版本](PROVENANCE.md) | AAMAS27 工作目录快照、PDF 日期、工具版本及许可证 |

PDF 仅收录两份英文 **2026-10-04 独立阅读版**。本仓库的 Lean 与 LaTeX 源码来自 **2026-10-08 当前工作目录**，包括尚未提交的证明导读和步骤注释。PDF 中的实验表与 `M.` / `S.` 外部引用对应当时版本。当前理论结果以源码和本仓库的新验证记录为准。

## 复现

先安装 [elan](https://github.com/leanprover/elan)，并让 `lean`、`lake` 在 PATH 中。仓库保留 `lean-toolchain` 与 `lake-manifest.json`。

```sh
git clone https://github.com/KataDavidXD/AgentUCT-Lean-Proofs.git
cd AgentUCT-Lean-Proofs
python scripts/verify_proofs.py --bootstrap
```

`--bootstrap` 下载所需 mathlib 编译缓存；已有环境可直接运行 `python scripts/verify_proofs.py`。验证覆盖默认构建、额外审计入口，以及模块版和英文单文件版每个公开定理的公理依赖。证明验证只需要 Python 标准库与 Lean/Lake。

工具栈固定为 **Lean 4.24.0 + mathlib v4.24.0 + lean4-skills 4.11.3 + lean-lsp-mcp 0.30.0**。Aesop 是 mathlib 的锁定依赖；`simp`、`ring`、`linarith`、`nlinarith`、`omega` 等按目标使用。Lean 内核检查最终证明项，技能和 MCP 帮助编写与诊断。

2026-10-08 本仓库副本验证通过：56 个 Lean 源文件、模块版与英文单文件版各 385 个公开定理公理检查、中英文导读各 96 个引用、Aesop/算术 tactics 示例；无证明占位、非标准公理或编译 error/warning。MCP 初始化、真实文件诊断、目标状态及一个定理的公理检查通过。首次客户端兼容问题及修正单独保留；Windows MCP 退出后观察到 Python pipe cleanup 的 ignored 异常，协议检查和进程 exit 0 的结果分别记录。

`vendor/` 保存 lean4-skills 与 lean-lsp-mcp 的完整固定版本源码及原许可证。mathlib 与 Aesop 由 Lake 锁定和获取；它们的编译缓存、模型权重与运行环境不进入 Git。
