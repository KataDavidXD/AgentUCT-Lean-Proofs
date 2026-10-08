# Lean 证明工作流

## 固定工具栈

| 层 | 用途 | 版本与入口 |
| --- | --- | --- |
| Lean 4 / Lake | 编译、类型检查、项目依赖与内核证明检查 | 4.24.0，`theory/lean/lean-toolchain` |
| mathlib | 数学定义、引理与 tactics | v4.24.0，`lakefile.toml` / `lake-manifest.json` |
| Aesop | 自动搜索证明项 | mathlib 的锁定依赖；可以 `import Aesop` |
| lean4-skills | 读目标、搜索、证明循环、review 与 checkpoint 的工作规范 | 4.11.3，[SKILL.md](vendor/lean4-skills/plugins/lean4/skills/lean4/SKILL.md) |
| lean-lsp-mcp | 目标状态、诊断、hover、引理搜索及尝试 tactics | 0.30.0，[源码](vendor/lean-lsp-mcp)与锁定 Python 依赖 |

原 AgentUCT 源码主要用 `simp`、`ring`、`linarith`、`nlinarith`、`omega` 和显式中间目标。Aesop 可用；无需将已有证明改写成 Aesop 证明才能使用这套工作流。

## 从干净克隆开始

安装 elan，确认 `lean` 和 `lake` 位于 PATH；Python 3.11+。从仓库根目录执行：

```sh
python scripts/verify_proofs.py --bootstrap
```

脚本下载项目所需 mathlib 编译缓存，构建默认目标，编译额外 Audit 入口和示例，然后分别导入模块版/英文版，对全部公开 theorem/lemma 运行 `#print axioms`。报告拒绝证明占位或非标准公理；允许 `propext`、`Classical.choice`、`Quot.sound`。报告保存在当天 `evidence/verification-YYYYMMDD`。这些检查检查数学证明，不参与实验调用准入。

在 VS Code 中打开 `theory/lean`，安装 Lean 4 扩展，使用默认构建任务。导读里的 96 条绿色 `#check` 信息显示真实声明类型。编辑器使用哪个目录，就在该目录构建；WSL 编译产物不会更新 Windows 项目。

## 技能与 MCP

归档包含完整工具源码，启用方式按 [lean4-skills 安装说明](vendor/lean4-skills/INSTALLATION.md)选择 core skill、portable runtime 或宿主原生插件。core skill 只有指令与参考文档；命令、hooks 和 helper runtime 取决于安装方式。当前归档不会修改全局 Codex 配置。

在 Bash / WSL 中使用仓库自带的 portable helper runtime，可为当前 shell 设置：

```sh
export LEAN4_PLUGIN_ROOT="$PWD/vendor/lean4-skills/plugins/lean4"
export LEAN4_SCRIPTS="$LEAN4_PLUGIN_ROOT/lib/scripts"
export LEAN4_REFS="$LEAN4_PLUGIN_ROOT/skills/lean4/references"
export PATH="$LEAN4_PLUGIN_ROOT/bin:$PATH"
```

Windows Git 不自动保留 Unix 可执行位；WSL/Bash 如提示 permission denied，可为这些 wrapper 和 shell helper 设置执行权限。具体技能指令和各宿主的发现方式保留在上游文档中。

安装本仓库归档的 MCP 环境：

```sh
uv sync --project vendor/lean-lsp-mcp --frozen --no-dev --python 3.12
uv run --project vendor/lean-lsp-mcp --frozen --no-dev --python 3.12 lean-lsp-mcp --lean-project-path /absolute/path/AgentUCT-Lean-Proofs/theory/lean
```

MCP 客户端配置样例见 [mcp-config.example.json](workflow/mcp-config.example.json)。替换两个绝对路径后导入客户端；进程通过 stdio 通信。若宿主支持 Codex TOML，可按相同 command/args 填写本地 MCP 项。项目根为 `theory/lean`。

可独立验证协议与实际文件诊断：

```sh
uv run --project vendor/lean-lsp-mcp --frozen --no-dev --python 3.12 python scripts/verify_mcp.py
```

这个检查初始化 MCP、读取实际文件诊断和 Lean goal，并检查一个已证明定理的公理。它不调用模型 API。额外语义搜索工具可能连接其各自上游搜索服务。

## 一次证明任务

1. 固定数学目标、量词、假设和交付范围；读声明冒号前后的内容。
2. 用 `lean_goal` / `lean_diagnostic_messages` 读取当前文件状态，搜索已有 mathlib 引理。
3. 用 `have`、`calc`、`rw`、`apply` 写出中间推导，按目标选择 tactics。常见顺序为 `rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → grind → aesop`。
4. 用 `lean_multi_attempt` 做局部尝试，检查当前文件诊断。跨模块修改后重建依赖，再检查文件。
5. 编辑模块化源码后运行 `python theory/scripts/build_english_proof_bundle.py`，更新英文阅读单文件；导入模块版或英文单文件版其中一个。
6. 在交付 checkpoint 执行 `python scripts/verify_proofs.py`。核对显式假设、无占位、公理依赖和数学源到文稿的对应。

引导式 `prove` 与自主 `autoprove` 的循环策略见上游技能；是否自动循环依用户指令和具体宿主能力。原有声明与 docstring 保持其契约，数学假设变更要明确记录。

## PDF 与证据

`materials/pdf` 保留已经独立编译和全页渲染验收的 2026-10-04 阅读版；`materials/latex` 保存 2026-10-08 当前相关数学源。两个时间点分别标明。修改文稿后独立编译，重置本地编号，解析外部引用，再渲染全部页面检查文字、公式、表格和字体。

PDF 结构检查可用 `python scripts/verify_pdfs.py`，需要 pypdf。原 PDF layout/编译/字体记录在 `evidence/historical`。本轮渲染与结构记录在 `evidence/verification-20261008`。

GitHub Actions 在 push / PR / 手动 dispatch 时运行 Lean 构建与全部公开定理公理检查，并上传当次证据。私密仓库内的 workflow 不发布 Pages 或公开论文。
