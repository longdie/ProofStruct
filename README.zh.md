# ProofStruct

ProofStruct 是一个用于 Lean 4 的证明蓝图提取与 Infoview 可视化工具。它可以从 Lean
文件中提取结构化证明蓝图，并在 Lean Infoview 中展示证明的高层规划结构和底层证据结构。

英文文档见 [README.md](README.md)。

ProofStruct 是 [ProofAtlas](https://github.com/MathNetwork/ProofAtlas) 的子项目。当前仓库
把 ProofStruct 中已经可用的部分整理为独立 Lake package，方便 Lean 用户在自己的项目中以
本地依赖的方式测试。

## 环境要求

- 默认使用 Linux 环境。
- 通过 `elan` 安装 Lean。
- Lean toolchain：`leanprover/lean4:v4.30.0-rc2`。
- Python `>=3.12,<3.13`。

Lean 配置已经固定在 [lean-toolchain](lean-toolchain) 和 [lakefile.toml](lakefile.toml)
中。如果把 ProofStruct 接入其他 Lean 项目，需要先确认目标项目的 Lean 配置兼容。

## 安装

克隆仓库：

```bash
git clone https://github.com/longdie/ProofStruct.git
cd ProofStruct
```

创建 Python 环境：

```bash
conda env create -f environment.yml
conda activate proofstruct
```

也可以使用 venv：

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

构建 Lean package：

```bash
lake update
lake build ProofStruct
```

## 快速开始

为示例文件生成形式化证明蓝图 JSON：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

然后用 VS Code 和 Lean extension 打开 [examples/example.lean](examples/example.lean)。示例文件中包含
一个 lemma、两个 theorem，以及 Infoview 命令：

```lean
#proof_blueprint demo_fermat
```

把光标放到该命令上，即可在 Infoview 中查看证明蓝图。

## 两种证明蓝图构建方式

### 推荐方式：终端批处理

默认工作流是在终端生成 JSON，然后由 Infoview 读取生成文件：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

这是正常使用时的推荐方式，因为它不会在 VS Code Lean server 中运行证明蓝图提取。

如果只想处理单个声明：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --theorem demo_fermat
```

### 可选方式：Lean 中显式即时生成

ProofStruct 也提供显式 bang 命令：

```lean
#proof_blueprint! demo_fermat
#proof_blueprint_english! demo_fermat
```

这两个命令会从 Lean 中调用 Python 批处理脚本，并启用安全检查。它们适合临时生成某个缺失的小蓝图。

即时生成会在运行期间阻塞 Lean command elaboration。对于包含 Mathlib 的项目，建议机器内存大于
24GB 再使用 `#proof_blueprint!` 或 `#proof_blueprint_english!`。不建议并行运行多个蓝图提取任务。

即时命令需要能找到 Python executable。可以设置 `PROOFSTRUCT_PYTHON`，也可以在本地
`proofstruct_config.toml` 中配置：

```toml
[python]
executable = "/absolute/path/to/python"
```

`proofstruct_config.toml` 是本地配置，不应该提交到 GitHub。

## Infoview 命令

```lean
#proof_blueprint theorem_name
```

读取已有 JSON 并显示蓝图。它永远不会自动生成缺失 JSON。

```lean
#proof_blueprint! theorem_name
```

如果当前源码 hash 缺少 formal 蓝图，则生成 formal 蓝图，然后显示。

```lean
#proof_blueprint_english! theorem_name
```

先确保 formal 蓝图存在，再在需要时生成 English 蓝图，最后显示 Formal/English 视图。

## 可选英文证明蓝图

English 蓝图需要 OpenAI-compatible LLM endpoint。

创建本地配置文件：

```bash
cp proofstruct_config.example.toml proofstruct_config.toml
```

通过配置文件中的环境变量提供 API key，例如：

```bash
export PROOFSTRUCT_LLM_API_KEY=<your-api-key>
```

在终端同时生成 formal 和 English 蓝图：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --english
```

## 批处理常用参数

常用参数：

- `--file <path>`：要处理的 Lean 文件。
- `--project-root <path>`：目标 Lake 项目根目录。
- `--theorem <name>`：只处理指定声明；可以重复传入。
- `--output-root <path>`：输出根目录，默认是 `<project-root>/output`。
- `--dataset <name>`：输出 dataset 名，默认是 Lean 文件名去掉 `.lean`。
- `--english`：生成 `english.layered.json`。
- `--english-only`：基于已有 formal JSON 生成 English。
- `--safe`：启用文件锁、内存/进程检查、超时和日志。

安全守卫参数：

- `--safe-max-lean-processes <n>`
- `--safe-min-available-memory-gb <gb>`
- `--safe-timeout-seconds <seconds>`
- `--safe-lock-wait-seconds <seconds>`

English 参数：

- `--english-config <path>`
- `--english-evidence-mode none|objects|all`
- `--english-plan-batch-size <n>`
- `--english-evidence-batch-size <n>`
- `--english-require-llm`

## 输出结构

生成文件保存在目标项目中：

```text
output/<file-stem>/<declaration-name>/manifest.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.evidence.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.layered.json
output/<file-stem>/<declaration-name>/<source-hash>/english.layered.json
```

`<source-hash>` 是 normalized declaration source block 的 SHA-256 hash 前 16 位。如果 theorem
陈述或证明发生变化，hash 也会变化。因此即使 theorem 名字不变，`#proof_blueprint` 也不会误用旧蓝图。

## 作为本地 Lake Dependency 使用

如果想在已有 Lean 项目中使用 ProofStruct，可以在目标项目的 `lakefile.toml` 中加入：

```toml
[[require]]
name = "ProofStruct"
path = "../ProofStruct"
```

然后运行：

```bash
lake update
lake build ProofStruct
```

在 Lean 文件中：

```lean
import ProofStruct

theorem example_theorem : True := by
  trivial

#proof_blueprint example_theorem
```

在目标项目根目录生成 JSON：

```bash
conda run --no-capture-output -n proofstruct python /absolute/path/to/ProofStruct/scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file MyProject/MyFile.lean
```

## 常见问题

- 如果 `#proof_blueprint` 报告找不到 JSON，请先运行 `batch_extract.py`，或者使用
  `#proof_blueprint!`。
- 如果当前源码与 manifest 不匹配，请在修改 theorem 后重新运行提取。
- 如果即时生成找不到 Python，请设置 `PROOFSTRUCT_PYTHON`，或者在 `proofstruct_config.toml`
  中配置 `[python].executable`。
- 如果 Infoview 仍然显示旧 widget，可以重启 Lean server 或重新加载 VS Code。
- 证明蓝图提取可能消耗较多内存，不建议并行运行多个提取任务。

## 联系方式

如有问题、建议或合作意向，请联系：

```text
stju_dzn@sjtu.edu.cn
```

## License

本项目遵循 [LICENSE](LICENSE) 文件中的许可条款。
