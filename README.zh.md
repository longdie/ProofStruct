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

## 快速开始：复现 example.lean

仓库中提供了示例文件：

```text
examples/example.lean
```

在终端生成形式化证明蓝图 JSON。默认命令不需要 API key：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

然后用 VS Code 和 Lean extension 打开 [examples/example.lean](examples/example.lean)。该文件已经
导入 ProofStruct，并包含类似命令：

```lean
#proof_blueprint fermat_little_theorem_1
```

当对应 JSON 已经生成后，Lean Infoview 会展示该 theorem 的证明蓝图。如果还需要可选的英文显示层，
见 [可选英文证明蓝图](#可选英文证明蓝图)。

## 生成证明蓝图

推荐默认使用 Python 批处理，一次处理完整 Lean 文件。默认情况下，ProofStruct 只生成形式化 Lean
蓝图文件：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

如果只想处理单个声明：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --theorem fermat_little_theorem_1
```

如果在其他 Lean 项目中使用 ProofStruct，请在目标项目根目录运行：

```bash
conda run --no-capture-output -n proofstruct python /absolute/path/to/ProofStruct/scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file MyProject/MyFile.lean
```

默认输出结构为：

```text
output/<file-stem>/<declaration-name>/manifest.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.evidence.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.layered.json
```

`<source-hash>` 是 normalized declaration source block 的 SHA-256 hash 前 16 位。如果 theorem
陈述或证明发生变化，hash 也会变化。因此即使 theorem 名字不变，`#proof_blueprint` 也不会误用旧蓝图。

这个默认流程已经足够用于 Infoview 可视化。它不会调用大模型，也不需要
`proofstruct_config.toml` 或 API key。

## Infoview 使用

在 Lean 文件中导入 ProofStruct，并在声明之后调用命令：

```lean
import ProofStruct

theorem my_theorem : True := by
  trivial

#proof_blueprint my_theorem
```

`#proof_blueprint` 会读取：

```text
output/<file-stem>/<declaration-name>/manifest.json
```

然后抽取当前声明源码块，与 manifest 中的 `normalized_source` 匹配，再加载：

```text
output/<file-stem>/<declaration-name>/<source-hash>/formal.layered.json
```

如果当前源码和 manifest 不匹配，命令会报错并提示重新运行批处理脚本，而不会自动读取旧 hash
目录中的蓝图。

## 可选英文证明蓝图

ProofStruct 可以在形式化 Lean 蓝图之外，可选生成英文显示层。这个功能默认关闭，因为它需要
OpenAI-compatible LLM endpoint。只需要形式化 Lean 蓝图的用户可以完全跳过本节。

创建本地配置文件：

```bash
cp proofstruct_config.example.toml proofstruct_config.toml
```

通过配置文件中的环境变量提供 API key，例如：

```bash
export PROOFSTRUCT_LLM_API_KEY=<your-api-key>
```

添加 `--english` 即可同时生成形式化蓝图和英文蓝图：

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --english
```

生成的英文 JSON 与形式化 layered JSON 在同一目录：

```text
output/<file-stem>/<declaration-name>/<source-hash>/english.layered.json
```

当这个文件存在时，Infoview widget 会启用 Formal/English 切换。本地
`proofstruct_config.toml` 已被 `.gitignore` 忽略，不应该提交到 GitHub。

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

在打开 Infoview 前，需要先在目标项目根目录生成形式化 JSON：

```bash
conda run --no-capture-output -n proofstruct python /absolute/path/to/ProofStruct/scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file MyProject/MyFile.lean
```

如果还需要可选英文显示层，请先配置 `proofstruct_config.toml`，然后在同一条命令中加入
`--english`。

## 仓库结构

```text
ProofStruct/                 Lean library、extractor 和 Infoview command
scripts/ProofStruct/         Python 批处理和英文生成脚本
widget/                      Infoview 前端组件
prompts/                     英文蓝图提示词模板
examples/                    示例 Lean 文件
docs/                        开发文档，使用 package 时不是必需
```

`output/` 下的生成文件不会提交到 GitHub。

## 常见问题

- 如果 `#proof_blueprint` 报告找不到 JSON，请先运行 `batch_extract.py`。
- 如果 `#proof_blueprint` 报告当前源码与 manifest 不匹配，请在修改 theorem 后重新运行
  `batch_extract.py`。
- 如果第一次构建时意外开始大量编译 mathlib，请检查当前 Lean 配置是否与本 package 兼容。
- 如果 Infoview 仍然显示旧 widget，可以重启 Lean server 或重新加载 VS Code。
- 证明蓝图提取可能消耗较多内存，不建议同时并行运行多个蓝图提取任务。

## 联系方式

如有问题、建议或合作意向，请联系：

```text
stju_dzn@sjtu.edu.cn
```

## License

本项目遵循 [LICENSE](LICENSE) 文件中的许可条款。
