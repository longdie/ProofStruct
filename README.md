# ProofStruct

ProofStruct extracts structured proof blueprints from Lean 4 files and displays them in the Lean
Infoview.  It is designed for users who want to inspect the high-level plan and fine-grained
evidence of Lean proofs without modifying the Lean kernel or running expensive extraction inside
the editor.

Chinese documentation is available in [README.zh.md](README.zh.md).

ProofStruct is developed as a subproject of
[ProofAtlas](https://github.com/MathNetwork/ProofAtlas).  This standalone repository packages the
usable ProofStruct components as a local Lake dependency so that Lean users can test the tool in
their own projects.

## Requirements

- Linux environment.
- Lean via `elan`.
- Lean toolchain: `leanprover/lean4:v4.30.0-rc2`.
- Python `>=3.12,<3.13`.

The Lean configuration is pinned in [lean-toolchain](lean-toolchain) and
[lakefile.toml](lakefile.toml).  If you use ProofStruct inside another Lean project, first make sure
the target project can build with a compatible Lean setup.

## Installation

Clone the repository:

```bash
git clone https://github.com/longdie/ProofStruct.git
cd ProofStruct
```

Create the Python environment:

```bash
conda env create -f environment.yml
conda activate proofstruct
```

Alternatively:

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

Build the Lean package:

```bash
lake update
lake build ProofStruct
```

## Quick Start: Reproduce the Example

The repository contains a sample Lean file:

```text
examples/example.lean
```

Generate the formal blueprint JSON files from the terminal.  This default command does not require
an API key:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

Then open [examples/example.lean](examples/example.lean) in VS Code with the Lean extension.  The file
already imports ProofStruct and contains commands such as:

```lean
#proof_blueprint fermat_little_theorem_1
```

After the JSON files exist, the Lean Infoview will display the corresponding proof blueprint.  If
you also want the optional English display layer, see [Optional English Blueprints](#optional-english-blueprints).

## Generating Blueprints

The recommended workflow is to process a complete Lean file with the Python batch command.  By
default, ProofStruct generates only the formal Lean blueprint files:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

To process a single declaration:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --theorem fermat_little_theorem_1
```

For a target project outside this repository, run the script from the target project root:

```bash
conda run --no-capture-output -n proofstruct python /absolute/path/to/ProofStruct/scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file MyProject/MyFile.lean
```

The default output layout is:

```text
output/<file-stem>/<declaration-name>/manifest.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.evidence.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.layered.json
```

`<source-hash>` is the first 16 hex characters of the SHA-256 hash of the normalized declaration
source block.  If the declaration statement or proof changes, the hash changes as well.  This
prevents `#proof_blueprint` from showing stale data for a theorem whose name stayed the same.

This default workflow is enough for Infoview visualization.  It does not call an LLM and does not
require `proofstruct_config.toml` or an API key.

## Infoview Usage

In a Lean file, import ProofStruct and call the command after the declaration:

```lean
import ProofStruct

theorem my_theorem : True := by
  trivial

#proof_blueprint my_theorem
```

`#proof_blueprint` reads:

```text
output/<file-stem>/<declaration-name>/manifest.json
```

It extracts the current declaration source block, matches it against `normalized_source` in the
manifest, and then loads:

```text
output/<file-stem>/<declaration-name>/<source-hash>/formal.layered.json
```

If the current source no longer matches the manifest, the command reports an error and asks you to
rerun the batch extractor.  It will not silently fall back to an older blueprint.

## Optional English Blueprints

ProofStruct can optionally generate an English display layer in addition to the formal Lean
blueprint.  This feature is disabled by default because it requires an OpenAI-compatible LLM
endpoint.  Users who only want the formal Lean blueprint can skip this section entirely.

Create a local configuration file:

```bash
cp proofstruct_config.example.toml proofstruct_config.toml
```

Set your API key through the environment variable configured in `proofstruct_config.toml`, for
example:

```bash
export PROOFSTRUCT_LLM_API_KEY=<your-api-key>
```

Generate formal and English blueprints by adding `--english`:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --english
```

The generated English file is stored next to the formal layered JSON:

```text
output/<file-stem>/<declaration-name>/<source-hash>/english.layered.json
```

When this file exists, the Infoview widget enables Formal/English switching.  The local
`proofstruct_config.toml` file is ignored by Git and should not be committed.

## Use as a Local Lake Dependency

To use ProofStruct in an existing Lean project, add it as a local dependency in the target
project's `lakefile.toml`:

```toml
[[require]]
name = "ProofStruct"
path = "../ProofStruct"
```

Then run:

```bash
lake update
lake build ProofStruct
```

In your Lean file:

```lean
import ProofStruct

theorem example_theorem : True := by
  trivial

#proof_blueprint example_theorem
```

Before opening the blueprint in the Infoview, generate formal JSON from the target project root:

```bash
conda run --no-capture-output -n proofstruct python /absolute/path/to/ProofStruct/scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file MyProject/MyFile.lean
```

To also generate the optional English layer, use the same command with `--english` after configuring
`proofstruct_config.toml`.

## Repository Layout

```text
ProofStruct/                 Lean library, extractor, and Infoview command
scripts/ProofStruct/         Python batch extraction and English generation scripts
widget/                      Infoview front-end component
prompts/                     Prompt templates for English blueprint generation
examples/                    Example Lean file
docs/                        Development notes, not required for package use
```

Generated files under `output/` are ignored by Git.

## Troubleshooting

- If `#proof_blueprint` reports that JSON is missing, run `batch_extract.py` first.
- If `#proof_blueprint` reports that the current source does not match the manifest, rerun
  `batch_extract.py` after editing the theorem.
- If the first build is unexpectedly compiling a large part of mathlib, check that your Lean setup is
  compatible with this package.
- If the Infoview still shows an old widget, restart the Lean server or reload VS Code.
- Blueprint extraction may use substantial memory.  Avoid running multiple blueprint extraction jobs in parallel.


## Contact

For questions, feedback, or collaboration, please contact:

```text
stju_dzn@sjtu.edu.cn
```

## License

This project is released under the terms of the [LICENSE](LICENSE) file.
