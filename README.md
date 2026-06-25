# ProofStruct

ProofStruct extracts structured proof blueprints from Lean 4 files and displays them in the Lean
Infoview.  It is designed for users who want to inspect both the high-level proof plan and the
fine-grained proof evidence of Lean proofs.

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

## Quick Start

Generate formal blueprint JSON files for the example file:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

Then open [examples/example.lean](examples/example.lean) in VS Code with the Lean extension.  The
example contains a lemma, two theorems, and the Infoview command:

```lean
#proof_blueprint demo_fermat
```

Put the cursor on the command to view the proof blueprint in the Infoview.

## Two Ways to Build Blueprints

### Recommended: terminal batch extraction

The default workflow is to generate JSON from the terminal, then let Infoview read the generated
files:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean
```

This is the recommended mode for normal use because it does not run extraction inside the VS Code
Lean server.

To process a single declaration:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --theorem demo_fermat
```

### Optional: explicit instant generation from Lean

ProofStruct also provides explicit bang commands:

```lean
#proof_blueprint! demo_fermat
#proof_blueprint_english! demo_fermat
```

These commands call the Python batch script from Lean with safety checks enabled.  They are useful
when you want to generate a small missing blueprint without leaving the editor.

Instant generation blocks the Lean command elaboration while it runs.  For Mathlib projects, a
machine with more than 24GB of memory is recommended.  Avoid running multiple blueprint extraction
jobs in parallel.

For instant commands, configure the Python executable either through `PROOFSTRUCT_PYTHON` or through
a local `proofstruct_config.toml`:

```toml
[python]
executable = "/absolute/path/to/python"
```

`proofstruct_config.toml` is local configuration and should not be committed.

## Infoview Commands

```lean
#proof_blueprint theorem_name
```

Reads existing JSON and displays the blueprint.  It never generates missing JSON.

```lean
#proof_blueprint! theorem_name
```

Generates the formal blueprint if the current source hash is missing, then displays it.

```lean
#proof_blueprint_english! theorem_name
```

Ensures the formal blueprint exists, generates the English blueprint if needed, then displays
Formal/English views.

## Optional English Blueprints

English blueprints require an OpenAI-compatible LLM endpoint.

Create a local configuration file:

```bash
cp proofstruct_config.example.toml proofstruct_config.toml
```

Set your API key through the environment variable configured in `proofstruct_config.toml`, for
example:

```bash
export PROOFSTRUCT_LLM_API_KEY=<your-api-key>
```

Generate formal and English blueprints from the terminal:

```bash
conda run --no-capture-output -n proofstruct python scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file examples/example.lean \
  --english
```

## Batch Options

Common options:

- `--file <path>`: Lean file to process.
- `--project-root <path>`: Lake project root.
- `--theorem <name>`: process one declaration; can be repeated.
- `--output-root <path>`: output root, defaulting to `<project-root>/output`.
- `--dataset <name>`: output dataset name, defaulting to the Lean file stem.
- `--english`: generate `english.layered.json`.
- `--english-only`: generate English from existing formal JSON.
- `--safe`: enable lock, memory/process checks, timeout, and logs.

Safety overrides:

- `--safe-max-lean-processes <n>`
- `--safe-min-available-memory-gb <gb>`
- `--safe-timeout-seconds <seconds>`
- `--safe-lock-wait-seconds <seconds>`

English options:

- `--english-config <path>`
- `--english-evidence-mode none|objects|all`
- `--english-plan-batch-size <n>`
- `--english-evidence-batch-size <n>`
- `--english-require-llm`

## Output Layout

Generated files are written under the target project:

```text
output/<file-stem>/<declaration-name>/manifest.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.evidence.json
output/<file-stem>/<declaration-name>/<source-hash>/formal.layered.json
output/<file-stem>/<declaration-name>/<source-hash>/english.layered.json
```

`<source-hash>` is the first 16 hex characters of the SHA-256 hash of the normalized declaration
source block.  If the declaration statement or proof changes, the hash changes as well.  This
prevents `#proof_blueprint` from showing stale data for a theorem whose name stayed the same.

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

Generate JSON from the target project root:

```bash
conda run --no-capture-output -n proofstruct python /absolute/path/to/ProofStruct/scripts/ProofStruct/batch_extract.py \
  --project-root . \
  --file MyProject/MyFile.lean
```

## Troubleshooting

- If `#proof_blueprint` reports that JSON is missing, run `batch_extract.py` first or use
  `#proof_blueprint!`.
- If the current source does not match the manifest, rerun extraction after editing the theorem.
- If instant generation cannot find Python, set `PROOFSTRUCT_PYTHON` or configure
  `[python].executable` in `proofstruct_config.toml`.
- If the Infoview still shows an old widget, restart the Lean server or reload VS Code.
- Blueprint extraction can use substantial memory.  Do not run multiple extraction jobs in parallel.

## Contact

For questions, feedback, or collaboration, please contact:

```text
stju_dzn@sjtu.edu.cn
```

## License

This project is released under the terms of the [LICENSE](LICENSE) file.
