from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


PACKAGE_ROOT = Path(__file__).resolve().parents[2]
SCRIPT_DIR = Path(__file__).resolve().parent
DECL_RE = re.compile(r"^\s*(theorem|lemma|example)\s+(\S+)")


def safe_component(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", text).strip("._") or "unnamed"


def decl_line_re(name: str) -> re.Pattern[str]:
    return re.compile(rf"^\s*(theorem|lemma|example)\s+{re.escape(name)}(?=$|[\s:\(\[])")


def normalize_decl_block(lines: list[str]) -> str:
    normalized = [line.rstrip(" \t\r") for line in lines]
    while normalized and not normalized[0].strip():
        normalized.pop(0)
    while normalized and not normalized[-1].strip():
        normalized.pop()
    return "\n".join(normalized)


def find_decl_block(source_file: Path, name: str) -> dict[str, object]:
    lines = source_file.read_text(encoding="utf-8").splitlines()
    start: int | None = None
    kind = ""
    pattern = decl_line_re(name)
    for idx, line in enumerate(lines):
        match = pattern.match(line)
        if match is None:
            continue
        start = idx
        kind = match.group(1)
        break
    if start is None:
        raise ValueError(f"declaration not found in {source_file}: {name}")

    end = len(lines)
    for idx in range(start + 1, len(lines)):
        stripped = lines[idx].lstrip()
        if DECL_RE.match(lines[idx]) or stripped.startswith("#proof_blueprint"):
            end = idx
            break

    normalized = normalize_decl_block(lines[start:end])
    digest = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
    return {
        "kind": kind,
        "start_line": start + 1,
        "end_line": end,
        "normalized_source": normalized,
        "hash": digest,
        "hash_dir": digest[:16],
    }


def resolve_source_path(path: Path) -> Path:
    if path.is_absolute():
        return path.resolve()
    candidates = [Path.cwd() / path, PACKAGE_ROOT / path]
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    return candidates[0].resolve()


def resolve_project_path(path: Path, project_root: Path) -> Path:
    if path.is_absolute():
        return path.resolve()
    return (project_root / path).resolve()


def find_lake_root(path: Path) -> Path | None:
    current = path.resolve()
    if current.is_file():
        current = current.parent
    for directory in (current, *current.parents):
        if (directory / "lakefile.toml").exists() or (directory / "lakefile.lean").exists():
            return directory
    return None


def run(cmd: list[str], *, cwd: Path) -> None:
    print("$", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def discover_theorems(source_file: Path) -> list[str]:
    names: list[str] = []
    for line in source_file.read_text(encoding="utf-8").splitlines():
        match = DECL_RE.match(line)
        if match is None:
            continue
        name = match.group(2).strip()
        if name not in names:
            names.append(name)
    return names


def load_manifest(path: Path, *, dataset: str, theorem: str, source_file: Path) -> dict[str, object]:
    if path.exists():
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                versions = data.get("versions")
                if isinstance(versions, list):
                    return data
        except json.JSONDecodeError:
            pass
    return {
        "schema_version": "proofstruct-output-manifest-v1",
        "dataset": dataset,
        "declaration": theorem,
        "source_file": str(source_file),
        "versions": [],
    }


def write_manifest(path: Path, manifest: dict[str, object], entry: dict[str, object]) -> None:
    versions = manifest.get("versions")
    if not isinstance(versions, list):
        versions = []
    versions = [item for item in versions if not (
        isinstance(item, dict) and item.get("hash") == entry["hash"]
    )]
    versions.append(entry)
    manifest["versions"] = versions
    manifest["latest_hash"] = entry["hash"]
    manifest["latest_hash_dir"] = entry["hash_dir"]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract ProofStruct blueprint JSON files.")
    parser.add_argument("--file", type=Path, default=PACKAGE_ROOT / "examples" / "example.lean")
    parser.add_argument(
        "--project-root",
        type=Path,
        help="Lake project that owns the Lean source. Defaults to the nearest lakefile ancestor.",
    )
    parser.add_argument("--theorem", action="append", dest="theorems")
    parser.add_argument(
        "--dataset",
        help="Dataset output name. Defaults to the Lean file stem, e.g. example for example.lean.",
    )
    parser.add_argument("--output-root", type=Path)
    parser.add_argument("--english", action="store_true", help="Generate english.layered.json.")
    parser.add_argument("--english-fallback-only", action="store_true")
    parser.add_argument("--english-require-llm", action="store_true")
    parser.add_argument(
        "--english-evidence-mode",
        choices=["none", "objects", "all"],
        default="objects",
    )
    parser.add_argument("--english-plan-batch-size", type=int, default=5)
    parser.add_argument("--english-evidence-batch-size", type=int, default=8)
    parser.add_argument("--english-config", type=Path)
    args = parser.parse_args()

    source_file = resolve_source_path(args.file)
    project_root = (
        resolve_source_path(args.project_root)
        if args.project_root
        else find_lake_root(source_file) or Path.cwd().resolve()
    )
    output_root = (
        resolve_project_path(args.output_root, project_root)
        if args.output_root
        else project_root / "output"
    )
    dataset = safe_component(args.dataset or source_file.stem)
    dataset_root = output_root / dataset
    if args.english_config:
        english_config = resolve_project_path(args.english_config, project_root)
    elif (project_root / "proofstruct_config.toml").exists():
        english_config = project_root / "proofstruct_config.toml"
    else:
        english_config = PACKAGE_ROOT / "proofstruct_config.toml"

    theorem_names = args.theorems or discover_theorems(source_file)
    if not theorem_names:
        parser.error(f"no theorem/lemma/example declarations found in {source_file}")

    for theorem in theorem_names:
        theorem_info = find_decl_block(source_file, theorem)
        theorem_root = dataset_root / safe_component(theorem)
        manifest_path = theorem_root / "manifest.json"
        theorem_dir = theorem_root / str(theorem_info["hash_dir"])
        theorem_dir.mkdir(parents=True, exist_ok=True)
        json_path = theorem_dir / "formal.evidence.json"
        layered_json_path = theorem_dir / "formal.layered.json"

        run(
            [
                "lake",
                "exe",
                "@ProofStruct/extract_layered_blueprint",
                "--",
                "--file",
                str(source_file),
                "--theorem",
                theorem,
                "--output",
                str(layered_json_path),
                "--blueprint-output",
                str(json_path),
            ],
            cwd=project_root,
        )

        if args.english:
            english_json_path = theorem_dir / "english.layered.json"
            english_cmd = [
                sys.executable,
                str(SCRIPT_DIR / "english_blueprint.py"),
                "--formal",
                str(layered_json_path),
                "--output",
                str(english_json_path),
                "--config",
                str(english_config),
                "--plan-batch-size",
                str(args.english_plan_batch_size),
                "--evidence-mode",
                args.english_evidence_mode,
                "--evidence-batch-size",
                str(args.english_evidence_batch_size),
            ]
            if args.english_fallback_only:
                english_cmd.append("--fallback-only")
            if args.english_require_llm:
                english_cmd.append("--require-llm")
            run(english_cmd, cwd=project_root)
            run(
                [
                    sys.executable,
                    str(SCRIPT_DIR / "english_blueprint.py"),
                    "--validate",
                    "--formal",
                    str(layered_json_path),
                    "--english",
                    str(english_json_path),
                ],
                cwd=project_root,
            )

        entry = {
            "hash": theorem_info["hash"],
            "hash_dir": theorem_info["hash_dir"],
            "declaration_kind": theorem_info["kind"],
            "source_file": str(source_file),
            "source_start_line": theorem_info["start_line"],
            "source_end_line": theorem_info["end_line"],
            "normalized_source": theorem_info["normalized_source"],
            "formal_evidence": f"{theorem_info['hash_dir']}/formal.evidence.json",
            "formal_layered": f"{theorem_info['hash_dir']}/formal.layered.json",
            "english_layered": f"{theorem_info['hash_dir']}/english.layered.json",
            "generated_at": datetime.now(timezone.utc).isoformat(),
        }
        manifest = load_manifest(
            manifest_path,
            dataset=dataset,
            theorem=theorem,
            source_file=source_file,
        )
        write_manifest(manifest_path, manifest, entry)


if __name__ == "__main__":
    main()
