from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
from contextlib import nullcontext
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from safety import (
    ProofStructSafetyGuard,
    SafetyError,
    apply_safety_overrides,
    load_instant_safety_config,
)


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


def run(cmd: list[str], *, cwd: Path, timeout_seconds: int | None = None) -> None:
    print("$", " ".join(cmd), flush=True)
    process = subprocess.Popen(cmd, cwd=cwd, start_new_session=True)
    try:
        return_code = process.wait(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait(timeout=5)
        except (ProcessLookupError, subprocess.TimeoutExpired):
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
        raise
    if return_code != 0:
        raise subprocess.CalledProcessError(return_code, cmd)


def temp_output_path(path: Path) -> Path:
    return path.with_name(f"{path.name}.tmp.{os.getpid()}")


def cleanup_temp_paths(paths: list[Path]) -> None:
    for path in paths:
        try:
            path.unlink(missing_ok=True)
        except OSError:
            pass


def replace_temp_output(temp_path: Path, final_path: Path) -> None:
    if not temp_path.exists():
        raise FileNotFoundError(f"expected temporary output was not created: {temp_path}")
    final_path.parent.mkdir(parents=True, exist_ok=True)
    temp_path.replace(final_path)


def write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp_path = temp_output_path(path)
    temp_path.write_text(text, encoding="utf-8")
    temp_path.replace(path)


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
    write_text_atomic(path, json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")


def output_item_value(item: dict[str, Any], key: str) -> Path:
    value = item[key]
    if not isinstance(value, Path):
        raise TypeError(f"expected Path for item[{key!r}], got {type(value).__name__}")
    return value


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
    parser.add_argument(
        "--english-only",
        action="store_true",
        help="Generate English JSON from existing formal.layered.json without running the Lean extractor.",
    )
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
    parser.add_argument(
        "--safe",
        action="store_true",
        help="Enable ProofStruct safety guard: lock, memory/process checks, and subprocess timeout.",
    )
    parser.add_argument(
        "--safe-config",
        type=Path,
        help="TOML config path for [instant] safety settings. Defaults to proofstruct_config.toml.",
    )
    parser.add_argument("--safe-max-lean-processes", type=int)
    parser.add_argument("--safe-min-available-memory-gb", type=float)
    parser.add_argument("--safe-timeout-seconds", type=int)
    parser.add_argument("--safe-lock-wait-seconds", type=int)
    args = parser.parse_args()
    if args.english_only and not args.english:
        parser.error("--english-only requires --english")

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
    if args.safe_config:
        safety_config_path = resolve_project_path(args.safe_config, project_root)
    elif (project_root / "proofstruct_config.toml").exists():
        safety_config_path = project_root / "proofstruct_config.toml"
    else:
        safety_config_path = PACKAGE_ROOT / "proofstruct_config.toml"
    safety_config = apply_safety_overrides(
        load_instant_safety_config(safety_config_path),
        max_lean_processes=args.safe_max_lean_processes,
        min_available_memory_gb=args.safe_min_available_memory_gb,
        timeout_seconds=args.safe_timeout_seconds,
        lock_wait_seconds=args.safe_lock_wait_seconds,
    )
    timeout_seconds = safety_config.timeout_seconds if args.safe else None

    theorem_names = args.theorems or discover_theorems(source_file)
    if not theorem_names:
        parser.error(f"no theorem/lemma/example declarations found in {source_file}")

    items = []
    temp_paths: list[Path] = []
    for theorem in theorem_names:
        theorem_info = find_decl_block(source_file, theorem)
        theorem_root = dataset_root / safe_component(theorem)
        manifest_path = theorem_root / "manifest.json"
        theorem_dir = theorem_root / str(theorem_info["hash_dir"])
        theorem_dir.mkdir(parents=True, exist_ok=True)
        json_path = theorem_dir / "formal.evidence.json"
        layered_json_path = theorem_dir / "formal.layered.json"
        json_temp_path = temp_output_path(json_path)
        layered_temp_path = temp_output_path(layered_json_path)
        temp_paths.extend([json_temp_path, layered_temp_path])
        items.append(
            {
                "theorem": theorem,
                "theorem_info": theorem_info,
                "manifest_path": manifest_path,
                "theorem_dir": theorem_dir,
                "json_path": json_path,
                "json_temp_path": json_temp_path,
                "layered_json_path": layered_json_path,
                "layered_temp_path": layered_temp_path,
            }
        )
    cleanup_temp_paths(temp_paths)

    guard = (
        ProofStructSafetyGuard(output_root=output_root, config=safety_config)
        if args.safe
        else nullcontext()
    )
    try:
        with guard:
            if args.safe:
                print(
                    "ProofStruct safety guard enabled: "
                    f"max_lean_processes={safety_config.max_lean_processes}, "
                    f"min_available_memory_gb={safety_config.min_available_memory_gb}, "
                    f"timeout_seconds={safety_config.timeout_seconds}, "
                    f"lock_wait_seconds={safety_config.lock_wait_seconds}",
                    flush=True,
                )

            if args.english_only:
                missing_formal = [
                    str(output_item_value(item, "layered_json_path"))
                    for item in items
                    if not output_item_value(item, "layered_json_path").exists()
                ]
                if missing_formal:
                    raise FileNotFoundError(
                        "formal layered JSON is required for --english-only:\n"
                        + "\n".join(missing_formal)
                    )
            else:
                if len(items) == 1:
                    item = items[0]
                    run(
                        [
                            "lake",
                            "exe",
                            "@ProofStruct/extract_layered_blueprint",
                            "--",
                            "--file",
                            str(source_file),
                            "--theorem",
                            str(item["theorem"]),
                            "--output",
                            str(item["layered_temp_path"]),
                            "--blueprint-output",
                            str(item["json_temp_path"]),
                        ],
                        cwd=project_root,
                        timeout_seconds=timeout_seconds,
                    )
                else:
                    file_cmd = [
                        "lake",
                        "exe",
                        "@ProofStruct/extract_file_blueprints",
                        "--",
                        "--file",
                        str(source_file),
                    ]
                    for item in items:
                        file_cmd.extend(
                            [
                                "--theorem",
                                str(item["theorem"]),
                                "--output",
                                str(item["layered_temp_path"]),
                                "--blueprint-output",
                                str(item["json_temp_path"]),
                            ]
                        )
                    run(file_cmd, cwd=project_root, timeout_seconds=timeout_seconds)

                for item in items:
                    replace_temp_output(
                        output_item_value(item, "layered_temp_path"),
                        output_item_value(item, "layered_json_path"),
                    )
                    replace_temp_output(
                        output_item_value(item, "json_temp_path"),
                        output_item_value(item, "json_path"),
                    )

            for item in items:
                theorem = str(item["theorem"])
                theorem_info = item["theorem_info"]
                manifest_path = output_item_value(item, "manifest_path")
                theorem_dir = output_item_value(item, "theorem_dir")
                layered_json_path = output_item_value(item, "layered_json_path")

                if args.english:
                    english_json_path = theorem_dir / "english.layered.json"
                    english_temp_path = temp_output_path(english_json_path)
                    temp_paths.append(english_temp_path)
                    cleanup_temp_paths([english_temp_path])
                    english_cmd = [
                        sys.executable,
                        str(SCRIPT_DIR / "english_blueprint.py"),
                        "--formal",
                        str(layered_json_path),
                        "--output",
                        str(english_temp_path),
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
                    run(english_cmd, cwd=project_root, timeout_seconds=timeout_seconds)
                    run(
                        [
                            sys.executable,
                            str(SCRIPT_DIR / "english_blueprint.py"),
                            "--validate",
                            "--formal",
                            str(layered_json_path),
                            "--english",
                            str(english_temp_path),
                        ],
                        cwd=project_root,
                        timeout_seconds=timeout_seconds,
                    )
                    replace_temp_output(english_temp_path, english_json_path)

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
    except SafetyError as exc:
        cleanup_temp_paths(temp_paths)
        print(f"ProofStruct safety guard blocked extraction: {exc}", file=sys.stderr)
        raise SystemExit(2) from exc
    except subprocess.TimeoutExpired as exc:
        cleanup_temp_paths(temp_paths)
        print(
            "ProofStruct extraction timed out "
            f"after {exc.timeout} seconds. Try terminal batch extraction later.",
            file=sys.stderr,
        )
        raise SystemExit(124) from exc
    except BaseException:
        cleanup_temp_paths(temp_paths)
        raise


if __name__ == "__main__":
    main()
