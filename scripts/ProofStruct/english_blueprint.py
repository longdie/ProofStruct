from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import orjson


PACKAGE_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_CONFIG = PACKAGE_ROOT / "proofstruct_config.toml"
DEFAULT_PROMPT_DIR = PACKAGE_ROOT / "prompts"
DEFAULT_MODEL = "deepseek-v4-pro-202606"
DEFAULT_BASE_URL = "https://tokenhub.tencentmaas.com/v1"
DEFAULT_API_KEY_ENV = "PROOFSTRUCT_LLM_API_KEY"


def read_json(path: Path) -> dict[str, Any]:
    return orjson.loads(path.read_bytes())


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(orjson.dumps(data, option=orjson.OPT_INDENT_2 | orjson.OPT_APPEND_NEWLINE))


def stable_hash_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_hash_obj(data: Any) -> str:
    payload = orjson.dumps(data, option=orjson.OPT_SORT_KEYS)
    return stable_hash_bytes(payload)


def clean(text: Any) -> str:
    return re.sub(r"\s+", " ", str(text or "")).strip()


def short(text: Any, limit: int = 180) -> str:
    value = clean(text)
    if len(value) <= limit:
        return value
    return value[: max(1, limit - 3)] + "..."


def load_toml(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    try:
        import tomllib
    except ImportError:  # pragma: no cover - Python < 3.11 only
        import tomli as tomllib  # type: ignore[no-redef]
    return tomllib.loads(path.read_text(encoding="utf-8"))


@dataclass
class LlmConfig:
    model: str = DEFAULT_MODEL
    base_url: str = DEFAULT_BASE_URL
    api_key: str = ""
    api_key_env: str = DEFAULT_API_KEY_ENV
    timeout_seconds: float = 120
    max_completion_tokens: int = 4096
    temperature: float = 0.1

    @property
    def resolved_api_key(self) -> str:
        if self.api_key:
            return self.api_key
        if self.api_key_env:
            return os.environ.get(self.api_key_env, "")
        return ""


def llm_config_from_sources(args: argparse.Namespace) -> LlmConfig:
    config = load_toml(Path(args.config)) if args.config else {}
    llm = config.get("llm", {}) if isinstance(config, dict) else {}
    return LlmConfig(
        model=args.model or str(llm.get("model") or DEFAULT_MODEL),
        base_url=args.base_url or str(llm.get("base_url") or DEFAULT_BASE_URL),
        api_key=args.api_key or str(llm.get("api_key") or ""),
        api_key_env=args.api_key_env or str(llm.get("api_key_env") or DEFAULT_API_KEY_ENV),
        timeout_seconds=float(args.timeout_seconds or llm.get("timeout_seconds") or 120),
        max_completion_tokens=int(args.max_completion_tokens or llm.get("max_completion_tokens") or 4096),
        temperature=float(args.temperature if args.temperature is not None else llm.get("temperature", 0.1)),
    )


def read_prompt(prompt_dir: Path, name: str) -> str:
    path = prompt_dir / name
    if not path.exists():
        raise FileNotFoundError(f"prompt file not found: {path}")
    return path.read_text(encoding="utf-8")


def node_id_set(nodes: list[dict[str, Any]]) -> list[str]:
    return [str(node.get("id", "")) for node in nodes]


def edge_signature(edges: list[dict[str, Any]]) -> list[tuple[str, str, str]]:
    out = []
    for idx, edge in enumerate(edges):
        edge_id = str(edge.get("id") or f"e{idx + 1}")
        out.append((edge_id, str(edge.get("from", "")), str(edge.get("to", ""))))
    return out


def validate_english_blueprint(formal: dict[str, Any], english: dict[str, Any]) -> None:
    formal_plan = formal.get("plan_graph", {})
    english_plan = english.get("plan_graph", {})
    formal_evidence = formal.get("evidence_graph", {})
    english_evidence = english.get("evidence_graph", {})

    checks = [
        (
            node_id_set(formal_plan.get("nodes", [])),
            node_id_set(english_plan.get("nodes", [])),
            "plan node ids differ",
        ),
        (
            node_id_set(formal_evidence.get("nodes", [])),
            node_id_set(english_evidence.get("nodes", [])),
            "evidence node ids differ",
        ),
        (
            edge_signature(formal_plan.get("edges", [])),
            edge_signature(english_plan.get("edges", [])),
            "plan edge signatures differ",
        ),
        (
            edge_signature(formal_evidence.get("edges", [])),
            edge_signature(english_evidence.get("edges", [])),
            "evidence edge signatures differ",
        ),
    ]
    for expected, actual, message in checks:
        if expected != actual:
            raise ValueError(message)

    formal_mapping = formal.get("mapping", {})
    english_mapping = english.get("mapping", {})
    if formal_mapping != english_mapping:
        raise ValueError("mapping differs")

    for node in english_plan.get("nodes", []):
        if not clean(node.get("english_label")):
            raise ValueError(f"missing english_label for plan node {node.get('id')}")
    for node in english_evidence.get("nodes", []):
        if not clean(node.get("english_label")):
            raise ValueError(f"missing english_label for evidence node {node.get('id')}")


def summarize_plan_node(node: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": node.get("id", ""),
        "kind": node.get("kind", ""),
        "label": node.get("label", ""),
        "detail_label": node.get("detail_label", ""),
        "role_summary": node.get("role_summary", ""),
        "display_inputs": node.get("display_inputs", []),
        "display_outputs": node.get("display_outputs", []),
    }


def summarize_evidence_node(node: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": node.get("id", ""),
        "kind": node.get("kind", ""),
        "class": node.get("class", ""),
        "display_label": node.get("display_label") or node.get("label", ""),
        "display_type": node.get("display_type") or node.get("type", ""),
        "raw_text": short(node.get("raw_text", ""), 220),
    }


def incoming_outgoing(nodes: list[dict[str, Any]], edges: list[dict[str, Any]], node_id: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    by_id = {str(node.get("id", "")): node for node in nodes}
    incoming = []
    outgoing = []
    for edge in edges:
        if edge.get("to") == node_id and edge.get("from") in by_id:
            incoming.append(summarize_plan_node(by_id[edge["from"]]))
        if edge.get("from") == node_id and edge.get("to") in by_id:
            outgoing.append(summarize_plan_node(by_id[edge["to"]]))
    return incoming, outgoing


def evidence_incoming_outgoing(
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    node_id: str,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    by_id = {str(node.get("id", "")): node for node in nodes}
    incoming = []
    outgoing = []
    for edge in edges:
        if edge.get("to") == node_id and edge.get("from") in by_id:
            incoming.append(summarize_evidence_node(by_id[edge["from"]]))
        if edge.get("from") == node_id and edge.get("to") in by_id:
            outgoing.append(summarize_evidence_node(by_id[edge["to"]]))
    return incoming, outgoing


def contained_evidence_summary(formal: dict[str, Any], plan_node: dict[str, Any], limit: int = 18) -> list[dict[str, Any]]:
    evidence_nodes = formal.get("evidence_graph", {}).get("nodes", [])
    by_id = {str(node.get("id", "")): node for node in evidence_nodes}
    out = []
    for node_id in plan_node.get("evidence_node_ids", [])[:limit]:
        node = by_id.get(str(node_id))
        if node:
            out.append(summarize_evidence_node(node))
    return out


def plan_context(formal: dict[str, Any], node: dict[str, Any]) -> dict[str, Any]:
    plan_graph = formal.get("plan_graph", {})
    plan_nodes = plan_graph.get("nodes", [])
    plan_edges = plan_graph.get("edges", [])
    incoming, outgoing = incoming_outgoing(plan_nodes, plan_edges, str(node.get("id", "")))
    return {
        "theorem": formal.get("theorem", {}),
        "current_node": node,
        "incoming_plan_nodes": incoming,
        "outgoing_plan_nodes": outgoing,
        "contained_evidence_nodes": contained_evidence_summary(formal, node),
    }


def plan_context_item(formal: dict[str, Any], node: dict[str, Any]) -> dict[str, Any]:
    context = plan_context(formal, node)
    return {
        "current_node": context["current_node"],
        "incoming_plan_nodes": context["incoming_plan_nodes"],
        "outgoing_plan_nodes": context["outgoing_plan_nodes"],
        "contained_evidence_nodes": context["contained_evidence_nodes"],
    }


def plan_context_batch(formal: dict[str, Any], nodes: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "theorem": formal.get("theorem", {}),
        "items": [plan_context_item(formal, node) for node in nodes],
    }


def evidence_parent_plans(formal: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {}
    for plan_node in formal.get("plan_graph", {}).get("nodes", []):
        summary = summarize_plan_node(plan_node)
        for evidence_id in plan_node.get("evidence_node_ids", []):
            out.setdefault(str(evidence_id), []).append(summary)
    return out


def evidence_context_batch(formal: dict[str, Any], nodes: list[dict[str, Any]]) -> dict[str, Any]:
    evidence_graph = formal.get("evidence_graph", {})
    evidence_nodes = evidence_graph.get("nodes", [])
    evidence_edges = evidence_graph.get("edges", [])
    parent_plans = evidence_parent_plans(formal)
    items = []
    for node in nodes:
        node_id = str(node.get("id", ""))
        incoming, outgoing = evidence_incoming_outgoing(evidence_nodes, evidence_edges, node_id)
        items.append(
            {
                "current_node": node,
                "parent_plan_nodes": parent_plans.get(node_id, []),
                "incoming_evidence_nodes": incoming[:8],
                "outgoing_evidence_nodes": outgoing[:8],
            }
        )
    return {
        "theorem": formal.get("theorem", {}),
        "items": items,
    }


def evidence_label(node: dict[str, Any]) -> str:
    return clean(
        node.get("display_label")
        or node.get("label")
        or node.get("display_type")
        or node.get("type")
        or node.get("name")
        or node.get("id")
    )


def fallback_plan_translation(node: dict[str, Any]) -> dict[str, Any]:
    label = clean(node.get("label") or node.get("id"))
    detail_label = clean(node.get("detail_label"))
    role = clean(node.get("role_summary"))
    kind = clean(node.get("kind"))
    outputs = [clean(item) for item in node.get("display_outputs", []) if clean(item)]
    inputs = [clean(item) for item in node.get("display_inputs", []) if clean(item)]

    if role:
        english_label = role
        english_label = re.sub(r"^prove\b", "Show", english_label, flags=re.IGNORECASE)
        english_label = re.sub(r"^close\b", "Close", english_label, flags=re.IGNORECASE)
        english_label = english_label[:1].upper() + english_label[1:]
        if not english_label.endswith("."):
            english_label += "."
    elif outputs:
        english_label = f"Establish {outputs[0]}."
    elif detail_label:
        english_label = f"Use this step to handle {detail_label}."
    else:
        english_label = f"Explain proof step {label}."

    if outputs:
        english_detail = f"This proof block produces {', '.join(outputs)}."
    elif detail_label:
        english_detail = f"This proof block is centered on {detail_label}."
    else:
        english_detail = f"This proof block has kind `{kind or 'unknown'}`."

    return {
        "id": node.get("id", ""),
        "english_label": short(english_label, 160),
        "english_detail": short(english_detail, 320),
        "english_inputs": inputs,
        "english_outputs": outputs,
        "translation_status": "fallback",
    }


def fallback_evidence_translation(node: dict[str, Any]) -> dict[str, Any]:
    label = evidence_label(node)
    kind = clean(node.get("kind"))
    class_name = clean(node.get("class"))
    if kind == "action" or class_name == "action":
        name = clean(node.get("name") or label or node.get("id"))
        english_label = name
        english_detail = f"Lean tactic/action `{name}`."
    elif kind == "theorem_goal":
        english_label = "The theorem goal."
        english_detail = label
    elif kind == "subgoal":
        english_label = "A proof subgoal."
        english_detail = label
    else:
        english_label = label
        english_detail = f"Formal object: {label}."
    return {
        "id": node.get("id", ""),
        "english_label": short(english_label, 160),
        "english_detail": short(english_detail, 320),
        "translation_status": "fallback",
    }


class LlmClient:
    def __init__(self, cfg: LlmConfig):
        try:
            from openai import OpenAI
        except ImportError as exc:
            raise RuntimeError("OpenAI SDK is not installed. Run: conda run -n proofstruct python -m pip install openai") from exc

        api_key = cfg.resolved_api_key
        if not api_key:
            raise RuntimeError(
                f"LLM API key is missing. Set {cfg.api_key_env} or add api_key to local config.toml."
            )
        self.cfg = cfg
        self.client = OpenAI(api_key=api_key, base_url=cfg.base_url, timeout=cfg.timeout_seconds)

    def call_json(self, prompt: str, payload: dict[str, Any]) -> dict[str, Any]:
        response = self.client.chat.completions.create(
            model=self.cfg.model,
            messages=[
                {"role": "system", "content": prompt},
                {"role": "user", "content": json.dumps(payload, ensure_ascii=False)},
            ],
            response_format={"type": "json_object"},
            max_completion_tokens=self.cfg.max_completion_tokens,
            temperature=self.cfg.temperature,
        )
        text = response.choices[0].message.content or ""
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            match = re.search(r"\{[\s\S]*\}", text)
            if not match:
                raise
            return json.loads(match.group(0))


def cache_path(cache_dir: Path, kind: str, node_id: str, model: str, prompt: str, context: dict[str, Any]) -> Path:
    digest = stable_hash_obj({"kind": kind, "model": model, "prompt": prompt, "context": context})
    safe_id = re.sub(r"[^A-Za-z0-9_.-]", "_", node_id).strip("._") or "node"
    return cache_dir / f"{kind}.{safe_id}.{digest[:16]}.json"


def translate_plan_nodes(
    formal: dict[str, Any],
    prompt: str,
    cfg: LlmConfig,
    cache_dir: Path,
    fallback_only: bool,
    require_llm: bool,
    batch_size: int,
) -> dict[str, dict[str, Any]]:
    nodes = formal.get("plan_graph", {}).get("nodes", [])
    translations: dict[str, dict[str, Any]] = {}
    client: LlmClient | None = None
    if not fallback_only:
        try:
            client = LlmClient(cfg)
        except Exception:
            if require_llm:
                raise
            client = None

    for batch in chunked(nodes, batch_size):
        context = plan_context_batch(formal, batch)
        batch_id = stable_hash_obj([node.get("id", "") for node in batch])[:16]
        path = cache_path(cache_dir, "plan", batch_id, cfg.model, prompt, context)
        cached: dict[str, Any] | None = read_json(path) if path.exists() else None
        if cached is not None and require_llm and cached.get("translation_status") != "llm":
            cached = None
        if cached is None:
            if client is None:
                cached = {
                    "items": [fallback_plan_translation(node) for node in batch],
                    "translation_status": "fallback",
                }
            else:
                try:
                    cached = client.call_json(prompt, context)
                    cached["translation_status"] = "llm"
                except Exception as exc:
                    if require_llm:
                        raise
                    cached = {
                        "items": [fallback_plan_translation(node) for node in batch],
                        "translation_status": "fallback",
                        "translation_error": str(exc),
                    }
            write_json(path, cached)

        batch_status = cached.get("translation_status", "llm")
        by_id = {str(item.get("id", "")): item for item in normalize_evidence_batch_response(cached)}
        for node in batch:
            node_id = str(node.get("id", ""))
            fallback = fallback_plan_translation(node)
            translated = by_id.get(node_id) or fallback
            translated["id"] = node_id
            translated.setdefault("english_label", fallback["english_label"])
            translated.setdefault("english_detail", fallback["english_detail"])
            translated.setdefault("english_inputs", node.get("display_inputs", []))
            translated.setdefault("english_outputs", node.get("display_outputs", []))
            translated.setdefault("translation_status", batch_status)
            if cached.get("translation_error"):
                translated["translation_error"] = cached["translation_error"]
            if translated.get("translation_status") == "llm":
                translated.setdefault("translation_model", cfg.model)
            translations[node_id] = translated
    return translations


def should_generate_evidence_with_llm(node: dict[str, Any], mode: str) -> bool:
    if mode == "none":
        return False
    if mode == "all":
        return True
    kind = clean(node.get("kind"))
    class_name = clean(node.get("class"))
    if kind == "action" or class_name == "action":
        return False
    if node.get("hidden_by_default") is True:
        return False
    return True


def chunked(items: list[dict[str, Any]], size: int) -> list[list[dict[str, Any]]]:
    size = max(1, int(size))
    return [items[i : i + size] for i in range(0, len(items), size)]


def normalize_evidence_batch_response(response: dict[str, Any]) -> list[dict[str, Any]]:
    items = response.get("items")
    if isinstance(items, list):
        return [item for item in items if isinstance(item, dict)]
    if response.get("id"):
        return [response]
    return []


def translate_evidence_nodes(
    formal: dict[str, Any],
    prompt: str,
    cfg: LlmConfig,
    cache_dir: Path,
    fallback_only: bool,
    require_llm: bool,
    mode: str,
    batch_size: int,
) -> dict[str, dict[str, Any]]:
    nodes = formal.get("evidence_graph", {}).get("nodes", [])
    translations: dict[str, dict[str, Any]] = {}
    llm_nodes = [node for node in nodes if should_generate_evidence_with_llm(node, mode)]

    client: LlmClient | None = None
    if llm_nodes and not fallback_only:
        try:
            client = LlmClient(cfg)
        except Exception:
            if require_llm:
                raise
            client = None

    for node in nodes:
        node_id = str(node.get("id", ""))
        if node not in llm_nodes:
            translations[node_id] = fallback_evidence_translation(node)

    for batch in chunked(llm_nodes, batch_size):
        context = evidence_context_batch(formal, batch)
        batch_id = stable_hash_obj([node.get("id", "") for node in batch])[:16]
        path = cache_path(cache_dir, "evidence", batch_id, cfg.model, prompt, context)
        cached: dict[str, Any] | None = read_json(path) if path.exists() else None
        if cached is not None and require_llm and cached.get("translation_status") != "llm":
            cached = None
        if cached is None:
            if client is None:
                cached = {
                    "items": [fallback_evidence_translation(node) for node in batch],
                    "translation_status": "fallback",
                }
            else:
                try:
                    cached = client.call_json(prompt, context)
                    cached["translation_status"] = "llm"
                except Exception as exc:
                    if require_llm:
                        raise
                    cached = {
                        "items": [fallback_evidence_translation(node) for node in batch],
                        "translation_status": "fallback",
                        "translation_error": str(exc),
                    }
            write_json(path, cached)

        batch_status = cached.get("translation_status", "llm")
        by_id = {str(item.get("id", "")): item for item in normalize_evidence_batch_response(cached)}
        for node in batch:
            node_id = str(node.get("id", ""))
            fallback = fallback_evidence_translation(node)
            translated = by_id.get(node_id) or fallback
            translated["id"] = node_id
            translated.setdefault("english_label", fallback["english_label"])
            translated.setdefault("english_detail", fallback["english_detail"])
            translated.setdefault("translation_status", batch_status)
            if cached.get("translation_error"):
                translated["translation_error"] = cached["translation_error"]
            if translated.get("translation_status") == "llm":
                translated.setdefault("translation_model", cfg.model)
            translations[node_id] = translated
    return translations


def build_english_blueprint(
    formal_path: Path,
    formal: dict[str, Any],
    plan_prompt: str,
    evidence_prompt: str,
    cfg: LlmConfig,
    cache_dir: Path,
    fallback_only: bool,
    require_llm: bool,
    plan_batch_size: int,
    evidence_mode: str,
    evidence_batch_size: int,
) -> dict[str, Any]:
    english = copy.deepcopy(formal)
    source_bytes = formal_path.read_bytes()
    english["schema_version"] = "english-layered-1"
    english["language"] = "en"
    english["source_layered_schema_version"] = formal.get("schema_version", "")
    english["source_layered_path"] = str(formal_path)
    english["source_hash"] = stable_hash_bytes(source_bytes)

    theorem = english.setdefault("theorem", {})
    theorem["english_type"] = clean(theorem.get("type", ""))

    plan_translations = translate_plan_nodes(
        formal=formal,
        prompt=plan_prompt,
        cfg=cfg,
        cache_dir=cache_dir,
        fallback_only=fallback_only,
        require_llm=require_llm,
        batch_size=plan_batch_size,
    )
    evidence_translations = translate_evidence_nodes(
        formal=formal,
        prompt=evidence_prompt,
        cfg=cfg,
        cache_dir=cache_dir,
        fallback_only=fallback_only,
        require_llm=require_llm,
        mode=evidence_mode,
        batch_size=evidence_batch_size,
    )

    for node in english.get("plan_graph", {}).get("nodes", []):
        node_id = str(node.get("id", ""))
        translated = plan_translations.get(node_id) or fallback_plan_translation(node)
        node["source_node_id"] = node_id
        node["formal_label"] = node.get("label", "")
        node["formal_detail_label"] = node.get("detail_label", "")
        node["formal_role_summary"] = node.get("role_summary", "")
        node["english_label"] = clean(translated.get("english_label"))
        node["english_detail"] = clean(translated.get("english_detail"))
        node["english_inputs"] = [clean(item) for item in translated.get("english_inputs", [])]
        node["english_outputs"] = [clean(item) for item in translated.get("english_outputs", [])]
        node["translation_status"] = translated.get("translation_status", "fallback")
        if translated.get("translation_model"):
            node["translation_model"] = translated["translation_model"]
        if translated.get("translation_error"):
            node["translation_error"] = translated["translation_error"]

    for node in english.get("evidence_graph", {}).get("nodes", []):
        node_id = str(node.get("id", ""))
        translated = evidence_translations.get(node_id) or fallback_evidence_translation(node)
        node["source_node_id"] = node_id
        node["formal_label"] = evidence_label(node)
        node["english_label"] = clean(translated.get("english_label"))
        node["english_detail"] = clean(translated.get("english_detail"))
        node["translation_status"] = translated.get("translation_status", "fallback")
        if translated.get("translation_model"):
            node["translation_model"] = translated["translation_model"]
        if translated.get("translation_error"):
            node["translation_error"] = translated["translation_error"]

    validate_english_blueprint(formal, english)
    return english


def theorem_dirs(input_dir: Path) -> list[Path]:
    if not input_dir.exists():
        return []
    return sorted(
        path for path in input_dir.iterdir()
        if path.is_dir() and (path / "formal.layered.json").exists()
    )


def default_output_for_formal(formal_path: Path) -> Path:
    return formal_path.parent / "english.layered.json"


def process_one(args: argparse.Namespace, formal_path: Path, output_path: Path | None = None) -> None:
    prompt_dir = Path(args.prompt_dir)
    plan_prompt = read_prompt(prompt_dir, "english_plan_graph.md")
    evidence_prompt = read_prompt(prompt_dir, "english_evidence_graph.md")
    cfg = llm_config_from_sources(args)
    formal = read_json(formal_path)
    output = output_path or default_output_for_formal(formal_path)
    cache_dir = Path(args.cache_dir) if args.cache_dir else output.parent / ".english_cache"
    cache_dir.mkdir(parents=True, exist_ok=True)
    english = build_english_blueprint(
        formal_path=formal_path,
        formal=formal,
        plan_prompt=plan_prompt,
        evidence_prompt=evidence_prompt,
        cfg=cfg,
        cache_dir=cache_dir,
        fallback_only=bool(args.fallback_only),
        require_llm=bool(args.require_llm),
        plan_batch_size=int(args.plan_batch_size),
        evidence_mode=str(args.evidence_mode),
        evidence_batch_size=int(args.evidence_batch_size),
    )
    write_json(output, english)
    print(f"wrote {output}")


def validate_pair(formal_path: Path, english_path: Path) -> None:
    formal = read_json(formal_path)
    english = read_json(english_path)
    validate_english_blueprint(formal, english)
    print(f"validated {english_path}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate English ProofStruct layered blueprints.")
    parser.add_argument("--formal", type=Path, help="Formal layered JSON path.")
    parser.add_argument("--output", type=Path, help="English layered JSON path.")
    parser.add_argument("--input-dir", type=Path, help="Dataset directory containing theorem subdirectories.")
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--prompt-dir", type=Path, default=DEFAULT_PROMPT_DIR)
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--model")
    parser.add_argument("--base-url")
    parser.add_argument("--api-key")
    parser.add_argument("--api-key-env")
    parser.add_argument("--timeout-seconds", type=float)
    parser.add_argument("--max-completion-tokens", type=int)
    parser.add_argument("--temperature", type=float)
    parser.add_argument("--fallback-only", action="store_true", help="Do not call the LLM; generate schema-valid fallback English text.")
    parser.add_argument("--require-llm", action="store_true", help="Fail instead of falling back when the LLM is unavailable.")
    parser.add_argument("--plan-batch-size", type=int, default=5)
    parser.add_argument(
        "--evidence-mode",
        choices=["none", "objects", "all"],
        default="objects",
        help="Which evidence nodes should use LLM generation. Actions still keep tactic names by default in objects mode.",
    )
    parser.add_argument("--evidence-batch-size", type=int, default=8)
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--english", type=Path, help="English layered JSON path for --validate.")
    args = parser.parse_args()

    try:
        if args.validate:
            if not args.formal or not args.english:
                parser.error("--validate requires --formal and --english")
            validate_pair(args.formal, args.english)
            return 0
        if args.input_dir:
            dirs = theorem_dirs(args.input_dir)
            if not dirs:
                parser.error(f"no theorem directories with formal.layered.json found in {args.input_dir}")
            for directory in dirs:
                process_one(args, directory / "formal.layered.json")
            return 0
        if not args.formal:
            parser.error("provide --formal or --input-dir")
        process_one(args, args.formal, args.output)
        return 0
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
