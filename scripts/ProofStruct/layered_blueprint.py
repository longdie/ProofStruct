from __future__ import annotations

import argparse
import re
from collections import defaultdict
from pathlib import Path
from typing import Any

import orjson


ACTION_TO_OUTPUT = {"action_to_output", "action_to_subgoal", "action_solves_goal"}
INPUT_EDGE_KINDS = {"input_to_action"}
IGNORED_PLAN_EDGE_KINDS = {"context_to_goal", "goal_to_action"}
TRANSFORM_TACTICS = {"rw", "simp", "change", "convert", "subst"}
AUTO_TACTICS = {"ring", "ring_nf", "omega", "norm_num", "linarith", "nlinarith", "aesop", "abel"}
SOLVE_TACTICS = {
    "exact",
    "assumption",
    "trivial",
    "contradiction",
    "rfl",
    "simpa",
    "simp",
    "infer_instance",
}
SPLIT_TACTICS = {"constructor", "refine", "apply", "ext", "left", "right"}
CASE_TACTICS = {"by_cases", "cases", "rcases"}
INLINE_BY_CONTAINER_TACTICS = {"exact", "refine", "apply", "calc", "constructor"}
LOW_VALUE_GLOBAL_PREFIXES = (
    "inst",
    "OfNat.",
    "OfNat.ofNat",
    "Nat.cast",
    "Int.inst",
    "HAdd.",
    "HSub.",
    "HMul.",
    "HDiv.",
    "HPow.",
    "CommSemiring.",
    "CommRing.",
    "Semiring.",
    "Semigroup",
    "NonUnital",
)
LOW_VALUE_GLOBALS = {
    "Nat",
    "Int",
    "Prime",
    "IsCoprime",
    "Not",
    "Dvd.dvd",
    "HAdd.hAdd",
    "HMul.hMul",
    "HSub.hSub",
    "OfNat.ofNat",
}


def read_json(path: Path) -> dict[str, Any]:
    return orjson.loads(path.read_bytes())


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(orjson.dumps(data, option=orjson.OPT_INDENT_2 | orjson.OPT_APPEND_NEWLINE))


def sanitize_id(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]+", "_", text).strip("_") or "node"


def action_order(node: dict[str, Any]) -> tuple[int, int, str]:
    source_line = int(node.get("source_line") or 0)
    match = re.search(r"a_sem_(\d+)_", node.get("id", ""))
    index = int(match.group(1)) if match else 10**9
    return source_line, index, node.get("id", "")


def line_end(node: dict[str, Any]) -> int:
    raw = node.get("raw_text") or ""
    return int(node.get("source_line") or 0) + raw.count("\n")


def is_by_container(node: dict[str, Any]) -> bool:
    name = node.get("name") or ""
    raw = node.get("raw_text") or ""
    return name in {"have", "let", "suffices", "show"} and ":=" in raw and re.search(r":=\s*by\b", raw) is not None


def is_inline_by_container(node: dict[str, Any]) -> bool:
    name = node.get("name") or ""
    raw = node.get("raw_text") or ""
    return name in INLINE_BY_CONTAINER_TACTICS and re.search(r"\bby\b", raw) is not None


def is_action_container(node: dict[str, Any]) -> bool:
    return is_by_container(node) or is_inline_by_container(node)


def contains_action(container: dict[str, Any], child: dict[str, Any], end_line: int | None = None) -> bool:
    if container["id"] == child["id"]:
        return False
    start = int(container.get("source_line") or 0)
    end = line_end(container) if end_line is None else end_line
    child_line = int(child.get("source_line") or 0)
    return start <= child_line <= end


def inferred_container_end(
    action: dict[str, Any],
    sorted_actions: list[dict[str, Any]],
    index: int,
) -> int:
    raw = str(action.get("raw_text") or "").strip()
    default_end = line_end(action)
    if not (is_by_container(action) and raw.endswith("by") and "\n" not in raw):
        return default_end
    after_keys = goal_keys(action.get("goals_after") or [])
    if not after_keys:
        return default_end
    end = default_end
    start_line = int(action.get("source_line") or 0)
    for later in sorted_actions[index + 1 :]:
        later_line = int(later.get("source_line") or 0)
        if later_line <= start_line:
            continue
        later_before = goal_keys(later.get("goals_before") or [])
        if later_before and later_before[0] in after_keys:
            break
        end = max(end, later_line)
    return end


def compact(text: str, limit: int = 100) -> str:
    text = " ".join(str(text or "").split())
    if len(text) <= limit:
        return text
    return text[: limit - 1] + "…"


def display_globals(globals_: list[str], raw_texts: list[str], limit: int = 5) -> list[str]:
    raw = "\n".join(raw_texts)
    tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+", raw))
    out: list[str] = []
    for item in list(tokens) + globals_:
        if not item or item in out:
            continue
        if item.startswith(LOW_VALUE_GLOBAL_PREFIXES):
            continue
        if item in LOW_VALUE_GLOBALS:
            continue
        out.append(item)
        if len(out) >= limit:
            break
    return out


def pretty_type(text: str) -> str:
    text = str(text or "")
    text = re.sub(r"↥([A-Za-z_][A-Za-z0-9_']*)", r"\1", text)
    text = re.sub(r"↑([a-z][A-Za-z0-9_']*)", r"(\1 : ℤ)", text)
    return re.sub(r"\s+", " ", text).strip()


def is_low_value_node(node: dict[str, Any]) -> bool:
    name = str(node.get("name") or "")
    typ = str(node.get("type") or "")
    return (
        name.startswith("inst")
        or "✝" in name
        or "_fvar" in typ
        or typ.startswith("failed to pretty print expression")
    )


def refresh_display_fields(node: dict[str, Any]) -> None:
    if node.get("class") == "action" or node.get("kind") == "action":
        raw = node.get("raw_text") or ""
        node["display_label"] = node.get("label") or raw or node.get("name") or node.get("id", "")
        node["display_type"] = ""
        node["hidden_by_default"] = False
        return
    display_name = node.get("display_name") or node.get("name") or node.get("id", "")
    display_type = pretty_type(node.get("type") or "")
    node["display_name"] = display_name
    node["display_type"] = display_type
    if node.get("kind") in {"theorem_goal", "subgoal"}:
        node["display_label"] = display_type or node.get("label") or display_name
    elif display_type:
        node["display_label"] = f"{display_name} : {display_type}"
    else:
        node["display_label"] = display_name
    node["hidden_by_default"] = is_low_value_node(node)


def enrich_evidence_nodes(nodes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    enriched = [dict(node) for node in nodes]
    by_name: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for node in enriched:
        refresh_display_fields(node)
        if node.get("class") != "action" and node.get("kind") != "action":
            name = node.get("name") or ""
            if name and not node.get("hidden_by_default"):
                by_name[name].append(node)
    for name, same_name_nodes in by_name.items():
        if len(same_name_nodes) <= 1:
            continue
        for idx, node in enumerate(same_name_nodes, start=1):
            node["version_index"] = idx
            node["version_count"] = len(same_name_nodes)
            node["display_name"] = f"{name}#{idx}"
            refresh_display_fields(node)
    return enriched


def parse_decl_output(node: dict[str, Any]) -> tuple[str, str]:
    raw = node.get("raw_text") or ""
    name = node.get("name") or ""
    if name not in {"have", "let", "suffices", "show"}:
        return "", ""
    body = raw.strip()
    if body.startswith(name):
        body = body[len(name) :].strip()
    before_assign = body.split(":=", 1)[0].strip()
    if ":" in before_assign:
        lhs, typ = before_assign.split(":", 1)
        return lhs.strip().split()[0] if lhs.strip() else "", typ.strip()
    parts = before_assign.split()
    return (parts[0], "") if parts else ("", "")


def introduced_names_from_raw(raw: str) -> list[str]:
    text = str(raw or "").strip()
    if not text:
        return []
    head, _, rest = text.partition(" ")
    if head not in {"intro", "intros", "rintro", "ext"}:
        return []
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_']*", rest)
    stop_words = {"with", "using", "at", "by", "show"}
    return [token for token in tokens if token not in stop_words]


def goal_target(goal: str) -> str:
    for line in str(goal or "").splitlines():
        line = line.strip()
        if line.startswith("⊢"):
            return line[1:].strip()
    return str(goal or "").strip()


def node_title(node: dict[str, Any], outputs: list[dict[str, Any]], solves: list[dict[str, Any]]) -> tuple[str, str]:
    name = node.get("name") or "proof"
    if name in {"intro", "intros", "rintro", "ext"}:
        names = introduced_names_from_raw(node.get("raw_text") or "")
        if names:
            return f"{name} -> {', '.join(names[:4])}", ""
    if name in {"have", "let", "suffices", "show"}:
        out_name, out_type = parse_decl_output(node)
        if not out_name and outputs:
            out_name = outputs[0].get("display_name") or outputs[0].get("name") or outputs[0].get("label") or ""
            out_type = outputs[0].get("display_type") or outputs[0].get("type") or ""
        title = f"{name} {out_name}".strip()
        return title, pretty_type(out_type) or compact(node.get("label") or "", 90)
    if solves:
        target = solves[0].get("display_type") or solves[0].get("type") or solves[0].get("label") or ""
        if solves[0].get("kind") == "theorem_goal":
            return "close theorem goal", target
        return f"solve {solves[0].get('display_name') or solves[0].get('name') or 'subgoal'}", target
    if outputs:
        output = outputs[0]
        return (
            f"{name} -> {output.get('display_name') or output.get('name') or output.get('kind')}",
            output.get("display_type") or output.get("type") or output.get("label") or "",
        )
    label = node.get("label") or node.get("raw_text") or name
    return name, compact(label, 90)


def classify_block(actions: list[dict[str, Any]], outputs: list[dict[str, Any]], solves: list[dict[str, Any]], opens: list[dict[str, Any]]) -> str:
    names = [node.get("name") or "" for node in actions]
    first = names[0] if names else ""
    output_kinds = {node.get("kind") for node in outputs}
    if first in {"intro", "intros", "rintro"}:
        return "introduce_context"
    if first in {"by_cases", "cases", "rcases"}:
        return "case_split"
    if first == "calc":
        return "calculation_chain"
    if first in {"have", "suffices", "show"}:
        return "prove_intermediate"
    if first == "let" or "constructed_object" in output_kinds:
        return "construct_object"
    if first in AUTO_TACTICS:
        return "automation"
    if first in TRANSFORM_TACTICS or (first in {"simp", "simpa"} and not solves):
        return "transform_goal"
    if opens or first in {"constructor", "refine", "apply", "ext"}:
        return "split_goal"
    if solves:
        if any(node.get("kind") == "theorem_goal" for node in solves):
            return "close_goal"
        return "solve_goal"
    if first in SOLVE_TACTICS:
        return "solve_goal"
    return "unknown"


def build_edge_indexes(edges: list[dict[str, Any]]) -> tuple[dict[str, list[dict[str, Any]]], dict[str, list[dict[str, Any]]]]:
    incoming: dict[str, list[dict[str, Any]]] = defaultdict(list)
    outgoing: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in edges:
        outgoing[edge["from"]].append(edge)
        incoming[edge["to"]].append(edge)
    return incoming, outgoing


def build_action_blocks(actions: list[dict[str, Any]]) -> list[list[dict[str, Any]]]:
    blocks: list[list[dict[str, Any]]] = []
    containers: list[tuple[dict[str, Any], list[dict[str, Any]], int]] = []
    sorted_actions = sorted(actions, key=action_order)
    for index, action in enumerate(sorted_actions):
        assigned = False
        for container, block, end_line in reversed(containers):
            if contains_action(container, action, end_line):
                block.append(action)
                assigned = True
                break
        if assigned:
            continue
        block = [action]
        blocks.append(block)
        if is_action_container(action):
            containers.append((action, block, inferred_container_end(action, sorted_actions, index)))
        containers = [
            (node, block_ref, end_line)
            for node, block_ref, end_line in containers
            if end_line >= int(action.get("source_line") or 0)
        ]
    return merge_transform_blocks(blocks)


def is_transform_only(block: list[dict[str, Any]], outgoing: dict[str, list[dict[str, Any]]] | None = None) -> bool:
    if len(block) != 1:
        return False
    action = block[0]
    name = action.get("name") or ""
    if name not in TRANSFORM_TACTICS:
        return False
    if outgoing is None:
        return True
    return not any(edge.get("kind") in ACTION_TO_OUTPUT for edge in outgoing.get(action["id"], []))


def merge_transform_blocks(blocks: list[list[dict[str, Any]]]) -> list[list[dict[str, Any]]]:
    merged: list[list[dict[str, Any]]] = []
    for block in blocks:
        if merged and is_transform_only(merged[-1]) and is_transform_only(block):
            merged[-1].extend(block)
        else:
            merged.append(block)
    return merged


def unique(items: list[str]) -> list[str]:
    out: list[str] = []
    for item in items:
        if item and item not in out:
            out.append(item)
    return out


def block_source_text(block_actions: list[dict[str, Any]]) -> str:
    texts = [str(node.get("raw_text") or "").strip() for node in block_actions if node.get("raw_text")]
    if not texts:
        return ""
    out: list[str] = []
    for text in texts:
        if any(text != existing and text in existing for existing in out):
            continue
        out = [existing for existing in out if existing not in text]
        out.append(text)
    return "\n".join(out)


def display_node_text(node: dict[str, Any]) -> str:
    return node.get("display_label") or node.get("label") or node.get("type") or node.get("name") or node.get("id", "")


def display_node_ref(node: dict[str, Any]) -> str:
    return compact(display_node_text(node), 120)


def block_display_text(raw_text: str, kind: str, opens: list[dict[str, Any]], solves: list[dict[str, Any]]) -> str:
    extra: list[str] = []
    if opens:
        extra.append("opens subgoals:")
        for node in opens:
            extra.append(f"- {compact(display_node_text(node), 140)}")
    if solves and kind in {"solve_goal", "close_goal", "automation"}:
        extra.append("solves:")
        for node in solves:
            extra.append(f"- {compact(display_node_text(node), 140)}")
    if extra and len(raw_text.splitlines()) <= 1:
        return raw_text.strip() + "\n\n" + "\n".join(extra)
    return raw_text


def block_goals_after(block_actions: list[dict[str, Any]]) -> list[str]:
    if not block_actions:
        return []
    root = block_actions[0]
    if is_by_container(root):
        return root.get("goals_after") or []
    root_raw = str(root.get("raw_text") or "")
    if len(block_actions) > 1 and all(str(child.get("raw_text") or "").strip() in root_raw for child in block_actions[1:]):
        return root.get("goals_after") or []
    return block_actions[-1].get("goals_after") or []


def goal_case_key(goal: str) -> str:
    for line in str(goal or "").splitlines():
        line = line.strip()
        if line.startswith("case "):
            case_name = line[len("case ") :].strip()
            return case_name or "case"
    return "main"


def goal_keys(goals: list[str]) -> list[str]:
    return unique([goal_case_key(goal) for goal in goals])


def branch_label(goal_key: str) -> str:
    if not goal_key or goal_key == "main":
        return ""
    return goal_key


def role_summary(
    kind: str,
    main_tactic: str,
    outputs: list[dict[str, Any]],
    solves: list[dict[str, Any]],
    opens: list[dict[str, Any]],
) -> str:
    if kind == "introduce_context":
        names = ", ".join(node.get("display_name") or node.get("name") or node["id"] for node in outputs[:4])
        return f"introduce {names}" if names else "introduce proof context"
    if kind == "prove_intermediate":
        if outputs:
            node = outputs[0]
            name = node.get("display_name") or node.get("name") or "intermediate result"
            typ = node.get("display_type") or node.get("type") or ""
            return f"prove {name}: {compact(typ, 80)}" if typ else f"prove {name}"
        return "prove intermediate result"
    if kind == "construct_object":
        names = ", ".join(node.get("display_name") or node.get("name") or node["id"] for node in outputs[:3])
        return f"construct {names}" if names else "construct object"
    if kind == "transform_goal":
        return f"transform goal with {main_tactic}"
    if kind == "calculation_chain":
        return "close goal by calculation chain"
    if kind == "automation":
        return f"solve side condition with {main_tactic}"
    if kind == "split_goal":
        return f"split goal with {main_tactic}" if opens else f"apply structural step {main_tactic}"
    if kind == "case_split":
        return f"split cases with {main_tactic}"
    if kind == "close_goal":
        return "close theorem goal"
    if kind == "solve_goal":
        if solves:
            return f"solve {display_node_ref(solves[0])}"
        return "solve current goal"
    return "proof step"


def assign_branch_metadata(plan_nodes: list[dict[str, Any]]) -> None:
    for node in plan_nodes:
        before_keys = goal_keys(node.get("goals_before") or [])
        after_keys = goal_keys(node.get("goals_after") or [])
        primary = before_keys[0] if before_keys else "main"
        node["goal_flow"] = {
            "primary": primary,
            "before": before_keys,
            "after": after_keys,
        }
        node["branch_id"] = "" if primary == "main" else primary
        node["branch_label"] = branch_label(primary)
        node["parent_split"] = ""
        node["branch_index"] = 0

    for idx, node in enumerate(plan_nodes):
        primary = node["goal_flow"]["primary"]
        if primary == "main":
            continue
        best_parent: dict[str, Any] | None = None
        best_key = ""
        for candidate in reversed(plan_nodes[:idx]):
            for key in candidate.get("goal_flow", {}).get("after", []):
                if primary == key or primary.startswith(key + "."):
                    best_parent = candidate
                    best_key = key
                    break
            if best_parent is not None:
                break
        if best_parent is None:
            continue
        after = best_parent.get("goal_flow", {}).get("after", [])
        node["parent_split"] = best_parent["id"]
        node["branch_index"] = after.index(best_key) + 1 if best_key in after else 0
        node["branch_label"] = branch_label(best_key or primary)


def attach_scope_metadata(nodes: list[dict[str, Any]], plan_nodes: list[dict[str, Any]]) -> None:
    plan_by_id = {node["id"]: node for node in plan_nodes}
    internal_owners: dict[str, list[str]] = defaultdict(list)
    boundary_owners: dict[str, list[str]] = defaultdict(list)
    for plan in plan_nodes:
        for node_id in plan.get("internal_evidence_node_ids", []):
            if plan["id"] not in internal_owners[node_id]:
                internal_owners[node_id].append(plan["id"])
        for node_id in plan.get("boundary_node_ids", []):
            if plan["id"] not in boundary_owners[node_id]:
                boundary_owners[node_id].append(plan["id"])
    for node in nodes:
        owner_ids = internal_owners.get(node["id"], [])
        if not owner_ids:
            owner_ids = boundary_owners.get(node["id"], [])
        if not owner_ids:
            continue
        scopes = unique([plan_by_id[plan_id].get("branch_id") or "main" for plan_id in owner_ids if plan_id in plan_by_id])
        if len(scopes) != 1:
            continue
        scope_id = scopes[0]
        node["scope_id"] = scope_id
        if (
            node.get("version_count", 0) > 1
            and scope_id != "main"
            and node.get("class") != "action"
            and node.get("kind") != "action"
        ):
            base_name = node.get("name") or node.get("display_name") or node["id"]
            node["display_name"] = f"{base_name}@{scope_id}"
            refresh_display_fields(node)


def refresh_plan_display_refs(plan_nodes: list[dict[str, Any]], node_by_id: dict[str, dict[str, Any]]) -> None:
    for plan in plan_nodes:
        inputs = [node_by_id[node_id] for node_id in plan.get("boundary_node_ids", []) if node_id in node_by_id]
        internal = [node_by_id[node_id] for node_id in plan.get("internal_evidence_node_ids", []) if node_id in node_by_id]
        outputs = [
            node
            for node in internal
            if node.get("kind") in {"intermediate", "constructed_object"}
            and node.get("class") != "action"
            and node.get("kind") != "action"
        ]
        solves = [
            node
            for node in internal
            if node.get("kind") in {"theorem_goal", "subgoal"}
            and (node.get("name") or node.get("id")) in set(plan.get("solves", []))
        ]
        opens = [
            node
            for node in internal
            if node.get("kind") == "subgoal"
            and (node.get("name") or node.get("id")) in set(plan.get("opens_subgoals", []))
        ]
        plan["display_inputs"] = unique([display_node_ref(node) for node in inputs if not node.get("hidden_by_default")])
        plan["display_outputs"] = unique([display_node_ref(node) for node in outputs if not node.get("hidden_by_default")])
        plan["display_solves"] = unique([display_node_ref(node) for node in solves if not node.get("hidden_by_default")])
        plan["display_opens_subgoals"] = unique([display_node_ref(node) for node in opens if not node.get("hidden_by_default")])


def build_layered_blueprint(data: dict[str, Any]) -> dict[str, Any]:
    nodes = enrich_evidence_nodes(data.get("nodes", []))
    edges = data.get("edges", [])
    node_by_id = {node["id"]: node for node in nodes}
    incoming, outgoing = build_edge_indexes(edges)
    actions = [
        node
        for node in nodes
        if (node.get("class") == "action" or node.get("kind") == "action")
        and int(node.get("source_line") or 0) > 0
    ]
    blocks = build_action_blocks(actions)

    action_to_block: dict[str, str] = {}
    node_owner: dict[str, str] = {}
    plan_nodes: list[dict[str, Any]] = []
    mapping: dict[str, dict[str, list[str]]] = {}

    for idx, block_actions in enumerate(blocks, start=1):
        plan_id = f"plan_{idx}"
        for action in block_actions:
            action_to_block[action["id"]] = plan_id
            node_owner[action["id"]] = plan_id

    for idx, block_actions in enumerate(blocks, start=1):
        plan_id = f"plan_{idx}"
        action_ids = [node["id"] for node in block_actions]
        action_set = set(action_ids)
        internal_node_ids: list[str] = list(action_ids)
        internal_edge_ids: list[str] = []
        boundary_node_ids: list[str] = []
        outputs: list[dict[str, Any]] = []
        solves: list[dict[str, Any]] = []
        opens: list[dict[str, Any]] = []
        inputs: list[dict[str, Any]] = []

        for edge_idx, edge in enumerate(edges, start=1):
            edge_id = edge.get("id") or f"e{edge_idx}"
            from_id = edge["from"]
            to_id = edge["to"]
            from_inside = from_id in action_set or from_id in internal_node_ids
            to_inside = to_id in action_set or to_id in internal_node_ids
            if from_id in action_set and edge.get("kind") in ACTION_TO_OUTPUT:
                target = node_by_id.get(to_id)
                if target is not None:
                    if target["id"] not in internal_node_ids:
                        internal_node_ids.append(target["id"])
                    node_owner[target["id"]] = plan_id
                    internal_edge_ids.append(edge_id)
                    if edge.get("kind") == "action_to_subgoal":
                        opens.append(target)
                    elif edge.get("kind") == "action_solves_goal":
                        solves.append(target)
                    else:
                        outputs.append(target)
            elif to_id in action_set and edge.get("kind") in INPUT_EDGE_KINDS:
                source = node_by_id.get(from_id)
                if source is not None:
                    if source["id"] not in boundary_node_ids and source["id"] not in internal_node_ids:
                        boundary_node_ids.append(source["id"])
                    inputs.append(source)
                    internal_edge_ids.append(edge_id)
            elif from_inside and to_inside:
                internal_edge_ids.append(edge_id)

        root = block_actions[0]
        title, subtitle = node_title(root, outputs, solves)
        start_line = min(int(node.get("source_line") or 0) for node in block_actions)
        end_line = max(line_end(node) for node in block_actions)
        tactics = unique([node.get("name") or "" for node in block_actions])
        raw_text = block_source_text(block_actions)
        used_globals = unique(sum((node.get("uses_global") or [] for node in block_actions), []))
        semantic_globals = unique(sum((node.get("semantic_uses_global") or [] for node in block_actions), []))
        used_globals = unique(used_globals + semantic_globals)
        display_used = display_globals(used_globals, [node.get("raw_text") or "" for node in block_actions])
        kind = classify_block(block_actions, outputs, solves, opens)
        display_text = block_display_text(raw_text, kind, opens, solves)
        role = role_summary(kind, root.get("name") or "", outputs, solves, opens)
        if kind == "introduce_context":
            raw_names = introduced_names_from_raw(raw_text)
            if raw_names:
                role = f"introduce {', '.join(raw_names[:4])}"
        goals_before = block_actions[0].get("goals_before") or []
        goals_after = block_goals_after(block_actions)
        local_context_before = block_actions[0].get("local_context") or []
        added_locals = [node.get("label") or node.get("name") or node["id"] for node in outputs if node.get("kind") in {"intermediate", "constructed_object"}]
        display_inputs = unique([display_node_ref(node) for node in inputs if not node.get("hidden_by_default")])
        display_outputs = unique([display_node_ref(node) for node in outputs if not node.get("hidden_by_default")])
        display_solves = unique([display_node_ref(node) for node in solves if not node.get("hidden_by_default")])
        display_opens = unique([display_node_ref(node) for node in opens if not node.get("hidden_by_default")])
        plan_node = {
            "id": plan_id,
            "kind": kind,
            "label": title,
            "detail_label": subtitle,
            "order_index": idx,
            "source_range": {
                "start_line": start_line,
                "end_line": end_line,
            },
            "raw_text": raw_text,
            "display_text": display_text,
            "main_tactic": root.get("name") or "",
            "tactics": tactics,
            "inputs": unique([node.get("name") or node["id"] for node in inputs]),
            "outputs": unique([node.get("name") or node["id"] for node in outputs]),
            "solves": unique([node.get("name") or node["id"] for node in solves]),
            "opens_subgoals": unique([node.get("name") or node["id"] for node in opens]),
            "display_inputs": display_inputs,
            "display_outputs": display_outputs,
            "display_solves": display_solves,
            "display_opens_subgoals": display_opens,
            "role_summary": role,
            "goals_before": goals_before,
            "goals_after": goals_after,
            "local_context_before": local_context_before,
            "local_context_after": [],
            "state_delta": {
                "added_locals": added_locals,
                "closed_goals": unique([node.get("label") or node.get("name") or node["id"] for node in solves]),
                "opened_goals": unique([node.get("label") or node.get("name") or node["id"] for node in opens]),
            },
            "used_globals": used_globals,
            "display_used_globals": display_used,
            "evidence_node_ids": unique(internal_node_ids + boundary_node_ids),
            "internal_evidence_node_ids": unique(internal_node_ids),
            "boundary_node_ids": unique(boundary_node_ids),
            "evidence_edge_ids": unique(internal_edge_ids),
        }
        plan_nodes.append(plan_node)
        mapping[plan_id] = {
            "evidence_nodes": plan_node["evidence_node_ids"],
            "internal_evidence_nodes": plan_node["internal_evidence_node_ids"],
            "boundary_nodes": plan_node["boundary_node_ids"],
            "evidence_edges": plan_node["evidence_edge_ids"],
        }

    assign_branch_metadata(plan_nodes)
    attach_scope_metadata(nodes, plan_nodes)
    refresh_plan_display_refs(plan_nodes, node_by_id)
    plan_edges = build_plan_edges(edges, node_owner, action_to_block, plan_nodes)
    return {
        "schema_version": "layered-1",
        "theorem": data.get("theorem", {}),
        "extraction_mode": data.get("extraction_mode", ""),
        "plan_graph": {
            "nodes": plan_nodes,
            "edges": plan_edges,
        },
        "evidence_graph": {
            "nodes": nodes,
            "edges": edges,
        },
        "mapping": mapping,
    }


def build_plan_edges(
    evidence_edges: list[dict[str, Any]],
    node_owner: dict[str, str],
    action_to_block: dict[str, str],
    plan_nodes: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    ordered_ids = [node["id"] for node in sorted(plan_nodes, key=lambda item: item["order_index"])]
    order = {node_id: idx for idx, node_id in enumerate(ordered_ids)}
    by_id = {node["id"]: node for node in plan_nodes}
    dependency_pairs: list[tuple[str, str, str, str]] = []
    for edge in evidence_edges:
        if edge.get("kind") in IGNORED_PLAN_EDGE_KINDS:
            continue
        source_owner = node_owner.get(edge["from"])
        target_owner = node_owner.get(edge["to"])
        if target_owner is None and edge["to"] in action_to_block:
            target_owner = action_to_block[edge["to"]]
        if source_owner is None or target_owner is None or source_owner == target_owner:
            continue
        if order.get(source_owner, 10**9) >= order.get(target_owner, -1):
            continue
        pair = (source_owner, target_owner, edge.get("kind", ""), edge.get("label", ""))
        if pair not in dependency_pairs:
            dependency_pairs.append(pair)

    def first_following_with_goal(start_idx: int, goal_key: str) -> str:
        for candidate in plan_nodes[start_idx + 1 :]:
            if candidate.get("goal_flow", {}).get("primary") == goal_key:
                return candidate["id"]
        return ""

    flow_pairs: list[tuple[str, str, str, str]] = []

    def add_flow(source: str, target: str, relation: str, goal_key: str) -> None:
        if not source or not target or source == target:
            return
        pair = (source, target, relation, goal_key)
        if pair not in flow_pairs:
            flow_pairs.append(pair)

    for idx, node in enumerate(plan_nodes):
        after_keys = node.get("goal_flow", {}).get("after", [])
        if not after_keys:
            continue
        if len(after_keys) > 1 or node.get("kind") in {"split_goal", "case_split"}:
            for key in after_keys:
                target = first_following_with_goal(idx, key)
                add_flow(node["id"], target, "branch", key)
        else:
            key = after_keys[0]
            target = first_following_with_goal(idx, key)
            add_flow(node["id"], target, "next_goal", key)

    flow_edges = [
        {
            "id": f"plan_flow_{idx}",
            "from": source,
            "to": target,
            "kind": "flow",
            "relation": relation,
            "goal_key": goal_key,
            "label": branch_label(goal_key) if relation == "branch" else "",
            "visible_by_default": True,
            "order_index": idx,
        }
        for idx, (source, target, relation, goal_key) in enumerate(flow_pairs, start=1)
        if source in by_id and target in by_id
    ]
    dependency_edges = [
        {
            "id": f"plan_dep_{idx}",
            "from": source,
            "to": target,
            "kind": "dependency",
            "relation": evidence_kind,
            "label": label,
            "visible_by_default": False,
            "order_index": len(flow_edges) + idx,
        }
        for idx, (source, target, evidence_kind, label) in enumerate(
            sorted(dependency_pairs, key=lambda pair: (order.get(pair[0], 10**9), order.get(pair[1], 10**9))),
            start=1,
        )
        if source in by_id and target in by_id
    ]
    return flow_edges + dependency_edges


def main() -> None:
    parser = argparse.ArgumentParser(description="Build a layered ProofStruct blueprint from an evidence blueprint JSON.")
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    data = read_json(args.input)
    layered = build_layered_blueprint(data)
    output = args.output or args.input.with_suffix(".layered.json")
    write_json(output, layered)
    print(f"wrote {output}")


if __name__ == "__main__":
    main()
