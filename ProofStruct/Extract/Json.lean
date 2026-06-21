import Lean
import ProofStruct.Extract.Graph

namespace ProofStruct

def blueprintSummary (bp : Blueprint) : String :=
  s!"{bp.theoremName}: {bp.nodes.size} nodes, {bp.edges.size} edges"

private partial def escapeJsonChars : List Char → List Char
  | [] => []
  | '"' :: rest => '\\' :: '"' :: escapeJsonChars rest
  | '\\' :: rest => '\\' :: '\\' :: escapeJsonChars rest
  | '\n' :: rest => '\\' :: 'n' :: escapeJsonChars rest
  | '\r' :: rest => '\\' :: 'r' :: escapeJsonChars rest
  | '\t' :: rest => '\\' :: 't' :: escapeJsonChars rest
  | c :: rest => c :: escapeJsonChars rest

def jsonStr (s : String) : String :=
  "\"" ++ String.ofList (escapeJsonChars s.toList) ++ "\""

def jsonNat (n : Nat) : String :=
  toString n

def jsonArray (items : Array String) : String :=
  "[" ++ String.intercalate ", " items.toList ++ "]"

def jsonStringArray (items : Array String) : String :=
  jsonArray (items.map jsonStr)

def indent (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

def nodeKindClass (kind : String) : String :=
  if kind = "action" then "action" else "proof"

def nodeToJson (node : BlueprintNode) : String :=
  let fields := #[
    s!"\"id\": {jsonStr node.id}",
    s!"\"kind\": {jsonStr node.kind}",
    s!"\"class\": {jsonStr (nodeKindClass node.kind)}",
    s!"\"name\": {jsonStr node.nodeName}",
    s!"\"type\": {jsonStr node.typeText}",
    s!"\"label\": {jsonStr node.label}",
    s!"\"raw_text\": {jsonStr node.rawText}",
    s!"\"source_line\": {jsonNat node.sourceLine}",
    s!"\"uses_local\": {jsonStringArray node.usesLocal}",
    s!"\"uses_global\": {jsonStringArray node.usesGlobal}",
    s!"\"goals_before\": {jsonStringArray node.goalsBefore}",
    s!"\"goals_after\": {jsonStringArray node.goalsAfter}",
    s!"\"local_context\": {jsonStringArray node.localContext}",
    s!"\"expr_type\": {jsonStr node.exprType}",
    s!"\"expected_type\": {jsonStr node.expectedType}",
    s!"\"semantic_uses_local\": {jsonStringArray node.semanticUsesLocal}",
    s!"\"semantic_uses_global\": {jsonStringArray node.semanticUsesGlobal}"
  ]
  "{\n" ++ indent 6 ++ String.intercalate (",\n" ++ indent 6) fields.toList ++ "\n" ++ indent 4 ++ "}"

def edgeToJson (edge : BlueprintEdge) : String :=
  let fields := #[
    s!"\"from\": {jsonStr edge.fromId}",
    s!"\"to\": {jsonStr edge.toId}",
    s!"\"kind\": {jsonStr edge.kind}",
    s!"\"label\": {jsonStr edge.label}"
  ]
  "{\n" ++ indent 6 ++ String.intercalate (",\n" ++ indent 6) fields.toList ++ "\n" ++ indent 4 ++ "}"

def blueprintToJson (bp : Blueprint) : String :=
  let theoremFields := #[
    s!"\"name\": {jsonStr bp.theoremName}",
    s!"\"type\": {jsonStr bp.theoremType}",
    s!"\"source_file\": {jsonStr bp.sourceFile}"
  ]
  let theoremJson :=
    "{\n" ++ indent 4 ++ String.intercalate (",\n" ++ indent 4) theoremFields.toList ++ "\n" ++ indent 2 ++ "}"
  let nodesJson :=
    "[\n" ++ indent 4 ++ String.intercalate (",\n" ++ indent 4) (bp.nodes.map nodeToJson).toList ++ "\n" ++ indent 2 ++ "]"
  let edgesJson :=
    "[\n" ++ indent 4 ++ String.intercalate (",\n" ++ indent 4) (bp.edges.map edgeToJson).toList ++ "\n" ++ indent 2 ++ "]"
  let fields := #[
    "\"schema_version\": \"0.1.0\"",
    "\"extraction_mode\": \"syntax_infotree_expr_primary\"",
    s!"\"theorem\": {theoremJson}",
    s!"\"nodes\": {nodesJson}",
    s!"\"edges\": {edgesJson}"
  ]
  "{\n" ++ indent 2 ++ String.intercalate (",\n" ++ indent 2) fields.toList ++ "\n}\n"

end ProofStruct
