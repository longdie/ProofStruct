import Lean
import ProofStruct.Extract.Graph

namespace ProofStruct

open Lean

private def jsonField (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

private def jsonStrField (j : Json) (key : String) (default : String := "") :
    Except String String := do
  match j.getObjVal? key with
  | .ok value => value.getStr?
  | .error _ => pure default

private def jsonNatField (j : Json) (key : String) (default : Nat := 0) :
    Except String Nat := do
  match j.getObjVal? key with
  | .ok value => fromJson? value
  | .error _ => pure default

private def jsonStringArrayField (j : Json) (key : String) :
    Except String (Array String) := do
  match j.getObjVal? key with
  | .ok value =>
      let values ← value.getArr?
      values.mapM (fun item => item.getStr?)
  | .error _ => pure #[]

private def nodeFromJson (j : Json) : Except String BlueprintNode := do
  pure {
    id := ← jsonStrField j "id"
    kind := ← jsonStrField j "kind"
    nodeName := ← jsonStrField j "name"
    typeText := ← jsonStrField j "type"
    label := ← jsonStrField j "label"
    rawText := ← jsonStrField j "raw_text"
    sourceLine := ← jsonNatField j "source_line"
    usesLocal := ← jsonStringArrayField j "uses_local"
    usesGlobal := ← jsonStringArrayField j "uses_global"
    goalsBefore := ← jsonStringArrayField j "goals_before"
    goalsAfter := ← jsonStringArrayField j "goals_after"
    localContext := ← jsonStringArrayField j "local_context"
    exprType := ← jsonStrField j "expr_type"
    expectedType := ← jsonStrField j "expected_type"
    semanticUsesLocal := ← jsonStringArrayField j "semantic_uses_local"
    semanticUsesGlobal := ← jsonStringArrayField j "semantic_uses_global"
  }

private def edgeFromJson (j : Json) : Except String BlueprintEdge := do
  pure {
    fromId := ← jsonStrField j "from"
    toId := ← jsonStrField j "to"
    kind := ← jsonStrField j "kind"
    label := ← jsonStrField j "label"
  }

def blueprintFromJson (j : Json) : Except String Blueprint := do
  let thmJson ← jsonField j "theorem"
  let nodeJsons ← (← jsonField j "nodes").getArr?
  let edgeJsons ← (← jsonField j "edges").getArr?
  pure {
    theoremName := ← jsonStrField thmJson "name"
    theoremType := ← jsonStrField thmJson "type"
    sourceFile := ← jsonStrField thmJson "source_file"
    nodes := ← nodeJsons.mapM nodeFromJson
    edges := ← edgeJsons.mapM edgeFromJson
  }

def blueprintFromJsonString (text : String) : Except String Blueprint := do
  let json ← Json.parse text
  blueprintFromJson json

end ProofStruct
