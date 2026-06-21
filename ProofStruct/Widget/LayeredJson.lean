import Lean
import ProofStruct.Extract.Graph

namespace ProofStruct

open Lean

structure InfoviewSourceRange where
  startLine : Nat := 0
  endLine : Nat := 0
deriving Repr, Inhabited

structure InfoviewPlanNode where
  id : String
  kind : String
  label : String := ""
  detailLabel : String := ""
  orderIndex : Nat := 0
  sourceRange : InfoviewSourceRange := {}
  rawText : String := ""
  displayText : String := ""
  mainTactic : String := ""
  tactics : Array String := #[]
  inputs : Array String := #[]
  outputs : Array String := #[]
  solves : Array String := #[]
  opensSubgoals : Array String := #[]
  displayInputs : Array String := #[]
  displayOutputs : Array String := #[]
  displaySolves : Array String := #[]
  displayOpensSubgoals : Array String := #[]
  roleSummary : String := ""
  goalsBefore : Array String := #[]
  goalsAfter : Array String := #[]
  localContextBefore : Array String := #[]
  localContextAfter : Array String := #[]
  usedGlobals : Array String := #[]
  displayUsedGlobals : Array String := #[]
  branchId : String := ""
  branchLabel : String := ""
  parentSplit : String := ""
  branchIndex : Nat := 0
  evidenceNodeIds : Array String := #[]
  internalEvidenceNodeIds : Array String := #[]
  boundaryNodeIds : Array String := #[]
  evidenceEdgeIds : Array String := #[]
deriving Repr, Inhabited

structure InfoviewPlanEdge where
  id : String
  fromId : String
  toId : String
  kind : String
  relation : String := ""
  goalKey : String := ""
  label : String := ""
  visibleByDefault : Bool := true
  orderIndex : Nat := 0
deriving Repr, Inhabited

structure InfoviewEvidenceNode where
  base : BlueprintNode
  className : String := ""
  displayName : String := ""
  displayType : String := ""
  displayLabel : String := ""
  hiddenByDefault : Bool := false
  scopeId : String := ""
deriving Repr, Inhabited

structure InfoviewEvidenceEdge where
  id : String
  fromId : String
  toId : String
  kind : String
  label : String := ""
deriving Repr, Inhabited

structure InfoviewLayeredBlueprint where
  schemaVersion : String := ""
  theoremName : String
  theoremType : String := ""
  sourceFile : String := ""
  extractionMode : String := ""
  planNodes : Array InfoviewPlanNode := #[]
  planEdges : Array InfoviewPlanEdge := #[]
  evidenceNodes : Array InfoviewEvidenceNode := #[]
  evidenceEdges : Array InfoviewEvidenceEdge := #[]
deriving Repr, Inhabited

private def jsonField (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

private def jsonObjField (j : Json) (key : String) : Except String Json := do
  match j.getObjVal? key with
  | .ok value => pure value
  | .error _ => pure (Json.mkObj [])

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

private def jsonBoolField (j : Json) (key : String) (default : Bool := false) :
    Except String Bool := do
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

private def sourceRangeFromJson (j : Json) : Except String InfoviewSourceRange := do
  pure {
    startLine := ← jsonNatField j "start_line"
    endLine := ← jsonNatField j "end_line"
  }

private def planNodeFromJson (j : Json) : Except String InfoviewPlanNode := do
  pure {
    id := ← jsonStrField j "id"
    kind := ← jsonStrField j "kind"
    label := ← jsonStrField j "label"
    detailLabel := ← jsonStrField j "detail_label"
    orderIndex := ← jsonNatField j "order_index"
    sourceRange := ← sourceRangeFromJson (← jsonObjField j "source_range")
    rawText := ← jsonStrField j "raw_text"
    displayText := ← jsonStrField j "display_text"
    mainTactic := ← jsonStrField j "main_tactic"
    tactics := ← jsonStringArrayField j "tactics"
    inputs := ← jsonStringArrayField j "inputs"
    outputs := ← jsonStringArrayField j "outputs"
    solves := ← jsonStringArrayField j "solves"
    opensSubgoals := ← jsonStringArrayField j "opens_subgoals"
    displayInputs := ← jsonStringArrayField j "display_inputs"
    displayOutputs := ← jsonStringArrayField j "display_outputs"
    displaySolves := ← jsonStringArrayField j "display_solves"
    displayOpensSubgoals := ← jsonStringArrayField j "display_opens_subgoals"
    roleSummary := ← jsonStrField j "role_summary"
    goalsBefore := ← jsonStringArrayField j "goals_before"
    goalsAfter := ← jsonStringArrayField j "goals_after"
    localContextBefore := ← jsonStringArrayField j "local_context_before"
    localContextAfter := ← jsonStringArrayField j "local_context_after"
    usedGlobals := ← jsonStringArrayField j "used_globals"
    displayUsedGlobals := ← jsonStringArrayField j "display_used_globals"
    branchId := ← jsonStrField j "branch_id"
    branchLabel := ← jsonStrField j "branch_label"
    parentSplit := ← jsonStrField j "parent_split"
    branchIndex := ← jsonNatField j "branch_index"
    evidenceNodeIds := ← jsonStringArrayField j "evidence_node_ids"
    internalEvidenceNodeIds := ← jsonStringArrayField j "internal_evidence_node_ids"
    boundaryNodeIds := ← jsonStringArrayField j "boundary_node_ids"
    evidenceEdgeIds := ← jsonStringArrayField j "evidence_edge_ids"
  }

private def planEdgeFromJson (j : Json) : Except String InfoviewPlanEdge := do
  pure {
    id := ← jsonStrField j "id"
    fromId := ← jsonStrField j "from"
    toId := ← jsonStrField j "to"
    kind := ← jsonStrField j "kind"
    relation := ← jsonStrField j "relation"
    goalKey := ← jsonStrField j "goal_key"
    label := ← jsonStrField j "label"
    visibleByDefault := ← jsonBoolField j "visible_by_default" true
    orderIndex := ← jsonNatField j "order_index"
  }

private def evidenceNodeFromJson (j : Json) : Except String InfoviewEvidenceNode := do
  let className ← jsonStrField j "class"
  pure {
    base := {
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
    className := className
    displayName := ← jsonStrField j "display_name"
    displayType := ← jsonStrField j "display_type"
    displayLabel := ← jsonStrField j "display_label"
    hiddenByDefault := ← jsonBoolField j "hidden_by_default" false
    scopeId := ← jsonStrField j "scope_id"
  }

private def evidenceEdgeFromJson (idx : Nat) (j : Json) : Except String InfoviewEvidenceEdge := do
  let parsedId ← jsonStrField j "id"
  pure {
    id := if parsedId = "" then s!"e{idx}" else parsedId
    fromId := ← jsonStrField j "from"
    toId := ← jsonStrField j "to"
    kind := ← jsonStrField j "kind"
    label := ← jsonStrField j "label"
  }

private def parseEvidenceEdges (edgeJsons : Array Json) :
    Except String (Array InfoviewEvidenceEdge) := do
  let mut out : Array InfoviewEvidenceEdge := #[]
  for i in [:edgeJsons.size] do
    out := out.push (← evidenceEdgeFromJson (i + 1) edgeJsons[i]!)
  pure out

def layeredBlueprintFromJson (j : Json) : Except String InfoviewLayeredBlueprint := do
  let theoremJson ← jsonField j "theorem"
  let planGraphJson ← jsonField j "plan_graph"
  let evidenceGraphJson ← jsonField j "evidence_graph"
  let planNodeJsons ← (← jsonField planGraphJson "nodes").getArr?
  let planEdgeJsons ← (← jsonField planGraphJson "edges").getArr?
  let evidenceNodeJsons ← (← jsonField evidenceGraphJson "nodes").getArr?
  let evidenceEdgeJsons ← (← jsonField evidenceGraphJson "edges").getArr?
  pure {
    schemaVersion := ← jsonStrField j "schema_version"
    theoremName := ← jsonStrField theoremJson "name"
    theoremType := ← jsonStrField theoremJson "type"
    sourceFile := ← jsonStrField theoremJson "source_file"
    extractionMode := ← jsonStrField j "extraction_mode"
    planNodes := ← planNodeJsons.mapM planNodeFromJson
    planEdges := ← planEdgeJsons.mapM planEdgeFromJson
    evidenceNodes := ← evidenceNodeJsons.mapM evidenceNodeFromJson
    evidenceEdges := ← parseEvidenceEdges evidenceEdgeJsons
  }

def layeredBlueprintFromJsonString (text : String) : Except String InfoviewLayeredBlueprint := do
  let json ← Json.parse text
  layeredBlueprintFromJson json

def InfoviewEvidenceNode.toBlueprintNode (node : InfoviewEvidenceNode) : BlueprintNode :=
  let displayName :=
    if node.displayName != "" then node.displayName else node.base.nodeName
  let displayType :=
    if node.displayType != "" then node.displayType else node.base.typeText
  let displayLabel :=
    if node.displayLabel != "" then node.displayLabel else node.base.label
  { node.base with
    nodeName := displayName
    typeText := displayType
    label := displayLabel
  }

def InfoviewEvidenceEdge.toBlueprintEdge (edge : InfoviewEvidenceEdge) : BlueprintEdge :=
  {
    fromId := edge.fromId
    toId := edge.toId
    kind := edge.kind
    label := edge.label
  }

private def visibleEvidenceNodes (nodes : Array InfoviewEvidenceNode) :
    Array InfoviewEvidenceNode :=
  nodes.filter (fun node => !node.hiddenByDefault)

private def visibleEvidenceIds (nodes : Array InfoviewEvidenceNode) : Array String :=
  nodes.map (fun node => node.base.id)

private def evidenceEdgesForVisibleNodes
    (edges : Array InfoviewEvidenceEdge) (visibleIds : Array String) :
    Array InfoviewEvidenceEdge :=
  edges.filter (fun edge => visibleIds.contains edge.fromId && visibleIds.contains edge.toId)

def InfoviewLayeredBlueprint.fullEvidenceBlueprint
    (lb : InfoviewLayeredBlueprint) (nameSuffix : String := "full") : Blueprint :=
  let nodes := visibleEvidenceNodes lb.evidenceNodes
  let ids := visibleEvidenceIds nodes
  let edges := evidenceEdgesForVisibleNodes lb.evidenceEdges ids
  {
    theoremName := s!"{lb.theoremName}-{nameSuffix}"
    theoremType := lb.theoremType
    sourceFile := lb.sourceFile
    nodes := nodes.map InfoviewEvidenceNode.toBlueprintNode
    edges := edges.map InfoviewEvidenceEdge.toBlueprintEdge
  }

def InfoviewLayeredBlueprint.evidenceBlueprintForPlan
    (lb : InfoviewLayeredBlueprint) (plan : InfoviewPlanNode) : Blueprint :=
  let wantedNodeIds := plan.evidenceNodeIds
  let wantedEdgeIds := plan.evidenceEdgeIds
  let nodes :=
    lb.evidenceNodes.filter (fun node =>
      !node.hiddenByDefault && wantedNodeIds.contains node.base.id)
  let ids := visibleEvidenceIds nodes
  let edges :=
    lb.evidenceEdges.filter (fun edge =>
      wantedEdgeIds.contains edge.id &&
        ids.contains edge.fromId &&
        ids.contains edge.toId)
  {
    theoremName := s!"{lb.theoremName}-{plan.id}"
    theoremType := if plan.roleSummary != "" then plan.roleSummary else lb.theoremType
    sourceFile := lb.sourceFile
    nodes := nodes.map InfoviewEvidenceNode.toBlueprintNode
    edges := edges.map InfoviewEvidenceEdge.toBlueprintEdge
  }

end ProofStruct
