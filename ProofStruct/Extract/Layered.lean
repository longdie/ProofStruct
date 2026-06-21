import ProofStruct.Extract.Graph
import ProofStruct.Extract.Json

namespace ProofStruct

structure EvidenceNode where
  base : BlueprintNode
  className : String := ""
  displayName : String := ""
  displayType : String := ""
  displayLabel : String := ""
  hiddenByDefault : Bool := false
  versionIndex : Nat := 0
  versionCount : Nat := 0
  scopeId : String := ""
deriving Repr, Inhabited

structure GoalFlow where
  primary : String := "main"
  before : Array String := #[]
  after : Array String := #[]
deriving Repr, Inhabited

structure StateDelta where
  addedLocals : Array String := #[]
  closedGoals : Array String := #[]
  openedGoals : Array String := #[]
deriving Repr, Inhabited

structure PlanNode where
  id : String
  kind : String
  label : String := ""
  detailLabel : String := ""
  orderIndex : Nat := 0
  startLine : Nat := 0
  endLine : Nat := 0
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
  stateDelta : StateDelta := {}
  usedGlobals : Array String := #[]
  displayUsedGlobals : Array String := #[]
  branchId : String := ""
  branchLabel : String := ""
  parentSplit : String := ""
  branchIndex : Nat := 0
  goalFlow : GoalFlow := {}
  evidenceNodeIds : Array String := #[]
  internalEvidenceNodeIds : Array String := #[]
  boundaryNodeIds : Array String := #[]
  evidenceEdgeIds : Array String := #[]
deriving Repr, Inhabited

structure PlanEdge where
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

structure LayeredBlueprint where
  theoremName : String
  theoremType : String := ""
  sourceFile : String := ""
  extractionMode : String := "syntax_infotree_expr_primary"
  planNodes : Array PlanNode := #[]
  planEdges : Array PlanEdge := #[]
  evidenceNodes : Array EvidenceNode := #[]
  evidenceEdges : Array BlueprintEdge := #[]
deriving Repr, Inhabited

private def containsSubstr (s needle : String) : Bool :=
  match s.splitOn needle with
  | [] => false
  | [_] => false
  | _ => true

private def dropChars (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

private def trim (s : String) : String :=
  s.trimAscii.toString

private def normalizeWhitespace (s : String) : String :=
  let normalized := String.ofList <| s.toList.map (fun c =>
    if c = '\n' || c = '\t' || c = '\r' then ' ' else c)
  String.intercalate " " ((normalized.splitOn " ").filter (· ≠ ""))

private def compact (s : String) (limit : Nat := 100) : String :=
  let text := normalizeWhitespace s
  if text.length <= limit then
    text
  else
    String.ofList (text.toList.take (limit - 1)) ++ "…"

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

private def uniquePush (items : Array String) (item : String) : Array String :=
  if item = "" || items.contains item then items else items.push item

private def uniqueStrings (items : Array String) : Array String :=
  items.foldl uniquePush #[]

private def mergeStrings (left right : Array String) : Array String :=
  right.foldl uniquePush left

private def concatStringArrays (items : Array (Array String)) : Array String :=
  items.foldl mergeStrings #[]

private def nodeClass (node : BlueprintNode) : String :=
  nodeKindClass node.kind

private def nodeNameOrId (node : EvidenceNode) : String :=
  if node.base.nodeName ≠ "" then node.base.nodeName else node.base.id

private def displayNodeText (node : EvidenceNode) : String :=
  if node.displayLabel ≠ "" then node.displayLabel
  else if node.base.label ≠ "" then node.base.label
  else if node.base.typeText ≠ "" then node.base.typeText
  else nodeNameOrId node

private def displayNodeRef (node : EvidenceNode) : String :=
  compact (displayNodeText node) 120

private def lowValueGlobalPrefixes : Array String := #[
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
  "NonUnital"
]

private def lowValueGlobals : Array String := #[
  "Nat",
  "Int",
  "Prime",
  "IsCoprime",
  "Not",
  "Dvd.dvd",
  "HAdd.hAdd",
  "HMul.hMul",
  "HSub.hSub",
  "OfNat.ofNat"
]

private def startsWithAny (s : String) (prefixes : Array String) : Bool :=
  prefixes.any (fun pref => s.startsWith pref)

private def prettyType (s : String) : String :=
  normalizeWhitespace s

private def isLowValueNode (node : BlueprintNode) : Bool :=
  let name := node.nodeName
  let typ := node.typeText
  name.startsWith "inst" ||
    containsSubstr name "✝" ||
    containsSubstr typ "_fvar" ||
    typ.startsWith "failed to pretty print expression"

private def baseDisplayName (node : BlueprintNode) : String :=
  if node.nodeName ≠ "" then node.nodeName else node.id

private def refreshEvidenceNode (node : EvidenceNode) (displayName? : Option String := none)
    (scopeId : String := node.scopeId) : EvidenceNode :=
  if node.base.kind = "action" || node.className = "action" then
    let label :=
      if node.base.label ≠ "" then node.base.label
      else if node.base.rawText ≠ "" then node.base.rawText
      else if node.base.nodeName ≠ "" then node.base.nodeName
      else node.base.id
    { node with
      className := "action"
      displayName := displayName?.getD (baseDisplayName node.base)
      displayType := ""
      displayLabel := label
      hiddenByDefault := false
      scopeId := scopeId }
  else
    let displayName := displayName?.getD (baseDisplayName node.base)
    let displayType := prettyType node.base.typeText
    let displayLabel :=
      if node.base.kind = "theorem_goal" || node.base.kind = "subgoal" then
        if displayType ≠ "" then displayType
        else if node.base.label ≠ "" then node.base.label
        else displayName
      else if displayType ≠ "" then
        s!"{displayName} : {displayType}"
      else
        displayName
    { node with
      className := "proof"
      displayName := displayName
      displayType := displayType
      displayLabel := displayLabel
      hiddenByDefault := isLowValueNode node.base
      scopeId := scopeId }

private def enrichEvidenceNodes (nodes : Array BlueprintNode) : Array EvidenceNode :=
  let initial := nodes.map (fun node => refreshEvidenceNode { base := node, className := nodeClass node })
  initial.mapIdx (fun i node =>
    if node.className = "action" || node.hiddenByDefault || node.base.nodeName = "" then
      node
    else
      let same := initial.filter (fun other =>
        other.className ≠ "action" &&
          !other.hiddenByDefault &&
          other.base.nodeName = node.base.nodeName)
      if same.size <= 1 then
        node
      else
        let preceding := (initial.take i).filter (fun other =>
          other.className ≠ "action" &&
            !other.hiddenByDefault &&
            other.base.nodeName = node.base.nodeName)
        let versionIndex := preceding.size + 1
        let displayName := s!"{node.base.nodeName}#{versionIndex}"
        refreshEvidenceNode { node with versionIndex := versionIndex, versionCount := same.size } (some displayName))

private def evidenceNodeById? (nodes : Array EvidenceNode) (id : String) : Option EvidenceNode :=
  nodes.find? (fun node => node.base.id = id)

private def planNodeById? (nodes : Array PlanNode) (id : String) : Option PlanNode :=
  nodes.find? (fun node => node.id = id)

private def assocGet? (items : Array (String × String)) (key : String) : Option String :=
  match items.find? (fun item => item.fst = key) with
  | some item => some item.snd
  | none => none

private def assocSet (items : Array (String × String)) (key value : String) : Array (String × String) :=
  let items := items.filter (fun item => item.fst ≠ key)
  items.push (key, value)

private def edgeId (_edge : BlueprintEdge) (idx : Nat) : String :=
  s!"e{idx}"

private def lineEnd (node : EvidenceNode) : Nat :=
  node.base.sourceLine + node.base.rawText.toList.foldl (fun acc c => if c = '\n' then acc + 1 else acc) 0

private def parseActionIndex (id : String) : Nat :=
  if id.startsWith "a_sem_" then
    match (dropChars id "a_sem_".length).splitOn "_" with
    | part :: _ => part.toNat?.getD 1000000000
    | _ => 1000000000
  else
    1000000000

private def actionLt (left right : EvidenceNode) : Bool :=
  if left.base.sourceLine != right.base.sourceLine then
    left.base.sourceLine < right.base.sourceLine
  else
    let li := parseActionIndex left.base.id
    let ri := parseActionIndex right.base.id
    if li != ri then li < ri else left.base.id < right.base.id

private def rhsAfterAssign (raw : String) : String :=
  match raw.splitOn ":=" with
  | _lhs :: rhsParts => trim (String.intercalate ":=" rhsParts)
  | _ => ""

private def isByContainer (node : EvidenceNode) : Bool :=
  let name := node.base.nodeName
  let raw := node.base.rawText
  (name = "have" || name = "let" || name = "suffices" || name = "show") &&
    containsSubstr raw ":=" &&
    (rhsAfterAssign raw).startsWith "by"

private def isInlineByContainer (node : EvidenceNode) : Bool :=
  let name := node.base.nodeName
  (name = "exact" || name = "refine" || name = "apply" || name = "calc" || name = "constructor") &&
    containsSubstr (" " ++ node.base.rawText ++ " ") " by "

private def isActionContainer (node : EvidenceNode) : Bool :=
  isByContainer node || isInlineByContainer node

private def containsAction (container child : EvidenceNode) (endLine? : Option Nat := none) : Bool :=
  if container.base.id = child.base.id then
    false
  else
    let start := container.base.sourceLine
    let endLine := endLine?.getD (lineEnd container)
    let childLine := child.base.sourceLine
    start <= childLine && childLine <= endLine

private def goalCaseKey (goal : String) : String :=
  let rec loop : List String → String
    | [] => "main"
    | line :: rest =>
        let line := trim line
        if line.startsWith "case " then
          let caseName := trim (dropChars line "case ".length)
          if caseName = "" then "case" else caseName
        else
          loop rest
  loop (goal.splitOn "\n")

private def goalKeys (goals : Array String) : Array String :=
  uniqueStrings (goals.map goalCaseKey)

private def inferredContainerEnd (action : EvidenceNode) (sortedActions : Array EvidenceNode)
    (index : Nat) : Nat :=
  let raw := trim action.base.rawText
  let defaultEnd := lineEnd action
  if !(isByContainer action && raw.endsWith "by" && !(containsSubstr raw "\n")) then
    defaultEnd
  else
    let afterKeys := goalKeys action.base.goalsAfter
    if afterKeys.isEmpty then
      defaultEnd
    else Id.run do
      let mut endLine := defaultEnd
      let startLine := action.base.sourceLine
      for later in sortedActions.extract (index + 1) sortedActions.size do
        let laterLine := later.base.sourceLine
        if laterLine > startLine then
          let laterBefore := goalKeys later.base.goalsBefore
          if laterBefore.any (fun key => afterKeys.contains key) then
            return endLine
          else
            endLine := Nat.max endLine laterLine
      return endLine

structure BlockContainer where
  node : EvidenceNode
  blockIndex : Nat
  endLine : Nat
deriving Repr, Inhabited

private def transformTactics : Array String := #["rw", "simp", "change", "convert", "subst"]
private def autoTactics : Array String := #["ring", "ring_nf", "omega", "norm_num", "linarith", "nlinarith", "aesop", "abel"]
private def solveTactics : Array String := #["exact", "assumption", "trivial", "contradiction", "rfl", "simpa", "simp", "infer_instance"]
private def inputEdgeKinds : Array String := #["input_to_action"]
private def actionToOutputKinds : Array String := #["action_to_output", "action_to_subgoal", "action_solves_goal"]
private def ignoredPlanEdgeKinds : Array String := #["context_to_goal", "goal_to_action"]

private def isTransformOnly (block : Array EvidenceNode) : Bool :=
  match block[0]? with
  | some action => block.size = 1 && transformTactics.contains action.base.nodeName
  | none => false

private def mergeTransformBlocks (blocks : Array (Array EvidenceNode)) : Array (Array EvidenceNode) := Id.run do
  let mut merged : Array (Array EvidenceNode) := #[]
  for block in blocks do
    match merged.back? with
    | some previous =>
        if isTransformOnly previous && isTransformOnly block then
          merged := merged.pop
          merged := merged.push (previous ++ block)
        else
          merged := merged.push block
    | none =>
        merged := merged.push block
  return merged

private def buildActionBlocks (actions : Array EvidenceNode) : Array (Array EvidenceNode) := Id.run do
  let sortedActions := actions.qsort actionLt
  let mut blocks : Array (Array EvidenceNode) := #[]
  let mut containers : Array BlockContainer := #[]
  for h : index in [:sortedActions.size] do
    let action := sortedActions[index]
    let mut assigned := false
    for container in containers.reverse do
      if !assigned && containsAction container.node action (some container.endLine) then
        let oldBlock := blocks[container.blockIndex]!
        blocks := blocks.set! container.blockIndex (oldBlock.push action)
        assigned := true
    if !assigned then
      let blockIndex := blocks.size
      blocks := blocks.push #[action]
      if isActionContainer action then
        containers := containers.push {
          node := action
          blockIndex := blockIndex
          endLine := inferredContainerEnd action sortedActions index
        }
    containers := containers.filter (fun item => item.endLine >= action.base.sourceLine)
  return mergeTransformBlocks blocks

private def parseDeclOutput (node : EvidenceNode) : String × String :=
  let raw := trim node.base.rawText
  let name := node.base.nodeName
  if !(name = "have" || name = "let" || name = "suffices" || name = "show") then
    ("", "")
  else
    let body := if raw.startsWith name then trim (dropChars raw name.length) else raw
    let beforeAssign :=
      match body.splitOn ":=" with
      | lhs :: _ => trim lhs
      | _ => body
    match beforeAssign.splitOn ":" with
    | lhs :: typParts =>
        let lhs := trim lhs
        let outName := (lhs.splitOn " ").filter (· ≠ "") |>.head?.getD ""
        (outName, trim (String.intercalate ":" typParts))
    | _ =>
        let parts := (beforeAssign.splitOn " ").filter (· ≠ "")
        (parts.head?.getD "", "")

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c = '_' || c = '\''

private def identTokens (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut current : List Char := []
  let flush := fun (out : Array String) (current : List Char) =>
    if current.isEmpty then out else out.push (String.ofList current.reverse)
  for c in s.toList do
    if isIdentChar c then
      current := c :: current
    else
      out := flush out current
      current := []
  out := flush out current
  return out

private def introducedNamesFromRaw (raw : String) : Array String :=
  let text := trim raw
  let parts := (text.splitOn " ").filter (· ≠ "")
  match parts with
  | head :: rest =>
      if head = "intro" || head = "intros" || head = "rintro" || head = "ext" then
        let stopWords : Array String := #["with", "using", "at", "by", "show"]
        (identTokens (String.intercalate " " rest)).filter (fun token => !stopWords.contains token)
      else
        #[]
  | _ => #[]

private def firstDisplay (nodes : Array EvidenceNode) : String :=
  match nodes[0]? with
  | some node => node.displayName
  | none => ""

private def nodeTitle (node : EvidenceNode) (outputs solves : Array EvidenceNode) : String × String :=
  let name := node.base.nodeName
  if name = "intro" || name = "intros" || name = "rintro" || name = "ext" then
    let names := introducedNamesFromRaw node.base.rawText
    if !names.isEmpty then
      (s!"{name} -> {String.intercalate ", " (names.toList.take 4)}", "")
    else
      (name, compact (if node.base.label ≠ "" then node.base.label else node.base.rawText) 90)
  else if name = "have" || name = "let" || name = "suffices" || name = "show" then
    let (parsedName, parsedType) := parseDeclOutput node
    let outName :=
      if parsedName ≠ "" then parsedName
      else match outputs[0]? with
        | some out => if out.displayName ≠ "" then out.displayName else nodeNameOrId out
        | none => ""
    let outType :=
      if parsedType ≠ "" then parsedType
      else match outputs[0]? with
        | some out => if out.displayType ≠ "" then out.displayType else out.base.typeText
        | none => ""
    (trim s!"{name} {outName}", if outType ≠ "" then prettyType outType else compact node.base.label 90)
  else
    match solves[0]? with
    | some solved =>
        let target :=
          if solved.displayType ≠ "" then solved.displayType
          else if solved.base.typeText ≠ "" then solved.base.typeText
          else solved.base.label
        if solved.base.kind = "theorem_goal" then
          ("close theorem goal", target)
        else
          (s!"solve {nodeNameOrId solved}", target)
    | none =>
        match outputs[0]? with
        | some output =>
            (s!"{name} -> {nodeNameOrId output}",
             if output.displayType ≠ "" then output.displayType
             else if output.base.typeText ≠ "" then output.base.typeText
             else output.base.label)
        | none =>
            (if name ≠ "" then name else "proof", compact (if node.base.label ≠ "" then node.base.label else node.base.rawText) 90)

private def classifyBlock (actions outputs solves opens : Array EvidenceNode) : String :=
  let first := match actions[0]? with | some node => node.base.nodeName | none => ""
  let outputKinds := outputs.map (fun node => node.base.kind)
  if first = "intro" || first = "intros" || first = "rintro" then "introduce_context"
  else if first = "by_cases" || first = "cases" || first = "rcases" then "case_split"
  else if first = "calc" then "calculation_chain"
  else if first = "have" || first = "suffices" || first = "show" then "prove_intermediate"
  else if first = "let" || outputKinds.contains "constructed_object" then "construct_object"
  else if autoTactics.contains first then "automation"
  else if transformTactics.contains first || ((first = "simp" || first = "simpa") && solves.isEmpty) then "transform_goal"
  else if !opens.isEmpty || first = "constructor" || first = "refine" || first = "apply" || first = "ext" then "split_goal"
  else if !solves.isEmpty then
    if solves.any (fun node => node.base.kind = "theorem_goal") then "close_goal" else "solve_goal"
  else if solveTactics.contains first then "solve_goal"
  else "unknown"

private def blockSourceText (actions : Array EvidenceNode) : String := Id.run do
  let mut out : Array String := #[]
  for action in actions do
    let text := trim action.base.rawText
    if text ≠ "" then
      if !(out.any (fun existing => text ≠ existing && containsSubstr existing text)) then
        out := out.filter (fun existing => !(existing ≠ text && containsSubstr text existing))
        unless out.contains text do
          out := out.push text
  return String.intercalate "\n" out.toList

private def blockDisplayText (rawText kind : String) (opens solves : Array EvidenceNode) : String := Id.run do
  let mut extra : Array String := #[]
  if !opens.isEmpty then
    extra := extra.push "opens subgoals:"
    for node in opens do
      extra := extra.push s!"- {compact (displayNodeText node) 140}"
  if !solves.isEmpty && (kind = "solve_goal" || kind = "close_goal" || kind = "automation") then
    extra := extra.push "solves:"
    for node in solves do
      extra := extra.push s!"- {compact (displayNodeText node) 140}"
  if !extra.isEmpty && (rawText.splitOn "\n").length <= 1 then
    return trim rawText ++ "\n\n" ++ String.intercalate "\n" extra.toList
  else
    return rawText

private def blockGoalsAfter (actions : Array EvidenceNode) : Array String :=
  match actions[0]? with
  | none => #[]
  | some root =>
      if isByContainer root then
        root.base.goalsAfter
      else
        let rootRaw := root.base.rawText
        if actions.size > 1 &&
            (actions.extract 1 actions.size).all (fun child => containsSubstr rootRaw (trim child.base.rawText)) then
          root.base.goalsAfter
        else
          match actions.back? with
          | some last => last.base.goalsAfter
          | none => #[]

private def displayGlobals (globals : Array String) (limit : Nat := 5) : Array String := Id.run do
  let mut out : Array String := #[]
  for item in globals do
    if item ≠ "" && !out.contains item &&
        !startsWithAny item lowValueGlobalPrefixes &&
        !lowValueGlobals.contains item then
      out := out.push item
      if out.size >= limit then
        return out
  return out

private def roleSummary (kind mainTactic : String) (outputs solves opens : Array EvidenceNode) : String :=
  if kind = "introduce_context" then
    let names := (outputs.extract 0 (Nat.min outputs.size 4)).map nodeNameOrId
    if names.isEmpty then "introduce proof context" else s!"introduce {String.intercalate ", " names.toList}"
  else if kind = "prove_intermediate" then
    match outputs[0]? with
    | some node =>
        let name := if node.displayName ≠ "" then node.displayName else "intermediate result"
        let typ := if node.displayType ≠ "" then node.displayType else node.base.typeText
        if typ ≠ "" then s!"prove {name}: {compact typ 80}" else s!"prove {name}"
    | none => "prove intermediate result"
  else if kind = "construct_object" then
    let names := (outputs.extract 0 (Nat.min outputs.size 3)).map nodeNameOrId
    if names.isEmpty then "construct object" else s!"construct {String.intercalate ", " names.toList}"
  else if kind = "transform_goal" then s!"transform goal with {mainTactic}"
  else if kind = "calculation_chain" then "close goal by calculation chain"
  else if kind = "automation" then s!"solve side condition with {mainTactic}"
  else if kind = "split_goal" then
    if !opens.isEmpty then s!"split goal with {mainTactic}" else s!"apply structural step {mainTactic}"
  else if kind = "case_split" then s!"split cases with {mainTactic}"
  else if kind = "close_goal" then "close theorem goal"
  else if kind = "solve_goal" then
    match solves[0]? with
    | some node => s!"solve {displayNodeRef node}"
    | none => "solve current goal"
  else
    "proof step"

private def branchLabel (goalKey : String) : String :=
  if goalKey = "" || goalKey = "main" then "" else goalKey

private def assignBranchMetadata (planNodes : Array PlanNode) : Array PlanNode := Id.run do
  let mut nodes := planNodes.map (fun node =>
    let beforeKeys := goalKeys node.goalsBefore
    let afterKeys := goalKeys node.goalsAfter
    let primary := beforeKeys[0]?.getD "main"
    { node with
      goalFlow := { primary := primary, before := beforeKeys, after := afterKeys }
      branchId := if primary = "main" then "" else primary
      branchLabel := branchLabel primary
      parentSplit := ""
      branchIndex := 0 })
  for idx in [:nodes.size] do
    let node := nodes[idx]!
    let primary := node.goalFlow.primary
    if primary ≠ "main" then
      let mut parentId := ""
      let mut bestKey := ""
      for candidate in (nodes.extract 0 idx).reverse do
        if parentId = "" then
          for key in candidate.goalFlow.after do
            if parentId = "" && (primary = key || primary.startsWith (key ++ ".")) then
              parentId := candidate.id
              bestKey := key
      if parentId ≠ "" then
        let parent := planNodeById? nodes parentId
        let branchIndex :=
          match parent with
          | some p =>
              match p.goalFlow.after.findIdx? (fun key => key = bestKey) with
              | some i => i + 1
              | none => 0
          | none => 0
        nodes := nodes.set! idx { node with
          parentSplit := parentId
          branchIndex := branchIndex
          branchLabel := branchLabel (if bestKey = "" then primary else bestKey) }
  return nodes

private def namesFromNodes (nodes : Array EvidenceNode) : Array String :=
  uniqueStrings (nodes.map nodeNameOrId)

private def displayRefs (nodes : Array EvidenceNode) : Array String :=
  uniqueStrings ((nodes.filter (fun node => !node.hiddenByDefault)).map displayNodeRef)

private def refreshPlanDisplayRefs (planNodes : Array PlanNode) (evidenceNodes : Array EvidenceNode) :
    Array PlanNode :=
  planNodes.map (fun plan =>
    let internal := plan.internalEvidenceNodeIds.filterMap (evidenceNodeById? evidenceNodes)
    let boundary := plan.boundaryNodeIds.filterMap (evidenceNodeById? evidenceNodes)
    let outputNodes := internal.filter (fun node =>
      (node.base.kind = "intermediate" || node.base.kind = "constructed_object") &&
        node.className ≠ "action" && node.base.kind ≠ "action")
    let solveSet := plan.solves
    let openSet := plan.opensSubgoals
    let solveNodes := internal.filter (fun node =>
      (node.base.kind = "theorem_goal" || node.base.kind = "subgoal") &&
        solveSet.contains (nodeNameOrId node))
    let openNodes := internal.filter (fun node =>
      node.base.kind = "subgoal" && openSet.contains (nodeNameOrId node))
    { plan with
      displayInputs := displayRefs boundary
      displayOutputs := displayRefs outputNodes
      displaySolves := displayRefs solveNodes
      displayOpensSubgoals := displayRefs openNodes })

private def attachScopeMetadata (evidenceNodes : Array EvidenceNode) (planNodes : Array PlanNode) :
    Array EvidenceNode :=
  evidenceNodes.map (fun node =>
    let internalOwners :=
      planNodes.filter (fun plan => plan.internalEvidenceNodeIds.contains node.base.id)
    let ownerPlans :=
      if internalOwners.isEmpty then
        planNodes.filter (fun plan => plan.boundaryNodeIds.contains node.base.id)
      else
        internalOwners
    if ownerPlans.isEmpty then
      node
    else
      let scopes := uniqueStrings (ownerPlans.map (fun plan => if plan.branchId = "" then "main" else plan.branchId))
      if scopes.size ≠ 1 then
        node
      else
        let scopeId := scopes[0]!
        if node.versionCount > 1 && scopeId ≠ "main" && node.className ≠ "action" && node.base.kind ≠ "action" then
          refreshEvidenceNode { node with scopeId := scopeId } (some s!"{baseDisplayName node.base}@{scopeId}") scopeId
        else
          refreshEvidenceNode { node with scopeId := scopeId } (some node.displayName) scopeId)

private def outputLabel (node : EvidenceNode) : String :=
  if node.base.label ≠ "" then node.base.label else nodeNameOrId node

private def buildPlanNodes (evidenceNodes : Array EvidenceNode) (evidenceEdges : Array BlueprintEdge) :
    Array PlanNode × Array (String × String) × Array (String × String) :=
  let actions := evidenceNodes.filter (fun node =>
    (node.className = "action" || node.base.kind = "action") && node.base.sourceLine > 0)
  let blocks := buildActionBlocks actions
  Id.run do
    let mut actionToBlock : Array (String × String) := #[]
    let mut nodeOwner : Array (String × String) := #[]
    for h : idx in [:blocks.size] do
      let planId := s!"plan_{idx + 1}"
      for action in blocks[idx] do
        actionToBlock := assocSet actionToBlock action.base.id planId
        nodeOwner := assocSet nodeOwner action.base.id planId

    let mut planNodes : Array PlanNode := #[]
    for h : idx in [:blocks.size] do
      let planId := s!"plan_{idx + 1}"
      let blockActions := blocks[idx]
      let actionIds := blockActions.map (fun node => node.base.id)
      let mut internalNodeIds := actionIds
      let mut internalEdgeIds : Array String := #[]
      let mut boundaryNodeIds : Array String := #[]
      let mut outputs : Array EvidenceNode := #[]
      let mut solves : Array EvidenceNode := #[]
      let mut opens : Array EvidenceNode := #[]
      let mut inputs : Array EvidenceNode := #[]

      for hEdge : edgeIdx0 in [:evidenceEdges.size] do
        let edge := evidenceEdges[edgeIdx0]
        let edgeId := edgeId edge (edgeIdx0 + 1)
        let fromId := edge.fromId
        let toId := edge.toId
        let fromInside := actionIds.contains fromId || internalNodeIds.contains fromId
        let toInside := actionIds.contains toId || internalNodeIds.contains toId
        if actionIds.contains fromId && actionToOutputKinds.contains edge.kind then
          match evidenceNodeById? evidenceNodes toId with
          | some target =>
              internalNodeIds := uniquePush internalNodeIds target.base.id
              nodeOwner := assocSet nodeOwner target.base.id planId
              internalEdgeIds := uniquePush internalEdgeIds edgeId
              if edge.kind = "action_to_subgoal" then
                opens := opens.push target
              else if edge.kind = "action_solves_goal" then
                solves := solves.push target
              else
                outputs := outputs.push target
          | none => pure ()
        else if actionIds.contains toId && inputEdgeKinds.contains edge.kind then
          match evidenceNodeById? evidenceNodes fromId with
          | some source =>
              if !boundaryNodeIds.contains source.base.id && !internalNodeIds.contains source.base.id then
                boundaryNodeIds := boundaryNodeIds.push source.base.id
              inputs := inputs.push source
              internalEdgeIds := uniquePush internalEdgeIds edgeId
          | none => pure ()
        else if fromInside && toInside then
          internalEdgeIds := uniquePush internalEdgeIds edgeId

      let root := blockActions[0]!
      let title := nodeTitle root outputs solves
      let startLine := blockActions.foldl (fun acc node => Nat.min acc node.base.sourceLine) root.base.sourceLine
      let endLine := blockActions.foldl (fun acc node => Nat.max acc (lineEnd node)) 0
      let tactics := uniqueStrings (blockActions.map (fun node => node.base.nodeName))
      let rawText := blockSourceText blockActions
      let usedGlobals :=
        uniqueStrings <|
          concatStringArrays (blockActions.map (fun node => node.base.usesGlobal)) ++
          concatStringArrays (blockActions.map (fun node => node.base.semanticUsesGlobal))
      let displayUsed := displayGlobals usedGlobals
      let kind := classifyBlock blockActions outputs solves opens
      let displayText := blockDisplayText rawText kind opens solves
      let mut role := roleSummary kind root.base.nodeName outputs solves opens
      if kind = "introduce_context" then
        let rawNames := introducedNamesFromRaw rawText
        if !rawNames.isEmpty then
          role := s!"introduce {String.intercalate ", " (rawNames.toList.take 4)}"
      let goalsBefore := root.base.goalsBefore
      let goalsAfter := blockGoalsAfter blockActions
      let localContextBefore := root.base.localContext
      let addedLocals := uniqueStrings ((outputs.filter (fun node =>
        node.base.kind = "intermediate" || node.base.kind = "constructed_object")).map outputLabel)
      let planNode : PlanNode := {
        id := planId
        kind := kind
        label := title.fst
        detailLabel := title.snd
        orderIndex := idx + 1
        startLine := startLine
        endLine := endLine
        rawText := rawText
        displayText := displayText
        mainTactic := root.base.nodeName
        tactics := tactics
        inputs := namesFromNodes inputs
        outputs := namesFromNodes outputs
        solves := namesFromNodes solves
        opensSubgoals := namesFromNodes opens
        displayInputs := displayRefs inputs
        displayOutputs := displayRefs outputs
        displaySolves := displayRefs solves
        displayOpensSubgoals := displayRefs opens
        roleSummary := role
        goalsBefore := goalsBefore
        goalsAfter := goalsAfter
        localContextBefore := localContextBefore
        localContextAfter := #[]
        stateDelta := {
          addedLocals := addedLocals
          closedGoals := uniqueStrings (solves.map outputLabel)
          openedGoals := uniqueStrings (opens.map outputLabel)
        }
        usedGlobals := usedGlobals
        displayUsedGlobals := displayUsed
        evidenceNodeIds := uniqueStrings (internalNodeIds ++ boundaryNodeIds)
        internalEvidenceNodeIds := uniqueStrings internalNodeIds
        boundaryNodeIds := uniqueStrings boundaryNodeIds
        evidenceEdgeIds := uniqueStrings internalEdgeIds
      }
      planNodes := planNodes.push planNode
    return (planNodes, nodeOwner, actionToBlock)

private def firstFollowingWithGoal (planNodes : Array PlanNode) (startIdx : Nat) (goalKey : String) : String :=
  let candidates := planNodes.extract (startIdx + 1) planNodes.size
  match candidates.find? (fun node => node.goalFlow.primary = goalKey) with
  | some node => node.id
  | none => ""

private def addFlowPair (pairs : Array (String × String × String × String))
    (source target relation goalKey : String) : Array (String × String × String × String) :=
  if source = "" || target = "" || source = target then
    pairs
  else
    let pair := (source, target, relation, goalKey)
    if pairs.contains pair then pairs else pairs.push pair

private def addDepPair (pairs : Array (String × String × String × String))
    (source target kind label : String) : Array (String × String × String × String) :=
  let pair := (source, target, kind, label)
  if pairs.contains pair then pairs else pairs.push pair

private def planOrder (planNodes : Array PlanNode) (id : String) : Nat :=
  match planNodes.findIdx? (fun node => node.id = id) with
  | some idx => idx
  | none => 1000000000

private def depPairLt (planNodes : Array PlanNode)
    (left right : String × String × String × String) : Bool :=
  let lo1 := planOrder planNodes left.1
  let ro1 := planOrder planNodes right.1
  if lo1 != ro1 then
    lo1 < ro1
  else
    planOrder planNodes left.2.1 < planOrder planNodes right.2.1

private def buildPlanEdges (evidenceEdges : Array BlueprintEdge)
    (nodeOwner actionToBlock : Array (String × String)) (planNodes : Array PlanNode) :
    Array PlanEdge :=
  Id.run do
    let mut dependencyPairs : Array (String × String × String × String) := #[]
    for edge in evidenceEdges do
      if !ignoredPlanEdgeKinds.contains edge.kind then
        let sourceOwner? := assocGet? nodeOwner edge.fromId
        let targetOwner? :=
          match assocGet? nodeOwner edge.toId with
          | some owner => some owner
          | none => assocGet? actionToBlock edge.toId
        match sourceOwner?, targetOwner? with
        | some sourceOwner, some targetOwner =>
            if sourceOwner ≠ targetOwner &&
                planOrder planNodes sourceOwner < planOrder planNodes targetOwner then
              dependencyPairs := addDepPair dependencyPairs sourceOwner targetOwner edge.kind edge.label
        | _, _ => pure ()

    let mut flowPairs : Array (String × String × String × String) := #[]
    for h : idx in [:planNodes.size] do
      let node := planNodes[idx]
      let afterKeys := node.goalFlow.after
      if !afterKeys.isEmpty then
        if afterKeys.size > 1 || node.kind = "split_goal" || node.kind = "case_split" then
          for key in afterKeys do
            let target := firstFollowingWithGoal planNodes idx key
            flowPairs := addFlowPair flowPairs node.id target "branch" key
        else
          let key := afterKeys[0]!
          let target := firstFollowingWithGoal planNodes idx key
          flowPairs := addFlowPair flowPairs node.id target "next_goal" key

    let mut out : Array PlanEdge := #[]
    for h : idx in [:flowPairs.size] do
      let pair := flowPairs[idx]
      if (planNodeById? planNodes pair.1).isSome && (planNodeById? planNodes pair.2.1).isSome then
        out := out.push {
          id := s!"plan_flow_{idx + 1}"
          fromId := pair.1
          toId := pair.2.1
          kind := "flow"
          relation := pair.2.2.1
          goalKey := pair.2.2.2
          label := if pair.2.2.1 = "branch" then branchLabel pair.2.2.2 else ""
          visibleByDefault := true
          orderIndex := idx + 1
        }
    let sortedDeps := dependencyPairs.qsort (depPairLt planNodes)
    for h : idx in [:sortedDeps.size] do
      let pair := sortedDeps[idx]
      if (planNodeById? planNodes pair.1).isSome && (planNodeById? planNodes pair.2.1).isSome then
        out := out.push {
          id := s!"plan_dep_{idx + 1}"
          fromId := pair.1
          toId := pair.2.1
          kind := "dependency"
          relation := pair.2.2.1
          goalKey := ""
          label := pair.2.2.2
          visibleByDefault := false
          orderIndex := flowPairs.size + idx + 1
        }
    return out

def buildLayeredBlueprint (bp : Blueprint) : LayeredBlueprint :=
  let evidenceNodes0 := enrichEvidenceNodes bp.nodes
  let built := buildPlanNodes evidenceNodes0 bp.edges
  let planNodes0 := assignBranchMetadata built.fst
  let evidenceNodes := attachScopeMetadata evidenceNodes0 planNodes0
  let planNodes := refreshPlanDisplayRefs planNodes0 evidenceNodes
  let planEdges := buildPlanEdges bp.edges built.snd.fst built.snd.snd planNodes
  {
    theoremName := bp.theoremName
    theoremType := bp.theoremType
    sourceFile := bp.sourceFile
    planNodes := planNodes
    planEdges := planEdges
    evidenceNodes := evidenceNodes
    evidenceEdges := bp.edges
  }

private def evidenceNodeToJson (node : EvidenceNode) : String :=
  let baseFields := #[
    s!"\"id\": {jsonStr node.base.id}",
    s!"\"kind\": {jsonStr node.base.kind}",
    s!"\"class\": {jsonStr node.className}",
    s!"\"name\": {jsonStr node.base.nodeName}",
    s!"\"type\": {jsonStr node.base.typeText}",
    s!"\"label\": {jsonStr node.base.label}",
    s!"\"raw_text\": {jsonStr node.base.rawText}",
    s!"\"source_line\": {jsonNat node.base.sourceLine}",
    s!"\"uses_local\": {jsonStringArray node.base.usesLocal}",
    s!"\"uses_global\": {jsonStringArray node.base.usesGlobal}",
    s!"\"goals_before\": {jsonStringArray node.base.goalsBefore}",
    s!"\"goals_after\": {jsonStringArray node.base.goalsAfter}",
    s!"\"local_context\": {jsonStringArray node.base.localContext}",
    s!"\"expr_type\": {jsonStr node.base.exprType}",
    s!"\"expected_type\": {jsonStr node.base.expectedType}",
    s!"\"semantic_uses_local\": {jsonStringArray node.base.semanticUsesLocal}",
    s!"\"semantic_uses_global\": {jsonStringArray node.base.semanticUsesGlobal}",
    s!"\"display_name\": {jsonStr node.displayName}",
    s!"\"display_type\": {jsonStr node.displayType}",
    s!"\"display_label\": {jsonStr node.displayLabel}",
    s!"\"hidden_by_default\": {jsonBool node.hiddenByDefault}"
  ]
  let versionFields :=
    if node.versionCount > 1 then
      #[
        s!"\"version_index\": {jsonNat node.versionIndex}",
        s!"\"version_count\": {jsonNat node.versionCount}"
      ]
    else #[]
  let scopeFields :=
    if node.scopeId ≠ "" then #[s!"\"scope_id\": {jsonStr node.scopeId}"] else #[]
  "{\n" ++ indent 8 ++
    String.intercalate (",\n" ++ indent 8) (baseFields ++ versionFields ++ scopeFields).toList ++
    "\n" ++ indent 6 ++ "}"

private def stateDeltaToJson (delta : StateDelta) : String :=
  let fields := #[
    s!"\"added_locals\": {jsonStringArray delta.addedLocals}",
    s!"\"closed_goals\": {jsonStringArray delta.closedGoals}",
    s!"\"opened_goals\": {jsonStringArray delta.openedGoals}"
  ]
  "{\n" ++ indent 10 ++ String.intercalate (",\n" ++ indent 10) fields.toList ++ "\n" ++ indent 8 ++ "}"

private def goalFlowToJson (flow : GoalFlow) : String :=
  let fields := #[
    s!"\"primary\": {jsonStr flow.primary}",
    s!"\"before\": {jsonStringArray flow.before}",
    s!"\"after\": {jsonStringArray flow.after}"
  ]
  "{\n" ++ indent 10 ++ String.intercalate (",\n" ++ indent 10) fields.toList ++ "\n" ++ indent 8 ++ "}"

private def planNodeToJson (node : PlanNode) : String :=
  let fields := #[
    s!"\"id\": {jsonStr node.id}",
    s!"\"kind\": {jsonStr node.kind}",
    s!"\"label\": {jsonStr node.label}",
    s!"\"detail_label\": {jsonStr node.detailLabel}",
    s!"\"order_index\": {jsonNat node.orderIndex}",
    "\"source_range\": {\n" ++ indent 10 ++ s!"\"start_line\": {jsonNat node.startLine},\n" ++
      indent 10 ++ s!"\"end_line\": {jsonNat node.endLine}\n" ++ indent 8 ++ "}",
    s!"\"raw_text\": {jsonStr node.rawText}",
    s!"\"display_text\": {jsonStr node.displayText}",
    s!"\"main_tactic\": {jsonStr node.mainTactic}",
    s!"\"tactics\": {jsonStringArray node.tactics}",
    s!"\"inputs\": {jsonStringArray node.inputs}",
    s!"\"outputs\": {jsonStringArray node.outputs}",
    s!"\"solves\": {jsonStringArray node.solves}",
    s!"\"opens_subgoals\": {jsonStringArray node.opensSubgoals}",
    s!"\"display_inputs\": {jsonStringArray node.displayInputs}",
    s!"\"display_outputs\": {jsonStringArray node.displayOutputs}",
    s!"\"display_solves\": {jsonStringArray node.displaySolves}",
    s!"\"display_opens_subgoals\": {jsonStringArray node.displayOpensSubgoals}",
    s!"\"role_summary\": {jsonStr node.roleSummary}",
    s!"\"goals_before\": {jsonStringArray node.goalsBefore}",
    s!"\"goals_after\": {jsonStringArray node.goalsAfter}",
    s!"\"local_context_before\": {jsonStringArray node.localContextBefore}",
    s!"\"local_context_after\": {jsonStringArray node.localContextAfter}",
    s!"\"state_delta\": {stateDeltaToJson node.stateDelta}",
    s!"\"used_globals\": {jsonStringArray node.usedGlobals}",
    s!"\"display_used_globals\": {jsonStringArray node.displayUsedGlobals}",
    s!"\"branch_id\": {jsonStr node.branchId}",
    s!"\"branch_label\": {jsonStr node.branchLabel}",
    s!"\"parent_split\": {jsonStr node.parentSplit}",
    s!"\"branch_index\": {jsonNat node.branchIndex}",
    s!"\"goal_flow\": {goalFlowToJson node.goalFlow}",
    s!"\"evidence_node_ids\": {jsonStringArray node.evidenceNodeIds}",
    s!"\"internal_evidence_node_ids\": {jsonStringArray node.internalEvidenceNodeIds}",
    s!"\"boundary_node_ids\": {jsonStringArray node.boundaryNodeIds}",
    s!"\"evidence_edge_ids\": {jsonStringArray node.evidenceEdgeIds}"
  ]
  "{\n" ++ indent 8 ++ String.intercalate (",\n" ++ indent 8) fields.toList ++ "\n" ++ indent 6 ++ "}"

private def planEdgeToJson (edge : PlanEdge) : String :=
  let baseFields := #[
    s!"\"id\": {jsonStr edge.id}",
    s!"\"from\": {jsonStr edge.fromId}",
    s!"\"to\": {jsonStr edge.toId}",
    s!"\"kind\": {jsonStr edge.kind}",
    s!"\"relation\": {jsonStr edge.relation}"
  ]
  let goalFields :=
    if edge.goalKey ≠ "" then #[s!"\"goal_key\": {jsonStr edge.goalKey}"] else #[]
  let tailFields := #[
    s!"\"label\": {jsonStr edge.label}",
    s!"\"visible_by_default\": {jsonBool edge.visibleByDefault}",
    s!"\"order_index\": {jsonNat edge.orderIndex}"
  ]
  "{\n" ++ indent 8 ++
    String.intercalate (",\n" ++ indent 8) (baseFields ++ goalFields ++ tailFields).toList ++
    "\n" ++ indent 6 ++ "}"

private def mappingEntryToJson (node : PlanNode) : String :=
  let fields := #[
    s!"\"evidence_nodes\": {jsonStringArray node.evidenceNodeIds}",
    s!"\"internal_evidence_nodes\": {jsonStringArray node.internalEvidenceNodeIds}",
    s!"\"boundary_nodes\": {jsonStringArray node.boundaryNodeIds}",
    s!"\"evidence_edges\": {jsonStringArray node.evidenceEdgeIds}"
  ]
  "{\n" ++ indent 8 ++ String.intercalate (",\n" ++ indent 8) fields.toList ++ "\n" ++ indent 6 ++ "}"

def layeredBlueprintToJson (lb : LayeredBlueprint) : String :=
  let theoremFields := #[
    s!"\"name\": {jsonStr lb.theoremName}",
    s!"\"type\": {jsonStr lb.theoremType}",
    s!"\"source_file\": {jsonStr lb.sourceFile}"
  ]
  let theoremJson :=
    "{\n" ++ indent 4 ++ String.intercalate (",\n" ++ indent 4) theoremFields.toList ++ "\n" ++ indent 2 ++ "}"
  let planNodesJson :=
    "[\n" ++ indent 6 ++ String.intercalate (",\n" ++ indent 6) (lb.planNodes.map planNodeToJson).toList ++ "\n" ++ indent 4 ++ "]"
  let planEdgesJson :=
    "[\n" ++ indent 6 ++ String.intercalate (",\n" ++ indent 6) (lb.planEdges.map planEdgeToJson).toList ++ "\n" ++ indent 4 ++ "]"
  let evidenceNodesJson :=
    "[\n" ++ indent 6 ++ String.intercalate (",\n" ++ indent 6) (lb.evidenceNodes.map evidenceNodeToJson).toList ++ "\n" ++ indent 4 ++ "]"
  let evidenceEdgesJson :=
    "[\n" ++ indent 6 ++ String.intercalate (",\n" ++ indent 6) (lb.evidenceEdges.map edgeToJson).toList ++ "\n" ++ indent 4 ++ "]"
  let mappingFields :=
    lb.planNodes.map (fun node => s!"\"{node.id}\": {mappingEntryToJson node}")
  let mappingJson :=
    "{\n" ++ indent 4 ++ String.intercalate (",\n" ++ indent 4) mappingFields.toList ++ "\n" ++ indent 2 ++ "}"
  let fields := #[
    "\"schema_version\": \"layered-1\"",
    s!"\"theorem\": {theoremJson}",
    s!"\"extraction_mode\": {jsonStr lb.extractionMode}",
    "\"plan_graph\": {\n" ++ indent 4 ++ s!"\"nodes\": {planNodesJson},\n" ++
      indent 4 ++ s!"\"edges\": {planEdgesJson}\n" ++ indent 2 ++ "}",
    "\"evidence_graph\": {\n" ++ indent 4 ++ s!"\"nodes\": {evidenceNodesJson},\n" ++
      indent 4 ++ s!"\"edges\": {evidenceEdgesJson}\n" ++ indent 2 ++ "}",
    s!"\"mapping\": {mappingJson}"
  ]
  "{\n" ++ indent 2 ++ String.intercalate (",\n" ++ indent 2) fields.toList ++ "\n}\n"

def blueprintToLayeredJson (bp : Blueprint) : String :=
  layeredBlueprintToJson (buildLayeredBlueprint bp)

end ProofStruct
