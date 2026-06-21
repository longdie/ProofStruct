import Lean
import Lean.Elab.Frontend
import Lean.Server.InfoUtils
import ProofStruct.Extract.DepPass
import ProofStruct.Extract.Graph
import ProofStruct.Extract.SyntaxPass

namespace ProofStruct

open Lean Lean.Elab

structure InfoStep where
  syntaxId : String
  goalsBefore : Array String := #[]
  goalsAfter : Array String := #[]
deriving Repr, Inhabited

structure SemanticTacticInfo where
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  syntaxText : String := ""
  sourceLineText : String := ""
  syntaxKind : String := ""
  goalsBefore : Array String := #[]
  goalsAfter : Array String := #[]
  localContext : Array String := #[]
  localContextAfter : Array String := #[]
deriving Repr, Inhabited

structure SemanticTermInfo where
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  syntaxText : String := ""
  syntaxKind : String := ""
  exprType : String := ""
  expectedType : String := ""
  localDeps : Array String := #[]
  globalDeps : Array String := #[]
deriving Repr, Inhabited

structure SemanticCommandInfo where
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  syntaxText : String := ""
  syntaxKind : String := ""
deriving Repr, Inhabited

structure SemanticSnapshot where
  tactics : Array SemanticTacticInfo := #[]
  terms : Array SemanticTermInfo := #[]
  commands : Array SemanticCommandInfo := #[]
deriving Repr, Inhabited

private def rangeOfSyntax? (ctx : ContextInfo) (stx : Syntax) :
    Option (Nat × Nat × Nat × Nat) := do
  let range ← stx.getRange? (canonicalOnly := true)
  let startPos := ctx.fileMap.toPosition range.start
  let endPos := ctx.fileMap.toPosition range.stop
  pure (startPos.line, startPos.column, endPos.line, endPos.column)

private def textOfSyntax (ctx : ContextInfo) (stx : Syntax) : String :=
  match stx.getRange? (canonicalOnly := true) with
  | some range => String.Pos.Raw.extract ctx.fileMap.source range.start range.stop
  | none => stx.reprint.getD ""

private def sourceLineTextOf (source : String) (line : Nat) : String :=
  match (source.splitOn "\n").toArray[line - 1]? with
  | some text => text.trimAscii.toString
  | none => ""

private def containsSubstr (s needle : String) : Bool :=
  match s.splitOn needle with
  | [] => false
  | [_] => false
  | _ => true

private def theoremCommandMatches (theoremName : String) (cmd : SemanticCommandInfo) : Bool :=
  let text := cmd.syntaxText.trimAscii.toString
  containsSubstr text s!"theorem {theoremName}" ||
  containsSubstr text s!"lemma {theoremName}" ||
  containsSubstr text s!"example {theoremName}"

private def infoInsideTarget? (target? : Option (Nat × Nat))
    (infoStartLine infoEndLine : Nat) : Bool :=
  match target? with
  | none => true
  | some (startLine, endLine) => startLine <= infoStartLine && infoEndLine <= endLine

private def commandToSemantic? (inputCtx : Parser.InputContext) (stx : Syntax) :
    Option SemanticCommandInfo := do
  let range ← stx.getRange? (canonicalOnly := true)
  let startPos := inputCtx.fileMap.toPosition range.start
  let endPos := inputCtx.fileMap.toPosition range.stop
  let syntaxText := String.Pos.Raw.extract inputCtx.fileMap.source range.start range.stop
  pure {
    startLine := startPos.line
    startCol := startPos.column
    endLine := endPos.line
    endCol := endPos.column
    syntaxText := syntaxText
    syntaxKind := toString stx.getKind
  }

private def ppGoalsWith (ctx : ContextInfo) (mctx : MetavarContext)
    (goals : List MVarId) : IO (Array String) := do
  ctx.runCoreM do
    let mut out : Array String := #[]
    for goal in goals do
      let fmt ← (Meta.ppGoal goal).run' {} { mctx := mctx }
      out := out.push fmt.pretty
    pure out

private def ppLocalContextWith (ctx : ContextInfo) (mctx : MetavarContext)
    (goals : List MVarId) : IO (Array String) := do
  ctx.runCoreM do
    (do
      match goals with
      | [] => pure #[]
      | goal :: _ =>
          let goalDecl ← goal.getDecl
          let mut out : Array String := #[]
          for localDecl in goalDecl.lctx do
            unless localDecl.isImplementationDetail || localDecl.isAuxDecl do
              let type ← instantiateMVars localDecl.type
              let fmt ← Meta.ppExpr type
              out := out.push s!"{localDecl.userName.eraseMacroScopes} : {fmt.pretty}"
          pure out).run' {} { mctx := mctx }

private def tacticInfoToSemantic (target? : Option (Nat × Nat))
    (ctx : ContextInfo) (info : TacticInfo) :
    IO (Option SemanticTacticInfo) := do
  match rangeOfSyntax? ctx info.stx with
  | none => pure none
  | some (startLine, startCol, endLine, endCol) =>
      if !infoInsideTarget? target? startLine endLine then
        pure none
      else
      let goalsBefore ← ppGoalsWith ctx info.mctxBefore info.goalsBefore
      let goalsAfter ← ppGoalsWith ctx info.mctxAfter info.goalsAfter
      let localContext ← ppLocalContextWith ctx info.mctxBefore info.goalsBefore
      let localContextAfter ← ppLocalContextWith ctx info.mctxAfter info.goalsAfter
      let syntaxText := textOfSyntax ctx info.stx
      let sourceLineText := sourceLineTextOf ctx.fileMap.source startLine
      let syntaxKind := toString info.stx.getKind
      pure <| some {
        startLine, startCol, endLine, endCol,
        syntaxText, sourceLineText, syntaxKind,
        goalsBefore, goalsAfter, localContext, localContextAfter
      }

private def ppExprString (expr : Expr) : MetaM String := do
  let fmt ← Meta.ppExpr expr
  pure fmt.pretty

private def termInfoToSemantic (target? : Option (Nat × Nat))
    (ctx : ContextInfo) (info : TermInfo) :
    IO (Option SemanticTermInfo) := do
  match rangeOfSyntax? ctx info.stx with
  | none => pure none
  | some (startLine, startCol, endLine, endCol) => do
      if !infoInsideTarget? target? startLine endLine then
        pure none
      else
      let payload ← info.runMetaM ctx do
        let expr ← instantiateMVars info.expr
        let exprType ←
          try
            let ty ← instantiateMVars (← Meta.inferType expr)
            ppExprString ty
          catch _ =>
            pure ""
        let expectedType ←
          match info.expectedType? with
          | none => pure ""
          | some expected => ppExprString (← instantiateMVars expected)
        let deps := collectExprDeps info.lctx expr
        let deps :=
          match info.expectedType? with
          | none => deps
          | some expected => deps.merge (collectExprDeps info.lctx expected)
        pure (exprType, expectedType, deps.localDeps, deps.globalDeps)
      let (exprType, expectedType, localDeps, globalDeps) := payload
      let syntaxText := textOfSyntax ctx info.stx
      let syntaxKind := toString info.stx.getKind
      pure <| some {
        startLine, startCol, endLine, endCol,
        syntaxText, syntaxKind,
        exprType, expectedType, localDeps, globalDeps
      }

private def collectSemanticFromTree (tree : InfoTree) (target? : Option (Nat × Nat) := none) :
    IO SemanticSnapshot := do
  tree.foldInfoM (init := {}) fun ctx info acc => do
    match info with
    | .ofTacticInfo tacticInfo =>
        match ← tacticInfoToSemantic target? ctx tacticInfo with
        | some semantic => pure { acc with tactics := acc.tactics.push semantic }
        | none => pure acc
    | .ofTermInfo termInfo =>
        match ← termInfoToSemantic target? ctx termInfo with
        | some semantic => pure { acc with terms := acc.terms.push semantic }
        | none => pure acc
    | _ => pure acc

private def mergeSnapshots (left right : SemanticSnapshot) : SemanticSnapshot :=
  { tactics := left.tactics ++ right.tactics
    terms := left.terms ++ right.terms
    commands := left.commands ++ right.commands }

private def sanitizeBlueprintDisplayCommands (source : String) : String :=
  let sanitizeLine (line : String) : String :=
    let trimmed := line.trimAsciiStart.copy
    if trimmed.startsWith "#proof_blueprint" then
      "-- " ++ line
    else
      line
  String.intercalate "\n" ((source.splitOn "\n").map sanitizeLine)

private def elaborateSemanticSnapshot (sourceFile source : String)
    (targetTheorem? : Option String := none) :
    IO (Except String SemanticSnapshot) := do
  try
    let summarizeMessages (messages : MessageLog) : IO String := do
      let mut rendered : Array String := #[]
      for msg in messages.toArray do
        rendered := rendered.push (← msg.toString)
      pure (String.intercalate "\n" rendered.toList)
    let source := sanitizeBlueprintDisplayCommands source
    initSearchPath (← findSysroot)
    unsafe enableInitializersExecution
    let inputCtx := Parser.mkInputContext source sourceFile
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    if messages.hasErrors then
      return .error s!"failed to parse Lean header\n{← summarizeMessages messages}"
    let opts : Options := {}
    let (env, messages) ← Elab.processHeader header opts messages inputCtx
      (leakEnv := true) (mainModule := `ProofStruct.SemanticInput)
    if messages.hasErrors then
      return .error s!"failed to process Lean imports\n{← summarizeMessages messages}"
    let commandState := Command.mkState env messages opts
    let commandState := { commandState with
      infoState := { commandState.infoState with enabled := true }
    }
    let frontendState ← Elab.IO.processCommands inputCtx parserState commandState
    if frontendState.commandState.messages.hasErrors then
      return .error s!"Lean elaboration produced errors\n{← summarizeMessages frontendState.commandState.messages}"
    let commands := frontendState.commands.filterMap (commandToSemantic? inputCtx)
    let targetRange? : Option (Nat × Nat) :=
      match targetTheorem? with
      | none => none
      | some theoremName =>
          (commands.find? (theoremCommandMatches theoremName)).map
            (fun cmd => (cmd.startLine, cmd.endLine))
    if targetTheorem?.isSome && targetRange?.isNone then
      return .error s!"theorem not found in semantic snapshot: {targetTheorem?.getD ""}"
    let infoState := (frontendState.commandState.infoState.substituteLazy).get
    let mut snapshot : SemanticSnapshot := {}
    for tree in infoState.trees do
      snapshot := mergeSnapshots snapshot (← collectSemanticFromTree tree targetRange?)
    snapshot := { snapshot with commands := commands }
    return .ok snapshot
  catch err =>
    return .error s!"semantic elaboration failed: {err}"

private def coversLine (line : Nat) (startLine endLine : Nat) : Bool :=
  startLine <= line && line <= endLine

private def tacticMatchesLine (line : Nat) (info : SemanticTacticInfo) : Bool :=
  coversLine line info.startLine info.endLine

private def splitFirst (s sep : String) : String × String :=
  match s.splitOn sep with
  | [] => ("", "")
  | h :: t => (h, String.intercalate sep t)

private def dropPrefix? (s pref : String) : Option String :=
  if s.startsWith pref then
    some (String.ofList (s.toList.drop pref.length))
  else
    none

private def actionPayloadText (node : BlueprintNode) : String :=
  let raw := node.rawText.trimAscii.toString
  if containsSubstr raw ":=" then
    let (_, rhs) := splitFirst raw ":="
    rhs.trimAscii.toString
  else
    let pref := node.nodeName ++ " "
    match dropPrefix? raw pref with
    | some payload => payload.trimAscii.toString
    | none => raw

private def textMatchesPayload (payload syntaxText : String) : Bool :=
  let payload := payload.trimAscii.toString
  let syntaxText := syntaxText.trimAscii.toString
  syntaxText ≠ "" && payload ≠ "" && payload ≠ "by" &&
    (payload == syntaxText || containsSubstr payload syntaxText || containsSubstr syntaxText payload)

private def termMatchesNode (node : BlueprintNode) (info : SemanticTermInfo) : Bool :=
  coversLine node.sourceLine info.startLine info.endLine &&
    textMatchesPayload (actionPayloadText node) info.syntaxText

private def termSpan (info : SemanticTermInfo) : Nat :=
  (info.endLine - info.startLine) * 10000 + (info.endCol - info.startCol)

private def firstTacticForNode (node : BlueprintNode) (snapshot : SemanticSnapshot) :
    Option SemanticTacticInfo :=
  let raw := node.rawText.trimAscii.toString
  let candidates := snapshot.tactics.filter (tacticMatchesLine node.sourceLine)
  match candidates.find? (fun info => info.syntaxText.trimAscii.toString == raw) with
  | some info => some info
  | none =>
      match candidates.find? (fun info => (info.syntaxText.trimAscii.toString).startsWith node.nodeName) with
      | some info => some info
      | none =>
          match candidates.find? (fun info => info.startLine == node.sourceLine) with
          | some info => some info
          | none => candidates[0]?

private def termsForNode (node : BlueprintNode) (snapshot : SemanticSnapshot) :
    Array SemanticTermInfo :=
  let matched := snapshot.terms.filter (termMatchesNode node)
  if matched.isEmpty then
    #[]
  else
    let maxSpan := matched.foldl (fun acc term => Nat.max acc (termSpan term)) 0
    matched.filter (fun term => termSpan term == maxSpan)

private def mergedTermDeps (terms : Array SemanticTermInfo) :
    Array String × Array String :=
  terms.foldl
    (fun (locals, globals) term =>
      (mergeStringArrays locals term.localDeps, mergeStringArrays globals term.globalDeps))
    (#[], #[])

private def firstNonempty (items : Array String) : String :=
  items.foldl (fun found item => if found = "" && item ≠ "" then item else found) ""

private def largestSpanTerms (terms : Array SemanticTermInfo) :
    Array SemanticTermInfo :=
  if terms.isEmpty then
    #[]
  else
    let maxSpan := terms.foldl (fun acc term => Nat.max acc (termSpan term)) 0
    terms.filter (fun term => termSpan term == maxSpan)

private def lineFallbackTermsForTactic (tactic : SemanticTacticInfo)
    (terms : Array SemanticTermInfo) : Array SemanticTermInfo :=
  let sameLine := terms.filter (fun term =>
    term.startLine == tactic.startLine &&
      tactic.startCol <= term.startCol &&
      term.syntaxText.trimAscii.toString ≠ "")
  let withDeps := sameLine.filter (fun term =>
    !term.localDeps.isEmpty || !term.globalDeps.isEmpty)
  largestSpanTerms (if withDeps.isEmpty then sameLine else withDeps)

private def tacticPayloadText (kind : String) (tactic : SemanticTacticInfo) : String :=
  let tempNode : BlueprintNode :=
    { id := "tmp"
      kind := "action"
      nodeName := kind
      rawText := tactic.syntaxText
      sourceLine := tactic.startLine }
  actionPayloadText tempNode

private def isHaveLetByProof (kind : String) (tactic : SemanticTacticInfo) : Bool :=
  (kind = "have" || kind = "let") && (tacticPayloadText kind tactic).startsWith "by"

private def termsForTactic (kind : String) (tactic : SemanticTacticInfo)
    (terms : Array SemanticTermInfo) : Array SemanticTermInfo :=
  let payload := tacticPayloadText kind tactic
  if isHaveLetByProof kind tactic then
    #[]
  else
    let matched := terms.filter (fun term =>
      tactic.startLine <= term.startLine &&
        term.endLine <= tactic.endLine &&
        textMatchesPayload payload term.syntaxText)
    let selected := largestSpanTerms matched
    let (selectedLocals, _) := mergedTermDeps selected
    if !selected.isEmpty && !selectedLocals.isEmpty then
      selected
    else
      let fallback := lineFallbackTermsForTactic tactic terms
      if fallback.isEmpty then selected else fallback

private def enrichNodeWithSemantic (snapshot : SemanticSnapshot) (node : BlueprintNode) :
    BlueprintNode :=
  if node.kind != "action" || node.sourceLine == 0 then
    node
  else
    let tactic? := firstTacticForNode node snapshot
    let terms := termsForNode node snapshot
    let (semanticLocals, semanticGlobals) := mergedTermDeps terms
    let exprType := firstNonempty (terms.map (·.exprType))
    let expectedType := firstNonempty (terms.map (·.expectedType))
    { node with
      goalsBefore := tactic?.map (·.goalsBefore) |>.getD #[]
      goalsAfter := tactic?.map (·.goalsAfter) |>.getD #[]
      localContext := tactic?.map (·.localContext) |>.getD #[]
      exprType := exprType
      expectedType := expectedType
      usesLocal := mergeStringArrays node.usesLocal semanticLocals
      usesGlobal := mergeStringArrays node.usesGlobal semanticGlobals
      semanticUsesLocal := semanticLocals
      semanticUsesGlobal := semanticGlobals
    }

private def localNodeId? (nodes : Array BlueprintNode) (localName : String) : Option String :=
  match nodes.find? (fun node => node.kind != "action" && node.nodeName == localName) with
  | some node => some node.id
  | none => none

private def hasEdge (edges : Array BlueprintEdge) (edge : BlueprintEdge) : Bool :=
  edges.any (fun existing =>
    existing.fromId == edge.fromId &&
    existing.toId == edge.toId &&
    existing.kind == edge.kind &&
    existing.label == edge.label)

private def addSemanticInputEdges (nodes : Array BlueprintNode) (edges : Array BlueprintEdge) :
    Array BlueprintEdge := Id.run do
  let mut out := edges
  for node in nodes do
    if node.kind == "action" then
      for localName in node.semanticUsesLocal do
        match localNodeId? nodes localName with
        | none => pure ()
        | some localId =>
            let edge : BlueprintEdge :=
              { fromId := localId, toId := node.id, kind := "input_to_action", label := localName }
            unless hasEdge out edge do
              out := out.push edge
  return out

private def pushEdgeUnique (edges : Array BlueprintEdge) (edge : BlueprintEdge) :
    Array BlueprintEdge :=
  if hasEdge edges edge then edges else edges.push edge

private def infoInsideCommand
    (startLine endLine : Nat) (infoStartLine infoEndLine : Nat) : Bool :=
  startLine <= infoStartLine && infoEndLine <= endLine

private def findTheoremCommand? (theoremName : String) (snapshot : SemanticSnapshot) :
    Option SemanticCommandInfo :=
  snapshot.commands.find? (theoremCommandMatches theoremName)

private def stripBranchBullet (s : String) : String :=
  let t := s.trimAscii.toString
  if t.startsWith "· " then
    (String.ofList (t.toList.drop 2)).trimAscii.toString
  else if t.startsWith "·" then
    (String.ofList (t.toList.drop 1)).trimAscii.toString
  else
    t

private def firstWord (s : String) : String :=
  let normalized := String.ofList <| (s.trimAscii.toString).toList.map (fun c =>
    if c = '\n' || c = '\t' then ' ' else c)
  match normalized.splitOn " " with
  | [] => ""
  | h :: _ => h

private def hasNewline (s : String) : Bool :=
  containsSubstr s "\n"

private def stripTrailingWrapperDelims (s : String) : String :=
  let rec trimRev : List Char → List Char
    | [] => []
    | c :: rest =>
        if c = '⟩' || c = ')' || c = '}' then
          trimRev rest
        else
          c :: rest
  String.ofList ((trimRev (s.trimAscii.toString.toList.reverse)).reverse)

private def sourceLineCompletion? (syntaxText source : String) : Option String :=
  let syntaxText := syntaxText.trimAscii.toString
  let source := source.trimAscii.toString
  if syntaxText = "" || source = "" || hasNewline syntaxText then
    none
  else if source.startsWith syntaxText && source.length > syntaxText.length then
    some source
  else
    match source.splitOn syntaxText with
    | before :: after :: _ =>
        if before.trimAscii.toString = "" then
          none
        else
          some (stripTrailingWrapperDelims (syntaxText ++ after))
    | _ => none

private def tacticActionText (info : SemanticTacticInfo) : String :=
  stripBranchBullet ((sourceLineCompletion? info.syntaxText info.sourceLineText).getD info.syntaxText)

private def actionKindFromSyntaxText (raw : String) : String :=
  let t := stripBranchBullet raw
  if t.startsWith "by_cases " then "by_cases"
  else if t.startsWith "norm_num" then "norm_num"
  else if t.startsWith "exact_mod_cast" then "exact_mod_cast"
  else if t.startsWith "ring_nf" then "ring_nf"
  else firstWord t

private def tacticSpan (info : SemanticTacticInfo) : Nat :=
  (info.endLine - info.startLine) * 10000 + (info.endCol - info.startCol)

private def recognizedTacticKind (kind : String) : Bool :=
  kind = "have" ||
  kind = "let" ||
  kind = "exact" ||
  kind = "exact_mod_cast" ||
  kind = "simp" ||
  kind = "simpa" ||
  kind = "rw" ||
  kind = "ext" ||
  kind = "subst" ||
  kind = "abel" ||
  kind = "infer_instance" ||
  kind = "norm_num" ||
  kind = "refine" ||
  kind = "calc" ||
  kind = "omega" ||
  kind = "ring" ||
  kind = "right" ||
  kind = "left" ||
  kind = "constructor" ||
  kind = "by_cases" ||
  kind = "cases" ||
  kind = "rcases" ||
  kind = "apply" ||
  kind = "intro" ||
  kind = "intros" ||
  kind = "rintro" ||
  kind = "rfl" ||
  kind = "ring_nf" ||
  kind = "linarith" ||
  kind = "nlinarith" ||
  kind = "change"

private def isSourceLevelTactic (info : SemanticTacticInfo) : Bool :=
  let kind := actionKindFromSyntaxText (tacticActionText info)
  recognizedTacticKind kind

private def sameTacticStartAndKind (left right : SemanticTacticInfo) : Bool :=
  left.startLine == right.startLine &&
  actionKindFromSyntaxText (tacticActionText left) == actionKindFromSyntaxText (tacticActionText right) &&
  (left.startCol == right.startCol ||
    containsSubstr (tacticActionText left) (tacticActionText right) ||
    containsSubstr (tacticActionText right) (tacticActionText left))

private def addMinimalTactic
    (items : Array SemanticTacticInfo) (candidate : SemanticTacticInfo) :
    Array SemanticTacticInfo := Id.run do
  let mut out : Array SemanticTacticInfo := #[]
  let mut inserted := false
  for item in items do
    if sameTacticStartAndKind item candidate then
      inserted := true
      if tacticSpan candidate < tacticSpan item ||
          (tacticSpan candidate == tacticSpan item &&
            (tacticActionText candidate).length < (tacticActionText item).length) then
        out := out.push candidate
      else
        out := out.push item
    else
      out := out.push item
  if inserted then out else out.push candidate

private def minimizeSourceTactics (items : Array SemanticTacticInfo) :
    Array SemanticTacticInfo :=
  items.foldl
    (fun acc item => if isSourceLevelTactic item then addMinimalTactic acc item else acc)
    #[]

private def isTokenChar (c : Char) : Bool :=
  c.isAlphanum || c = '_' || c = '.' || c = '\''

private def cleanToken (token : String) : String :=
  String.ofList (token.toList.filter isTokenChar)

private def splitTokenSeparators (s : String) : String :=
  String.ofList <| s.toList.map (fun c =>
    if isTokenChar c then c else ' ')

private def extractTokens (raw : String) : Array String :=
  ((splitTokenSeparators raw).splitOn " ").foldl
    (fun acc p =>
      let t := cleanToken p
      if t = "" then acc else acc.push t)
    #[]

private def tokenUsesLocal (tokens : Array String) (name : String) : Bool :=
  tokens.any (fun token => token = name || token.startsWith (name ++ "."))

private def uniqueStrings (items : Array String) : Array String :=
  items.foldl
    (fun acc item =>
      let item := item.trimAscii.toString
      if item = "" || acc.contains item then acc else acc.push item)
    #[]

private def sourceGlobalTokens (raw : String) : Array String :=
  uniqueStrings <| (extractTokens raw).filter (fun token => containsSubstr token ".")

private def semanticActionLabel (kind raw : String) (globals : Array String) : String :=
  let sourceGlobals := sourceGlobalTokens raw
  let labelItems := if sourceGlobals.isEmpty then globals else sourceGlobals
  if labelItems.isEmpty then kind else String.intercalate "; " labelItems.toList

private def goalTarget (goal : String) : String :=
  let lines := goal.splitOn "\n"
  let rec findTarget : List String → String
    | [] => goal.trimAscii.toString
    | line :: rest =>
        let line := line.trimAscii.toString
        if line.startsWith "⊢" then
          (String.ofList (line.toList.drop 1)).trimAscii.toString
        else
          findTarget rest
  findTarget lines

private def firstGoalTarget (goals : Array String) : String :=
  match goals[0]? with
  | some goal => goalTarget goal
  | none => ""

private def parseLocalNames (raw : String) : Array String :=
  raw.splitOn " " |>.foldl
    (fun acc name =>
      let name := name.trimAscii.toString
      if name = "" || acc.contains name then acc else acc.push name)
    #[]

private def parseLocalDecl (decl : String) : Array (String × String) :=
  if containsSubstr decl " : " then
    let (name, typeText) := splitFirst decl " : "
    let typeText := typeText.trimAscii.toString
    if typeText = "" then
      #[]
    else
      (parseLocalNames name).map (fun name => (name, typeText))
  else
    #[]

private def parseLocalContext (locals : Array String) : Array (String × String) :=
  locals.foldl (fun acc decl => acc ++ parseLocalDecl decl) #[]

private def localContextFromGoal (goal : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for line in goal.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.startsWith "⊢" then
      return out
    else
      out := out ++ parseLocalDecl line
  return out

private def localContextFromGoals (goals : Array String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for goal in goals do
    out := out ++ localContextFromGoal goal
  return out

private def tacticLocalContextBeforeForNodes (tactic : SemanticTacticInfo) :
    Array (String × String) :=
  localContextFromGoals tactic.goalsBefore ++ parseLocalContext tactic.localContext

private def tacticLocalContextAfterForNodes (tactic : SemanticTacticInfo) :
    Array (String × String) :=
  localContextFromGoals tactic.goalsAfter ++ parseLocalContext tactic.localContextAfter

structure LocalNodeInfo where
  name : String
  typeText : String
  nodeId : String
  initial : Bool
deriving Repr, Inhabited

private def isTypeWhitespace (c : Char) : Bool :=
  c = ' ' || c = '\n' || c = '\t' || c = '\r'

private def normalizeTypeText (typeText : String) : String :=
  String.ofList <| typeText.toList.filter (fun c => !isTypeWhitespace c)

private def sameLocalInfo (info : LocalNodeInfo) (name typeText : String) : Bool :=
  info.name == name && info.typeText == typeText

private def localNameCount (infos : Array LocalNodeInfo) (name : String) : Nat :=
  (infos.filter (fun info => info.name == name)).size

private def typeHead (typeText : String) : String :=
  firstWord typeText

private def hasConcreteTypeHead (infos : Array LocalNodeInfo) (typeText : String) : Bool :=
  let head := typeHead typeText
  head ≠ "" && infos.any (fun info =>
    typeHead info.typeText == head && !containsSubstr info.typeText "_fvar")

private def nodeIdExists (infos : Array LocalNodeInfo) (nodeId : String) : Bool :=
  infos.any (fun info => info.nodeId == nodeId)

private partial def uniqueLocalNodeId (infos : Array LocalNodeInfo) (baseId : String)
    (idx : Nat) : String :=
  let candidate := if idx == 0 then baseId else s!"{baseId}_{idx + 1}"
  if nodeIdExists infos candidate then
    uniqueLocalNodeId infos baseId (idx + 1)
  else
    candidate

private def addLocalInfo
    (infos : Array LocalNodeInfo) (name typeText : String) (initial : Bool) :
    Array LocalNodeInfo :=
  let name := name.trimAscii.toString
  let typeText := typeText.trimAscii.toString
  if name = "" || typeText = "" ||
      typeText.startsWith "failed to pretty print expression" ||
      (containsSubstr typeText "_fvar" && infos.any (fun info => info.name == name)) ||
      (name == "inst" && containsSubstr typeText "_fvar" && hasConcreteTypeHead infos typeText) ||
      infos.any (fun info => sameLocalInfo info name typeText ||
        (info.name == name && normalizeTypeText info.typeText == normalizeTypeText typeText)) then
    infos
  else
    let baseId := "n_" ++ sanitizeId name
    let nodeId := uniqueLocalNodeId infos baseId 0
    infos.push { name := name, typeText := typeText, nodeId := nodeId, initial := initial }

private def collectLocalInfos (tactics : Array SemanticTacticInfo) : Array LocalNodeInfo := Id.run do
  let mut infos : Array LocalNodeInfo := #[]
  match tactics[0]? with
  | some first =>
      for (name, typeText) in tacticLocalContextBeforeForNodes first do
        infos := addLocalInfo infos name typeText true
  | none => pure ()
  for tactic in tactics do
    for (name, typeText) in tacticLocalContextBeforeForNodes tactic do
      infos := addLocalInfo infos name typeText false
    for (name, typeText) in tacticLocalContextAfterForNodes tactic do
      infos := addLocalInfo infos name typeText false
  return infos

private def findLocalByNameType?
    (infos : Array LocalNodeInfo) (name typeText : String) : Option LocalNodeInfo :=
  infos.find? (fun info => info.name == name && info.typeText == typeText)

private def findLocalByNameTypeNormalized?
    (infos : Array LocalNodeInfo) (name typeText : String) : Option LocalNodeInfo :=
  let target := normalizeTypeText typeText
  infos.find? (fun info =>
    info.name == name && normalizeTypeText info.typeText == target)

private def findLocalByCompatibleInstanceType?
    (infos : Array LocalNodeInfo) (name typeText : String) : Option LocalNodeInfo :=
  if name != "inst" || !containsSubstr typeText "_fvar" then
    none
  else
    let head := typeHead typeText
    let candidates := infos.filter (fun info =>
      typeHead info.typeText == head && !containsSubstr info.typeText "_fvar")
    match candidates with
    | #[info] => some info
    | _ => none

private def findLocalByName? (infos : Array LocalNodeInfo) (name : String) :
    Option LocalNodeInfo :=
  match infos.filter (fun info => info.name == name) with
  | #[info] => some info
  | many =>
      many.find? (fun info => info.initial) <|> many[0]?

private def localInfoForAction?
    (infos : Array LocalNodeInfo) (tactic : SemanticTacticInfo) (name : String) :
    Option LocalNodeInfo :=
  match (tacticLocalContextBeforeForNodes tactic).find? (fun decl => decl.fst == name) with
  | some (_, typeText) =>
      findLocalByNameType? infos name typeText <|>
        findLocalByNameTypeNormalized? infos name typeText <|>
        findLocalByCompatibleInstanceType? infos name typeText <|>
        findLocalByName? infos name
  | none => findLocalByName? infos name

private def localDepsFromText
    (infos : Array LocalNodeInfo) (tactic : SemanticTacticInfo) (text : String) :
    Array String := Id.run do
  let tokens := extractTokens text
  let mut out : Array String := #[]
  for (name, _) in tacticLocalContextBeforeForNodes tactic do
    if tokenUsesLocal tokens name then
      match localInfoForAction? infos tactic name with
      | some _ => out := pushUnique out name
      | none => pure ()
  return out

private def firstGoalText (goals : Array String) : String :=
  match goals[0]? with
  | some goal => goal
  | none => ""

private def contextSolverKind (kind : String) : Bool :=
  kind = "omega" || kind = "linarith" || kind = "nlinarith"

private def sourceDepsShouldSupplement (kind : String) : Bool :=
  kind = "simp" || kind = "simpa" || kind = "rw" ||
    kind = "exact" || kind = "exact_mod_cast"

private def fallbackLocalDepsForTactic
    (infos : Array LocalNodeInfo) (tactic : SemanticTacticInfo) : Array String :=
  let kind := actionKindFromSyntaxText tactic.syntaxText
  let sourceDeps :=
    mergeStringArrays
      (localDepsFromText infos tactic tactic.syntaxText)
      (localDepsFromText infos tactic tactic.sourceLineText)
  let targetDeps := localDepsFromText infos tactic (firstGoalTarget tactic.goalsBefore)
  let deps := mergeStringArrays sourceDeps targetDeps
  if deps.isEmpty && contextSolverKind kind then
    localDepsFromText infos tactic (firstGoalText tactic.goalsBefore)
  else
    deps

structure ProducedLocal where
  name : String
  typeText : String := ""
  label : String := ""
deriving Repr, Inhabited

private def haveLikeBody (kind raw : String) : String :=
  let body := (String.ofList ((stripBranchBullet raw).toList.drop (kind.length + 1))).trimAscii.toString
  body

private def haveLikeRhsText (kind raw : String) : String :=
  let (_, afterAssign) := splitFirst (haveLikeBody kind raw) ":="
  afterAssign.trimAscii.toString

private def haveLikeHasByProof (kind raw : String) : Bool :=
  (kind = "have" || kind = "let") && (haveLikeRhsText kind raw).startsWith "by"

private def parseHaveLikeProduced (kind raw : String) : Array ProducedLocal :=
  let (beforeAssign, _) := splitFirst (haveLikeBody kind raw) ":="
  let (beforeColon, afterColon) := splitFirst beforeAssign ":"
  let hasType := containsSubstr beforeAssign ":"
  let name := if hasType then firstWord beforeColon else firstWord beforeAssign
  let typeText := if hasType then afterColon.trimAscii.toString else ""
  if name = "" then #[] else #[{ name := name, typeText := typeText, label := kind }]

private def parseByCasesProduced (raw : String) : Array ProducedLocal :=
  let body := (String.ofList ((stripBranchBullet raw).toList.drop "by_cases ".length)).trimAscii.toString
  let (beforeColon, afterColon) := splitFirst body ":"
  let hasType := containsSubstr body ":"
  let name := firstWord beforeColon
  let typeText := if hasType then afterColon.trimAscii.toString else body
  if name = "" || typeText = "" then #[]
  else #[
    { name := name, typeText := typeText, label := "true branch" },
    { name := name, typeText := "¬ " ++ typeText, label := "false branch" }
  ]

private def parseProducedNamesAfterKind (kind raw label : String) : Array ProducedLocal :=
  let text := stripBranchBullet raw
  let body := (String.ofList (text.toList.drop kind.length)).trimAscii.toString
  let tokens := extractTokens body
  tokens.foldl
    (fun acc token =>
      if token = "" || token = "with" || token = "at" || token = "using" ||
          token = "by" || token = "show" then
        acc
      else
        acc.push { name := token, label := label })
    #[]

private def producedLocalsFromSyntax (kind raw : String) : Array ProducedLocal :=
  if kind = "have" || kind = "let" then parseHaveLikeProduced kind raw
  else if kind = "by_cases" then parseByCasesProduced raw
  else if kind = "intro" || kind = "intros" || kind = "rintro" || kind = "ext" then
    parseProducedNamesAfterKind kind raw kind
  else #[]

private def sameProducedLocal (left right : ProducedLocal) : Bool :=
  left.name == right.name &&
    normalizeTypeText left.typeText == normalizeTypeText right.typeText

private def pushProducedUnique
    (items : Array ProducedLocal) (item : ProducedLocal) : Array ProducedLocal :=
  if item.name = "" || items.any (fun existing => sameProducedLocal existing item) then
    items
  else if item.typeText != "" && items.any (fun existing =>
      existing.name == item.name && existing.typeText == "") then
    items.map (fun existing =>
      if existing.name == item.name && existing.typeText == "" then item else existing)
  else if item.typeText == "" && items.any (fun existing =>
      existing.name == item.name && existing.typeText != "") then
    items
  else
    items.push item

private def localDeclExists
    (items : Array (String × String)) (name typeText : String) : Bool :=
  items.any (fun item =>
    item.fst == name &&
      normalizeTypeText item.snd == normalizeTypeText typeText)

private def producedLocalsFromContextDelta
    (kind : String) (tactic : SemanticTacticInfo) : Array ProducedLocal :=
  if !(kind = "intro" || kind = "intros" || kind = "rintro" || kind = "ext" ||
      kind = "rw" ||
      kind = "cases" || kind = "rcases") then
    #[]
  else
    let before := tacticLocalContextBeforeForNodes tactic
    let after := tacticLocalContextAfterForNodes tactic
    after.foldl
      (fun acc (name, typeText) =>
        if localDeclExists before name typeText then
          acc
        else
          pushProducedUnique acc { name := name, typeText := typeText, label := kind })
      #[]

private def producedLocalsForTactic
    (kind raw : String) (tactic : SemanticTacticInfo) : Array ProducedLocal :=
  let fromSyntax := producedLocalsFromSyntax kind raw
  let fromContext := producedLocalsFromContextDelta kind tactic
  fromContext.foldl pushProducedUnique fromSyntax

private def sourceDisplayProducedLocals (tactics : Array SemanticTacticInfo) :
    Array ProducedLocal := Id.run do
  let mut out : Array ProducedLocal := #[]
  for tactic in tactics do
    let raw := tacticActionText tactic
    let kind := actionKindFromSyntaxText raw
    if kind = "have" || kind = "let" then
      for produced in parseHaveLikeProduced kind raw do
        if produced.typeText != "" then
          out := pushProducedUnique out produced
  return out

private def sourceDisplayForLocal?
    (items : Array ProducedLocal) (info : LocalNodeInfo) : Option ProducedLocal :=
  if info.initial then
    none
  else
    let candidates := items.filter (fun item => item.name == info.name && item.typeText != "")
    match candidates.filter (fun item => normalizeTypeText item.typeText == normalizeTypeText info.typeText) with
    | #[item] => some item
    | _ =>
        match candidates with
        | #[item] =>
            if typeHead item.typeText == typeHead info.typeText then
              some item
            else
              none
        | _ => none

private def localNodeToBlueprintWithSourceDisplay
    (sourceDisplays : Array ProducedLocal) (info : LocalNodeInfo) : BlueprintNode :=
  let displayType :=
    match sourceDisplayForLocal? sourceDisplays info with
    | some produced => produced.typeText
    | none => info.typeText
  let labelText := s!"{info.name} : {displayType}"
  { id := info.nodeId
    kind := if info.initial then "hypothesis" else "intermediate"
    nodeName := info.name
    typeText := displayType
    label := labelText }

private def producedLocalDisplay (produced : ProducedLocal) : String :=
  if produced.typeText = "" then
    produced.name
  else
    s!"{produced.name} : {produced.typeText}"

private def actionLabelForTactic
    (kind raw : String) (globals : Array String)
    (produced : Array ProducedLocal) : String :=
  if kind = "have" || kind = "let" then
    if haveLikeHasByProof kind raw then
      kind
    else
      let rhs := haveLikeRhsText kind raw
      if rhs != "" then rhs
      else
        match produced[0]? with
        | some output => producedLocalDisplay output
        | none => semanticActionLabel kind raw globals
  else
    semanticActionLabel kind raw globals

private def localInfoForProduced?
    (infos : Array LocalNodeInfo) (produced : ProducedLocal) : Option LocalNodeInfo :=
  if produced.typeText ≠ "" then
    findLocalByNameType? infos produced.name produced.typeText <|>
      findLocalByNameTypeNormalized? infos produced.name produced.typeText <|>
      if localNameCount infos produced.name == 1 then
        findLocalByName? infos produced.name
      else
        none
  else
    findLocalByName? infos produced.name

private def tacticInsideContainer (container child : SemanticTacticInfo) : Bool :=
  !(container.startLine == child.startLine && container.startCol == child.startCol) &&
    container.startLine <= child.startLine &&
    child.endLine <= container.endLine

private def containerSpan (info : SemanticTacticInfo) : Nat :=
  tacticSpan info

private def localInfoForEnclosingProducedTarget?
    (infos : Array LocalNodeInfo) (tactics : Array SemanticTacticInfo)
    (tactic : SemanticTacticInfo) (targetType : String) : Option LocalNodeInfo := Id.run do
  let target := normalizeTypeText targetType
  if target = "" then
    return none
  let mut best : Option (Nat × LocalNodeInfo) := none
  for container in tactics do
    let raw := tacticActionText container
    let kind := actionKindFromSyntaxText raw
    if (kind = "have" || kind = "let") && haveLikeHasByProof kind raw &&
        tacticInsideContainer container tactic then
      for produced in parseHaveLikeProduced kind raw do
        if produced.typeText != "" && normalizeTypeText produced.typeText == target then
          match localInfoForProduced? infos produced with
          | none => pure ()
          | some localInfo =>
              let span := containerSpan container
              match best with
              | none => best := some (span, localInfo)
              | some (bestSpan, _) =>
                  if span < bestSpan then
                    best := some (span, localInfo)
  return best.map (fun item => item.snd)

private def firstNonemptyLine (text : String) : String :=
  text.splitOn "\n" |>.foldl
    (fun found line =>
      if found ≠ "" then
        found
      else
        let line := line.trimAscii.toString
        if line = "" then "" else line)
    ""

private def goalCaseName (goal : String) : String :=
  let line := firstNonemptyLine goal
  if line.startsWith "case " then line else ""

private def goalNodeKey (caseName targetType : String) : String :=
  if caseName = "" then
    "⊢ " ++ targetType
  else
    caseName ++ "\n⊢ " ++ targetType

private def findGoalNode? (nodes : Array BlueprintNode) (key : String) :
    Option BlueprintNode :=
  nodes.find? (fun node => node.kind != "action" && node.rawText == key)

private def ensureTargetNode
    (nodes : Array BlueprintNode) (goalType goalText : String) (idx : Nat) :
    Array BlueprintNode × String :=
  let targetType := goalTarget goalText
  let caseName := goalCaseName goalText
  let targetType := targetType.trimAscii.toString
  let key := goalNodeKey caseName targetType
  if targetType = "" then
    (nodes, "n_goal")
  else if targetType == goalType && caseName == "" then
    (nodes, "n_goal")
  else
    match findGoalNode? nodes key with
    | some node => (nodes, node.id)
    | none =>
        let name :=
          if caseName = "" then s!"subgoal_{idx}"
          else sanitizeId caseName
        let nodeId := s!"n_subgoal_{idx}_{sanitizeId key}"
        let label := if caseName = "" then targetType else s!"{caseName}\n{targetType}"
        let node : BlueprintNode :=
          { id := nodeId
            kind := "subgoal"
            nodeName := name
            typeText := targetType
            label := label
            rawText := key }
        (nodes.push node, nodeId)

private def localInfoForSolvedTarget?
    (infos : Array LocalNodeInfo) (targetType : String) : Option LocalNodeInfo :=
  let target := normalizeTypeText targetType
  if target = "" then
    none
  else
    match infos.filter (fun info =>
      !info.initial && normalizeTypeText info.typeText == target) with
    | #[info] => some info
    | many => many[0]?

private def localInfoForFreshSolvedTarget?
    (infos : Array LocalNodeInfo) (tactic : SemanticTacticInfo)
    (targetType : String) : Option LocalNodeInfo :=
  let target := normalizeTypeText targetType
  if target = "" then
    none
  else
    let before := tacticLocalContextBeforeForNodes tactic
    let candidates := infos.filter (fun info =>
      !info.initial &&
        normalizeTypeText info.typeText == target &&
        !localDeclExists before info.name info.typeText)
    match candidates with
    | #[info] => some info
    | many => many[0]?

private def hasProducedOutput (produced : Array ProducedLocal) : Bool :=
  !produced.isEmpty

private def shouldSolveCurrentTarget (kind : String) (tactic : SemanticTacticInfo)
    (produced : Array ProducedLocal) : Bool :=
  produced.isEmpty &&
    (kind = "exact" || kind = "simp" || kind = "simpa" ||
      kind = "omega" || kind = "ring" || kind = "ring_nf" ||
      kind = "norm_num" || kind = "rfl" || kind = "abel" ||
      kind = "infer_instance" ||
      kind = "linarith" || kind = "nlinarith" ||
      tactic.goalsAfter.isEmpty)

private def shouldCreateSubgoals (kind : String) (produced : Array ProducedLocal) : Bool :=
  kind = "by_cases" ||
  kind = "cases" ||
  kind = "rcases" ||
  kind = "constructor" ||
  kind = "ext" ||
  kind = "subst" ||
  kind = "refine" ||
  kind = "apply" ||
  kind = "intro" ||
  kind = "intros" ||
  kind = "rintro" ||
  kind = "rw" ||
  kind = "right" ||
  kind = "left" ||
  kind = "change" ||
  produced.isEmpty

structure GoalGroup where
  parentId : String
  actionId : String
  tacticKind : String
  childIds : Array String := #[]
deriving Repr, Inhabited

structure SolvedGoal where
  goalId : String
  solverId : String
deriving Repr, Inhabited

private def goalIsSolved (solved : Array SolvedGoal) (goalId : String) : Bool :=
  solved.any (fun item => item.goalId == goalId)

private def addSolvedGoal (solved : Array SolvedGoal) (goalId solverId : String) :
    Array SolvedGoal :=
  if goalIsSolved solved goalId then solved else solved.push { goalId, solverId }

private def allGoalsSolved (solved : Array SolvedGoal) (goalIds : Array String) : Bool :=
  goalIds.all (goalIsSolved solved)

private def goalGroupKey (group : GoalGroup) : String :=
  group.actionId ++ "->" ++ group.parentId

private partial def uniqueBlueprintNodeId (nodes : Array BlueprintNode) (baseId : String)
    (idx : Nat) : String :=
  let candidate := if idx == 0 then baseId else s!"{baseId}_{idx + 1}"
  if nodes.any (fun node => node.id == candidate) then
    uniqueBlueprintNodeId nodes baseId (idx + 1)
  else
    candidate

private def closureNodeName (kind : String) : String :=
  if kind = "by_cases" || kind = "constructor" || kind = "refine" then
    "join"
  else
    "close"

private def closureNodeLabel (kind : String) : String :=
  if kind = "by_cases" then "all cases complete"
  else if kind = "constructor" then "all constructor goals complete"
  else if kind = "refine" then "all refine goals complete"
  else s!"{kind} subgoal complete"

private def closeCompletedGoalGroups
    (nodes0 : Array BlueprintNode) (edges0 : Array BlueprintEdge)
    (groups : Array GoalGroup) (solved0 : Array SolvedGoal) :
    Array BlueprintNode × Array BlueprintEdge × Array SolvedGoal := Id.run do
  let mut nodes := nodes0
  let mut edges := edges0
  let mut solved := solved0
  let mut closed : Array String := #[]
  let mut changed := true
  while changed do
    changed := false
    for group in groups do
      let key := goalGroupKey group
      if !closed.contains key && allGoalsSolved solved group.childIds then
        let baseId := "a_close_" ++ sanitizeId group.actionId
        let closeId := uniqueBlueprintNodeId nodes baseId 0
        let closeNode : BlueprintNode :=
          { id := closeId
            kind := "action"
            nodeName := closureNodeName group.tacticKind
            label := closureNodeLabel group.tacticKind
            rawText := group.tacticKind }
        nodes := nodes.push closeNode
        for childId in group.childIds do
          edges := pushEdgeUnique edges
            { fromId := childId
              toId := closeId
              kind := "subgoal_to_join"
              label := "proved" }
        edges := pushEdgeUnique edges
          { fromId := closeId
            toId := group.parentId
            kind := "action_solves_goal"
            label := closureNodeLabel group.tacticKind }
        solved := addSolvedGoal solved group.parentId closeId
        closed := closed.push key
        changed := true
  (nodes, edges, solved)

private def buildSemanticPrimaryBlueprint
    (sourceFile theoremName : String) (command : SemanticCommandInfo)
    (tactics : Array SemanticTacticInfo) (terms : Array SemanticTermInfo) :
    Except String Blueprint := do
  if tactics.isEmpty then
    throw s!"no tactic InfoTree entries found for theorem {theoremName}"
  let firstTactic := tactics[0]!
  let theoremType := firstGoalTarget firstTactic.goalsBefore
  let goalType := if theoremType = "" then command.syntaxText else theoremType
  let goalNode : BlueprintNode :=
    { id := "n_goal"
      kind := "theorem_goal"
      nodeName := theoremName ++ ".goal"
      typeText := goalType
      label := goalType
      rawText := goalType }
  let localInfos := collectLocalInfos tactics
  let sourceDisplays := sourceDisplayProducedLocals tactics
  let mut nodes := localInfos.map (localNodeToBlueprintWithSourceDisplay sourceDisplays)
  nodes := nodes.push goalNode
  let mut edges : Array BlueprintEdge := #[]
  for localInfo in localInfos do
    if localInfo.initial then
      edges := pushEdgeUnique edges
        { fromId := localInfo.nodeId
          toId := "n_goal"
          kind := "context_to_goal"
          label := "context" }
  let mut goalGroups : Array GoalGroup := #[]
  let mut solvedGoals : Array SolvedGoal := #[]
  for i in [:tactics.size] do
    let tactic := tactics[i]!
    let raw := tacticActionText tactic
    let tacticForAction := { tactic with syntaxText := raw }
    let kind := actionKindFromSyntaxText raw
    let relatedTerms := termsForTactic kind tacticForAction terms
    let (semanticLocalsFromTerms, semanticGlobals) := mergedTermDeps relatedTerms
    let produced := producedLocalsForTactic kind raw tacticForAction
    let fallbackLocals :=
      if !isHaveLetByProof kind tacticForAction &&
          (semanticLocalsFromTerms.isEmpty || sourceDepsShouldSupplement kind) then
        fallbackLocalDepsForTactic localInfos tacticForAction
      else
        #[]
    let semanticLocals0 := mergeStringArrays semanticLocalsFromTerms fallbackLocals
    let producedNames := produced.map (·.name)
    let semanticLocals :=
      if kind = "rw" then
        semanticLocals0
      else
        semanticLocals0.filter (fun localName => !producedNames.contains localName)
    let exprType := firstNonempty (relatedTerms.map (·.exprType))
    let expectedType := firstNonempty (relatedTerms.map (·.expectedType))
    let actionId := s!"a_sem_{i + 1}_{sanitizeId kind}_{tactic.startLine}"
    let actionNode : BlueprintNode :=
      { id := actionId
        kind := "action"
        nodeName := kind
        label := actionLabelForTactic kind raw semanticGlobals produced
        rawText := raw
        sourceLine := tactic.startLine
        usesLocal := semanticLocals
        usesGlobal := semanticGlobals
        goalsBefore := tactic.goalsBefore
        goalsAfter := tactic.goalsAfter
        localContext := tactic.localContext
        exprType := exprType
        expectedType := expectedType
        semanticUsesLocal := semanticLocals
        semanticUsesGlobal := semanticGlobals }
    nodes := nodes.push actionNode
    for localName in semanticLocals do
      match localInfoForAction? localInfos tactic localName with
      | none => pure ()
      | some localInfo =>
          edges := pushEdgeUnique edges
            { fromId := localInfo.nodeId, toId := actionId, kind := "input_to_action", label := localName }
    let currentGoalText :=
      match tactic.goalsBefore[0]? with
      | some goal => goal
      | none => goalType
    let ensured := ensureTargetNode nodes goalType currentGoalText (i + 1)
    let currentGoalTarget := goalTarget currentGoalText
    let freshLocalTarget? :=
      localInfoForEnclosingProducedTarget? localInfos tactics tacticForAction currentGoalTarget
    let targetId :=
      match freshLocalTarget? with
      | some localInfo => localInfo.nodeId
      | none => ensured.snd
    if freshLocalTarget?.isNone then
      nodes := ensured.fst
      edges := pushEdgeUnique edges
        { fromId := targetId, toId := actionId, kind := "goal_to_action", label := "current target" }
    for output in produced do
      match localInfoForProduced? localInfos output with
      | none => pure ()
      | some localInfo =>
          edges := pushEdgeUnique edges
            { fromId := actionId
              toId := localInfo.nodeId
              kind := "action_to_output"
              label := if output.label = "" then kind else output.label }
    if shouldSolveCurrentTarget kind tactic produced then
      match freshLocalTarget? with
      | some localInfo =>
          edges := pushEdgeUnique edges
            { fromId := actionId
              toId := localInfo.nodeId
              kind := "action_to_output"
              label := kind }
      | none =>
          edges := pushEdgeUnique edges
            { fromId := actionId, toId := targetId, kind := "action_solves_goal", label := kind }
          solvedGoals := addSolvedGoal solvedGoals targetId actionId
    else if shouldCreateSubgoals kind produced then
      let mut childIds : Array String := #[]
      for goal in tactic.goalsAfter do
        if goalTarget goal ≠ "" then
          let ensuredAfter := ensureTargetNode nodes goalType goal (i + 1)
          nodes := ensuredAfter.fst
          let childId := ensuredAfter.snd
          if childId != targetId then
            childIds := childIds.push childId
            edges := pushEdgeUnique edges
              { fromId := actionId
                toId := childId
                kind := "action_to_subgoal"
                label := kind }
      if !childIds.isEmpty then
        goalGroups := goalGroups.push
          { parentId := targetId
            actionId := actionId
            tacticKind := kind
            childIds := childIds }
      else if tactic.goalsAfter.isEmpty then
        edges := pushEdgeUnique edges
          { fromId := actionId, toId := targetId, kind := "action_solves_goal", label := kind }
        solvedGoals := addSolvedGoal solvedGoals targetId actionId
  let closed := closeCompletedGoalGroups nodes edges goalGroups solvedGoals
  pure {
    theoremName := theoremName
    theoremType := goalType
    sourceFile := sourceFile
    nodes := closed.fst
    edges := closed.snd.fst }

def enrichBlueprintWithInfo (sourceFile source : String) (bp : Blueprint) :
    IO (Except String Blueprint) := do
  match ← elaborateSemanticSnapshot sourceFile source (some bp.theoremName) with
  | .error err => pure (.error err)
  | .ok snapshot =>
      let nodes := bp.nodes.map (enrichNodeWithSemantic snapshot)
      let edges := addSemanticInputEdges nodes bp.edges
      pure <| .ok { bp with nodes, edges }

def extractBlueprintSemanticPrimary (sourceFile source theoremName : String) :
    IO (Except String Blueprint) := do
  match ← elaborateSemanticSnapshot sourceFile source (some theoremName) with
  | .error err => pure (.error err)
  | .ok snapshot =>
      match findTheoremCommand? theoremName snapshot with
      | none => pure (.error s!"theorem command not found in elaborated Syntax: {theoremName}")
      | some command =>
          let tactics := minimizeSourceTactics <| snapshot.tactics.filter (fun info =>
            infoInsideCommand command.startLine command.endLine info.startLine info.endLine)
          let terms := snapshot.terms.filter (fun info =>
            infoInsideCommand command.startLine command.endLine info.startLine info.endLine)
          pure <| buildSemanticPrimaryBlueprint sourceFile theoremName command tactics terms

end ProofStruct
