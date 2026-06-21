import Lean
import ProofStruct.Extract.Graph

namespace ProofStruct

structure SyntaxStep where
  id : String
  kind : String
  rawText : String
  lineNo : Nat
  indent : Nat := 0
  name : String := ""
  typeText : String := ""
  termText : String := ""
deriving Repr, Inhabited

structure LocalRef where
  name : String
  nodeId : String
deriving Repr, Inhabited

structure Binder where
  name : String
  typeText : String
deriving Repr, Inhabited

private def trim (s : String) : String := s.trimAscii.toString

private def dropChars (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

private def takeChars (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take n)

private def joinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinSep sep xs

private def joinLines (lines : List String) : String :=
  joinSep "\n" lines

private def splitFirst (s sep : String) : String × String :=
  match s.splitOn sep with
  | [] => ("", "")
  | h :: t => (h, joinSep sep t)

private def containsSubstr (s needle : String) : Bool :=
  match s.splitOn needle with
  | [] => false
  | [_] => false
  | _ => true

private def stripBullet (s : String) : String :=
  let t := trim s
  if t.startsWith "· " then
    trim (dropChars t 2)
  else if t.startsWith "·" then
    trim (dropChars t 1)
  else
    t

private partial def countLeadingSpacesAux : List Char → Nat → Nat
  | [], acc => acc
  | ' ' :: rest, acc => countLeadingSpacesAux rest (acc + 1)
  | '\t' :: rest, acc => countLeadingSpacesAux rest (acc + 2)
  | _ :: _, acc => acc

private def lineIndent (s : String) : Nat :=
  countLeadingSpacesAux s.toList 0

private def isRecognizedStart (s : String) : Bool :=
  let t := stripBullet s
  t.startsWith "have " ||
  t.startsWith "let " ||
  t.startsWith "exact " ||
  t.startsWith "simpa " ||
  t.startsWith "rw " ||
  t.startsWith "norm_num" ||
  t.startsWith "refine " ||
  t.startsWith "calc" ||
  t.startsWith "omega" ||
  t.startsWith "ring" ||
  t.startsWith "right" ||
  t.startsWith "left" ||
  t.startsWith "constructor" ||
  t.startsWith "by_cases " ||
  t.startsWith "apply " ||
  t.startsWith "intro " ||
  t.startsWith "intros " ||
  t.startsWith "change "

private def hasAssign (s : String) : Bool :=
  containsSubstr s ":="

private partial def collectHaveLines : List (Nat × String) → List String → List String × List (Nat × String)
  | [], acc => (acc.reverse, [])
  | (_n, line) :: rest, acc =>
      let current := acc.reverse
      let raw := joinLines (current ++ [stripBullet line])
      if hasAssign raw then
        let (_, afterAssign) := splitFirst raw ":="
        let after := trim afterAssign
        if after = "" then
          match rest with
          | [] => ((stripBullet line :: acc).reverse, [])
          | (_n2, line2) :: rest2 =>
              if isRecognizedStart line2 then
                ((stripBullet line :: acc).reverse, rest)
              else
                ((stripBullet line2 :: stripBullet line :: acc).reverse, rest2)
        else
          ((stripBullet line :: acc).reverse, rest)
      else
        collectHaveLines rest (stripBullet line :: acc)

private def firstWord (s : String) : String :=
  match (trim s).splitOn " " with
  | [] => ""
  | h :: _ => h

private def words (s : String) : Array String :=
  ((trim s).splitOn " ").foldl
    (fun acc w =>
      let w := trim w
      if w = "" then acc else acc.push w)
    #[]

private def parseHaveLike (kind firstPrefix raw : String) (lineNo indent : Nat) : SyntaxStep :=
  let body := trim (dropChars (trim raw) firstPrefix.length)
  let (beforeAssign, afterAssign) := splitFirst body ":="
  let (beforeColon, afterColon) := splitFirst beforeAssign ":"
  let name :=
    if containsSubstr beforeAssign ":" then firstWord beforeColon else firstWord beforeAssign
  let typeText :=
    if containsSubstr beforeAssign ":" then trim afterColon else ""
  { id := "", kind := kind, rawText := raw, lineNo := lineNo, indent := indent,
    name := name, typeText := typeText, termText := trim afterAssign }

private def parseByCases (raw : String) (lineNo indent : Nat) : SyntaxStep :=
  let body := trim (dropChars (trim raw) "by_cases ".length)
  let (beforeColon, afterColon) := splitFirst body ":"
  let name := firstWord beforeColon
  let typeText := if containsSubstr body ":" then trim afterColon else trim body
  { id := "", kind := "by_cases", rawText := raw, lineNo := lineNo, indent := indent,
    name := name, typeText := typeText }

private def parseSimple (kind pref raw : String) (lineNo indent : Nat) : SyntaxStep :=
  let term := trim (dropChars (trim raw) pref.length)
  { id := "", kind := kind, rawText := raw, lineNo := lineNo, indent := indent, termText := term }

private def parseLineStep (lineNo : Nat) (line : String) : Option SyntaxStep :=
  let t := stripBullet line
  let indent := lineIndent line
  if t = "" then none
  else if t.startsWith "let " then some (parseHaveLike "let" "let " t lineNo indent)
  else if t.startsWith "by_cases " then some (parseByCases t lineNo indent)
  else if t.startsWith "exact " then some (parseSimple "exact" "exact " t lineNo indent)
  else if t.startsWith "simpa " then some (parseSimple "simpa" "simpa " t lineNo indent)
  else if t.startsWith "rw " then some (parseSimple "rw" "rw " t lineNo indent)
  else if t.startsWith "norm_num" then some (parseSimple "norm_num" "norm_num" t lineNo indent)
  else if t.startsWith "refine " then some (parseSimple "refine" "refine " t lineNo indent)
  else if t.startsWith "calc" then some (parseSimple "calc" "calc" t lineNo indent)
  else if t.startsWith "omega" then some (parseSimple "omega" "omega" t lineNo indent)
  else if t.startsWith "ring" then some (parseSimple "ring" "ring" t lineNo indent)
  else if t.startsWith "right" then some (parseSimple "right" "right" t lineNo indent)
  else if t.startsWith "left" then some (parseSimple "left" "left" t lineNo indent)
  else if t.startsWith "constructor" then some (parseSimple "constructor" "constructor" t lineNo indent)
  else if t.startsWith "apply " then some (parseSimple "apply" "apply " t lineNo indent)
  else if t.startsWith "intro " then some (parseSimple "intro" "intro " t lineNo indent)
  else if t.startsWith "intros " then some (parseSimple "intros" "intros " t lineNo indent)
  else if t.startsWith "change " then some (parseSimple "change" "change " t lineNo indent)
  else if hasAssign t then some { id := "", kind := "calc_step", rawText := t, lineNo := lineNo, indent := indent, termText := t }
  else none

private partial def parseProofStepsAux : List (Nat × String) → Array SyntaxStep → Array SyntaxStep
  | [], acc => acc
  | (n, line) :: rest, acc =>
      let t := stripBullet line
      if t = "" then
        parseProofStepsAux rest acc
      else if t.startsWith "have " then
        let (rawLines, rest') := collectHaveLines ((n, line) :: rest) []
        let raw := joinLines rawLines
        parseProofStepsAux rest' (acc.push (parseHaveLike "have" "have " raw n (lineIndent line)))
      else
        match parseLineStep n line with
        | some step => parseProofStepsAux rest (acc.push step)
        | none => parseProofStepsAux rest acc

private def parseProofSteps (lines : List (Nat × String)) : Array SyntaxStep :=
  parseProofStepsAux lines #[]

private partial def findTopLevelColonAux : List Char → Nat → Nat → Option Nat → Option Nat
  | [], _, _, last => last
  | c :: rest, idx, depth, last =>
      let depth' :=
        if c = '(' || c = '[' || c = '{' then depth + 1
        else if c = ')' || c = ']' || c = '}' then depth - 1
        else depth
      let last' := if c = ':' && depth = 0 && last.isNone then some idx else last
      findTopLevelColonAux rest (idx + 1) depth' last'

private def findTopLevelColon (s : String) : Option Nat :=
  findTopLevelColonAux s.toList 0 0 none

private partial def collectGroup
    (openChar closeChar : Char) : Nat → List Char → List Char → String × List Char
  | _, [], acc => (String.ofList acc.reverse, [])
  | depth, c :: rest, acc =>
      if c = openChar then
        collectGroup openChar closeChar (depth + 1) rest (c :: acc)
      else if c = closeChar then
        if depth = 1 then
          (String.ofList acc.reverse, rest)
        else
          collectGroup openChar closeChar (depth - 1) rest (c :: acc)
      else
        collectGroup openChar closeChar depth rest (c :: acc)

private partial def collectBinderGroupsAux : List Char → Array (Char × String) → Array (Char × String)
  | [], acc => acc
  | c :: rest, acc =>
      if c = '(' then
        let (body, rest') := collectGroup '(' ')' 1 rest []
        collectBinderGroupsAux rest' (acc.push ('(', body))
      else if c = '[' then
        let (body, rest') := collectGroup '[' ']' 1 rest []
        collectBinderGroupsAux rest' (acc.push ('[', body))
      else
        collectBinderGroupsAux rest acc

private def collectBinderGroups (s : String) : Array (Char × String) :=
  collectBinderGroupsAux s.toList #[]

private def parseBinderGroup (idx : Nat) (group : Char × String) : Array Binder :=
  let (openChar, body) := group
  let body := trim body
  if containsSubstr body ":" then
    let (namesText, typeText) := splitFirst body ":"
    let names := words namesText
    names.map (fun name => { name := name, typeText := trim typeText })
  else if openChar = '[' then
    #[{ name := s!"inst_{idx}", typeText := body }]
  else
    #[]

private def parseBinders (declBeforeType : String) : Array Binder := Id.run do
  let groups := collectBinderGroups declBeforeType
  let mut binders : Array Binder := #[]
  for i in [:groups.size] do
    let group := groups[i]!
    binders := binders ++ parseBinderGroup (i + 1) group
  return binders

private def sanitizeChar (c : Char) : Char :=
  if c.isAlphanum || c = '_' then c else '_'

def sanitizeId (s : String) : String :=
  let cleaned := String.ofList ((trim s).toList.map sanitizeChar)
  if cleaned = "" then "anon" else cleaned

private def uniqueStrings (items : Array String) : Array String :=
  items.foldl
    (fun acc item =>
      let item := trim item
      if item = "" || acc.contains item then acc else acc.push item)
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
  tokens.any (fun tok => tok = name || tok.startsWith (name ++ "."))

private def localDeps (raw produced : String) (locals : Array LocalRef) : Array LocalRef :=
  let tokens := extractTokens raw
  locals.foldl
    (fun acc loc =>
      if loc.name = produced then acc
      else if tokenUsesLocal tokens loc.name then
        if acc.any (fun x => x.name = loc.name) then acc else acc.push loc
      else acc)
    #[]

private def extractGlobals (raw : String) (kind : String) : Array String :=
  let pieces := extractTokens raw
  let dotted := pieces.foldl
    (fun acc p =>
      if containsSubstr p "." then acc.push p
      else acc)
    #[]
  let withTactic :=
    if kind = "ring" || kind = "omega" || kind = "norm_num" || kind = "exact_mod_cast" then
      dotted.push kind
    else
      dotted
  uniqueStrings withTactic

private def actionLabel (step : SyntaxStep) (globals : Array String) : String :=
  if globals.isEmpty then step.kind else String.intercalate "; " globals.toList

private def theoremStart (theoremName line : String) : Bool :=
  let t := trim line
  t.startsWith s!"theorem {theoremName} " || t.startsWith s!"theorem {theoremName}\n" ||
  t = s!"theorem {theoremName}"

private def anyTheoremStart (line : String) : Bool :=
  (trim line).startsWith "theorem "

private def findTheoremRange (lines : List String) (theoremName : String) : Except String (Nat × Nat) := do
  let mut start? : Option Nat := none
  let mut stop? : Option Nat := none
  let mut idx := 0
  for line in lines do
    if start?.isNone && theoremStart theoremName line then
      start? := some idx
    else
      match start? with
      | some s =>
          if idx > s && anyTheoremStart line && stop?.isNone then
            stop? := some idx
      | none => pure ()
    idx := idx + 1
  match start? with
  | none => throw s!"theorem not found: {theoremName}"
  | some s =>
      let e := stop?.getD lines.length
      return (s, e)

private def indexedSlice (lines : List String) (start stop : Nat) : List (Nat × String) := Id.run do
  let arr := lines.toArray
  let mut out : List (Nat × String) := []
  for i in [start:stop] do
    out := (i + 1, arr[i]!) :: out
  return out.reverse

private def splitAtBy (block : List (Nat × String)) : Except String (String × List (Nat × String)) := do
  let mut declLines : List String := []
  let mut proofLines : List (Nat × String) := []
  let mut found := false
  for (n, line) in block do
    if !found && containsSubstr line ":= by" then
      let (before, after) := splitFirst line ":= by"
      declLines := before :: declLines
      let rest := trim after
      if rest ≠ "" then
        proofLines := (n, rest) :: proofLines
      found := true
    else if found then
      proofLines := (n, line) :: proofLines
    else
      declLines := line :: declLines
  if !found then
    throw "could not find ':= by' in theorem block"
  return (joinLines declLines.reverse, proofLines.reverse)

private def theoremTypeAndPrefix (decl : String) : String × String :=
  match findTopLevelColon decl with
  | none => (decl, "")
  | some idx =>
      let prefText := takeChars decl idx
      let typeText := trim (dropChars decl (idx + 1))
      (prefText, typeText)

private def makeHypNode (binder : Binder) : BlueprintNode :=
  let id := "n_" ++ sanitizeId binder.name
  let labelText := if binder.typeText = "" then binder.name else binder.name ++ " : " ++ binder.typeText
  { id := id, kind := "hypothesis", nodeName := binder.name, typeText := binder.typeText, label := labelText, sourceLine := 0, rawText := "", usesLocal := #[], usesGlobal := #[] }

private def addInputEdges (actionId : String) (deps : Array LocalRef) : Array BlueprintEdge :=
  deps.map (fun dep =>
    { fromId := dep.nodeId, toId := actionId, kind := "input_to_action", label := dep.name })

private def stepOutputNode? (step : SyntaxStep) : Option BlueprintNode :=
  if step.kind = "have" then
    let stepName := step.name
    let stepType := step.typeText
    let id := "n_" ++ sanitizeId stepName
    let labelText := if stepType = "" then stepName else stepName ++ " : " ++ stepType
    let node : BlueprintNode := { id := id, kind := "intermediate", nodeName := stepName, typeText := stepType, label := labelText, rawText := step.rawText, sourceLine := step.lineNo }
    some node
  else if step.kind = "let" then
    let stepName := step.name
    let stepType := step.typeText
    let id := "n_" ++ sanitizeId stepName
    let labelText := if stepType = "" then stepName else stepName ++ " : " ++ stepType
    let node : BlueprintNode := { id := id, kind := "constructed_object", nodeName := stepName, typeText := stepType, label := labelText, rawText := step.rawText, sourceLine := step.lineNo }
    some node
  else
    none

private def buildAction
    (targetId : String) (idx : Nat) (step : SyntaxStep) (locals : Array LocalRef) :
    BlueprintNode × Array BlueprintNode × Array BlueprintEdge × Array LocalRef :=
  let actionId := s!"a_{idx}_{step.kind}_{step.lineNo}"
  let deps := localDeps step.rawText step.name locals
  let globals := extractGlobals step.rawText step.kind
  let action : BlueprintNode :=
    { id := actionId, kind := "action", nodeName := step.kind, label := actionLabel step globals, rawText := step.rawText, sourceLine := step.lineNo, usesLocal := deps.map (fun d => d.name), usesGlobal := globals }
  let inputEdges := addInputEdges actionId deps
  let goalEdge : BlueprintEdge := { fromId := targetId, toId := actionId, kind := "goal_to_action", label := "current target" }
  if step.kind = "exact" || step.kind = "simpa" then
    let solveEdge : BlueprintEdge := { fromId := actionId, toId := targetId, kind := "action_solves_goal", label := step.kind }
    (action, #[], inputEdges.push goalEdge |>.push solveEdge, #[])
  else if step.kind = "have" || step.kind = "let" then
    match stepOutputNode? step with
    | none => (action, #[], inputEdges.push goalEdge, #[])
    | some outNode =>
        let outEdge : BlueprintEdge := { fromId := actionId, toId := outNode.id, kind := "action_to_output", label := step.kind }
        let newLocal := { name := step.name, nodeId := outNode.id }
        (action, #[outNode], inputEdges.push goalEdge |>.push outEdge, #[newLocal])
  else if step.kind = "by_cases" then
    let trueId := "n_" ++ sanitizeId step.name ++ "_true"
    let falseId := "n_" ++ sanitizeId step.name ++ "_false"
    let trueNode : BlueprintNode :=
      { id := trueId, kind := "subgoal", nodeName := step.name, typeText := step.typeText, label := "case " ++ step.name ++ " : " ++ step.typeText, rawText := step.rawText, sourceLine := step.lineNo }
    let falseNode : BlueprintNode :=
      { id := falseId, kind := "subgoal", nodeName := "not_" ++ step.name, typeText := "¬ " ++ step.typeText, label := "case ¬ " ++ step.typeText, rawText := step.rawText, sourceLine := step.lineNo }
    let edges := inputEdges.push goalEdge
      |>.push { fromId := actionId, toId := trueId, kind := "action_to_subgoal", label := "true branch" }
      |>.push { fromId := actionId, toId := falseId, kind := "action_to_subgoal", label := "false branch" }
    (action, #[trueNode, falseNode], edges, #[{ name := step.name, nodeId := trueId }])
  else if step.kind = "refine" || step.kind = "constructor" || step.kind = "right" || step.kind = "left" then
    let subId := s!"n_subgoal_{idx}_{step.lineNo}"
    let subNode : BlueprintNode :=
      { id := subId, kind := "subgoal", nodeName := s!"subgoal_{idx}", typeText := "", label := "subgoal after " ++ step.kind, rawText := step.rawText, sourceLine := step.lineNo }
    let edge := { fromId := actionId, toId := subId, kind := "action_to_subgoal", label := step.kind }
    (action, #[subNode], inputEdges.push goalEdge |>.push edge, #[])
  else
    (action, #[], inputEdges.push goalEdge, #[])

private partial def popInactiveTargets (indent : Nat) (stack : Array (Nat × String)) : Array (Nat × String) :=
  if stack.isEmpty then
    stack
  else
    let top := stack[stack.size - 1]!
    if top.fst >= indent then
      popInactiveTargets indent stack.pop
    else
      stack

private def currentTarget (goalId : String) (stack : Array (Nat × String)) : String :=
  if stack.isEmpty then goalId else (stack[stack.size - 1]!).snd

private def isByBlockHave (step : SyntaxStep) : Bool :=
  step.kind = "have" && trim step.termText = "by"

private def buildBlueprintFromParts
    (sourceFile theoremName theoremType declPrefix : String) (steps : Array SyntaxStep) : Blueprint := Id.run do
  let binders := parseBinders declPrefix
  let goalId := "n_goal"
  let goalNode : BlueprintNode :=
    { id := goalId, kind := "theorem_goal", nodeName := theoremName ++ ".goal", typeText := theoremType, label := theoremType, rawText := theoremType }
  let mut bp := emptyBlueprint sourceFile theoremName theoremType
  let mut locals : Array LocalRef := #[]
  for binder in binders do
    let node := makeHypNode binder
    bp := bp.addNode node
    locals := locals.push { name := binder.name, nodeId := node.id }
  bp := bp.addNode goalNode
  let mut targetStack : Array (Nat × String) := #[]
  for i in [:steps.size] do
    let step := steps[i]!
    targetStack := popInactiveTargets step.indent targetStack
    let targetId := currentTarget goalId targetStack
    let (action, outNodes, edges, newLocals) := buildAction targetId (i + 1) step locals
    bp := bp.addNode action
    for node in outNodes do
      bp := bp.addNode node
    bp := bp.addEdges edges
    locals := locals ++ newLocals
    if isByBlockHave step then
      targetStack := targetStack.push (step.indent, "n_" ++ sanitizeId step.name)
  return bp

def extractBlueprintFromSource (sourceFile source theoremName : String) : Except String Blueprint := do
  let lines := source.splitOn "\n"
  let (start, stop) ← findTheoremRange lines theoremName
  let block := indexedSlice lines start stop
  let (decl, proofLines) ← splitAtBy block
  let (declPrefix, theoremType) := theoremTypeAndPrefix decl
  let steps := parseProofSteps proofLines
  return buildBlueprintFromParts sourceFile theoremName theoremType declPrefix steps

end ProofStruct
