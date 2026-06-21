import ProofWidgets.Component.HtmlDisplay
import ProofStruct.Widget.LayeredJson
import ProofStruct.Widget.RenderGraphDisplay

namespace ProofStruct

open Lean
open ProofWidgets
open scoped ProofWidgets.Jsx

private def cleanText (s : String) : String :=
  let flat1 := String.intercalate " " (s.splitOn "\n")
  let flat2 := String.intercalate " " (flat1.splitOn "\r")
  let flat3 := String.intercalate " " (flat2.splitOn "\t")
  let words :=
    flat3.splitOn " " |>.filterMap fun word =>
      let word := word.trimAscii.toString
      if word = "" then none else some word
  String.intercalate " " words

private def truncateText (s : String) (maxChars : Nat := 64) : String :=
  let s := cleanText s
  if s.length <= maxChars then s else (s.take (maxChars - 3)).copy ++ "..."

private def nonemptyLines (lines : Array String) : Array String :=
  lines.foldl
    (fun acc line =>
      let line := cleanText line
      if line = "" then acc else acc.push line)
    #[]

private def splitWordsNearMiddle? (text : String) : Option (String × String) :=
  let words :=
    text.splitOn " " |>.filterMap fun word =>
      let word := cleanText word
      if word = "" then none else some word
  if words.length < 2 then
    none
  else
    let arr := words.toArray
    let mid := arr.size / 2
    let left := String.intercalate " " (arr.extract 0 mid |>.toList)
    let right := String.intercalate " " (arr.extract mid arr.size |>.toList)
    if left = "" || right = "" then none else some (left, right)

private def wrapTextLines (text : String) (maxChars : Nat) : Array String :=
  let text := cleanText text
  if text = "" then
    #[]
  else if text.length <= maxChars then
    #[text]
  else
    match splitWordsNearMiddle? text with
    | some (left, right) =>
        nonemptyLines #[truncateText left maxChars, truncateText right maxChars]
    | none =>
        #[truncateText text maxChars]

private def planNodeSourceText (node : InfoviewPlanNode) : String :=
  let startLine := node.sourceRange.startLine
  let endLine := node.sourceRange.endLine
  let tacticText :=
    if node.tactics.isEmpty then node.mainTactic else String.intercalate "/" node.tactics.toList
  let lineText :=
    if startLine == 0 then
      ""
    else if endLine != 0 && endLine != startLine then
      s!"line {startLine}-{endLine}"
    else
      s!"line {startLine}"
  if lineText = "" then tacticText
  else if tacticText = "" then lineText
  else s!"{lineText} | {tacticText}"

private def planNodeLines (node : InfoviewPlanNode) : Array String :=
  let title := if node.label != "" then node.label else node.id
  let role :=
    if node.roleSummary != "" then node.roleSummary
    else if node.detailLabel != "" then node.detailLabel
    else node.kind
  let branch :=
    if node.branchLabel != "" then s!"branch {node.branchLabel}" else ""
  nonemptyLines <|
    #[title] ++
    wrapTextLines role 42 ++
    #[branch, planNodeSourceText node]

private def longestLineLength (lines : Array String) : Nat :=
  lines.foldl (fun acc line => Nat.max acc line.length) 0

private def planNodeWidth (lines : Array String) : Nat :=
  Nat.min 340 (Nat.max 180 (112 + longestLineLength lines * 7))

private def planNodeHeight (lines : Array String) : Nat :=
  Nat.min 116 (Nat.max 58 (34 + lines.size * 15))

private def planStrokeColor (kind : String) : String :=
  match kind with
  | "introduce_context" => "#2563eb"
  | "prove_intermediate" => "#2563eb"
  | "construct_object" => "#2563eb"
  | "transform_goal" => "#0f766e"
  | "calculation_chain" => "#0f766e"
  | "automation" => "#d97706"
  | "split_goal" => "#7c3aed"
  | "case_split" => "#7c3aed"
  | "solve_goal" => "#16a34a"
  | "close_goal" => "#15803d"
  | _ => "#64748b"

private def planFillColor (kind : String) : String :=
  match kind with
  | "introduce_context" => "rgba(37, 99, 235, 0.10)"
  | "prove_intermediate" => "rgba(37, 99, 235, 0.10)"
  | "construct_object" => "rgba(37, 99, 235, 0.10)"
  | "transform_goal" => "rgba(15, 118, 110, 0.11)"
  | "calculation_chain" => "rgba(15, 118, 110, 0.11)"
  | "automation" => "rgba(217, 119, 6, 0.13)"
  | "split_goal" => "rgba(124, 58, 237, 0.12)"
  | "case_split" => "rgba(124, 58, 237, 0.12)"
  | "solve_goal" => "rgba(22, 163, 74, 0.11)"
  | "close_goal" => "rgba(21, 128, 61, 0.14)"
  | _ => "rgba(100, 116, 139, 0.10)"

private def visiblePlanEdge (edge : InfoviewPlanEdge) : Bool :=
  edge.kind = "flow" && edge.visibleByDefault

private def safeToken (s : String) : String :=
  let token := s.foldl (fun acc c => if c.isAlphanum then acc.push c else acc.push '-') ""
  if token = "" then "layered" else token

private def findPlanNodeIndex? (nodes : Array InfoviewPlanNode) (id : String) : Option Nat := Id.run do
  let mut found : Option Nat := none
  for i in [:nodes.size] do
    if found.isNone && nodes[i]!.id == id then
      found := some i
  return found

private def computeRanks (nodes : Array InfoviewPlanNode) (edges : Array InfoviewPlanEdge) :
    Array Nat :=
  Id.run do
    let mut ranks := Array.replicate nodes.size 0
    for _ in [:nodes.size + edges.size + 1] do
      for edge in edges do
        match findPlanNodeIndex? nodes edge.fromId, findPlanNodeIndex? nodes edge.toId with
        | some fromIdx, some toIdx =>
            let nextRank := Nat.min nodes.size (ranks[fromIdx]! + 1)
            if ranks[toIdx]! < nextRank then
              ranks := ranks.set! toIdx nextRank
        | _, _ => pure ()
    return ranks

private def maxArray (xs : Array Nat) : Nat :=
  xs.foldl Nat.max 0

private def layerCounts (ranks : Array Nat) : Array Nat :=
  Id.run do
    let mut counts := Array.replicate (maxArray ranks + 1) 0
    for rank in ranks do
      counts := counts.set! rank (counts[rank]! + 1)
    return counts

structure PlanStaticNode where
  node : InfoviewPlanNode
  lines : Array String
  width : Nat
  height : Nat
  rank : Nat
  slot : Nat
  x : Nat
  y : Nat

private def planStaticLayout (nodes : Array InfoviewPlanNode) (edges : Array InfoviewPlanEdge) :
    Array PlanStaticNode :=
  Id.run do
    let ranks := computeRanks nodes edges
    let counts := layerCounts ranks
    let maxLayer := Nat.max 1 (maxArray counts)
    let mut used := Array.replicate counts.size 0
    let cellW := 330
    let rowH := 150
    let padX := 48
    let padY := 44
    let mut out : Array PlanStaticNode := #[]
    for i in [:nodes.size] do
      let node := nodes[i]!
      let lines := planNodeLines node
      let rank := ranks[i]!
      let slot := used[rank]!
      used := used.set! rank (slot + 1)
      let width := planNodeWidth lines
      let height := planNodeHeight lines
      let layerWidth := counts[rank]!
      let layerOffset := (maxLayer - layerWidth) * cellW / 2
      let x := padX + layerOffset + slot * cellW + cellW / 2
      let y := padY + rank * rowH + rowH / 2
      out := out.push { node, lines, width, height, rank, slot, x, y }
    return out

private def findPlanStaticNode? (layout : Array PlanStaticNode) (id : String) :
    Option PlanStaticNode := Id.run do
  let mut found : Option PlanStaticNode := none
  for item in layout do
    if found.isNone && item.node.id == id then
      found := some item
  return found

private def canvasSize (layout : Array PlanStaticNode) : Nat × Nat :=
  layout.foldl
    (fun (dims : Nat × Nat) item =>
      let width := item.x + item.width / 2 + 48
      let height := item.y + item.height / 2 + 48
      (Nat.max dims.1 width, Nat.max dims.2 height))
    (120, 120)

private def planNodeTooltip (node : InfoviewPlanNode) : String :=
  let rows := #[
    ("id", node.id),
    ("kind", node.kind),
    ("role", node.roleSummary),
    ("raw", node.rawText),
    ("inputs", String.intercalate ", " node.displayInputs.toList),
    ("outputs", String.intercalate ", " node.displayOutputs.toList),
    ("solves", String.intercalate ", " node.displaySolves.toList)
  ]
  String.intercalate "\n" <|
    rows.toList.filterMap fun (key, value) =>
      let value := cleanText value
      if value = "" then none else some s!"{key}: {value}"

private def tspanHtml (line : String) (dy : Int) : Html :=
  <tspan x={0} dy={dy}>{.text line}</tspan>

private def textLineHtmls (lines : Array String) : Array Html :=
  Id.run do
    let mut out : Array Html := #[]
    let start : Int := -Int.ofNat ((lines.size - 1) * 7)
    for i in [:lines.size] do
      let dy := if i == 0 then start else (15 : Int)
      out := out.push (tspanHtml lines[i]! dy)
    return out

private def planNodeSvg (item : PlanStaticNode) : Html :=
  let halfW : Int := Int.ofNat item.width / 2
  let halfH : Int := Int.ofNat item.height / 2
  let transform := s!"translate({item.x}, {item.y})"
  let textChildren := textLineHtmls item.lines
  (<g transform={transform}>
    <title>{.text (planNodeTooltip item.node)}</title>
    <rect
      x={Lean.toJson (-halfW)}
      y={Lean.toJson (-halfH)}
      width={item.width}
      height={item.height}
      rx={10}
      fill={planFillColor item.node.kind}
      stroke={planStrokeColor item.node.kind}
      strokeWidth={Lean.toJson (1.9 : Float)}
    />
    <text
      textAnchor="middle"
      dominantBaseline="middle"
      fontFamily="var(--vscode-editor-font-family, monospace)"
      fontSize={11}
      fill="var(--vscode-editor-foreground)">
      {...textChildren}
    </text>
  </g>)

structure PlanAnchorPoint where
  x : Int
  y : Int

private def absInt (x : Int) : Int :=
  if x < 0 then -x else x

inductive PlanPortSide where
  | top
  | bottom
  | left
  | right
  deriving Inhabited, BEq, DecidableEq

private def preferredPorts (source target : PlanStaticNode) : PlanPortSide × PlanPortSide :=
  let dx := Int.ofNat target.x - Int.ofNat source.x
  let dy := Int.ofNat target.y - Int.ofNat source.y
  if source.rank = target.rank then
    if dx >= 0 then (.right, .left) else (.left, .right)
  else if dy >= 0 then
    if dx > 180 then (.right, .left)
    else if dx < -180 then (.left, .right)
    else (.bottom, .top)
  else
    if dx > 180 then (.right, .left)
    else if dx < -180 then (.left, .right)
    else (.top, .bottom)

private def anchorPoint (item : PlanStaticNode) (side : PlanPortSide) : PlanAnchorPoint :=
  let x := Int.ofNat item.x
  let y := Int.ofNat item.y
  let halfW := Int.ofNat item.width / 2
  let halfH := Int.ofNat item.height / 2
  match side with
  | .top => { x := x, y := y - halfH }
  | .bottom => { x := x, y := y + halfH }
  | .left => { x := x - halfW, y := y }
  | .right => { x := x + halfW, y := y }

private def markerIdForColor (scope : String) (color : String) : String :=
  s!"{scope}-arrow-{safeToken color}"

private def markerDefSvg (markerId color : String) : Html :=
  <marker
    id={markerId}
    viewBox="0 0 10 10"
    refX={8}
    refY={5}
    markerWidth={6}
    markerHeight={6}
    orient="auto-start-reverse">
    <path
      d="M 0 0 L 10 5 L 0 10 z"
      fill={color}
      opacity={Lean.toJson (0.88 : Float)}
    />
  </marker>

private def planMarkerSvg (scope : String) : Html :=
  <defs>
    {markerDefSvg (markerIdForColor scope "#2563eb") "#2563eb"}
    {markerDefSvg (markerIdForColor scope "#0f766e") "#0f766e"}
    {markerDefSvg (markerIdForColor scope "#d97706") "#d97706"}
    {markerDefSvg (markerIdForColor scope "#7c3aed") "#7c3aed"}
    {markerDefSvg (markerIdForColor scope "#16a34a") "#16a34a"}
    {markerDefSvg (markerIdForColor scope "#15803d") "#15803d"}
    {markerDefSvg (markerIdForColor scope "#64748b") "#64748b"}
  </defs>

private def planEdgeSvg (scope : String) (layout : Array PlanStaticNode)
    (edge : InfoviewPlanEdge) : Option Html :=
  match findPlanStaticNode? layout edge.fromId, findPlanStaticNode? layout edge.toId with
  | some source, some target =>
      let (sourceSide, targetSide) := preferredPorts source target
      let start := anchorPoint source sourceSide
      let finish := anchorPoint target targetSide
      let dx := finish.x - start.x
      let dy := finish.y - start.y
      let d :=
        match sourceSide, targetSide with
        | .left, .right | .right, .left =>
            let bend := max 36 (absInt dx / 2)
            let c1x := if sourceSide = .right then start.x + bend else start.x - bend
            let c2x := if targetSide = .left then finish.x - bend else finish.x + bend
            s!"M {start.x} {start.y} C {c1x} {start.y}, {c2x} {finish.y}, {finish.x} {finish.y}"
        | _, _ =>
            let bend := max 38 (absInt dy / 2)
            let c1y := if sourceSide = .bottom then start.y + bend else start.y - bend
            let c2y := if targetSide = .top then finish.y - bend else finish.y + bend
            s!"M {start.x} {start.y} C {start.x} {c1y}, {finish.x} {c2y}, {finish.x} {finish.y}"
      let stroke := planStrokeColor target.node.kind
      some <|
        (<path
          d={d}
          fill="none"
          stroke={stroke}
          strokeWidth={Lean.toJson (1.8 : Float)}
          opacity={Lean.toJson (0.82 : Float)}
          markerEnd={s!"url(#{markerIdForColor scope stroke})"}
        />)
  | _, _ => none

private def planZoomCss (scope : String) (canvasW canvasH : Nat) : String :=
  let options : Array Nat := #[50, 75, 100, 125, 150]
  let base :=
    String.intercalate "\n" <|
      [
        "." ++ scope ++ "-zoom-input { display:none; }",
        "." ++ scope ++ "-zoom-label { display:inline-block; margin:0 6px 8px 0; padding:2px 8px; border:1px solid var(--vscode-editorWidget-border, #555); border-radius:999px; cursor:pointer; font-size:12px; user-select:none; }",
        "." ++ scope ++ "-viewport { overflow:auto; max-height:560px; border:1px solid var(--vscode-editorWidget-border, #555); background:var(--vscode-editor-background); padding:8px; }",
        "." ++ scope ++ "-canvas { display:block; width:" ++ toString canvasW ++ "px; height:" ++ toString canvasH ++ "px; }"
      ]
  let rules :=
    options.toList.map fun scale =>
      let id := s!"{scope}-zoom-{scale}"
      let scaledW := Nat.max 180 (canvasW * scale / 100)
      let scaledH := Nat.max 120 (canvasH * scale / 100)
      "#" ++ id ++ ":checked + label { background:rgba(59, 130, 246, 0.18); border-color:#3b82f6; }\n" ++
      "#" ++ id ++ ":checked ~ ." ++ scope ++ "-viewport ." ++ scope ++ "-canvas { width:" ++
      toString scaledW ++ "px; height:" ++ toString scaledH ++ "px; }"
  String.intercalate "\n" (base :: rules)

private def planGraphHtml (lb : InfoviewLayeredBlueprint) : Html :=
  let edges := lb.planEdges.filter visiblePlanEdge
  let layout := planStaticLayout lb.planNodes edges
  let (canvasW, canvasH) := canvasSize layout
  let scope := s!"proofstruct-layered-plan-{safeToken lb.theoremName}"
  let edgeHtmls := Id.run do
    let mut out : Array Html := #[]
    for edge in edges do
      match planEdgeSvg scope layout edge with
      | some html => out := out.push html
      | none => pure ()
    return out
  let nodeHtmls := layout.map planNodeSvg
  let viewBox := s!"0 0 {canvasW} {canvasH}"
  let css := planZoomCss scope canvasW canvasH
  let zoomOptions : Array (Nat × String) := #[(50, "50%"), (75, "75%"), (100, "100%"), (125, "125%"), (150, "150%")]
  let zoomInputs := Id.run do
    let mut out : Array Html := #[]
    for i in [:zoomOptions.size] do
      let (scale, label) := zoomOptions[i]!
      let id := s!"{scope}-zoom-{scale}"
      if i = 2 then
        out := out.push (<input id={id} className={s!"{scope}-zoom-input"} type="radio" name={s!"{scope}-zoom"} defaultChecked={true} />)
      else
        out := out.push (<input id={id} className={s!"{scope}-zoom-input"} type="radio" name={s!"{scope}-zoom"} />)
      out := out.push (<label htmlFor={id} className={s!"{scope}-zoom-label"}>{.text label}</label>)
    return out
  (<div>
    <style>{.text css}</style>
    <div style={json% { margin: "0 0 8px 0", opacity: 0.72, fontSize: "12px" }}>
      {.text "Plan edges are intentionally unlabeled in infoview. Use node details below for text."}
    </div>
    {...zoomInputs}
    <div className={s!"{scope}-viewport"}>
      <svg
        xmlns="http://www.w3.org/2000/svg"
        viewBox={viewBox}
        className={s!"{scope}-canvas"}>
        {planMarkerSvg scope}
        <rect
          x={0}
          y={0}
          width={canvasW}
          height={canvasH}
          fill="var(--vscode-editor-background)"
        />
        <g>{...edgeHtmls}</g>
        <g>{...nodeHtmls}</g>
      </svg>
    </div>
  </div>)

private def displayArray (items : Array String) : Array String :=
  items.filterMap fun item =>
    let item := item.trimAscii.toString
    if item = "" then none else some item

private def arrayBlock (title : String) (items : Array String) : Html :=
  let items := displayArray items
  if items.isEmpty then
    <div style={json% { marginBottom: "6px", opacity: 0.62 }}>
      {.text s!"{title}: none"}
    </div>
  else
    let listItems := items.map (fun item => (<li>{.text item}</li>))
    (<div style={json% { marginBottom: "8px" }}>
      <div style={json% { fontWeight: "600", marginBottom: "3px" }}>{.text title}</div>
      <ul style={json% { marginTop: "0", paddingLeft: "18px" }}>
        {...listItems}
      </ul>
    </div>)

private def preBlock (title text : String) : Html :=
  let text := text.trimAscii.toString
  if text = "" then
    <div style={json% { marginBottom: "6px", opacity: 0.62 }}>
      {.text s!"{title}: none"}
    </div>
  else
    <div style={json% { marginBottom: "10px" }}>
      <div style={json% { fontWeight: "600", marginBottom: "3px" }}>{.text title}</div>
      <pre style={json% {
        whiteSpace: "pre-wrap",
        overflow: "auto",
        padding: "8px",
        border: "1px solid var(--vscode-editorWidget-border, #555)",
        borderRadius: "6px",
        background: "rgba(127, 127, 127, 0.08)"
      }}>{.text text}</pre>
    </div>

private def joinedPreBlock (title : String) (items : Array String) : Html :=
  let items := displayArray items
  preBlock title (String.intercalate "\n\n---\n\n" items.toList)

private def planNodeSummary (node : InfoviewPlanNode) : String :=
  let source := planNodeSourceText node
  let label := if node.label != "" then node.label else node.id
  if source = "" then label else s!"{label} ({source})"

private def planNodeDetailsHtml (lb : InfoviewLayeredBlueprint) (node : InfoviewPlanNode) : Html :=
  let subBp := lb.evidenceBlueprintForPlan node
  let evidenceHtml :=
    if subBp.nodes.isEmpty then
      <div style={json% { marginTop: "8px", opacity: 0.66 }}>
        {.text "No visible evidence nodes for this Plan Node."}
      </div>
    else
      blueprintGraphHtml subBp
  (<details style={json% {
      margin: "10px 0",
      padding: "8px",
      border: "1px solid var(--vscode-editorWidget-border, #555)",
      borderRadius: "8px"
    }}>
    <summary className="pointer">
      {.text (planNodeSummary node)}
    </summary>
    <div style={json% { marginTop: "8px" }}>
      <div style={json% { opacity: 0.78, marginBottom: "8px" }}>
        {.text s!"kind: {node.kind}"}
      </div>
      {preBlock "Role" node.roleSummary}
      {preBlock "Proof block" node.rawText}
      {arrayBlock "Inputs" node.displayInputs}
      {arrayBlock "Outputs" node.displayOutputs}
      {arrayBlock "Solves" node.displaySolves}
      {arrayBlock "Opens subgoals" node.displayOpensSubgoals}
      {arrayBlock "Core globals" node.displayUsedGlobals}
      {joinedPreBlock "Goals before" node.goalsBefore}
      {joinedPreBlock "Goals after" node.goalsAfter}
      <div style={json% { marginTop: "12px", fontWeight: "600" }}>
        {.text "Selected Evidence"}
      </div>
      {evidenceHtml}
    </div>
  </details>)

private def planNodeListHtml (lb : InfoviewLayeredBlueprint) : Html :=
  let entries := lb.planNodes.map (planNodeDetailsHtml lb)
  (<div>
    <h3 style={json% { margin: "14px 0 8px 0" }}>{.text "Plan Nodes"}</h3>
    {...entries}
  </div>)

private def fullEvidenceHtml (lb : InfoviewLayeredBlueprint) : Html :=
  let bp := lb.fullEvidenceBlueprint "full-evidence"
  (<details style={json% { marginTop: "14px" }}>
    <summary className="pointer">{.text "Full Evidence Graph"}</summary>
    <div style={json% { marginTop: "8px" }}>
      {blueprintGraphHtml bp}
    </div>
  </details>)

def layeredBlueprintHtml (dataSource : String) (lb : InfoviewLayeredBlueprint) : Html :=
  let subtitle :=
    if lb.theoremType = "" then lb.theoremName else s!"{lb.theoremName}: {truncateText lb.theoremType 110}"
  (<details «open»={true}>
    <summary className="mv2 pointer">
      {.text s!"Layered proof blueprint: {lb.theoremName}"}
    </summary>
    <div className="ml1">
      <div style={json% { margin: "6px 0 8px 0", opacity: 0.84 }}>
        {.text subtitle}
      </div>
      <div style={json% { marginBottom: "10px", opacity: 0.66, fontSize: "12px" }}>
        {.text s!"data source: {dataSource}"}
      </div>
      <h3 style={json% { margin: "12px 0 8px 0" }}>{.text "Proof Plan Graph"}</h3>
      {planGraphHtml lb}
      {planNodeListHtml lb}
      {fullEvidenceHtml lb}
    </div>
  </details>)

end ProofStruct
