import ProofWidgets.Component.HtmlDisplay
import ProofStruct.Extract.Graph
import ProofStruct.Widget.Types

namespace ProofStruct

open Lean
open ProofWidgets
open scoped ProofWidgets.Jsx

private def truncateText (s : String) (maxChars : Nat := 44) : String :=
  if s.length <= maxChars then s else (s.take (maxChars - 3)).copy ++ "..."

private def cleanText (s : String) : String :=
  let flat1 := String.intercalate " " (s.splitOn "\n")
  let flat2 := String.intercalate " " (flat1.splitOn "\r")
  let flat3 := String.intercalate " " (flat2.splitOn "\t")
  let words :=
    flat3.splitOn " " |>.filterMap fun word =>
      let word := word.trimAscii.toString
      if word = "" then none else some word
  String.intercalate " " words

private def nonemptyLines (lines : Array String) : Array String :=
  lines.foldl
    (fun acc line =>
      let line := cleanText line
      if line = "" then acc else acc.push line)
    #[]

private def theoremText (node : BlueprintNode) (bp : Blueprint) : String :=
  let text :=
    if node.kind = "theorem_goal" && bp.theoremType != "" then
      bp.theoremType
    else if node.label != "" then
      node.label
    else if node.typeText != "" then
      node.typeText
    else if node.nodeName != "" && node.typeText != "" then
      s!"{node.nodeName} : {node.typeText}"
    else if node.nodeName != "" then
      node.nodeName
    else
      node.rawText
  cleanText text

private def compactActionText (node : BlueprintNode) : String :=
  let text :=
    if node.label != "" && node.label != node.nodeName then
      node.label
    else if node.label == node.nodeName then
      ""
    else
      node.rawText
  truncateText (cleanText text) 36

private def ordinaryNodeText (node : BlueprintNode) : String :=
  let text :=
    if node.label != "" then
      node.label
    else if node.nodeName != "" && node.typeText != "" then
      s!"{node.nodeName} : {node.typeText}"
    else if node.nodeName != "" then
      node.nodeName
    else if node.typeText != "" then
      node.typeText
    else if node.rawText != "" then
      node.rawText
    else
      node.kind
  cleanText text

private def splitOnFirstColon? (text : String) : Option (String × String) :=
  match text.splitOn ":" with
  | [] => none
  | [_] => none
  | left :: rest =>
      let left := cleanText left
      let right := cleanText (String.intercalate ":" rest)
      if left = "" || right = "" then none else some (left, right)

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
    match splitOnFirstColon? text with
    | some (left, right) =>
        #[truncateText s!"{left} :" maxChars, truncateText right maxChars]
    | none =>
        match splitWordsNearMiddle? text with
        | some (left, right) =>
            nonemptyLines #[truncateText left maxChars, truncateText right maxChars]
        | none =>
            #[truncateText text maxChars]

private def nodeLines (bp : Blueprint) (node : BlueprintNode) : Array String :=
  nonemptyLines <|
    match node.kind with
    | "theorem_goal" =>
        #["goal"] ++ wrapTextLines (theoremText node bp) 38
    | "subgoal" =>
        #["subgoal"] ++ wrapTextLines (theoremText node bp) 34
    | "action" =>
        let title :=
          if node.nodeName != "" then node.nodeName else "action"
        let base := #[title, compactActionText node]
        if node.sourceLine == 0 then base else base.push s!"line {node.sourceLine}"
    | _ =>
        let lines := wrapTextLines (ordinaryNodeText node) 32
        if lines.isEmpty then #[node.kind] else lines

private def longestLineLength (lines : Array String) : Nat :=
  lines.foldl (fun acc line => Nat.max acc line.length) 0

private def nodeWidth (node : BlueprintNode) (lines : Array String) : Nat :=
  let longest := longestLineLength lines
  let base :=
    if node.kind = "theorem_goal" || node.kind = "subgoal" then
      164
    else if node.kind = "action" then
      136
    else
      84
  let grown := base + longest * 7
  let cap :=
    if node.kind = "theorem_goal" || node.kind = "subgoal" then
      320
    else if node.kind = "action" then
      248
    else
      228
  Nat.min cap (Nat.max base grown)

private def nodeHeight (node : BlueprintNode) (lines : Array String) : Nat :=
  let base :=
    if node.kind = "theorem_goal" || node.kind = "subgoal" then
      34
    else if node.kind = "action" then
      32
    else
      24
  Nat.min 92 (Nat.max 36 (base + lines.size * 15))

private def nodeStrokeColor (node : BlueprintNode) : String :=
  match node.kind with
  | "theorem_goal" => "#2f855a"
  | "subgoal" => "#7c3aed"
  | "action" => "#c27803"
  | "hypothesis" => "#2b6cb0"
  | "intermediate" => "#2b6cb0"
  | "constructed_object" => "#2b6cb0"
  | _ => "#64748b"

private def nodeFillColor (node : BlueprintNode) : String :=
  match node.kind with
  | "action" => "rgba(194, 120, 3, 0.10)"
  | "theorem_goal" => "rgba(47, 133, 90, 0.10)"
  | "subgoal" => "rgba(124, 58, 237, 0.10)"
  | _ => "rgba(43, 108, 176, 0.08)"

private def nodeDashArray? (node : BlueprintNode) : Option String :=
  if node.kind = "subgoal" then some "6,4" else none

private def keepEdge (viewMode : BlueprintViewMode) (edge : BlueprintEdge) : Bool :=
  match viewMode with
  | .dependency => edge.kind != "goal_to_action" && edge.kind != "context_to_goal"
  | .process => true

private def edgeColor (edge : BlueprintEdge) : String :=
  match edge.kind with
  | "input_to_action" => "#2b6cb0"
  | "action_to_output" => "#c27803"
  | "action_solves_goal" => "#2f855a"
  | "action_to_subgoal" => "#7c3aed"
  | "subgoal_to_join" => "#7c3aed"
  | "goal_to_action" => "#6b7280"
  | "context_to_goal" => "#94a3b8"
  | _ => "#64748b"

private def edgeDashArray? (edge : BlueprintEdge) : Option String :=
  match edge.kind with
  | "subgoal_to_join" => some "6,4"
  | "goal_to_action" => some "4,4"
  | "context_to_goal" => some "2,4"
  | _ => none

private def safeToken (s : String) : String :=
  let token := s.foldl (fun acc c => if c.isAlphanum then acc.push c else acc.push '-') ""
  if token = "" then "bp" else token

private def findNodeIndex? (nodes : Array BlueprintNode) (id : String) : Option Nat := Id.run do
  let mut found : Option Nat := none
  for i in [:nodes.size] do
    if found.isNone && nodes[i]!.id == id then
      found := some i
  return found

private def computeRanks (nodes : Array BlueprintNode) (edges : Array BlueprintEdge) : Array Nat :=
  Id.run do
    let mut ranks := Array.replicate nodes.size 0
    for _ in [:nodes.size + edges.size + 1] do
      for edge in edges do
        match findNodeIndex? nodes edge.fromId, findNodeIndex? nodes edge.toId with
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

structure StaticNode where
  node : BlueprintNode
  lines : Array String
  width : Nat
  height : Nat
  rank : Nat
  slot : Nat
  x : Nat
  y : Nat

private def staticLayout (bp : Blueprint) (edges : Array BlueprintEdge) : Array StaticNode :=
  Id.run do
    let ranks := computeRanks bp.nodes edges
    let counts := layerCounts ranks
    let maxLayer := Nat.max 1 (maxArray counts)
    let mut used := Array.replicate counts.size 0
    let cellW := 258
    let rowH := 132
    let padX := 42
    let padY := 42
    let mut out : Array StaticNode := #[]
    for i in [:bp.nodes.size] do
      let node := bp.nodes[i]!
      let lines := nodeLines bp node
      let rank := ranks[i]!
      let slot := used[rank]!
      used := used.set! rank (slot + 1)
      let width := nodeWidth node lines
      let height := nodeHeight node lines
      let layerWidth := counts[rank]!
      let layerOffset := (maxLayer - layerWidth) * cellW / 2
      let x := padX + layerOffset + slot * cellW + cellW / 2
      let y := padY + rank * rowH + rowH / 2
      out := out.push { node, lines, width, height, rank, slot, x, y }
    return out

private def findStaticNode? (layout : Array StaticNode) (id : String) : Option StaticNode := Id.run do
  let mut found : Option StaticNode := none
  for item in layout do
    if found.isNone && item.node.id == id then
      found := some item
  return found

private def canvasSize (layout : Array StaticNode) : Nat × Nat :=
  layout.foldl
    (fun (dims : Nat × Nat) item =>
      let width := item.x + item.width / 2 + 42
      let height := item.y + item.height / 2 + 42
      (Nat.max dims.1 width, Nat.max dims.2 height))
    (84, 84)

private def nodeTooltip (bp : Blueprint) (node : BlueprintNode) : String :=
  let rows := #[
    ("theorem", bp.theoremName),
    ("kind", node.kind),
    ("id", node.id),
    ("name", node.nodeName),
    ("label", node.label),
    ("type", node.typeText),
    ("raw", node.rawText),
    ("source line", if node.sourceLine == 0 then "" else toString node.sourceLine),
    ("uses local", String.intercalate ", " node.usesLocal.toList),
    ("uses global", String.intercalate ", " node.usesGlobal.toList)
  ]
  String.intercalate "\n" <|
    rows.toList.filterMap fun (key, value) =>
      let value := cleanText value
      if value = "" then none else some s!"{key}: {value}"

private def edgeTooltip (edge : BlueprintEdge) : String :=
  let rows := #[
    ("kind", edge.kind),
    ("from", edge.fromId),
    ("to", edge.toId),
    ("label", edge.label)
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

private def nodeShapeAttrs (item : StaticNode) : Array (String × Json) :=
  match nodeDashArray? item.node with
  | some dash => #[("strokeDasharray", Lean.toJson dash)]
  | none => #[]

private def nodeSvg (bp : Blueprint) (item : StaticNode) : Html :=
  let w := item.width
  let h := item.height
  let halfW : Int := Int.ofNat w / 2
  let halfH : Int := Int.ofNat h / 2
  let stroke := nodeStrokeColor item.node
  let fill := nodeFillColor item.node
  let extraAttrs := nodeShapeAttrs item
  let textChildren := textLineHtmls item.lines
  let transform := s!"translate({item.x}, {item.y})"
  let shape :=
    if item.node.kind = "theorem_goal" then
      (<ellipse
        cx={0}
        cy={0}
        rx={halfW}
        ry={halfH}
        fill={fill}
        stroke={stroke}
        strokeWidth={Lean.toJson (1.8 : Float)}
        {...extraAttrs}
      />)
    else
      (<rect
        x={Lean.toJson (-halfW)}
        y={Lean.toJson (-halfH)}
        width={w}
        height={h}
        rx={6}
        fill={fill}
        stroke={stroke}
        strokeWidth={Lean.toJson (1.8 : Float)}
        {...extraAttrs}
      />)
  (<g transform={transform}>
    <title>{.text (nodeTooltip bp item.node)}</title>
    {shape}
    <text
      textAnchor="middle"
      dominantBaseline="middle"
      fontFamily="var(--vscode-editor-font-family, monospace)"
      fontSize={11}
      fill="var(--vscode-editor-foreground)">
      {...textChildren}
    </text>
  </g>)

inductive PortSide where
  | top
  | bottom
  | left
  | right
  deriving Inhabited, BEq, DecidableEq

structure AnchorPoint where
  x : Int
  y : Int

private def absInt (x : Int) : Int :=
  if x < 0 then -x else x

private def clampInt (x lo hi : Int) : Int :=
  if x < lo then lo else if x > hi then hi else x

private def outgoingEdgeStats (edges : Array BlueprintEdge) (edgeIdx : Nat) (fromId : String) : Nat × Nat :=
  Id.run do
    let mut index := 0
    let mut total := 0
    for i in [:edges.size] do
      let edge := edges[i]!
      if edge.fromId = fromId then
        if i < edgeIdx then
          index := index + 1
        total := total + 1
    return (index, total)

private def incomingEdgeStats (edges : Array BlueprintEdge) (edgeIdx : Nat) (toId : String) : Nat × Nat :=
  Id.run do
    let mut index := 0
    let mut total := 0
    for i in [:edges.size] do
      let edge := edges[i]!
      if edge.toId = toId then
        if i < edgeIdx then
          index := index + 1
        total := total + 1
    return (index, total)

private def spreadOffset (count index limit step : Nat) : Int :=
  if count <= 1 then
    0
  else
    let wanted := step * (count - 1)
    let span := Int.ofNat (Nat.min limit wanted)
    let denom := Int.ofNat (count - 1)
    let unit :=
      if denom = 0 then
        0
      else
        span / denom
    Int.ofNat index * unit - span / 2

private def preferredPorts (source target : StaticNode) : PortSide × PortSide :=
  let dx := Int.ofNat target.x - Int.ofNat source.x
  let dy := Int.ofNat target.y - Int.ofNat source.y
  if source.rank = target.rank then
    if dx >= 0 then (.right, .left) else (.left, .right)
  else if dy >= 0 then
    if dx > 150 then (.right, .left)
    else if dx < -150 then (.left, .right)
    else (.bottom, .top)
  else
    if dx > 150 then (.right, .left)
    else if dx < -150 then (.left, .right)
    else (.top, .bottom)

private def anchorPoint (item : StaticNode) (side : PortSide) (offset : Int) : AnchorPoint :=
  let x := Int.ofNat item.x
  let y := Int.ofNat item.y
  let halfW := Int.ofNat item.width / 2
  let halfH := Int.ofNat item.height / 2
  let usableX := Int.ofNat (Nat.max 8 (item.width / 2 - 16))
  let usableY := Int.ofNat (Nat.max 6 (item.height / 2 - 12))
  match side with
  | .top =>
      { x := x + clampInt offset (-usableX) usableX, y := y - halfH }
  | .bottom =>
      { x := x + clampInt offset (-usableX) usableX, y := y + halfH }
  | .left =>
      { x := x - halfW, y := y + clampInt offset (-usableY) usableY }
  | .right =>
      { x := x + halfW, y := y + clampInt offset (-usableY) usableY }

private def edgeStrokeColor (target : BlueprintNode) (edge : BlueprintEdge) : String :=
  let targetColor := nodeStrokeColor target
  if targetColor != "" then targetColor else edgeColor edge

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
      opacity={Lean.toJson (0.86 : Float)}
    />
  </marker>

private def markerSvg (scope : String) : Html :=
  <defs>
    {markerDefSvg (markerIdForColor scope "#2b6cb0") "#2b6cb0"}
    {markerDefSvg (markerIdForColor scope "#c27803") "#c27803"}
    {markerDefSvg (markerIdForColor scope "#2f855a") "#2f855a"}
    {markerDefSvg (markerIdForColor scope "#7c3aed") "#7c3aed"}
    {markerDefSvg (markerIdForColor scope "#64748b") "#64748b"}
  </defs>

private def isVerticalSide (side : PortSide) : Bool :=
  match side with
  | .top | .bottom => true
  | .left | .right => false

private def isHorizontalSide (side : PortSide) : Bool :=
  match side with
  | .left | .right => true
  | .top | .bottom => false

private def edgeSvg (scope : String) (layout : Array StaticNode) (edges : Array BlueprintEdge)
    (edgeIdx : Nat) : Option Html :=
  let edge := edges[edgeIdx]!
  match findStaticNode? layout edge.fromId, findStaticNode? layout edge.toId with
  | some source, some target =>
      let (sourceIndex, sourceCount) := outgoingEdgeStats edges edgeIdx edge.fromId
      let (targetIndex, targetCount) := incomingEdgeStats edges edgeIdx edge.toId
      let (sourceSide, targetSide) := preferredPorts source target
      let sourceOffset :=
        if isVerticalSide sourceSide then
          spreadOffset sourceCount sourceIndex (Nat.max 18 (source.width / 2 - 18)) 18
        else
          spreadOffset sourceCount sourceIndex (Nat.max 12 (source.height / 2 - 10)) 12
      let targetOffset :=
        if isVerticalSide targetSide then
          spreadOffset targetCount targetIndex (Nat.max 18 (target.width / 2 - 18)) 18
        else
          spreadOffset targetCount targetIndex (Nat.max 12 (target.height / 2 - 10)) 12
      let start := anchorPoint source sourceSide sourceOffset
      let finish := anchorPoint target targetSide targetOffset
      let dx := finish.x - start.x
      let dy := finish.y - start.y
      let d :=
        if isHorizontalSide sourceSide && isHorizontalSide targetSide then
          let bend := max 30 (absInt dx / 2)
          let c1x := if sourceSide = .right then start.x + bend else start.x - bend
          let c2x := if targetSide = .left then finish.x - bend else finish.x + bend
          s!"M {start.x} {start.y} C {c1x} {start.y}, {c2x} {finish.y}, {finish.x} {finish.y}"
        else
          let bend := max 30 (absInt dy / 2)
          let c1y := if sourceSide = .bottom then start.y + bend else start.y - bend
          let c2y := if targetSide = .top then finish.y - bend else finish.y + bend
          s!"M {start.x} {start.y} C {start.x} {c1y}, {finish.x} {c2y}, {finish.x} {finish.y}"
      let stroke := edgeStrokeColor target.node edge
      let extraAttrs : Array (String × Json) :=
        match edgeDashArray? edge with
        | some dash => #[("strokeDasharray", Lean.toJson dash)]
        | none => #[]
      some <|
        (<path
          d={d}
          fill="none"
          stroke={stroke}
          strokeWidth={Lean.toJson (1.7 : Float)}
          opacity={Lean.toJson (0.82 : Float)}
          markerEnd={s!"url(#{markerIdForColor scope stroke})"}
          {...extraAttrs}>
          <title>{.text (edgeTooltip edge)}</title>
        </path>)
  | _, _ => none

private def zoomCss (scope : String) (canvasW canvasH : Nat) : String :=
  let options : Array (Nat × String) := #[(50, "50%"), (75, "75%"), (100, "100%"), (125, "125%"), (150, "150%")]
  let base :=
    String.intercalate "\n" <|
      [
        "." ++ scope ++ "-zoom-input { display:none; }",
        "." ++ scope ++ "-zoom-label { display:inline-block; margin:0 6px 8px 0; padding:2px 8px; border:1px solid var(--vscode-editorWidget-border, #555); border-radius:999px; cursor:pointer; font-size:12px; user-select:none; }",
        "." ++ scope ++ "-zoom-help { margin:0 0 8px 0; font-size:12px; opacity:0.72; }",
        "." ++ scope ++ "-viewport { overflow:auto; max-height:620px; border:1px solid var(--vscode-editorWidget-border, #555); background:var(--vscode-editor-background); padding:8px; }",
        "." ++ scope ++ "-canvas { display:block; width:" ++ toString canvasW ++ "px; height:" ++ toString canvasH ++ "px; }"
      ]
  let rules :=
    options.toList.map fun (scale, _) =>
      let id := s!"{scope}-zoom-{scale}"
      let scaledW := Nat.max 180 (canvasW * scale / 100)
      let scaledH := Nat.max 120 (canvasH * scale / 100)
      "#" ++ id ++ ":checked + label { background:rgba(59, 130, 246, 0.18); border-color:#3b82f6; }\n" ++
      "#" ++ id ++ ":checked ~ ." ++ scope ++ "-viewport ." ++ scope ++ "-canvas { width:" ++
      toString scaledW ++ "px; height:" ++ toString scaledH ++ "px; }"
  String.intercalate "\n" (base :: rules)

private def blueprintSvgHtml (bp : Blueprint) (viewMode : BlueprintViewMode) : Html :=
  let edges := bp.edges.filter (keepEdge viewMode)
  let layout := staticLayout bp edges
  let (canvasW, canvasH) := canvasSize layout
  let viewToken :=
    match viewMode with
    | .dependency => "dependency"
    | .process => "process"
  let scope := s!"proofstruct-{safeToken bp.theoremName}-{viewToken}"
  let edgeHtmls := Id.run do
    let mut out : Array Html := #[]
    for i in [:edges.size] do
      match edgeSvg scope layout edges i with
      | some html => out := out.push html
      | none => pure ()
    return out
  let nodeHtmls := layout.map (nodeSvg bp)
  let viewBox := s!"0 0 {canvasW} {canvasH}"
  let css := zoomCss scope canvasW canvasH
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
    <div className={s!"{scope}-zoom-help"}>
      {.text "Zoom:"}
    </div>
    {...zoomInputs}
    <div className={s!"{scope}-viewport"}>
      <svg
        xmlns="http://www.w3.org/2000/svg"
        viewBox={viewBox}
        className={s!"{scope}-canvas"}>
        {markerSvg scope}
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

def blueprintGraphHtml (bp : Blueprint) (viewMode : BlueprintViewMode := .dependency) : Html :=
  let viewName :=
    match viewMode with
    | .dependency => "dependency"
    | .process => "process"
  let subtitle :=
    if bp.theoremType = "" then
      s!"{bp.theoremName} ({viewName} view)"
    else
      s!"{bp.theoremName} ({viewName} view): {truncateText bp.theoremType 96}"
  (<details «open»={true}>
    <summary className="mv2 pointer">
      {.text s!"Proof blueprint: {bp.theoremName}"}
    </summary>
    <div className="ml1">
      <div style={json% { margin: "6px 0 10px 0", opacity: 0.8 }}>
        {.text subtitle}
      </div>
      <div style={json% { marginBottom: "8px", opacity: 0.7, fontSize: "12px" }}>
        {.text "Static layered layout. Use the zoom controls below, and hover a node or edge for full details."}
      </div>
      {blueprintSvgHtml bp viewMode}
    </div>
  </details>)

end ProofStruct
