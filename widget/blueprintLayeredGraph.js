import * as React from 'react'

const e = React.createElement

const PLAN_COLORS = {
  introduce_context: ['rgba(37, 99, 235, 0.10)', '#2563eb'],
  prove_intermediate: ['rgba(37, 99, 235, 0.10)', '#2563eb'],
  construct_object: ['rgba(37, 99, 235, 0.10)', '#2563eb'],
  transform_goal: ['rgba(15, 118, 110, 0.11)', '#0f766e'],
  calculation_chain: ['rgba(15, 118, 110, 0.11)', '#0f766e'],
  automation: ['rgba(217, 119, 6, 0.13)', '#d97706'],
  split_goal: ['rgba(124, 58, 237, 0.12)', '#7c3aed'],
  case_split: ['rgba(124, 58, 237, 0.12)', '#7c3aed'],
  solve_goal: ['rgba(22, 163, 74, 0.11)', '#16a34a'],
  close_goal: ['rgba(21, 128, 61, 0.14)', '#15803d'],
  unknown: ['rgba(100, 116, 139, 0.10)', '#64748b'],
}

const EVIDENCE_COLORS = {
  theorem_goal: ['rgba(47, 133, 90, 0.10)', '#2f855a'],
  subgoal: ['rgba(124, 58, 237, 0.10)', '#7c3aed'],
  action: ['rgba(194, 120, 3, 0.10)', '#c27803'],
  hypothesis: ['rgba(43, 108, 176, 0.08)', '#2b6cb0'],
  intermediate: ['rgba(43, 108, 176, 0.08)', '#2b6cb0'],
  constructed_object: ['rgba(43, 108, 176, 0.08)', '#2b6cb0'],
  unknown: ['rgba(100, 116, 139, 0.08)', '#64748b'],
}

function arr(x) {
  return Array.isArray(x) ? x : []
}

function clean(text) {
  return String(text || '').replace(/\s+/g, ' ').trim()
}

function short(text, limit = 72) {
  const t = clean(text)
  return t.length <= limit ? t : `${t.slice(0, Math.max(1, limit - 3))}...`
}

function safeToken(text) {
  return clean(text).replace(/[^A-Za-z0-9_-]/g, '-') || 'proofstruct'
}

function colorFor(kind, palette) {
  return palette[kind] || palette.unknown
}

function rangeText(sourceRange) {
  const start = sourceRange?.start_line || 0
  const end = sourceRange?.end_line || start
  if (!start) return ''
  return end && end !== start ? `line ${start}-${end}` : `line ${start}`
}

function languageKey(graphKind, nodeId) {
  return `${graphKind}:${nodeId}`
}

function nodeMap(layered, graphKind) {
  const nodes = graphKind === 'plan'
    ? arr(layered?.plan_graph?.nodes)
    : arr(layered?.evidence_graph?.nodes)
  return new Map(nodes.map(node => [node.id, node]))
}

function languageForNode(graphKind, nodeId, globalLanguage, overrides) {
  return overrides?.[languageKey(graphKind, nodeId)] || globalLanguage || 'formal'
}

function mergePlanNodeForLanguage(formalNode, englishNode, language) {
  const hasEnglish = !!englishNode?.english_label
  const merged = {
    ...formalNode,
    _language: language,
    _english_available: hasEnglish,
    _formal_label: formalNode.label || formalNode.id,
    _formal_role_summary: formalNode.role_summary || formalNode.detail_label || '',
    _english_label: englishNode?.english_label || '',
    _english_detail: englishNode?.english_detail || '',
  }
  if (language === 'english' && hasEnglish) {
    merged.label = englishNode.english_label || formalNode.label || formalNode.id
    merged.role_summary = englishNode.english_detail || englishNode.english_label || formalNode.role_summary || ''
    merged.display_inputs = arr(englishNode.english_inputs).length ? englishNode.english_inputs : formalNode.display_inputs
    merged.display_outputs = arr(englishNode.english_outputs).length ? englishNode.english_outputs : formalNode.display_outputs
  }
  return merged
}

function mergeEvidenceNodeForLanguage(formalNode, englishNode, language) {
  const hasEnglish = !!englishNode?.english_label
  const formalLabel = formalNode.display_label || formalNode.label || formalNode.type || formalNode.name || formalNode.id
  const merged = {
    ...formalNode,
    _language: language,
    _english_available: hasEnglish,
    _formal_label: formalLabel,
    _english_label: englishNode?.english_label || '',
    _english_detail: englishNode?.english_detail || '',
  }
  if (language === 'english' && hasEnglish) {
    const label = englishNode.english_label || formalLabel
    merged.display_label = label
    merged.label = label
    if (formalNode.kind !== 'action') {
      merged.display_type = ''
    }
  }
  return merged
}

function displayLayeredForLanguage(layered, englishLayered, globalLanguage, overrides) {
  if (!englishLayered) return layered
  const englishPlan = nodeMap(englishLayered, 'plan')
  const englishEvidence = nodeMap(englishLayered, 'evidence')
  const planNodes = arr(layered?.plan_graph?.nodes).map(node => {
    const language = languageForNode('plan', node.id, globalLanguage, overrides)
    return mergePlanNodeForLanguage(node, englishPlan.get(node.id), language)
  })
  const evidenceNodes = arr(layered?.evidence_graph?.nodes).map(node => {
    const language = languageForNode('evidence', node.id, globalLanguage, overrides)
    return mergeEvidenceNodeForLanguage(node, englishEvidence.get(node.id), language)
  })
  return {
    ...layered,
    plan_graph: { ...(layered.plan_graph || {}), nodes: planNodes },
    evidence_graph: { ...(layered.evidence_graph || {}), nodes: evidenceNodes },
  }
}

function planNodeLines(node) {
  const tactics = arr(node.tactics).join('/') || node.main_tactic || ''
  const source = rangeText(node.source_range)
  const sourceLine = source && tactics ? `${source} | ${tactics}` : source || tactics
  return [
    node.label || node.id,
    short(node.role_summary || node.detail_label || node.kind, 74),
    node.branch_label ? `branch ${node.branch_label}` : '',
    sourceLine,
  ].filter(Boolean)
}

function evidenceNodeLines(node) {
  const label = node.display_label || node.label || node.type || node.name || node.id
  if (node.kind === 'action') {
    return [node.name || 'action', short(label, 54)].filter(Boolean)
  }
  if (node.kind === 'theorem_goal') {
    return ['goal', short(label, 62)]
  }
  if (node.kind === 'subgoal') {
    return ['subgoal', short(label, 58)]
  }
  return [short(label, 62)]
}

function nodeSize(lines, kind, graphKind) {
  const longest = lines.reduce((m, line) => Math.max(m, clean(line).length), 0)
  const isEvidence = graphKind === 'evidence'
  const base = kind === 'action' ? 134 : isEvidence ? 112 : 188
  const cap = kind === 'action' ? 248 : isEvidence ? 260 : 350
  const width = Math.min(cap, Math.max(base, 92 + longest * 7))
  const height = Math.min(118, Math.max(isEvidence ? 44 : 62, 32 + lines.length * 16))
  return { width, height }
}

function visiblePlanEdges(layered) {
  return arr(layered?.plan_graph?.edges).filter(edge =>
    (edge.kind || 'flow') === 'flow' && edge.visible_by_default !== false
  )
}

function edgeId(edge, idx) {
  return edge.id || `e${idx + 1}`
}

function isDependencyEvidenceEdge(edge) {
  return edge.kind !== 'goal_to_action' && edge.kind !== 'context_to_goal'
}

function selectedEvidence(layered, planNode) {
  const wantedNodes = new Set(arr(planNode?.evidence_node_ids))
  const wantedEdges = new Set(arr(planNode?.evidence_edge_ids))
  const nodes = arr(layered?.evidence_graph?.nodes).filter(node =>
    wantedNodes.has(node.id) && node.hidden_by_default !== true
  )
  const visibleIds = new Set(nodes.map(node => node.id))
  const edges = arr(layered?.evidence_graph?.edges).filter((edge, idx) =>
    wantedEdges.has(edgeId(edge, idx)) &&
    isDependencyEvidenceEdge(edge) &&
    visibleIds.has(edge.from) &&
    visibleIds.has(edge.to)
  )
  return { nodes, edges }
}

function fullEvidence(layered) {
  const nodes = arr(layered?.evidence_graph?.nodes).filter(node => node.hidden_by_default !== true)
  const visibleIds = new Set(nodes.map(node => node.id))
  const edges = arr(layered?.evidence_graph?.edges).filter(edge =>
    isDependencyEvidenceEdge(edge) && visibleIds.has(edge.from) && visibleIds.has(edge.to)
  )
  return { nodes, edges }
}

function dependencyRanks(nodes, edges) {
  const ids = new Map(nodes.map((node, idx) => [node.id, idx]))
  const adjacency = nodes.map(() => [])
  for (const edge of edges) {
    const from = ids.get(edge.from)
    const to = ids.get(edge.to)
    if (from == null || to == null || from === to) continue
    adjacency[from].push(to)
  }

  // Collapse cycles first; longest-path relaxation is only valid on the resulting DAG.
  const indices = new Array(nodes.length).fill(-1)
  const lowLinks = new Array(nodes.length).fill(-1)
  const onStack = new Array(nodes.length).fill(false)
  const stack = []
  const components = []
  let nextIndex = 0

  function visit(nodeIndex) {
    indices[nodeIndex] = nextIndex
    lowLinks[nodeIndex] = nextIndex
    nextIndex += 1
    stack.push(nodeIndex)
    onStack[nodeIndex] = true

    for (const target of adjacency[nodeIndex]) {
      if (indices[target] < 0) {
        visit(target)
        lowLinks[nodeIndex] = Math.min(lowLinks[nodeIndex], lowLinks[target])
      } else if (onStack[target]) {
        lowLinks[nodeIndex] = Math.min(lowLinks[nodeIndex], indices[target])
      }
    }

    if (lowLinks[nodeIndex] !== indices[nodeIndex]) return
    const component = []
    while (stack.length > 0) {
      const member = stack.pop()
      onStack[member] = false
      component.push(member)
      if (member === nodeIndex) break
    }
    components.push(component)
  }

  for (let idx = 0; idx < nodes.length; idx += 1) {
    if (indices[idx] < 0) visit(idx)
  }

  const componentOf = new Array(nodes.length).fill(0)
  components.forEach((component, componentIndex) => {
    component.forEach(nodeIndex => { componentOf[nodeIndex] = componentIndex })
  })
  const successors = components.map(() => new Set())
  const indegrees = new Array(components.length).fill(0)
  for (let from = 0; from < adjacency.length; from += 1) {
    for (const to of adjacency[from]) {
      const sourceComponent = componentOf[from]
      const targetComponent = componentOf[to]
      if (sourceComponent === targetComponent || successors[sourceComponent].has(targetComponent)) continue
      successors[sourceComponent].add(targetComponent)
      indegrees[targetComponent] += 1
    }
  }

  const componentRanks = new Array(components.length).fill(0)
  const queue = []
  indegrees.forEach((indegree, componentIndex) => {
    if (indegree === 0) queue.push(componentIndex)
  })
  for (let cursor = 0; cursor < queue.length; cursor += 1) {
    const component = queue[cursor]
    for (const target of successors[component]) {
      componentRanks[target] = Math.max(componentRanks[target], componentRanks[component] + 1)
      indegrees[target] -= 1
      if (indegrees[target] === 0) queue.push(target)
    }
  }
  return componentOf.map(component => componentRanks[component])
}

function computeLayout(nodes, edges, graphKind) {
  const ranks = dependencyRanks(nodes, edges)
  const counts = []
  ranks.forEach(rank => { counts[rank] = (counts[rank] || 0) + 1 })
  const maxLayer = Math.max(1, ...counts.map(x => x || 0))
  const used = new Array(counts.length).fill(0)
  const cellW = graphKind === 'plan' ? 330 : 270
  const rowH = graphKind === 'plan' ? 150 : 130
  const padX = 48
  const padY = 44
  const maxColumns = graphKind === 'plan' ? maxLayer : Math.min(4, maxLayer)
  const rankStartRows = new Map()
  let nextRow = 0
  counts.forEach((count, rank) => {
    if (!count) return
    rankStartRows.set(rank, nextRow)
    nextRow += Math.ceil(count / maxColumns)
  })

  const items = nodes.map((node, idx) => {
    const lines = graphKind === 'plan' ? planNodeLines(node) : evidenceNodeLines(node)
    const { width, height } = nodeSize(lines, node.kind, graphKind)
    const rank = ranks[idx]
    const slot = used[rank] || 0
    used[rank] = slot + 1
    const layerWidth = counts[rank] || 1
    const row = Math.floor(slot / maxColumns)
    const rowSlot = slot % maxColumns
    const rowWidth = Math.min(maxColumns, layerWidth - row * maxColumns)
    const layerOffset = ((maxColumns - rowWidth) * cellW) / 2
    const layoutRow = (rankStartRows.get(rank) || 0) + row
    return {
      node, lines, width, height, rank, slot, layoutRow,
      x: padX + layerOffset + rowSlot * cellW + cellW / 2,
      y: padY + layoutRow * rowH + rowH / 2,
    }
  })

  const width = Math.max(240, ...items.map(item => item.x + item.width / 2 + 48))
  const height = Math.max(160, ...items.map(item => item.y + item.height / 2 + 48))
  const byId = new Map(items.map(item => [item.node.id, item]))
  return { items, byId, width, height }
}

function anchor(item, side) {
  if (side === 'top') return { x: item.x, y: item.y - item.height / 2 }
  if (side === 'bottom') return { x: item.x, y: item.y + item.height / 2 }
  if (side === 'left') return { x: item.x - item.width / 2, y: item.y }
  return { x: item.x + item.width / 2, y: item.y }
}

function ports(source, target) {
  const dx = target.x - source.x
  const dy = target.y - source.y
  const sameVisualRow = Math.abs(dy) < Math.max(48, (source.height + target.height) / 3)
  if (sameVisualRow) return dx >= 0 ? ['right', 'left'] : ['left', 'right']
  if (dy >= 0) {
    if (dx > 180) return ['right', 'left']
    if (dx < -180) return ['left', 'right']
    return ['bottom', 'top']
  }
  if (dx > 180) return ['right', 'left']
  if (dx < -180) return ['left', 'right']
  return ['top', 'bottom']
}

function edgePath(source, target) {
  const [sourceSide, targetSide] = ports(source, target)
  const start = anchor(source, sourceSide)
  const finish = anchor(target, targetSide)
  const dx = finish.x - start.x
  const dy = finish.y - start.y
  if ((sourceSide === 'left' || sourceSide === 'right') &&
      (targetSide === 'left' || targetSide === 'right')) {
    const bend = Math.max(36, Math.abs(dx) / 2)
    const c1x = sourceSide === 'right' ? start.x + bend : start.x - bend
    const c2x = targetSide === 'left' ? finish.x - bend : finish.x + bend
    return `M ${start.x} ${start.y} C ${c1x} ${start.y}, ${c2x} ${finish.y}, ${finish.x} ${finish.y}`
  }
  const bend = Math.max(38, Math.abs(dy) / 2)
  const c1y = sourceSide === 'bottom' ? start.y + bend : start.y - bend
  const c2y = targetSide === 'top' ? finish.y - bend : finish.y + bend
  return `M ${start.x} ${start.y} C ${start.x} ${c1y}, ${finish.x} ${c2y}, ${finish.x} ${finish.y}`
}

function SvgText({ lines }) {
  const start = -((lines.length - 1) * 7)
  return e('text', {
    textAnchor: 'middle',
    dominantBaseline: 'middle',
    fontFamily: 'var(--vscode-editor-font-family, monospace)',
    fontSize: 11,
    fill: 'var(--vscode-editor-foreground)',
  }, lines.map((line, idx) => e('tspan', {
    key: idx,
    x: 0,
    dy: idx === 0 ? start : 15,
  }, line)))
}

function NodeLanguageButton({ item, graphKind, languageForNode, toggleNodeLanguage }) {
  if (!item.node._english_available || typeof toggleNodeLanguage !== 'function') return null
  const language = languageForNode?.(graphKind, item.node.id) || item.node._language || 'formal'
  const label = language === 'english' ? 'Lean' : 'EN'
  const width = language === 'english' ? 34 : 24
  const x = item.width / 2 - width - 6
  const y = item.height / 2 - 18
  return e('g', {
    transform: `translate(${x}, ${y})`,
    onPointerDown: event => {
      event.preventDefault()
      event.stopPropagation()
    },
    onClick: event => {
      event.preventDefault()
      event.stopPropagation()
      toggleNodeLanguage(graphKind, item.node.id)
    },
    style: { cursor: 'pointer' },
  }, [
    e('rect', {
      key: 'bg',
      x: 0,
      y: 0,
      width,
      height: 14,
      rx: 7,
      fill: language === 'english' ? 'rgba(59, 130, 246, 0.22)' : 'rgba(127, 127, 127, 0.16)',
      stroke: language === 'english' ? '#3b82f6' : 'var(--vscode-editorWidget-border, #555)',
      strokeWidth: 1,
    }),
    e('text', {
      key: 'text',
      x: width / 2,
      y: 9.5,
      textAnchor: 'middle',
      fontFamily: 'var(--vscode-editor-font-family, sans-serif)',
      fontSize: 8.5,
      fill: 'var(--vscode-editor-foreground)',
    }, label),
  ])
}

function MarkerDefs({ scope }) {
  const colors = ['#2563eb', '#0f766e', '#d97706', '#7c3aed', '#16a34a', '#15803d', '#64748b', '#2b6cb0', '#c27803', '#2f855a']
  return e('defs', null, colors.map(color => e('marker', {
    key: color,
    id: `${scope}-arrow-${safeToken(color)}`,
    viewBox: '0 0 10 10',
    refX: 8,
    refY: 5,
    markerWidth: 6,
    markerHeight: 6,
    orient: 'auto-start-reverse',
  }, e('path', {
    d: 'M 0 0 L 10 5 L 0 10 z',
    fill: color,
    opacity: 0.88,
  }))))
}

function applyNodePositions(layout, positions) {
  const items = layout.items.map(item => {
    const position = positions?.[item.node.id]
    const x = Number(position?.x)
    const y = Number(position?.y)
    if (!Number.isFinite(x) || !Number.isFinite(y)) return item
    return { ...item, x, y }
  })
  const width = Math.max(240, ...items.map(item => item.x + item.width / 2 + 48))
  const height = Math.max(160, ...items.map(item => item.y + item.height / 2 + 48))
  const byId = new Map(items.map(item => [item.node.id, item]))
  return { ...layout, items, byId, width, height }
}

function svgPoint(svg, event) {
  if (!svg) return null
  const matrix = svg.getScreenCTM()
  if (!matrix) return null
  const point = svg.createSVGPoint()
  point.x = event.clientX
  point.y = event.clientY
  return point.matrixTransform(matrix.inverse())
}

function setNodePosition(setPositions, nodeId, x, y) {
  setPositions(previous => ({
    ...previous,
    [nodeId]: {
      x: Math.round(x * 10) / 10,
      y: Math.round(y * 10) / 10,
    },
  }))
}

function hasNodePositions(positions) {
  return Object.keys(positions || {}).length > 0
}

function ResetLayoutButton({ positions, setPositions }) {
  if (!setPositions || !hasNodePositions(positions)) return null
  return e('button', {
    onClick: () => setPositions({}),
    style: {
      padding: '2px 8px',
      borderRadius: '999px',
      border: '1px solid var(--vscode-editorWidget-border, #555)',
      background: 'transparent',
      color: 'var(--vscode-editor-foreground)',
      cursor: 'pointer',
      fontSize: '12px',
      margin: '0 0 8px 0',
    }
  }, 'Reset layout')
}

function ActionButton({ children, onClick, active = false }) {
  return e('button', {
    onClick,
    style: {
      padding: '2px 8px',
      borderRadius: '999px',
      border: `1px solid ${active ? '#3b82f6' : 'var(--vscode-editorWidget-border, #555)'}`,
      background: active ? 'rgba(59, 130, 246, 0.18)' : 'transparent',
      color: 'var(--vscode-editor-foreground)',
      cursor: 'pointer',
      fontSize: '12px',
      margin: '0 0 8px 0',
    }
  }, children)
}

function LanguageControls({ hasEnglish, globalLanguage, setGlobalLanguage, resetOverrides, overrideCount }) {
  return e('div', {
    style: {
      display: 'flex',
      gap: '6px',
      flexWrap: 'wrap',
      alignItems: 'center',
      margin: '8px 0 10px 0',
    }
  }, [
    e('span', {
      key: 'label',
      style: { opacity: 0.72, fontSize: '12px', marginRight: '2px' },
    }, 'Language'),
    e(ActionButton, {
      key: 'formal',
      active: globalLanguage === 'formal',
      onClick: () => setGlobalLanguage('formal'),
    }, 'Formal'),
    e(ActionButton, {
      key: 'english',
      active: globalLanguage === 'english',
      onClick: () => hasEnglish && setGlobalLanguage('english'),
    }, hasEnglish ? 'English' : 'English unavailable'),
    overrideCount > 0
      ? e(ActionButton, {
          key: 'reset',
          onClick: resetOverrides,
        }, `Reset node language (${overrideCount})`)
      : null,
  ])
}

function offsetLayout(layout, dx, dy) {
  const items = layout.items.map(item => ({ ...item, x: item.x + dx, y: item.y + dy }))
  const byId = new Map(items.map(item => [item.node.id, item]))
  return {
    ...layout,
    items,
    byId,
    width: layout.width + dx,
    height: layout.height + dy,
  }
}

function GraphSvg({
  graphKind,
  nodes,
  edges,
  selectedId,
  onSelect,
  zoom,
  scope,
  positions = {},
  setPositions,
  languageForNode,
  toggleNodeLanguage,
}) {
  const baseLayout = React.useMemo(
    () => computeLayout(nodes, edges, graphKind),
    [nodes, edges, graphKind]
  )
  const layout = React.useMemo(
    () => applyNodePositions(baseLayout, positions),
    [baseLayout, positions]
  )
  const palette = graphKind === 'plan' ? PLAN_COLORS : EVIDENCE_COLORS
  const svgRef = React.useRef(null)
  const dragRef = React.useRef(null)
  const draggable = typeof setPositions === 'function'

  function beginDrag(event, item) {
    if (event.button != null && event.button !== 0) return
    onSelect?.(item.node.id, item.node)
    if (!draggable) return
    const point = svgPoint(svgRef.current, event)
    if (!point) return
    event.preventDefault()
    event.stopPropagation()
    dragRef.current = {
      nodeId: item.node.id,
      node: item.node,
      pointerId: event.pointerId,
      startX: point.x,
      startY: point.y,
      offsetX: point.x - item.x,
      offsetY: point.y - item.y,
      minX: item.width / 2 + 16,
      minY: item.height / 2 + 16,
      moved: false,
    }
    try {
      event.currentTarget.setPointerCapture(event.pointerId)
    } catch (_) {
      // Pointer capture is best-effort inside the infoview webview.
    }
  }

  function moveDrag(event) {
    const drag = dragRef.current
    if (!drag || drag.pointerId !== event.pointerId || !draggable) return
    const point = svgPoint(svgRef.current, event)
    if (!point) return
    event.preventDefault()
    event.stopPropagation()
    const x = Math.max(drag.minX, point.x - drag.offsetX)
    const y = Math.max(drag.minY, point.y - drag.offsetY)
    if (Math.abs(point.x - drag.startX) > 4 || Math.abs(point.y - drag.startY) > 4) {
      drag.moved = true
    }
    setNodePosition(setPositions, drag.nodeId, x, y)
  }

  function endDrag(event) {
    const drag = dragRef.current
    if (!drag || drag.pointerId !== event.pointerId) return
    dragRef.current = null
    try {
      event.currentTarget.releasePointerCapture(event.pointerId)
    } catch (_) {
      // Pointer capture release is best-effort inside the infoview webview.
    }
  }

  return e('div', {
    style: {
      overflow: 'auto',
      maxHeight: graphKind === 'plan' ? '560px' : '520px',
      border: '1px solid var(--vscode-editorWidget-border, #555)',
      background: 'var(--vscode-editor-background)',
      padding: '8px',
    }
  }, e('svg', {
    ref: svgRef,
    xmlns: 'http://www.w3.org/2000/svg',
    viewBox: `0 0 ${layout.width} ${layout.height}`,
    style: {
      display: 'block',
      width: `${Math.max(180, layout.width * zoom)}px`,
      height: `${Math.max(120, layout.height * zoom)}px`,
    }
  }, [
    e(MarkerDefs, { key: 'defs', scope }),
    e('rect', {
      key: 'bg',
      x: 0,
      y: 0,
      width: layout.width,
      height: layout.height,
      fill: 'var(--vscode-editor-background)',
    }),
    e('g', { key: 'edges' }, edges.map((edge, idx) => {
      const source = layout.byId.get(edge.from)
      const target = layout.byId.get(edge.to)
      if (!source || !target) return null
      const [, stroke] = colorFor(target.node.kind, palette)
      return e('path', {
        key: edge.id || `${edge.from}-${edge.to}-${idx}`,
        d: edgePath(source, target),
        fill: 'none',
        stroke,
        strokeWidth: 1.8,
        opacity: 0.82,
        markerEnd: `url(#${scope}-arrow-${safeToken(stroke)})`,
      })
    })),
    e('g', { key: 'nodes' }, layout.items.map(item => {
      const [fill, stroke] = colorFor(item.node.kind, palette)
      const selected = selectedId === item.node.id
      return e('g', {
        key: item.node.id,
        transform: `translate(${item.x}, ${item.y})`,
        onPointerDown: event => beginDrag(event, item),
        onPointerMove: moveDrag,
        onPointerUp: endDrag,
        onPointerCancel: endDrag,
        style: {
          cursor: draggable ? 'grab' : onSelect ? 'pointer' : 'default',
          touchAction: 'none',
          userSelect: 'none',
        },
      }, [
        e('title', { key: 'title' }, clean(item.node.role_summary || item.node.display_label || item.node.label || item.node.type || item.node.id)),
        e('rect', {
          key: 'shape',
          x: -item.width / 2,
          y: -item.height / 2,
          width: item.width,
          height: item.height,
          rx: item.node.kind === 'theorem_goal' ? item.height / 2 : 10,
          fill,
          stroke: selected ? '#f97316' : stroke,
          strokeWidth: selected ? 3 : 1.9,
          strokeDasharray: item.node.kind === 'subgoal' ? '6,4' : undefined,
        }),
        e(SvgText, { key: 'text', lines: item.lines }),
        e(NodeLanguageButton, {
          key: 'lang',
          item,
          graphKind,
          languageForNode,
          toggleNodeLanguage,
        }),
      ])
    })),
  ]))
}

function PlanExplorerGraph({
  planNodes,
  planEdges,
  selectedPlanId,
  onSelectPlan,
  selectedGraph,
  selectedEvidenceId,
  onSelectEvidence,
  zoom,
  scope,
  viewMode,
  setViewMode,
  planPositions,
  setPlanPositions,
  evidencePositions,
  setEvidencePositions,
  languageForNode,
  toggleNodeLanguage,
}) {
  const planBaseLayout = React.useMemo(
    () => computeLayout(planNodes, planEdges, 'plan'),
    [planNodes, planEdges]
  )
  const planLayout = React.useMemo(
    () => applyNodePositions(planBaseLayout, planPositions),
    [planBaseLayout, planPositions]
  )
  const evidenceBaseLayout = React.useMemo(
    () => computeLayout(selectedGraph.nodes, selectedGraph.edges, 'evidence'),
    [selectedGraph.nodes, selectedGraph.edges]
  )
  const evidenceRelativeLayout = React.useMemo(
    () => applyNodePositions(evidenceBaseLayout, evidencePositions),
    [evidenceBaseLayout, evidencePositions]
  )
  const selectedPlanItem = planLayout.byId.get(selectedPlanId)
  const showEvidence = viewMode === 'plan-with-evidence' && selectedPlanItem && selectedGraph.nodes.length > 0
  const evidenceOffset = showEvidence
    ? {
        x: selectedPlanItem.x + selectedPlanItem.width / 2 + 88,
        y: Math.max(46, selectedPlanItem.y - evidenceRelativeLayout.height / 2),
      }
    : { x: 0, y: 0 }
  const evidenceLayout = showEvidence
    ? offsetLayout(evidenceRelativeLayout, evidenceOffset.x, evidenceOffset.y)
    : evidenceRelativeLayout
  const width = showEvidence
    ? Math.max(planLayout.width, evidenceOffset.x + evidenceRelativeLayout.width + 72)
    : planLayout.width
  const height = showEvidence
    ? Math.max(planLayout.height, evidenceOffset.y + evidenceRelativeLayout.height + 82)
    : planLayout.height
  const svgRef = React.useRef(null)
  const dragRef = React.useRef(null)

  function beginDrag(event, item, setPositions, onSelect, storedOffset) {
    if (event.button != null && event.button !== 0) return
    onSelect?.(item.node.id, item.node)
    const point = svgPoint(svgRef.current, event)
    if (!point) return
    event.preventDefault()
    event.stopPropagation()
    dragRef.current = {
      nodeId: item.node.id,
      node: item.node,
      pointerId: event.pointerId,
      setPositions,
      startX: point.x,
      startY: point.y,
      storeOffsetX: storedOffset.x,
      storeOffsetY: storedOffset.y,
      offsetX: point.x - item.x,
      offsetY: point.y - item.y,
      minX: storedOffset.x + item.width / 2 + 16,
      minY: storedOffset.y + item.height / 2 + 16,
      moved: false,
    }
    try {
      event.currentTarget.setPointerCapture(event.pointerId)
    } catch (_) {
      // Pointer capture is best-effort inside the infoview webview.
    }
  }

  function moveDrag(event) {
    const drag = dragRef.current
    if (!drag || drag.pointerId !== event.pointerId) return
    const point = svgPoint(svgRef.current, event)
    if (!point) return
    event.preventDefault()
    event.stopPropagation()
    const x = Math.max(drag.minX, point.x - drag.offsetX)
    const y = Math.max(drag.minY, point.y - drag.offsetY)
    if (Math.abs(point.x - drag.startX) > 4 || Math.abs(point.y - drag.startY) > 4) {
      drag.moved = true
    }
    setNodePosition(drag.setPositions, drag.nodeId, x - drag.storeOffsetX, y - drag.storeOffsetY)
  }

  function endDrag(event) {
    const drag = dragRef.current
    if (!drag || drag.pointerId !== event.pointerId) return
    dragRef.current = null
    try {
      event.currentTarget.releasePointerCapture(event.pointerId)
    } catch (_) {
      // Pointer capture release is best-effort inside the infoview webview.
    }
  }

  function renderPlanNode(item) {
    const [fill, stroke] = colorFor(item.node.kind, PLAN_COLORS)
    const selected = selectedPlanId === item.node.id
    const dimmed = showEvidence && !selected
    return e('g', {
      key: item.node.id,
      transform: `translate(${item.x}, ${item.y})`,
      opacity: dimmed ? 0.26 : 1,
      onPointerDown: event => beginDrag(event, item, setPlanPositions, id => {
        onSelectPlan(id, item.node)
        setViewMode('plan-with-evidence')
      }, { x: 0, y: 0 }),
      onPointerMove: moveDrag,
      onPointerUp: endDrag,
      onPointerCancel: endDrag,
      style: { cursor: 'grab', touchAction: 'none', userSelect: 'none' },
    }, [
      e('title', { key: 'title' }, clean(item.node.role_summary || item.node.detail_label || item.node.label || item.node.id)),
      e('rect', {
        key: 'shape',
        x: -item.width / 2,
        y: -item.height / 2,
        width: item.width,
        height: item.height,
        rx: 10,
        fill,
        stroke: selected ? '#f97316' : stroke,
        strokeWidth: selected ? 3 : 1.9,
      }),
      e(SvgText, { key: 'text', lines: item.lines }),
      e(NodeLanguageButton, {
        key: 'lang',
        item,
        graphKind: 'plan',
        languageForNode,
        toggleNodeLanguage,
      }),
    ])
  }

  function renderEvidenceNode(item) {
    const [fill, stroke] = colorFor(item.node.kind, EVIDENCE_COLORS)
    const selected = selectedEvidenceId === item.node.id
    return e('g', {
      key: item.node.id,
      transform: `translate(${item.x}, ${item.y})`,
      onPointerDown: event => beginDrag(event, item, setEvidencePositions, onSelectEvidence, evidenceOffset),
      onPointerMove: moveDrag,
      onPointerUp: endDrag,
      onPointerCancel: endDrag,
      onDoubleClick: event => {
        event.preventDefault()
        event.stopPropagation()
        setViewMode('evidence-focus')
      },
      style: { cursor: 'grab', touchAction: 'none', userSelect: 'none' },
    }, [
      e('title', { key: 'title' }, clean(item.node.display_label || item.node.label || item.node.type || item.node.name || item.node.id)),
      e('rect', {
        key: 'shape',
        x: -item.width / 2,
        y: -item.height / 2,
        width: item.width,
        height: item.height,
        rx: item.node.kind === 'theorem_goal' ? item.height / 2 : 10,
        fill,
        stroke: selected ? '#f97316' : stroke,
        strokeWidth: selected ? 3 : 1.9,
        strokeDasharray: item.node.kind === 'subgoal' ? '6,4' : undefined,
      }),
      e(SvgText, { key: 'text', lines: item.lines }),
      e(NodeLanguageButton, {
        key: 'lang',
        item,
        graphKind: 'evidence',
        languageForNode,
        toggleNodeLanguage,
      }),
    ])
  }

  return e('div', {
    style: {
      overflow: 'auto',
      maxHeight: '620px',
      border: '1px solid var(--vscode-editorWidget-border, #555)',
      background: 'var(--vscode-editor-background)',
      padding: '8px',
    }
  }, e('svg', {
    ref: svgRef,
    xmlns: 'http://www.w3.org/2000/svg',
    viewBox: `0 0 ${width} ${height}`,
    style: {
      display: 'block',
      width: `${Math.max(180, width * zoom)}px`,
      height: `${Math.max(120, height * zoom)}px`,
    }
  }, [
    e(MarkerDefs, { key: 'defs', scope }),
    e('rect', {
      key: 'bg',
      x: 0,
      y: 0,
      width,
      height,
      fill: 'var(--vscode-editor-background)',
    }),
    e('g', { key: 'plan-edges' }, planEdges.map((edge, idx) => {
      const source = planLayout.byId.get(edge.from)
      const target = planLayout.byId.get(edge.to)
      if (!source || !target) return null
      const [, stroke] = colorFor(target.node.kind, PLAN_COLORS)
      const incident = selectedPlanId === edge.from || selectedPlanId === edge.to
      return e('path', {
        key: edge.id || `${edge.from}-${edge.to}-${idx}`,
        d: edgePath(source, target),
        fill: 'none',
        stroke,
        strokeWidth: incident ? 2.2 : 1.5,
        opacity: showEvidence ? incident ? 0.74 : 0.16 : 0.82,
        markerEnd: `url(#${scope}-arrow-${safeToken(stroke)})`,
      })
    })),
    showEvidence ? e('g', { key: 'evidence-panel' }, [
      e('path', {
        key: 'connector',
        d: edgePath(selectedPlanItem, {
          ...selectedPlanItem,
          x: evidenceOffset.x + 8,
          y: evidenceOffset.y + 26,
          width: 16,
          height: 16,
          rank: selectedPlanItem.rank,
        }),
        fill: 'none',
        stroke: '#64748b',
        strokeWidth: 1.5,
        strokeDasharray: '5,5',
        opacity: 0.72,
      }),
      e('rect', {
        key: 'panel-bg',
        x: evidenceOffset.x - 22,
        y: evidenceOffset.y - 36,
        width: evidenceRelativeLayout.width + 44,
        height: evidenceRelativeLayout.height + 68,
        rx: 16,
        fill: 'rgba(127, 127, 127, 0.055)',
        stroke: 'var(--vscode-editorWidget-border, #555)',
        strokeWidth: 1.4,
        onPointerDown: event => {
          event.preventDefault()
          event.stopPropagation()
          setViewMode('evidence-focus')
        },
        style: { cursor: 'zoom-in' },
      }),
      e('text', {
        key: 'panel-title',
        x: evidenceOffset.x,
        y: evidenceOffset.y - 14,
        fill: 'var(--vscode-editor-foreground)',
        fontFamily: 'var(--vscode-editor-font-family, sans-serif)',
        fontSize: 12,
        fontWeight: 700,
        onPointerDown: event => {
          event.preventDefault()
          event.stopPropagation()
          setViewMode('evidence-focus')
        },
        style: { cursor: 'zoom-in' },
      }, 'Selected Evidence · click panel to focus'),
      e('g', { key: 'evidence-edges' }, selectedGraph.edges.map((edge, idx) => {
        const source = evidenceLayout.byId.get(edge.from)
        const target = evidenceLayout.byId.get(edge.to)
        if (!source || !target) return null
        const [, stroke] = colorFor(target.node.kind, EVIDENCE_COLORS)
        return e('path', {
          key: edge.id || `${edge.from}-${edge.to}-${idx}`,
          d: edgePath(source, target),
          fill: 'none',
          stroke,
          strokeWidth: 1.6,
          opacity: 0.78,
          markerEnd: `url(#${scope}-arrow-${safeToken(stroke)})`,
        })
      })),
      e('g', { key: 'evidence-nodes' }, evidenceLayout.items.map(renderEvidenceNode)),
    ]) : null,
    e('g', { key: 'plan-nodes' }, planLayout.items.map(renderPlanNode)),
  ]))
}

function ZoomControls({ zoom, setZoom }) {
  const options = [0.5, 0.75, 1, 1.25, 1.5]
  return e('div', { style: { display: 'flex', gap: '6px', flexWrap: 'wrap', marginBottom: '8px' } },
    options.map(value => e('button', {
      key: value,
      onClick: () => setZoom(value),
      style: {
        padding: '2px 8px',
        borderRadius: '999px',
        border: `1px solid ${zoom === value ? '#3b82f6' : 'var(--vscode-editorWidget-border, #555)'}`,
        background: zoom === value ? 'rgba(59, 130, 246, 0.18)' : 'transparent',
        color: 'var(--vscode-editor-foreground)',
        cursor: 'pointer',
        fontSize: '12px',
      }
    }, `${Math.round(value * 100)}%`))
  )
}

function FieldList({ title, items }) {
  const values = arr(items).map(clean).filter(Boolean)
  if (!values.length) {
    return e('div', { style: { opacity: 0.62, marginBottom: '6px' } }, `${title}: none`)
  }
  return e('div', { style: { marginBottom: '8px' } }, [
    e('div', { key: 'title', style: { fontWeight: 600, marginBottom: '3px' } }, title),
    e('ul', { key: 'list', style: { marginTop: 0, paddingLeft: '18px' } },
      values.map((item, idx) => e('li', { key: idx }, item)))
  ])
}

function PreBlock({ title, text }) {
  const value = String(text || '').trim()
  if (!value) return e('div', { style: { opacity: 0.62, marginBottom: '6px' } }, `${title}: none`)
  return e('div', { style: { marginBottom: '10px' } }, [
    e('div', { key: 'title', style: { fontWeight: 600, marginBottom: '3px' } }, title),
    e('pre', {
      key: 'pre',
      style: {
        whiteSpace: 'pre-wrap',
        overflow: 'auto',
        padding: '8px',
        border: '1px solid var(--vscode-editorWidget-border, #555)',
        borderRadius: '6px',
        background: 'rgba(127, 127, 127, 0.08)',
      }
    }, value)
  ])
}

function PlanDetails({ node }) {
  if (!node) return e('div', { style: { opacity: 0.65 } }, 'Select a Plan Node.')
  const goalsBefore = arr(node.goals_before).join('\n\n---\n\n')
  const goalsAfter = arr(node.goals_after).join('\n\n---\n\n')
  const language = node._language || 'formal'
  return e('div', null, [
    e('h3', { key: 'h', style: { margin: '0 0 8px 0' } }, node.label || node.id),
    e('div', { key: 'kind', style: { opacity: 0.78, marginBottom: '8px' } },
      `kind: ${node.kind || ''} · language: ${language}`),
    e(PreBlock, { key: 'role', title: language === 'english' ? 'English explanation' : 'Role', text: node.role_summary }),
    language === 'english'
      ? e(PreBlock, { key: 'formal-role', title: 'Formal role', text: node._formal_role_summary })
      : node._english_detail
        ? e(PreBlock, { key: 'english-role', title: 'English explanation', text: node._english_detail })
        : null,
    e(PreBlock, { key: 'proof', title: 'Proof block', text: node.raw_text }),
    e(FieldList, { key: 'inputs', title: 'Inputs', items: node.display_inputs }),
    e(FieldList, { key: 'outputs', title: 'Outputs', items: node.display_outputs }),
    e(FieldList, { key: 'solves', title: 'Solves', items: node.display_solves }),
    e(FieldList, { key: 'opens', title: 'Opens subgoals', items: node.display_opens_subgoals }),
    e(FieldList, { key: 'globals', title: 'Core globals', items: node.display_used_globals }),
    e(PreBlock, { key: 'before', title: 'Goals before', text: goalsBefore }),
    e(PreBlock, { key: 'after', title: 'Goals after', text: goalsAfter }),
  ])
}

function EvidenceDetails({ node }) {
  if (!node) return null
  const goalsBefore = arr(node.goals_before).join('\n\n---\n\n')
  const goalsAfter = arr(node.goals_after).join('\n\n---\n\n')
  const title = node.display_label || node.label || node.name || node.type || node.id
  const language = node._language || 'formal'
  return e('div', { style: { marginTop: '10px' } }, [
    e('h4', { key: 'h', style: { margin: '0 0 6px 0' } }, short(title, 96)),
    e('div', { key: 'kind', style: { opacity: 0.78, marginBottom: '8px' } },
      `kind: ${node.kind || ''} · language: ${language}`),
    node._english_detail
      ? e(PreBlock, { key: 'english-detail', title: 'English explanation', text: node._english_detail })
      : null,
    language === 'english'
      ? e(PreBlock, { key: 'formal-label', title: 'Formal label', text: node._formal_label })
      : null,
    e(PreBlock, { key: 'type', title: 'Type', text: node.display_type || node.type }),
    e(PreBlock, { key: 'raw', title: 'Raw text', text: node.raw_text || node.source_text }),
    e(FieldList, { key: 'locals', title: 'Local refs', items: node.uses_local || node.used_locals || node.display_used_locals }),
    e(FieldList, { key: 'globals', title: 'Global refs', items: node.uses_global || node.used_globals || node.display_used_globals }),
    e(PreBlock, { key: 'before', title: 'Goals before', text: goalsBefore }),
    e(PreBlock, { key: 'after', title: 'Goals after', text: goalsAfter }),
  ])
}

function PlanList({ nodes, selectedId, setSelectedId }) {
  return e('div', null, arr(nodes).map(node => {
    const selected = selectedId === node.id
    return e('button', {
      key: node.id,
      onClick: () => setSelectedId(node.id),
      style: {
        display: 'block',
        width: '100%',
        textAlign: 'left',
        margin: '0 0 6px 0',
        padding: '7px 9px',
        borderRadius: '8px',
        border: `1px solid ${selected ? '#f97316' : 'var(--vscode-editorWidget-border, #555)'}`,
        background: selected ? 'rgba(249, 115, 22, 0.14)' : 'rgba(127, 127, 127, 0.06)',
        color: 'var(--vscode-editor-foreground)',
        cursor: 'pointer',
        fontFamily: 'var(--vscode-editor-font-family, monospace)',
      }
    }, [
      e('div', { key: 'label', style: { fontWeight: 700 } }, node.label || node.id),
      e('div', { key: 'role', style: { opacity: 0.72, fontSize: '11px', marginTop: '2px' } },
        short(node.role_summary || node.detail_label || node.kind, 92)),
    ])
  }))
}

export default function BlueprintLayeredGraph(props) {
  const formalLayered = props.layered || {}
  const englishLayered = props.englishLayered || null
  const hasEnglish = !!englishLayered
  const [globalLanguage, setGlobalLanguage] = React.useState('formal')
  const [nodeLanguageOverrides, setNodeLanguageOverrides] = React.useState({})
  const layered = React.useMemo(
    () => displayLayeredForLanguage(formalLayered, englishLayered, globalLanguage, nodeLanguageOverrides),
    [formalLayered, englishLayered, globalLanguage, nodeLanguageOverrides]
  )
  const theorem = layered.theorem || {}
  const planNodes = arr(layered.plan_graph?.nodes)
  const planEdges = visiblePlanEdges(layered)
  const [selectedId, setSelectedId] = React.useState(planNodes[0]?.id || '')
  const [selectedEvidenceId, setSelectedEvidenceId] = React.useState('')
  const [selectedFullEvidenceId, setSelectedFullEvidenceId] = React.useState('')
  const [viewMode, setViewMode] = React.useState('plan')
  const [planZoom, setPlanZoom] = React.useState(1)
  const [evidenceZoom, setEvidenceZoom] = React.useState(1)
  const [fullZoom, setFullZoom] = React.useState(0.75)
  const [planPositions, setPlanPositions] = React.useState({})
  const [selectedEvidencePositionsByPlan, setSelectedEvidencePositionsByPlan] = React.useState({})
  const [fullEvidencePositions, setFullEvidencePositions] = React.useState({})
  const overrideCount = Object.keys(nodeLanguageOverrides || {}).length

  React.useEffect(() => {
    if (!planNodes.some(node => node.id === selectedId)) {
      setSelectedId(planNodes[0]?.id || '')
    }
  }, [planNodes, selectedId])

  React.useEffect(() => {
    setSelectedEvidenceId('')
  }, [selectedId])

  const selected = planNodes.find(node => node.id === selectedId) || planNodes[0]
  const selectedGraph = selectedEvidence(layered, selected)
  const fullGraph = fullEvidence(layered)
  const selectedFullEvidenceNode = fullGraph.nodes.find(node => node.id === selectedFullEvidenceId)
  const selectedEvidencePositionKey = selected?.id || ''
  const selectedEvidencePositions = selectedEvidencePositionsByPlan[selectedEvidencePositionKey] || {}
  const setCurrentSelectedEvidencePositions = React.useCallback((update) => {
    if (!selectedEvidencePositionKey) return
    setSelectedEvidencePositionsByPlan(previous => {
      const current = previous[selectedEvidencePositionKey] || {}
      const next = typeof update === 'function' ? update(current) : update
      return { ...previous, [selectedEvidencePositionKey]: next || {} }
    })
  }, [selectedEvidencePositionKey])

  React.useEffect(() => {
    if (viewMode === 'evidence-focus' && selectedGraph.nodes.length === 0) {
      setViewMode('plan')
    }
  }, [viewMode, selectedGraph.nodes.length])

  function selectPlanNode(id) {
    setSelectedId(id)
    setViewMode('plan-with-evidence')
  }

  function selectSelectedEvidenceNode(id) {
    setSelectedEvidenceId(id)
  }

  function selectFullEvidenceNode(id) {
    setSelectedFullEvidenceId(id)
  }

  function actualNodeLanguage(graphKind, nodeId) {
    return languageForNode(graphKind, nodeId, globalLanguage, nodeLanguageOverrides)
  }

  function toggleNodeLanguage(graphKind, nodeId) {
    if (!hasEnglish) return
    const key = languageKey(graphKind, nodeId)
    const current = actualNodeLanguage(graphKind, nodeId)
    const next = current === 'english' ? 'formal' : 'english'
    setNodeLanguageOverrides(previous => {
      const updated = { ...previous, [key]: next }
      if (updated[key] === globalLanguage) {
        delete updated[key]
      }
      return updated
    })
  }

  const scope = safeToken(theorem.name || 'proofstruct-layered')
  const theoremType =
    globalLanguage === 'english' && englishLayered?.theorem?.english_type
      ? englishLayered.theorem.english_type
      : theorem.type
  const subtitle = theoremType ? `${theorem.name}: ${short(theoremType, 120)}` : theorem.name || 'proof blueprint'
  const inEvidenceFocus = viewMode === 'evidence-focus'
  const hasSelectedEvidence = selectedGraph.nodes.length > 0

  return e('div', {
    style: {
      padding: '8px',
      color: 'var(--vscode-editor-foreground)',
      fontFamily: 'var(--vscode-editor-font-family, sans-serif)',
    }
  }, [
    e('details', { key: 'root', open: true }, [
      e('summary', { key: 'summary', style: { cursor: 'pointer', marginBottom: '8px' } },
        `Layered proof blueprint: ${theorem.name || ''}`),
      e('div', { key: 'subtitle', style: { opacity: 0.84, margin: '6px 0 6px 0' } }, subtitle),
      e('div', { key: 'source', style: { opacity: 0.62, fontSize: '12px', marginBottom: '10px' } },
        `data source: ${props.dataSource || ''}${props.englishDataSource ? ` · english: ${props.englishDataSource}` : ''}`),
      e(LanguageControls, {
        key: 'language',
        hasEnglish,
        globalLanguage,
        setGlobalLanguage,
        resetOverrides: () => setNodeLanguageOverrides({}),
        overrideCount,
      }),
      e('h3', { key: 'planh', style: { margin: '12px 0 8px 0' } },
        inEvidenceFocus ? 'Selected Evidence Focus' : 'Proof Plan Explorer'),
      e('div', { key: 'hint', style: { margin: '0 0 8px 0', opacity: 0.72, fontSize: '12px' } },
        inEvidenceFocus
          ? 'Click an Evidence Node to inspect it. Drag nodes freely; edges intentionally have no annotations.'
          : 'Click a Plan Node to open its Evidence in the same canvas. Drag nodes to adjust layout.'),
      inEvidenceFocus
        ? e('div', { key: 'focus-controls', style: { display: 'flex', gap: '6px', flexWrap: 'wrap', alignItems: 'center' } }, [
            e(ActionButton, {
              key: 'back',
              onClick: () => setViewMode('plan-with-evidence'),
            }, 'Back to Proof Plan'),
            e(ZoomControls, { key: 'focuszoom', zoom: evidenceZoom, setZoom: setEvidenceZoom }),
            e(ResetLayoutButton, {
              key: 'focusreset',
              positions: selectedEvidencePositions,
              setPositions: setCurrentSelectedEvidencePositions,
            }),
          ])
        : e('div', { key: 'plan-controls', style: { display: 'flex', gap: '6px', flexWrap: 'wrap', alignItems: 'center' } }, [
            e(ZoomControls, { key: 'planzoom', zoom: planZoom, setZoom: setPlanZoom }),
            e(ResetLayoutButton, { key: 'planreset', positions: planPositions, setPositions: setPlanPositions }),
            hasSelectedEvidence && viewMode === 'plan-with-evidence'
              ? e(ResetLayoutButton, {
                  key: 'previewreset',
                  positions: selectedEvidencePositions,
                  setPositions: setCurrentSelectedEvidencePositions,
                })
              : null,
            hasSelectedEvidence && viewMode === 'plan-with-evidence'
              ? e(ActionButton, {
                  key: 'focus',
                  onClick: () => setViewMode('evidence-focus'),
                }, 'Focus Evidence')
              : null,
            viewMode === 'plan-with-evidence'
              ? e(ActionButton, {
                  key: 'hide',
                  onClick: () => setViewMode('plan'),
                }, 'Hide Evidence')
              : null,
          ]),
      inEvidenceFocus
        ? hasSelectedEvidence
          ? e('div', { key: 'focusbody' }, [
              e(GraphSvg, {
                key: 'focusgraph',
                graphKind: 'evidence',
                nodes: selectedGraph.nodes,
                edges: selectedGraph.edges,
                selectedId: selectedEvidenceId,
                onSelect: selectSelectedEvidenceNode,
                zoom: evidenceZoom,
                scope: `${scope}-focus`,
                positions: selectedEvidencePositions,
                setPositions: setCurrentSelectedEvidencePositions,
                languageForNode: actualNodeLanguage,
                toggleNodeLanguage,
              }),
              e(EvidenceDetails, {
                key: 'focusdetails',
                node: selectedGraph.nodes.find(node => node.id === selectedEvidenceId),
              }),
            ])
          : e('div', { key: 'empty-focus', style: { opacity: 0.65 } }, 'No visible evidence nodes for this Plan Node.')
        : e(PlanExplorerGraph, {
            key: 'planexplorer',
            planNodes,
            planEdges,
            selectedPlanId: selectedId,
            onSelectPlan: selectPlanNode,
            selectedGraph,
            selectedEvidenceId,
            onSelectEvidence: selectSelectedEvidenceNode,
            zoom: planZoom,
            scope: `${scope}-explorer`,
            viewMode,
            setViewMode,
            planPositions,
            setPlanPositions,
            evidencePositions: selectedEvidencePositions,
            setEvidencePositions: setCurrentSelectedEvidencePositions,
            languageForNode: actualNodeLanguage,
            toggleNodeLanguage,
          }),
      e('div', {
        key: 'main',
        style: {
          display: 'grid',
          gridTemplateColumns: 'minmax(190px, 0.42fr) minmax(260px, 1fr)',
          gap: '12px',
          marginTop: '14px',
        }
      }, [
        e('div', { key: 'list' }, [
          e('h3', { key: 'h', style: { margin: '0 0 8px 0' } }, 'Plan Nodes'),
          e(PlanList, { key: 'items', nodes: planNodes, selectedId, setSelectedId: selectPlanNode }),
        ]),
        e('div', { key: 'details' }, [
          e(PlanDetails, { key: 'pd', node: selected }),
        ])
      ]),
      e('details', { key: 'full', style: { marginTop: '16px' } }, [
        e('summary', { key: 's', style: { cursor: 'pointer' } }, 'Full Evidence Graph'),
        e('div', { key: 'body', style: { marginTop: '8px' } }, [
          e('div', {
            key: 'hint',
            style: { margin: '0 0 8px 0', opacity: 0.68, fontSize: '12px' }
          }, 'dependency view · rank layout · click nodes to inspect · drag nodes to adjust layout · edges have no annotations'),
          e(ZoomControls, { key: 'fz', zoom: fullZoom, setZoom: setFullZoom }),
          e(ResetLayoutButton, { key: 'freset', positions: fullEvidencePositions, setPositions: setFullEvidencePositions }),
          e(GraphSvg, {
            key: 'fg',
            graphKind: 'evidence',
            nodes: fullGraph.nodes,
            edges: fullGraph.edges,
            selectedId: selectedFullEvidenceId,
            onSelect: selectFullEvidenceNode,
            zoom: fullZoom,
            scope: `${scope}-full`,
            positions: fullEvidencePositions,
            setPositions: setFullEvidencePositions,
            languageForNode: actualNodeLanguage,
            toggleNodeLanguage,
          }),
          e(EvidenceDetails, { key: 'fdetails', node: selectedFullEvidenceNode }),
        ])
      ])
    ])
  ])
}
