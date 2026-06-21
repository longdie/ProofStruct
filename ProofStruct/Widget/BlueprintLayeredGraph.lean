import ProofWidgets.Component.Basic

namespace ProofStruct

open Lean
open ProofWidgets

def blueprintLayeredGraphWidgetVersion : String :=
  "2026-06-20-scc-rank-layout-v2"

@[widget_module]
def BlueprintLayeredGraph : Widget.Module where
  javascript := include_str ".." / ".." / "widget" / "blueprintLayeredGraph.js"

end ProofStruct
