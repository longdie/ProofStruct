import Lean

namespace ProofStruct

structure SourceRange where
  file : String
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
deriving Repr, Inhabited

structure BlueprintNode where
  id : String
  kind : String
  nodeName : String := ""
  typeText : String := ""
  label : String := ""
  rawText : String := ""
  sourceLine : Nat := 0
  usesLocal : Array String := #[]
  usesGlobal : Array String := #[]
  goalsBefore : Array String := #[]
  goalsAfter : Array String := #[]
  localContext : Array String := #[]
  exprType : String := ""
  expectedType : String := ""
  semanticUsesLocal : Array String := #[]
  semanticUsesGlobal : Array String := #[]
deriving Repr, Inhabited

structure BlueprintEdge where
  fromId : String
  toId : String
  kind : String
  label : String := ""
deriving Repr, Inhabited

structure Blueprint where
  theoremName : String
  theoremType : String := ""
  sourceFile : String
  nodes : Array BlueprintNode := #[]
  edges : Array BlueprintEdge := #[]
deriving Repr, Inhabited

def emptyBlueprint (sourceFile theoremName theoremType : String) : Blueprint :=
  { theoremName := theoremName, theoremType := theoremType, sourceFile := sourceFile }

def Blueprint.addNode (bp : Blueprint) (node : BlueprintNode) : Blueprint :=
  { bp with nodes := bp.nodes.push node }

def Blueprint.addEdge (bp : Blueprint) (edge : BlueprintEdge) : Blueprint :=
  { bp with edges := bp.edges.push edge }

def Blueprint.addEdges (bp : Blueprint) (edges : Array BlueprintEdge) : Blueprint :=
  { bp with edges := bp.edges ++ edges }

end ProofStruct
