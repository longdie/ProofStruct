import Lean

namespace ProofStruct

structure ExprDeps where
  localDeps : Array String := #[]
  globalDeps : Array String := #[]
deriving Repr, Inhabited

structure StepDeps where
  localDeps : Array String := #[]
  globalDeps : Array Lean.Name := #[]
deriving Repr, Inhabited

private def trim (s : String) : String :=
  s.trimAscii.toString

def pushUnique (items : Array String) (item : String) : Array String :=
  let item := trim item
  if item = "" || items.contains item then items else items.push item

def mergeStringArrays (left right : Array String) : Array String :=
  right.foldl pushUnique left

def ExprDeps.merge (left right : ExprDeps) : ExprDeps :=
  { localDeps := mergeStringArrays left.localDeps right.localDeps
    globalDeps := mergeStringArrays left.globalDeps right.globalDeps }

private def localNameFor? (lctx : Lean.LocalContext) (fvarId : Lean.FVarId) : Option String := do
  let decl ← lctx.find? fvarId
  pure decl.userName.eraseMacroScopes.toString

private def addLocal (deps : ExprDeps) (name : String) : ExprDeps :=
  { deps with localDeps := pushUnique deps.localDeps name }

private def addGlobal (deps : ExprDeps) (name : Lean.Name) : ExprDeps :=
  { deps with globalDeps := pushUnique deps.globalDeps name.eraseMacroScopes.toString }

partial def collectExprDeps (lctx : Lean.LocalContext) (expr : Lean.Expr) : ExprDeps :=
  match expr.consumeMData with
  | .bvar _ => {}
  | .mvar _ => {}
  | .sort _ => {}
  | .lit _ => {}
  | .const declName _ =>
      addGlobal {} declName
  | .fvar fvarId =>
      match localNameFor? lctx fvarId with
      | some name => addLocal {} name
      | none => addLocal {} fvarId.name.eraseMacroScopes.toString
  | .app fn arg =>
      (collectExprDeps lctx fn).merge (collectExprDeps lctx arg)
  | .lam _ binderType body _ =>
      (collectExprDeps lctx binderType).merge (collectExprDeps lctx body)
  | .forallE _ binderType body _ =>
      (collectExprDeps lctx binderType).merge (collectExprDeps lctx body)
  | .letE _ type value body _ =>
      ((collectExprDeps lctx type).merge (collectExprDeps lctx value)).merge
        (collectExprDeps lctx body)
  | .mdata _ body =>
      collectExprDeps lctx body
  | .proj typeName _ struct =>
      (addGlobal {} typeName).merge (collectExprDeps lctx struct)

end ProofStruct
