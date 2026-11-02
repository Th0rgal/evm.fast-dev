import Lean

/-! Project a tuple or record before simplifying its unused fields. Each
replacement uses ordinary definitional equality in the consuming CBV proof. -/
open Lean Meta

/- Reducible projection functions can become lambda applications during CBV's
initial unfolding pass. Beta-reduce those applications before CBV evaluates
their tuple arguments, so unused compiler outputs remain unevaluated. -/
cbv_simproc ↓ wave8Beta (_) := fun expression => do
  unless expression.isApp && expression.getAppFn.isLambda do return .rfl
  let result ← Sym.shareCommon expression.headBeta
  return .step result (← mkEqRefl expression)

private def compilerProjection (name : Name) : Bool :=
  name == ``Prod || name == `Flapjack.FunDecl ||
    name == `Flapjack.Pancake.PanStructs.CompileShapeExact.ContextExact || name == `Flapjack.HolFiniteMapExact ||
    name == `Flapjack.Pancake.PanLang.FunDeclHOL ||
    name == `Flapjack.PanGlobalsContextExact ||
    name == `Flapjack.PanToCrepContextExact ||
    name == `Flapjack.CrepToLoopContextExact

cbv_simproc ↓ wave8Project (_) := fun expression => do
  if expression.isAppOf `Flapjack.HolFiniteMapExact.lookup then return .rfl
  -- Allocator analyses return tuples through well-founded recursion. Let CBV
  -- evaluate those calls by their equation lemmas before projecting; WHNF
  -- would instead expand their termination machinery over the whole program.
  if (expression.find? fun term =>
      match term.getAppFn.constName? with
      | some name => (`Flapjack.WordAlloc).isPrefixOf name
      | none => false).isSome then return .rfl
  let result ← withTransparency .all do
    if let .proj name _ _ := expression then
      if compilerProjection name then reduceProj? expression else pure none
    else reduceProjOf? expression compilerProjection
  let some result := result | return .rfl
  return .step result (← mkEqRefl expression)
