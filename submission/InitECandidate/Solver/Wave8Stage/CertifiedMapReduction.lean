import InitECandidate.Solver.Wave8Stage.CertifiedProjectionReduction

/-! Expose one output constructor before simplifying a mapped input list.
This preserves demand-driven projections from tuples containing program bodies.
Each replacement is an ordinary kernel-checkable definitional equality. -/
open Lean Meta

def wave8BetaListHead (expression : Expr) : Expr :=
  if expression.isAppOfArity ``List.cons 3 then
    let args := expression.getAppArgs
    mkApp3 expression.getAppFn args[0]! args[1]!.headBeta args[2]!
  else expression

cbv_simproc ↓ wave8Map (List.map _ _) := fun expression => do
  let result ← withTransparency .all (whnf expression)
  let result := wave8BetaListHead result
  if result.isAppOf ``List.cons || result.isAppOf ``List.nil then
    return .step result (← mkEqRefl expression)
  return .rfl
