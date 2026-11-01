import Lean

/-! Retain an explicit witness from an existing existential proof. This
elaborator unfolds theorem proofs, preserves equality transports and rebuilds
ordinary introductions. Each new bound is a separate proof obligation. It does
not add declarations, trust axioms, or bypass Lean's kernel. -/
namespace InitECandidate.Solver.Wave8Stage.ExposeWitness
open Lean Meta Elab Tactic

private partial def unfoldProof (e : Expr) : MetaM Expr := do
  let e ← withTransparency .all <| whnf e
  if let .const name levels := e.getAppFn then
    if let .thmInfo info ← getConstInfo name then
      return ← unfoldProof (mkAppN (info.value.instantiateLevelParams info.levelParams levels)
        e.getAppArgs)
  return e

private partial def strengthenType (type bound : Expr) : MetaM Expr := do
  let type ← whnf type
  if let .forallE name domain body bi := type then
    withLocalDecl name bi domain fun x => do
      mkForallFVars #[x] (← strengthenType (body.instantiate1 x) bound)
  else if type.isAppOfArity ``Exists 2 then
    let alpha := type.getArg! 0
    let pred := type.getArg! 1
    withLocalDeclD `n alpha fun n => do
      let pair := mkApp2 (mkConst ``And) (bound.beta #[n]) (pred.beta #[n])
      let pred' ← mkLambdaFVars #[n] pair
      return mkApp2 type.getAppFn alpha pred'
  else
    throwError "Expected an existential type, got {type}"

private partial def strengthenEquality (eq bound : Expr) : MetaM Expr := do
  let eq ← withTransparency .reducible <| whnf eq
  let eq := eq.consumeMData
  let args := eq.getAppArgs
  if eq.isAppOfArity ``id 2 then
    strengthenEquality args[1]! bound
  else if eq.isAppOfArity ``congrArg 6 then
    let f' ← withLocalDeclD `x args[0]! fun x => do
      mkLambdaFVars #[x] (← strengthenType (mkApp args[4]! x) bound)
    mkAppM ``congrArg #[f', args[5]!]
  else if eq.isAppOfArity ``Eq.symm 4 then
    mkAppM ``Eq.symm #[← strengthenEquality args[3]! bound]
  else if eq.isAppOfArity ``Eq.trans 6 then
    mkAppM ``Eq.trans #[← strengthenEquality args[4]! bound,
      ← strengthenEquality args[5]! bound]
  else if eq.isAppOfArity ``Eq.refl 2 then
    mkEqRefl (← strengthenType args[1]! bound)
  else
    throwError "Cannot strengthen propositional equality with head {eq.getAppFn}"

private partial def strengthenProof (original bound : Expr) :
    MetaM (Expr × Array MVarId) := do
  let e ← unfoldProof original
  if let .lam name domain body bi := e then
    withLocalDecl name bi domain fun x => do
      let (result, goals) ← strengthenProof (body.instantiate1 x) bound
      return (← mkLambdaFVars #[x] result, goals)
  else if e.isAppOfArity ``Exists.intro 4 then
    let alpha := e.getArg! 0
    let pred := e.getArg! 1
    let witness := e.getArg! 2
    let evidence := e.getArg! 3
    let numerical ← mkFreshExprSyntheticOpaqueMVar (bound.beta #[witness])
    let pair := mkApp4 (mkConst ``And.intro) (bound.beta #[witness])
      (pred.beta #[witness]) numerical evidence
    let type ← strengthenType (← inferType e) bound
    let result := mkApp4 (mkConst ``Exists.intro type.getAppFn.constLevels!)
      alpha (type.getArg! 1) witness pair
    return (result, #[numerical.mvarId!])
  else if e.isAppOf ``Eq.rec then
    let args := e.getAppArgs
    unless args.size ≥ 6 do throwError "Incomplete equality transport"
    if args[0]!.isSort && args[0]!.sortLevel!.isZero then
      let eq' ← strengthenEquality args[5]! bound
      let (base, goals) ← strengthenProof args[3]! bound
      let core ← mkAppM ``Eq.mp #[eq', base]
      return (mkAppN core (args.extract 6 args.size), goals)
    let motive := args[2]!
    let motive' ← try
        forallTelescope (← inferType motive) fun xs _ => do
          mkLambdaFVars xs (← strengthenType (mkAppN motive xs) bound)
      catch _ => throwError "Cannot strengthen equality motive {motive} over {args[0]!}"
    let (base, goals) ← strengthenProof args[3]! bound
    let result := mkAppN e.getAppFn ((args.set! 2 motive').set! 3 base)
    return (result, goals)
  else if e.isAppOf ``False.elim then
    let args := e.getAppArgs
    let target ← strengthenType (← inferType e) bound
    return (← mkAppM ``False.elim #[target, args.back!], #[])
  else
    throwError "Expected an existential introduction or equality transport; exposed head is {e.getAppFn}"

elab "expose_witness " old:term : tactic => withMainContext do
  let original ← instantiateMVars (← Term.elabTerm old none)
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  unless target.isAppOfArity ``Exists 2 do
    throwError "Expected an existential goal"
  let bound ← withLocalDeclD `n (target.getArg! 0) fun n => do
    let body ← whnf ((target.getArg! 1).beta #[n])
    unless body.isAppOfArity ``And 2 do
      throwError "Expected a conjunction in the strengthened predicate"
    mkLambdaFVars #[n] (body.getArg! 0)
  let (result, goals) ← strengthenProof original bound
  unless ← isDefEq (← inferType result) target do
    throwError "Exposed witness has an incompatible predicate"
  goal.assign result
  replaceMainGoal goals.toList

end InitECandidate.Solver.Wave8Stage.ExposeWitness
