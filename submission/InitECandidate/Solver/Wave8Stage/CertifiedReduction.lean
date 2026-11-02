import Lean

/-! Staged proof-producing reduction for the concrete compiler. Each command
stores a reduced closed term and its equality certificate. Both declarations
go through Lean's ordinary kernel checker; evaluation never supplies a proof
without a checked equality term. Local pre-simprocs can preserve program
bodies while reducing the enclosing declaration-list structure. -/

open Lean Meta Elab Command

/- Alias unfolding only substitutes definition bodies; it does not inspect
local-variable types. Use the binder-preserving traversal so shared proof
terms in compiled constants are not repeatedly opened and abstracted. -/
private def unfoldCompilerAliases (expression : Expr) : MetaM Expr :=
  Core.transform expression (pre := Sym.unfoldReducibleStep)

private def shareCompilerData : Sym.Simp.Simproc := fun expression => do
  let .const name levels := expression | return .rfl
  unless (`InitECandidate).isPrefixOf name || (`InitE).isPrefixOf name do return .rfl
  if (← Lean.Meta.Tactic.Cbv.isCbvOpaque name) then return .rfl
  let info ← getConstInfo name
  unless info.isDefinition && info.hasValue do return .rfl
  if info.type matches .forallE .. then return .rfl
  if (← whnfD info.type) matches .forallE .. then return .rfl
  unless info.levelParams.length == levels.length do return .rfl
  let body ← instantiateValueLevelParams info levels
  let body ← unfoldCompilerAliases body
  let body ← Sym.shareCommon body
  return .step body (← mkEqRefl expression)

elab "wave8_certified_reduce " id:ident " := " value:term : command => do
  liftTermElabM do
    let expression ← Term.elabTerm value none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasSorry then
      throwError "Staged reduction requires successful term elaboration"
    if expression.hasMVar || expression.hasFVar then
      throwError "Staged reduction requires a closed term"
    let type ← inferType expression
    -- Fresh data definitions can contain a large shared DAG. Start the reducer
    -- with that DAG exposed so its full sharing pass runs before incremental
    -- sharing is used for individual reduction steps.
    let mut input := expression
    while input.isConst do
      let some unfolded ← withTransparency .all (unfoldDefinition? input) | break
      input := unfolded
    input ← unfoldCompilerAliases input
    let oldSimprocs := Lean.Meta.Tactic.Cbv.cbvSimprocExtension.getState (← getEnv)
    modifyEnv fun env => Lean.Meta.Tactic.Cbv.cbvSimprocExtension.modifyState env fun state =>
      state.addCore #[.star] `wave8ShareCompilerData .pre shareCompilerData
    let result ← try Lean.Meta.Tactic.Cbv.cbvEntry input
      finally modifyEnv fun env =>
        Lean.Meta.Tactic.Cbv.cbvSimprocExtension.modifyState env fun _ => oldSimprocs
    let reduced := result.getResultExpr input
    let proof ← match result with
      | .rfl .. => mkEqRefl expression
      | .step _ proof .. => pure proof
    let name := (← getCurrNamespace) ++ id.getId
    addDecl (.defnDecl {
      name, levelParams := [], type, value := reduced
      hints := .regular (getMaxHeight (← getEnv) reduced + 1)
      safety := .safe })
    let equation := name.appendAfter "_eq"
    let equationType ← mkEq expression (mkConst name)
    addDecl (.thmDecl { name := equation, levelParams := [], type := equationType, value := proof })
    logInfo m!"Certified {name}"
