import InitECandidate.Solver.Wave8Stage.CertifiedReduction

/-! Select a single entry from a certified literal list without evaluating
other entries. The generated selection equation is checked by the kernel. -/

open Lean Meta Elab Command

elab "wave8_list_entry " id:ident " := " value:term " at " index:num : command => do
  liftTermElabM do
    let expression ← Term.elabTerm value none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasSorry then
      throwError "List selection requires successful term elaboration"
    if expression.hasMVar || expression.hasFVar then
      throwError "List selection requires a closed term"
    let mut current ← withTransparency .all (whnf expression)
    for _ in [:index.getNat] do
      unless current.isAppOfArity ``List.cons 3 do
        throwError "List selection index exceeds the literal list"
      current ← withTransparency .all (whnf current.getAppArgs[2]!)
    unless current.isAppOfArity ``List.cons 3 do
      throwError "List selection requires a nonempty literal list"
    let selected := current.getAppArgs[1]!
    let type ← inferType selected
    let name := (← getCurrNamespace) ++ id.getId
    addDecl (.defnDecl {
      name, levelParams := [], type, value := selected
      hints := .regular (getMaxHeight (← getEnv) selected + 1)
      safety := .safe })
    let getter ← mkAppM ``getElem? #[expression, mkNatLit index.getNat]
    let selectedOption ← mkAppM ``Option.some #[mkConst name]
    let equationType ← mkEq getter selectedOption
    let proof ← mkEqRefl getter
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := equationType, value := proof })
    logInfo m!"Selected {name} at index {index.getNat}"
