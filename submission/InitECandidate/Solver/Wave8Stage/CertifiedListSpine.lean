import Lean

/-! Expose a closed list's spine using weak-head reduction. Element bodies are
left intact. The resulting equality is checked by the ordinary Lean kernel. -/
open Lean Meta Elab Command

elab "wave8_list_spine " id:ident " := " value:term : command => do
  liftTermElabM do
    let expression ← Term.elabTerm value none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasSorry || expression.hasMVar || expression.hasFVar then
      throwError "List spine requires a successfully elaborated closed term"
    let type ← inferType expression
    let mut current := expression
    let mut heads := #[]
    let mut elementType := mkSort .zero
    repeat
      current ← withTransparency .all (whnf current)
      if current.isAppOfArity ``List.cons 3 then
        let args := current.getAppArgs
        elementType := args[0]!
        heads := heads.push args[1]!
        current := args[2]!
      else if current.isAppOfArity ``List.nil 1 then
        elementType := current.getAppArgs[0]!
        break
      else
        throwError "List spine did not reduce to a constructor"
    let levels := (← whnf type).getAppFn.constLevels!
    let mut reduced := mkApp (mkConst ``List.nil levels) elementType
    for head in heads.reverse do
      reduced := mkApp3 (mkConst ``List.cons levels) elementType head reduced
    let name := (← getCurrNamespace) ++ id.getId
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := type
      value := reduced
      hints := .regular (getMaxHeight (← getEnv) reduced + 1)
      safety := .safe })
    let equationType ← mkEq expression (mkConst name)
    let proof ← mkEqRefl expression
    addDecl (.thmDecl {
      name := name.appendAfter "_eq"
      levelParams := []
      type := equationType
      value := proof })
    logInfo m!"Certified spine {name}, {heads.size} elements"
