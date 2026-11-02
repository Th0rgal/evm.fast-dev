import Lean

/-! Expose an application at a named compiler boundary and share its closed
arguments. The reconstructed application equality is kernel checked. -/
open Lean Meta Elab Command

elab "wave8_expose " id:ident " := " value:term " until " fn:ident : command => do
  liftTermElabM do
    let function ← realizeGlobalConstNoOverloadWithInfo fn
    let expression ← Term.elabTerm value none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasSorry || expression.hasMVar || expression.hasFVar then
      throwError "Application exposure requires a successfully elaborated closed term"
    let some application ← withTransparency .all (whnfUntil expression function)
      | throwError "Requested application head was not reached"
    let name := (← getCurrNamespace) ++ id.getId
    let mut arguments := #[]
    for argument in application.getAppArgs, index in [:application.getAppNumArgs] do
      let argName := name ++ Name.mkSimple s!"arg{index}"
      addDecl (.defnDecl {
        name := argName
        levelParams := []
        type := ← inferType argument
        value := argument
        hints := .regular (getMaxHeight (← getEnv) argument + 1)
        safety := .safe })
      arguments := arguments.push (mkConst argName)
    if let some last := arguments.back? then
      addDecl (.defnDecl {
        name := name ++ `last
        levelParams := []
        type := ← inferType last
        value := last
        hints := .regular (getMaxHeight (← getEnv) last + 1)
        safety := .safe })
    let result := mkAppN application.getAppFn arguments
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := ← inferType expression
      value := result
      hints := .regular (getMaxHeight (← getEnv) result + 1)
      safety := .safe })
    addDecl (.thmDecl {
      name := name.appendAfter "_eq"
      levelParams := []
      type := ← mkEq expression (mkConst name)
      value := ← mkEqRefl expression })
    logInfo m!"Exposed {name}, {arguments.size} arguments"
