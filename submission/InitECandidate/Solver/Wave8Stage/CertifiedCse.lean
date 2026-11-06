import InitECandidate.Solver.Wave8Stage.PrefixChecks.Support

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend

theorem cse_seq_split (left right : WordLangProgHOL (BitVec 64))
    (data : WordCse.Knowledge)
    (first second : WordCse.Knowledge × WordLangProgHOL (BitVec 64))
    (hfirst : WordCse.wordCse data left = first)
    (hsecond : WordCse.wordCse first.1 right = second) :
    WordCse.wordCse data (.seq left right) =
      (second.1, .seq first.2 second.2) := by
  simp only [WordCse.wordCse, hfirst, hsecond]

open Lean Meta Elab Command in
private partial def solveCse (program data : Expr) : MetaM (Expr × Expr) := do
  let program ← withTransparency .all (whnf program)
  IO.eprintln s!"CSE node {program.getAppFn.constName!}"
  let width := mkNatLit 64
  let inst ← synthInstance (← mkAppM ``NeZero #[width])
  let function := mkApp2 (mkConst ``WordCse.wordCse) width inst
  let knowledge := mkConst ``WordCse.Knowledge
  let progType ← inferType program
  let fst := mkApp2 (mkConst ``Prod.fst [Level.zero, Level.zero]) knowledge progType
  let snd := mkApp2 (mkConst ``Prod.snd [Level.zero, Level.zero]) knowledge progType
  let call := mkApp2 function data program
  let (result, proof) ← if program.isAppOfArity ``WordLangProgHOL.seq 3 then do
    let args := program.getAppArgs
    let (first, hfirst) ← solveCse args[1]! data
    let middle ← withTransparency .all (whnf (mkApp fst first))
    let (second, hsecond) ← solveCse args[2]! middle
    let final := mkApp fst second
    let left := mkApp snd first
    let right := mkApp snd second
    let body := mkApp3 (mkConst ``WordLangProgHOL.seq [Level.zero]) (mkApp (mkConst ``BitVec) width) left right
    let result := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) knowledge progType final body
    let proof := mkAppN (mkConst ``cse_seq_split) #[args[1]!, args[2]!, data, first, second, hfirst, hsecond]
    pure (result, proof)
  else do
    let reduced ← Lean.Meta.Tactic.Cbv.cbvEntry call
    let proof ← match reduced with
      | .rfl .. => mkEqRefl call
      | .step _ p .. => pure p
    pure (reduced.getResultExpr call, proof)
  let name ← mkFreshUserName ((← getCurrNamespace) ++ `cseStep)
  addDecl (.thmDecl { name, levelParams := [], type := ← mkEq call result, value := proof })
  IO.eprintln s!"CSE checked {name}"
  return (result, mkConst name)

open Lean Meta Elab Command in
elab "wave8_certified_cse " id:ident " := " value:term : command => do
  liftTermElabM do
    let expression ← Term.elabTerm value none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    let data ← Term.elabTerm (← `(WordCse.emptyData)) none
    let (result, proof) ← solveCse expression data
    let body ← withTransparency .all (whnf (← mkAppM ``Prod.snd #[result]))
    let name := (← getCurrNamespace) ++ id.getId
    let type ← inferType expression
    addDecl (.defnDecl {
      name, levelParams := [], type, value := body
      hints := .regular (getMaxHeight (← getEnv) body + 1)
      safety := .safe })
    let project ← Term.elabTerm (← `(@Prod.snd WordCse.Knowledge (WordLangProgHOL (BitVec 64)))) none
    let proof ← mkAppM ``congrArg #[project, proof]
    let lhs ← mkAppM ``WordCse.wordCommonSubexpElim #[expression]
    let eqType ← mkEq lhs (mkConst name)
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := eqType, value := proof })
    logInfo m!"Staged CSE {name}"

end InitECandidate.Solver.Wave8Stage
