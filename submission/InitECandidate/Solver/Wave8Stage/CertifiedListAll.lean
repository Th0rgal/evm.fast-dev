import InitECandidate.Solver.Wave8Stage.CertifiedReduction

namespace InitECandidate.Solver.Wave8Stage.CertifiedListAll

theorem cons {α : Type} (f : α → Bool) (head : α) (tail : List α)
    (first : f head = true) (rest : tail.all f = true) :
    (head :: tail).all f = true := by
  exact Bool.and_eq_true_iff.mpr ⟨first,rest⟩

end InitECandidate.Solver.Wave8Stage.CertifiedListAll

open Lean Meta Elab Tactic

/-- Assemble previously checked element certificates. The tactic traverses
only the literal list spine; it never evaluates the predicate or the other
program bodies while selecting one element. -/
elab "wave8_all " "[" certificates:term,* "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_,lhs,rhs) := target.eq? | throwError "Expected a Boolean list-all equation"
  unless lhs.isAppOfArity ``List.all 3 && rhs.isConstOf ``Bool.true do
    throwError "Expected `list.all predicate = true`"
  let arguments := lhs.getAppArgs
  let predicate := arguments[2]!
  let mut current ← withTransparency .all (whnf arguments[1]!)
  let mut entries : Array (Expr × Expr) := #[]
  while current.isAppOfArity ``List.cons 3 do
    let parts := current.getAppArgs
    entries := entries.push (parts[1]!,parts[2]!)
    current ← withTransparency .all (whnf parts[2]!)
  unless current.isAppOfArity ``List.nil 1 do
    throwError "The list did not reduce to a literal spine"
  let terms := certificates.getElems
  unless terms.size = entries.size do
    throwError "Expected {entries.size} element certificates, received {terms.size}"
  let mut proof ← mkEqRefl (mkConst ``Bool.true)
  for i in [:entries.size] do
    let j := entries.size - 1 - i
    let (head,tail) := entries[j]!
    let expected ← mkEq (mkApp predicate head) (mkConst ``Bool.true)
    let first ← Term.elabTerm terms[j]! (some expected)
    Term.synthesizeSyntheticMVarsNoPostponing
    let first ← instantiateMVars first
    if first.hasSorry then
      throwError "Every element requires a successfully elaborated proof"
    proof ← mkAppM ``InitECandidate.Solver.Wave8Stage.CertifiedListAll.cons
      #[predicate,head,tail,first,proof]
  goal.assign proof
  replaceMainGoal []
