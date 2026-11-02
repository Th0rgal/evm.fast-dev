import InitECandidate.Solver.Wave8Stage.PrefixChecks.Support

/-! Staged certified reduction of `removeDeadProg` along the `seq` spine. -/
set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage
open Flapjack

def combineDeadSeq {width : Nat} (s1' s2' : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match s1', s2' with
  | .skip, _ => s2'
  | _, .skip => s1'
  | _, _ => .seq s1' s2'

theorem removeDead_seq_split {width : Nat} [NeZero width]
    (s1 s2 : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet))
    (r2 r1 : WordLangProgHOL (BitVec width) × NumSet × List WordStoreHOL)
    (h2 : WordAlloc.removeDead s2 live nlive lt = r2)
    (h1 : WordAlloc.removeDead s1 r2.2.1 r2.2.2 lt = r1) :
    WordAlloc.removeDead (.seq s1 s2) live nlive lt =
      (combineDeadSeq r1.1 r2.1, r1.2.1, r1.2.2) := by
  rcases r2 with ⟨s2', s2live, s2nlive⟩
  rcases r1 with ⟨s1', s1live, s1nlive⟩
  simp only [WordAlloc.removeDead, h2, combineDeadSeq]
  rw [show (s2', s2live, s2nlive).2.1 = s2live from rfl,
      show (s2', s2live, s2nlive).2.2 = s2nlive from rfl] at h1
  rw [h1]
  rfl

open Lean Meta Elab Command in
private partial def countSeqExpr (e : Expr) : Nat :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    1 + countSeqExpr args[1]! + countSeqExpr args[2]!
  else 0

open Lean Meta Elab Command in
private partial def solveRemoveDeadSubtree (e live nlive lt : Expr) : MetaM (Expr × Expr) := do
  if e.isAppOfArity ``WordLangProgHOL.seq 3 && countSeqExpr e > 25 then
    let args := e.getAppArgs
    let s1 := args[1]!
    let s2 := args[2]!
    let (r2, h2) ← solveRemoveDeadSubtree s2 live nlive lt
    let r2_2 ← mkAppM ``Prod.snd #[r2]
    let r2_live ← withTransparency .all (whnf (← mkAppM ``Prod.fst #[r2_2]))
    let r2_nlive ← withTransparency .all (whnf (← mkAppM ``Prod.snd #[r2_2]))
    let (r1, h1) ← solveRemoveDeadSubtree s1 r2_live r2_nlive lt
    let r1_prog ← mkAppM ``Prod.fst #[r1]
    let r2_prog ← mkAppM ``Prod.fst #[r2]
    let comb ← withTransparency .all (whnf (← mkAppM ``combineDeadSeq #[r1_prog, r2_prog]))
    let r1_2 ← mkAppM ``Prod.snd #[r1]
    let r1_live ← withTransparency .all (whnf (← mkAppM ``Prod.fst #[r1_2]))
    let r1_nlive ← withTransparency .all (whnf (← mkAppM ``Prod.snd #[r1_2]))
    let resTuple ← mkAppM ``Prod.mk #[comb, ← mkAppM ``Prod.mk #[r1_live, r1_nlive]]
    let stepPrf ← mkAppM ``removeDead_seq_split #[s1, s2, live, nlive, lt, r2, r1, h2, h1]
    return (resTuple, stepPrf)
  else
    let call ← mkAppM ``WordAlloc.removeDead #[e, live, nlive, lt]
    let cbvRes ← Lean.Meta.Tactic.Cbv.cbvEntry call
    let reduced := cbvRes.getResultExpr call
    let prf ← match cbvRes with
      | .rfl .. => mkEqRefl call
      | .step _ p .. => pure p
    return (reduced, prf)

end InitECandidate.Solver.Wave8Stage

open Lean Meta Elab Command Flapjack InitECandidate.Solver.Wave8Stage in
elab "wave8_certified_remove_dead " id:ident " := " progTerm:term : command => do
  liftTermElabM do
    let progExpr ← Term.elabTerm progTerm none
    Term.synthesizeSyntheticMVarsNoPostponing
    let progExpr ← instantiateMVars progExpr
    let val ← withTransparency .all (whnf progExpr)
    let lnExpr ← Term.elabTerm (← `((.ln : NumSet))) none
    let nilStore ← Term.elabTerm (← `(([] : List WordStoreHOL))) none
    let nilLt ← Term.elabTerm (← `(([] : List (NumSet × NumSet)))) none
    let (resTuple, hTree) ← solveRemoveDeadSubtree val lnExpr nilStore nilLt
    let deadProg ← withTransparency .all (whnf (← mkAppM ``Prod.fst #[resTuple]))
    let name := (← getCurrNamespace) ++ id.getId
    let type ← inferType progExpr
    addDecl (.defnDecl {
      name, levelParams := [], type, value := deadProg
      hints := .regular (getMaxHeight (← getEnv) deadProg + 1)
      safety := .safe })
    let lhs ← mkAppM ``WordAlloc.removeDeadProg #[progExpr]
    let eqType ← mkEq lhs (mkConst name)
    let fstFn ← Term.elabTerm (← `(@Prod.fst (WordLangProgHOL (BitVec 64)) (NumSet × List WordStoreHOL))) none
    let prf ← mkAppM ``congrArg #[fstFn, hTree]
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := eqType, value := prf })
    logInfo m!"Staged removeDeadProg {name}"
