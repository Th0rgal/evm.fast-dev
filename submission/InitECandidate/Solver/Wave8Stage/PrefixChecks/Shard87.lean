import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87PreAlloc

/-! One original compiler entry, independently checked through named passes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

open Lean Meta Elab Command in
elab "wave8_shard87_check" : command => do
  liftTermElabM do
    let currNs ← getCurrNamespace
    let mut simprocs ← Lean.Meta.Tactic.Cbv.getCbvSimprocs
    simprocs := simprocs.erase `wave8Project |>.erase `wave8Beta |>.erase `wave8Map
    let opts ← getOptions
    let config : Sym.Simp.Config := { maxSteps := Lean.Option.get opts Lean.Meta.Tactic.Cbv.cbv.maxSteps }
    let cbvEntryVal := (← getConstInfo ``Lean.Meta.Tactic.Cbv.cbvEntry).value!
    let mut mkMethodsName := Name.anonymous
    for c in cbvEntryVal.getUsedConstants do
      if c.toString.endsWith "mkCbvMethods" then mkMethodsName := c
    let methodsVal ← unsafe evalConst (Lean.Meta.Tactic.Cbv.CbvSimprocs → Sym.Simp.Methods) mkMethodsName
    let methods := methodsVal simprocs

    let checkLhs ← Term.elabTerm (← `(WordCostCheck.checkProgram ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal 20000 $(mkIdent (currNs ++ `prefixProgram)) (ConcreteWordCostAnnotations.summaries (some $(mkIdent (currNs ++ `name)))))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let checkLhs ← instantiateMVars checkLhs
    let checkU ← Sym.unfoldReducible checkLhs
    let (resExpr, checkPrf) ← (Sym.withoutShareCommonChecks do
      let checkS ← Sym.shareCommon checkU
      let act : Sym.Simp.SimpM (Expr × Expr) := do
        let r ← Sym.Simp.simp checkS
        let e' := r.getResultExpr checkS
        let p ← match r with
          | .rfl .. => liftMetaM <| mkEqRefl e'
          | .step _ p .. => pure p
        return (e', p)
      act.run' methods config).run
    let checkEqType ← mkEq checkLhs resExpr
    addDecl (.thmDecl {
      name := currNs ++ `checkedProgram, levelParams := [], type := checkEqType, value := checkPrf })

wave8_shard87_check

theorem checkedEntry : ConcreteWordCheckInput.check entry = true := by
  unfold ConcreteWordCheckInput.check
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq]
  exact checkedProgram

wave8_list_spine entries := (ConcreteCompilerWord.source.drop 87).take 1

theorem checked : entries.all ConcreteWordCheckInput.check = true := by
  wave8_all [checkedEntry]

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
