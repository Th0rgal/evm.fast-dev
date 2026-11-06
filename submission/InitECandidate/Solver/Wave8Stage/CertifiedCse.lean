import InitECandidate.Solver.Wave8Stage.PrefixChecks.Support

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend

theorem eq_false_true : (false = true) = False := by decide
theorem eq_true_false : (true = false) = False := by decide
theorem eq_true_true : (true = true) = True := by decide
theorem eq_false_false : (false = false) = True := by decide
theorem and_false_left (q : Prop) : (False ∧ q) = False := by simp
theorem and_true_left (q : Prop) : (True ∧ q) = q := by simp
theorem and_false_right (p : Prop) : (p ∧ False) = False := by simp
theorem and_true_right (p : Prop) : (p ∧ True) = p := by simp
theorem or_false_left (q : Prop) : (False ∨ q) = q := by simp
theorem or_true_left (q : Prop) : (True ∨ q) = True := by simp
theorem or_false_right (p : Prop) : (p ∨ False) = p := by simp
theorem or_true_right (p : Prop) : (p ∨ True) = True := by simp
theorem not_true_eq : (¬ True) = False := by simp
theorem not_false_eq : (¬ False) = True := by simp
theorem list_mem_nil {α : Type _} (a : α) : List.Mem a ([] : List α) = False :=
  propext (Iff.intro (fun h => nomatch h) False.elim)
theorem list_mem_cons {α : Type _} (a b : α) (l : List α) : List.Mem a (b :: l) = (a = b ∨ List.Mem a l) :=
  propext (Iff.intro
    (fun h => match h with | .head _ => Or.inl rfl | .tail _ h => Or.inr h)
    (fun h => match h with | Or.inl e => e ▸ .head _ | Or.inr h => .tail _ h))

attribute [cbv_eval] eq_false_true eq_true_false eq_true_true eq_false_false
  and_false_left and_true_left and_false_right and_true_right
  or_false_left or_true_left or_false_right or_true_right
  not_true_eq not_false_eq list_mem_nil list_mem_cons

def plugCseLeft {width : Nat} (P chunk : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match chunk with
  | .seq s1 s2 => .seq (plugCseLeft P s1) s2
  | _ => P

def wordCseChunk {width : Nat} [NeZero width]
    (d0 : WordCse.Knowledge) (outP : WordLangProgHOL (BitVec width))
    (chunk : WordLangProgHOL (BitVec width)) :
    WordCse.Knowledge × WordLangProgHOL (BitVec width) :=
  match chunk with
  | .seq s1 s2 =>
    let (d1, s1') := wordCseChunk d0 outP s1
    let (d2, s2') := WordCse.wordCse d1 s2
    (d2, .seq s1' s2')
  | _ => (d0, outP)

theorem wordCse_plugLeft_eq (P chunk : WordLangProgHOL (BitVec 64))
    (data d0 : WordCse.Knowledge) (outP : WordLangProgHOL (BitVec 64))
    (hP : WordCse.wordCse data P = (d0, outP)) :
    WordCse.wordCse data (plugCseLeft P chunk) = wordCseChunk d0 outP chunk := by
  cases chunk <;> try (simpa [plugCseLeft, wordCseChunk] using hP)
  case seq s1 s2 =>
    have ih1 := wordCse_plugLeft_eq P s1 data d0 outP hP
    simp only [plugCseLeft, WordCse.wordCse, ih1, wordCseChunk]

theorem wordCse_plugLeft_step (P chunk : WordLangProgHOL (BitVec 64))
    (data d0 outData : WordCse.Knowledge) (outP outRes : WordLangProgHOL (BitVec 64))
    (hP : WordCse.wordCse data P = (d0, outP))
    (hChunk : wordCseChunk d0 outP chunk = (outData, outRes)) :
    WordCse.wordCse data (plugCseLeft P chunk) = (outData, outRes) := by
  rw [wordCse_plugLeft_eq P chunk data d0 outP hP, hChunk]

theorem cse_seq_split_pair (left right outLeft outRight : WordLangProgHOL (BitVec 64))
    (data midData outData : WordCse.Knowledge)
    (hfirst : WordCse.wordCse data left = (midData, outLeft))
    (hsecond : WordCse.wordCse midData right = (outData, outRight)) :
    WordCse.wordCse data (.seq left right) =
      (outData, .seq outLeft outRight) := by
  simp only [WordCse.wordCse, hfirst, hsecond]

theorem cse_finalize (prog outProg : WordLangProgHOL (BitVec 64))
    (outData : WordCse.Knowledge)
    (h : WordCse.wordCse WordCse.emptyData prog = (outData, outProg)) :
    WordCse.wordCommonSubexpElim prog = outProg := by
  simp only [WordCse.wordCommonSubexpElim, h]

open Lean Meta Elab Command in
private partial def cleanCseProg (e : Expr) : MetaM Expr := do
  let e ← withTransparency .all (whnf e)
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let s1 ← cleanCseProg args[1]!
    let s2 ← cleanCseProg args[2]!
    return mkApp3 e.getAppFn args[0]! s1 s2
  else
    return e

open Lean Meta Elab Command in
private partial def countCseLeaves (e : Expr) : Nat :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    countCseLeaves args[1]! + countCseLeaves args[2]!
  else
    1

open Lean Meta Elab Command in
private partial def collectLeftSpine (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let acc := collectLeftSpine args[1]! acc
    acc.push args[2]!
  else
    acc.push e

open Lean Meta Elab Command in
private partial def evalCseSimp (functionS fstS seqFn bv64 : Expr) (e : Expr) (curData : Expr) :
    Sym.Simp.SimpM (Expr × Expr) := do
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let (midData, out1) ← evalCseSimp functionS fstS seqFn bv64 args[1]! curData
    let (outData, out2) ← evalCseSimp functionS fstS seqFn bv64 args[2]! midData
    return (outData, mkApp3 seqFn bv64 out1 out2)
  else
    let eU ← liftMetaM <| Sym.unfoldReducible e
    let eS ← Sym.shareCommon eU
    let tJ ← Sym.Internal.mkAppS₂ functionS curData eS
    let rJ ← Sym.Simp.simp tJ
    let outJ := rJ.getResultExpr tJ
    let pOut := outJ.getAppArgs[3]!
    let fstApp ← Sym.Internal.mkAppS fstS outJ
    let resFst ← Sym.Simp.simp fstApp
    let nextData := resFst.getResultExpr fstApp
    return (nextData, pOut)

open Lean Meta Elab Command in
private partial def solveLeftSpineChunks (currNs : Name) (functionS chunkFn fstS seqFn skipExpr bv64 prodMk : Expr)
    (items : Array Expr) (inData : Expr) : Sym.Simp.SimpM (Expr × Expr × Expr × Expr) := do
  let mut curData := inData
  let mut accInProg := items[0]!
  let (d0, out0) ← evalCseSimp functionS fstS seqFn bv64 items[0]! curData
  curData := d0
  let mut accOutProg := out0
  let mut idx := 1
  -- Accumulate first chunk up to ~500 leaves
  let mut leavesInChunk := countCseLeaves items[0]!
  while idx < items.size && leavesInChunk + countCseLeaves items[idx]! <= 500 do
    let item := items[idx]!
    let (dNext, outItem) ← evalCseSimp functionS fstS seqFn bv64 item curData
    curData := dNext
    accInProg := mkApp3 seqFn bv64 accInProg item
    accOutProg := mkApp3 seqFn bv64 accOutProg outItem
    leavesInChunk := leavesInChunk + countCseLeaves item
    idx := idx + 1
  let lhs0 := mkApp2 functionS inData accInProg
  let rhs0 := mkApp2 prodMk curData accOutProg
  let thm0 ← liftMetaM <| mkFreshUserName (currNs ++ `cseChunk)
  let rfl0 ← liftMetaM <| mkEqRefl rhs0
  liftMetaM <| addDecl (.thmDecl {
    name := thm0, levelParams := [],
    type := ← liftMetaM <| mkEq lhs0 rhs0, value := rfl0 })
  let mut accProof := mkConst thm0
  while idx < items.size do
    let prevData := curData
    let prevInProg := accInProg
    let prevOutProg := accOutProg
    let mut chunkTerm := skipExpr
    let mut chunkLeaves := 0
    while idx < items.size && (chunkLeaves == 0 || chunkLeaves + countCseLeaves items[idx]! <= 500) do
      let item := items[idx]!
      let (dNext, outItem) ← evalCseSimp functionS fstS seqFn bv64 item curData
      curData := dNext
      chunkTerm := mkApp3 seqFn bv64 chunkTerm item
      accInProg := mkApp3 seqFn bv64 accInProg item
      accOutProg := mkApp3 seqFn bv64 accOutProg outItem
      chunkLeaves := chunkLeaves + countCseLeaves item
      idx := idx + 1
    let chunkLhs := mkApp3 chunkFn prevData prevOutProg chunkTerm
    let chunkRhs := mkApp2 prodMk curData accOutProg
    let chunkThm ← liftMetaM <| mkFreshUserName (currNs ++ `cseChunk)
    let chunkRfl ← liftMetaM <| mkEqRefl chunkRhs
    liftMetaM <| addDecl (.thmDecl {
      name := chunkThm, levelParams := [],
      type := ← liftMetaM <| mkEq chunkLhs chunkRhs, value := chunkRfl })
    let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `cseStep)
    let stepLhs := mkApp2 functionS inData accInProg
    let stepVal := mkAppN (mkConst ``wordCse_plugLeft_step)
      #[prevInProg, chunkTerm, inData, prevData, curData, prevOutProg, accOutProg, accProof, mkConst chunkThm]
    liftMetaM <| addDecl (.thmDecl {
      name := stepThm, levelParams := [],
      type := ← liftMetaM <| mkEq stepLhs chunkRhs, value := stepVal })
    accProof := mkConst stepThm
  return (accInProg, curData, accOutProg, accProof)

open Lean Meta Elab Command in
private partial def solveCseExact
    (currNs : Name)
    (function functionS fstS seqFn bv64 prodMk : Expr)
    (e : Expr) (inData : Expr) (forceSeal : Bool) :
    Sym.Simp.SimpM (Expr × Expr × Expr × Nat) := do
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let s1 := args[1]!
    let s2 := args[2]!
    let (midData, out1, prf1, cnt1) ←
      solveCseExact currNs function functionS fstS seqFn bv64 prodMk s1 inData false
    let (outData, out2, prf2, cnt2) ←
      solveCseExact currNs function functionS fstS seqFn bv64 prodMk s2 midData false
    let outProg := mkApp3 seqFn bv64 out1 out2
    let prf := mkAppN (mkConst ``cse_seq_split_pair)
      #[s1, s2, out1, out2, inData, midData, outData, prf1, prf2]
    let totalCnt := cnt1 + cnt2
    if forceSeal || totalCnt >= 200 then
      let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `cseStep)
      let lhs := mkApp2 function inData e
      let rhs := mkApp2 prodMk outData outProg
      liftMetaM <| addDecl (.thmDecl {
        name := stepThm, levelParams := [],
        type := ← liftMetaM <| mkEq lhs rhs, value := prf })
      return (outData, outProg, mkConst stepThm, 0)
    else
      return (outData, outProg, prf, totalCnt)
  else
    let eU ← liftMetaM <| Sym.unfoldReducible e
    let eS ← Sym.shareCommon eU
    let tJ ← Sym.Internal.mkAppS₂ functionS inData eS
    let rJ ← Sym.Simp.simp tJ
    let outJ := rJ.getResultExpr tJ
    let pOut := outJ.getAppArgs[3]!
    let fstApp ← Sym.Internal.mkAppS fstS outJ
    let resFst ← Sym.Simp.simp fstApp
    let nextData := resFst.getResultExpr fstApp
    let rhs := mkApp2 prodMk nextData pOut
    let rflPrf ← liftMetaM <| mkEqRefl rhs
    if forceSeal then
      let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `cseLeaf)
      let lhs := mkApp2 function inData e
      liftMetaM <| addDecl (.thmDecl {
        name := stepThm, levelParams := [],
        type := ← liftMetaM <| mkEq lhs rhs, value := rflPrf })
      return (nextData, pOut, mkConst stepThm, 0)
    else
      return (nextData, pOut, rflPrf, 1)

open Lean Meta Elab Command in
elab "wave8_certified_cse " id:ident " := " value:term : command => do
  liftTermElabM do
    let expression ← Term.elabTerm value none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    let cleaned ← if expression.isConst then
      pure (← getConstInfo expression.constName!).value!
    else
      cleanCseProg expression
    let data := mkConst ``WordCse.emptyData
    let width := mkNatLit 64
    let inst ← synthInstance (← mkAppM ``NeZero #[width])
    let function := mkApp2 (mkConst ``WordCse.wordCse) width inst
    let knowledge := mkConst ``WordCse.Knowledge
    let bv64 := mkApp (mkConst ``BitVec) width
    let progType := mkApp (mkConst ``WordLangProgHOL [Level.zero]) bv64
    let fst := mkApp2 (mkConst ``Prod.fst [Level.zero, Level.zero]) knowledge progType
    let seqFn := mkConst ``WordLangProgHOL.seq [Level.zero]
    let prodMk := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) knowledge progType

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

    let dataU ← Sym.unfoldReducible data
    let functionU ← Sym.unfoldReducible function
    let fstU ← Sym.unfoldReducible fst
    let currNs ← getCurrNamespace

    let (finalData, finalOutProg, finalProof, _) ← liftMetaM <| (Sym.withoutShareCommonChecks do
      let dataS ← Sym.shareCommon dataU
      let functionS ← Sym.shareCommon functionU
      let fstS ← Sym.shareCommon fstU
      let simpAct : Sym.Simp.SimpM (Expr × Expr × Expr × Nat) :=
        solveCseExact currNs functionU functionS fstS seqFn bv64 prodMk cleaned dataS true
      simpAct.run' methods config).run

    let name := currNs ++ id.getId
    addDecl (.defnDecl {
      name, levelParams := [], type := progType, value := finalOutProg
      hints := .regular (getMaxHeight (← getEnv) finalOutProg + 1)
      safety := .safe })
    let lhs ← mkAppM ``WordCse.wordCommonSubexpElim #[expression]
    let eqType ← mkEq lhs (mkConst name)
    let eqProof := mkAppN (mkConst ``cse_finalize) #[cleaned, finalOutProg, finalData, finalProof]
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := eqType, value := eqProof })
    logInfo m!"Staged CSE {name}"

end InitECandidate.Solver.Wave8Stage
