import InitECandidate.Solver.Wave8Stage.CertifiedCse
import InitECandidate.Solver.Wave8Stage.CertifiedRemoveDead

/-! Shared chunked post-SSA and pre-allocation passes (`removeDeadProg`, `copyProp`,
`threeToTwoRegProg`, `removeUnreach`, `checkProgram`) for Wave 8 Stage 5 shards. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

def copyPropChunk {width : Nat} [NeZero width]
    (outP : WordLangProgHOL (BitVec width)) (cs0 : WordCopy.CopyState)
    (chunk : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) × WordCopy.CopyState :=
  match chunk with
  | .seq s1 s2 =>
    let (s1', cs1) := copyPropChunk outP cs0 s1
    let (s2', cs2) := WordCopy.copyPropProg s2 cs1
    (.seq s1' s2', cs2)
  | _ => (outP, cs0)

theorem copyProp_plugLeft_eq (P chunk : WordLangProgHOL (BitVec 64))
    (cs cs0 : WordCopy.CopyState) (outP : WordLangProgHOL (BitVec 64))
    (hP : WordCopy.copyPropProg P cs = (outP, cs0)) :
    WordCopy.copyPropProg (plugCseLeft P chunk) cs = copyPropChunk outP cs0 chunk := by
  cases chunk <;> try (simpa [plugCseLeft, copyPropChunk] using hP)
  case seq s1 s2 =>
    have ih1 := copyProp_plugLeft_eq P s1 cs cs0 outP hP
    simp only [plugCseLeft, WordCopy.copyPropProg, ih1, copyPropChunk]

theorem copyProp_plugLeft_step (P chunk : WordLangProgHOL (BitVec 64))
    (cs cs0 outCs : WordCopy.CopyState) (outP outRes : WordLangProgHOL (BitVec 64))
    (hP : WordCopy.copyPropProg P cs = (outP, cs0))
    (hChunk : copyPropChunk outP cs0 chunk = (outRes, outCs)) :
    WordCopy.copyPropProg (plugCseLeft P chunk) cs = (outRes, outCs) := by
  rw [copyProp_plugLeft_eq P chunk cs cs0 outP hP, hChunk]

theorem copyProp_seq_split_pair (left right outLeft outRight : WordLangProgHOL (BitVec 64))
    (cs midCs outCs : WordCopy.CopyState)
    (hfirst : WordCopy.copyPropProg left cs = (outLeft, midCs))
    (hsecond : WordCopy.copyPropProg right midCs = (outRight, outCs)) :
    WordCopy.copyPropProg (.seq left right) cs =
      (.seq outLeft outRight, outCs) := by
  simp only [WordCopy.copyPropProg, hfirst, hsecond]

theorem copyProp_finalize (prog outProg : WordLangProgHOL (BitVec 64))
    (outCs : WordCopy.CopyState)
    (h : WordCopy.copyPropProg prog WordCopy.emptyEq = (outProg, outCs)) :
    WordCopy.copyProp prog = outProg := by
  simp only [WordCopy.copyProp, h]

def plugDeadRight {width : Nat} (chunk S : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match chunk with
  | .seq s1 s2 => .seq s1 (plugDeadRight s2 S)
  | _ => S

def removeDeadChunk {width : Nat} [NeZero width]
    (chunk : WordLangProgHOL (BitVec width))
    (rS : WordLangProgHOL (BitVec width) × NumSet × List WordStoreHOL)
    (lt : List (NumSet × NumSet)) :
    WordLangProgHOL (BitVec width) × NumSet × List WordStoreHOL :=
  match chunk with
  | .seq s1 s2 =>
    let (s2', s2live, s2nlive) := removeDeadChunk s2 rS lt
    let (s1', s1live, s1nlive) := WordAlloc.removeDead s1 s2live s2nlive lt
    (combineDeadSeq s1' s2', s1live, s1nlive)
  | _ => rS

theorem removeDead_plugRight_eq (chunk S : WordLangProgHOL (BitVec 64))
    (live : NumSet) (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet))
    (rS : WordLangProgHOL (BitVec 64) × NumSet × List WordStoreHOL)
    (hS : WordAlloc.removeDead S live nlive lt = rS) :
    WordAlloc.removeDead (plugDeadRight chunk S) live nlive lt = removeDeadChunk chunk rS lt := by
  cases chunk <;> try (simpa [plugDeadRight, removeDeadChunk] using hS)
  case seq s1 s2 =>
    have ih2 := removeDead_plugRight_eq s2 S live nlive lt rS hS
    rcases hChunk : removeDeadChunk s2 rS lt with ⟨s2', s2live, s2nlive⟩
    rcases h1 : WordAlloc.removeDead s1 s2live s2nlive lt with ⟨s1', s1live, s1nlive⟩
    simp only [plugDeadRight, WordAlloc.removeDead, ih2, removeDeadChunk, hChunk, h1, combineDeadSeq]
    cases s1' <;> cases s2' <;> rfl

theorem removeDead_plugRight_step (chunk S : WordLangProgHOL (BitVec 64))
    (live : NumSet) (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet))
    (rS rNext : WordLangProgHOL (BitVec 64) × NumSet × List WordStoreHOL)
    (hS : WordAlloc.removeDead S live nlive lt = rS)
    (hChunk : removeDeadChunk chunk rS lt = rNext) :
    WordAlloc.removeDead (plugDeadRight chunk S) live nlive lt = rNext := by
  rw [removeDead_plugRight_eq chunk S live nlive lt rS hS, hChunk]

def removeDeadLeftChunk {width : Nat} [NeZero width]
    (outP : WordLangProgHOL (BitVec width))
    (chunk : WordLangProgHOL (BitVec width))
    (live : NumSet) (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet)) :
    WordLangProgHOL (BitVec width) × NumSet × List WordStoreHOL :=
  match chunk with
  | .seq s1 s2 =>
    let (s2', s2live, s2nlive) := WordAlloc.removeDead s2 live nlive lt
    let (s1', midLive, midNlive) := removeDeadLeftChunk outP s1 s2live s2nlive lt
    (combineDeadSeq s1' s2', midLive, midNlive)
  | _ => (outP, live, nlive)

theorem removeDead_plugLeft_step (P chunk : WordLangProgHOL (BitVec 64))
    (outP outRes : WordLangProgHOL (BitVec 64))
    (live midLive outLive : NumSet)
    (nlive midNlive outNlive : List WordStoreHOL)
    (lt : List (NumSet × NumSet))
    (hChunk : removeDeadLeftChunk outP chunk live nlive lt = (outRes, midLive, midNlive))
    (hP : WordAlloc.removeDead P midLive midNlive lt = (outP, outLive, outNlive)) :
    WordAlloc.removeDead (plugCseLeft P chunk) live nlive lt = (outRes, outLive, outNlive) := by
  cases chunk <;> try (
    simp only [removeDeadLeftChunk] at hChunk
    injection hChunk with hRes hPair
    injection hPair with hmLive hmNlive
    subst hRes hmLive hmNlive
    simpa [plugCseLeft] using hP)
  case seq s1 s2 =>
    simp only [removeDeadLeftChunk] at hChunk
    rcases h2 : WordAlloc.removeDead s2 live nlive lt with ⟨s2', s2live, s2nlive⟩
    rcases h1 : removeDeadLeftChunk outP s1 s2live s2nlive lt with ⟨s1', mLive, mNlive⟩
    rw [h2, h1] at hChunk
    injection hChunk with hRes hPair
    injection hPair with hmLive hmNlive
    subst hRes hmLive hmNlive
    have ih := removeDead_plugLeft_step P s1 outP s1' s2live mLive outLive s2nlive mNlive outNlive lt h1 hP
    simp only [plugCseLeft, WordAlloc.removeDead, h2, ih, combineDeadSeq]
    cases s1' <;> cases s2' <;> rfl

theorem combineDeadSeq_right_skip (s1 : WordLangProgHOL (BitVec 64)) :
    combineDeadSeq s1 .skip = s1 := by
  cases s1 <;> rfl

theorem combineDeadSeq_left_skip (s2 : WordLangProgHOL (BitVec 64)) :
    combineDeadSeq .skip s2 = s2 := rfl

theorem combineDeadSeq_seq_left (a b s2 : WordLangProgHOL (BitVec 64))
    (h : combineDeadSeq (.seq .skip .skip) s2 = .seq (.seq .skip .skip) s2) :
    combineDeadSeq (.seq a b) s2 = .seq (.seq a b) s2 := by
  cases s2 <;> first | rfl | cases h

theorem removeDead_seq_split_pair (s1 s2 out1 out2 outComb : WordLangProgHOL (BitVec 64))
    (live midLive outLive : NumSet)
    (nlive midNlive outNlive : List WordStoreHOL)
    (lt : List (NumSet × NumSet))
    (h2 : WordAlloc.removeDead s2 live nlive lt = (out2, midLive, midNlive))
    (h1 : WordAlloc.removeDead s1 midLive midNlive lt = (out1, outLive, outNlive))
    (hComb : combineDeadSeq out1 out2 = outComb) :
    WordAlloc.removeDead (.seq s1 s2) live nlive lt = (outComb, outLive, outNlive) := by
  rw [removeDead_seq_split s1 s2 live nlive lt (out2, midLive, midNlive) (out1, outLive, outNlive) h2 h1, hComb]

theorem removeDead_finalize (prog outProg : WordLangProgHOL (BitVec 64))
    (live : NumSet) (nlive : List WordStoreHOL)
    (h : WordAlloc.removeDead prog .ln [] [] = (outProg, live, nlive)) :
    WordAlloc.removeDeadProg prog = outProg := by
  unfold WordAlloc.removeDeadProg
  rw [h]

theorem preAllocation_step
    (arity : Nat)
    (w s : WordLangProgHOL (BitVec 64)) (t : Nat)
    (sel ssa dead com cop two unr pref : WordLangProgHOL (BitVec 64))
    (h1 : WordSimp.compileExp w = s)
    (h2 : maxVarHOL s + 1 = t)
    (h3 : WordInst.instSelectExecutable riscvConfig t s = sel)
    (h4 : WordAlloc.fullSsaCcTrans arity sel = ssa)
    (h5 : WordAlloc.removeDeadProg ssa = dead)
    (h6 : WordCse.wordCommonSubexpElim dead = com)
    (h7 : WordCopy.copyProp com = cop)
    (h8 : WordInst.threeToTwoRegProg riscvConfig.twoRegArith cop = two)
    (h9 : WordUnreach.removeUnreach two = unr)
    (h10 : WordAlloc.removeDeadProg unr = pref) :
    WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith arity w = pref := by
  simp only [WordCostCompilerControl.preAllocation, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

open Lean Meta Elab Command in
private partial def countLeaves (e : Expr) : Nat :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    countLeaves args[1]! + countLeaves args[2]!
  else
    1

open Lean Meta Elab Command in
private partial def collectLeftSpine50 (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    if countLeaves args[2]! <= 50 then
      let acc := collectLeftSpine50 args[1]! acc
      acc.push args[2]!
    else
      acc.push e
  else
    acc.push e

open Lean Meta Elab Command in
private partial def collectLeftSpine (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    if countLeaves args[2]! <= 400 then
      let acc := collectLeftSpine args[1]! acc
      acc.push args[2]!
    else
      acc.push e
  else
    acc.push e

open Lean Meta Elab Command in
private partial def collectRightSpine (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    collectRightSpine args[2]! (acc.push args[1]!)
  else
    acc.push e

open Lean Meta Elab Command in
private partial def evalRemoveDeadSimp (rdFnS nilLtS seqFn bv64 : Expr) (e : Expr) (curLive curNlive : Expr) :
    Sym.Simp.SimpM (Expr × Expr × Expr) := do
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let (s2', s2live, s2nlive) ← evalRemoveDeadSimp rdFnS nilLtS seqFn bv64 args[2]! curLive curNlive
    let (s1', s1live, s1nlive) ← evalRemoveDeadSimp rdFnS nilLtS seqFn bv64 args[1]! s2live s2nlive
    let prog :=
      if s1'.isAppOfArity ``WordLangProgHOL.skip 1 then s2'
      else if s2'.isAppOfArity ``WordLangProgHOL.skip 1 then s1'
      else mkApp3 seqFn bv64 s1' s2'
    return (prog, s1live, s1nlive)
  else
    let eU ← liftMetaM <| Sym.unfoldReducible e
    let eS ← Sym.shareCommon eU
    let c1 ← Sym.Internal.mkAppS₂ rdFnS eS curLive
    let c2 ← Sym.Internal.mkAppS₂ c1 curNlive nilLtS
    let r ← Sym.Simp.simp c2
    let out := r.getResultExpr c2
    let pOut := out.getAppArgs[2]!
    let snd := out.getAppArgs[3]!
    let nextLive := snd.getAppArgs[2]!
    let nextNlive := snd.getAppArgs[3]!
    return (pOut, nextLive, nextNlive)

open Lean Meta Elab Command in
private def mkCombineDeadProof (seqFn skipExpr bv64 out1 out2 : Expr) : MetaM (Expr × Expr) := do
  if out2.isAppOfArity ``WordLangProgHOL.skip 1 then
    return (out1, mkApp (mkConst ``combineDeadSeq_right_skip) out1)
  else if out1.isAppOfArity ``WordLangProgHOL.skip 1 then
    return (out2, mkApp (mkConst ``combineDeadSeq_left_skip) out2)
  else if out1.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args1 := out1.getAppArgs
    let a := args1[1]!
    let b := args1[2]!
    let dummySeq := mkApp3 seqFn bv64 skipExpr skipExpr
    let dummyRes := mkApp3 seqFn bv64 dummySeq out2
    let hDummy ← mkEqRefl dummyRes
    let outComb := mkApp3 seqFn bv64 out1 out2
    let prf := mkApp4 (mkConst ``combineDeadSeq_seq_left) a b out2 hDummy
    return (outComb, prf)
  else
    let outComb := mkApp3 seqFn bv64 out1 out2
    let prf ← mkEqRefl outComb
    return (outComb, prf)

open Lean Meta Elab Command in
private partial def solveRemoveDeadExact
    (currNs : Name)
    (rdFn rdFnS nilLtS seqFn skipExpr bv64 prodMk1 prodMk2 : Expr)
    (e : Expr) (inLive inNlive : Expr) (forceSeal : Bool) :
    Sym.Simp.SimpM (Expr × Expr × Expr × Expr × Nat) := do
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let s1 := args[1]!
    let s2 := args[2]!
    let (out2, midLive, midNlive, prf2, cnt2) ←
      solveRemoveDeadExact currNs rdFn rdFnS nilLtS seqFn skipExpr bv64 prodMk1 prodMk2 s2 inLive inNlive false
    let (out1, outLive, outNlive, prf1, cnt1) ←
      solveRemoveDeadExact currNs rdFn rdFnS nilLtS seqFn skipExpr bv64 prodMk1 prodMk2 s1 midLive midNlive false
    let (outComb, combPrf) ← liftMetaM <| mkCombineDeadProof seqFn skipExpr bv64 out1 out2
    let prf := mkAppN (mkConst ``removeDead_seq_split_pair)
      #[s1, s2, out1, out2, outComb, inLive, midLive, outLive, inNlive, midNlive, outNlive, nilLtS,
        prf2, prf1, combPrf]
    let totalCnt := cnt1 + cnt2
    if forceSeal || totalCnt >= 200 then
      let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `rdStep)
      let lhs := mkApp4 rdFn e inLive inNlive nilLtS
      let rhs := mkApp2 prodMk1 outComb (mkApp2 prodMk2 outLive outNlive)
      liftMetaM <| addDecl (.thmDecl {
        name := stepThm, levelParams := [],
        type := ← liftMetaM <| mkEq lhs rhs, value := prf })
      return (outComb, outLive, outNlive, mkConst stepThm, 0)
    else
      return (outComb, outLive, outNlive, prf, totalCnt)
  else
    let eU ← liftMetaM <| Sym.unfoldReducible e
    let eS ← Sym.shareCommon eU
    let c1 ← Sym.Internal.mkAppS₂ rdFnS eS inLive
    let c2 ← Sym.Internal.mkAppS₂ c1 inNlive nilLtS
    let r ← Sym.Simp.simp c2
    let out := r.getResultExpr c2
    let pOut := out.getAppArgs[2]!
    let snd := out.getAppArgs[3]!
    let nextLive := snd.getAppArgs[2]!
    let nextNlive := snd.getAppArgs[3]!
    let rhs := mkApp2 prodMk1 pOut (mkApp2 prodMk2 nextLive nextNlive)
    let rflPrf ← liftMetaM <| mkEqRefl rhs
    if forceSeal then
      let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `rdLeaf)
      let lhs := mkApp4 rdFn e inLive inNlive nilLtS
      liftMetaM <| addDecl (.thmDecl {
        name := stepThm, levelParams := [],
        type := ← liftMetaM <| mkEq lhs rhs, value := rflPrf })
      return (pOut, nextLive, nextNlive, mkConst stepThm, 0)
    else
      return (pOut, nextLive, nextNlive, rflPrf, 1)

open Lean Meta Elab Command in
elab "wave8_chunked_remove_dead " id:ident " := " src:ident : command => do
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

    let width := mkNatLit 64
    let inst ← synthInstance (← mkAppM ``NeZero #[width])
    let bv64 := mkApp (mkConst ``BitVec) width
    let progType := mkApp (mkConst ``WordLangProgHOL [Level.zero]) bv64
    let seqFn := mkConst ``WordLangProgHOL.seq [Level.zero]
    let skipExpr := mkApp (mkConst ``WordLangProgHOL.skip [Level.zero]) bv64

    let srcDecl ← getConstInfo (currNs ++ src.getId)
    let srcConst := mkConst srcDecl.name
    let srcVal := srcDecl.value!

    let rdFn ← Sym.unfoldReducible (mkApp2 (mkConst ``WordAlloc.removeDead) width inst)
    let lnUnit ← Sym.unfoldReducible (mkApp (mkConst ``Spt.ln) (mkConst ``Unit))
    let nilStore ← Sym.unfoldReducible (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``WordStoreHOL))
    let numSet := mkConst ``NumSet
    let pairNumSet := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) numSet numSet
    let nilLt ← Sym.unfoldReducible (mkApp (mkConst ``List.nil [Level.zero]) pairNumSet)
    let storeListType := mkApp (mkConst ``List [Level.zero]) (mkConst ``WordStoreHOL)
    let pair2Type := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) numSet storeListType
    let prodMk1 := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) progType pair2Type
    let prodMk2 := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) numSet storeListType

    let (deadProg, finalLive, finalNlive, rdTreePrf, _) ← (Sym.withoutShareCommonChecks do
      let rdFnS ← Sym.shareCommon rdFn
      let initLive ← Sym.shareCommon lnUnit
      let initNlive ← Sym.shareCommon nilStore
      let nilLtS ← Sym.shareCommon nilLt
      let act : Sym.Simp.SimpM (Expr × Expr × Expr × Expr × Nat) :=
        solveRemoveDeadExact currNs rdFn rdFnS nilLtS seqFn skipExpr bv64 prodMk1 prodMk2 srcVal initLive initNlive true
      act.run' methods config).run
    let defName := currNs ++ id.getId
    addDecl (.defnDecl {
      name := defName, levelParams := [], type := progType, value := deadProg
      hints := .regular (getMaxHeight (← getEnv) deadProg + 1), safety := .safe })
    let defConst := mkConst defName
    let lhs ← mkAppM ``WordAlloc.removeDeadProg #[srcConst]
    let eqType ← mkEq lhs defConst
    let prf := mkAppN (mkConst ``removeDead_finalize) #[srcVal, deadProg, finalLive, finalNlive, rdTreePrf]
    addDecl (.thmDecl {
      name := defName.appendAfter "_eq", levelParams := [], type := eqType, value := prf })
    logInfo m!"Staged removeDead {defName}"

open Lean Meta Elab Command in
private partial def evalCopySimp (functionS sndS seqFn bv64 : Expr) (e : Expr) (curCs : Expr) :
    Sym.Simp.SimpM (Expr × Expr) := do
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let (out1, midCs) ← evalCopySimp functionS sndS seqFn bv64 args[1]! curCs
    let (out2, outCs) ← evalCopySimp functionS sndS seqFn bv64 args[2]! midCs
    return (mkApp3 seqFn bv64 out1 out2, outCs)
  else
    let eU ← liftMetaM <| Sym.unfoldReducible e
    let eS ← Sym.shareCommon eU
    let tJ ← Sym.Internal.mkAppS₂ functionS eS curCs
    let rJ ← Sym.Simp.simp tJ
    let outJ := rJ.getResultExpr tJ
    let pOut := outJ.getAppArgs[2]!
    let sndApp ← Sym.Internal.mkAppS sndS outJ
    let resSnd ← Sym.Simp.simp sndApp
    let nextCs := resSnd.getResultExpr sndApp
    return (pOut, nextCs)

open Lean Meta Elab Command in
private partial def solveCopyLeftSpineChunks (currNs : Name) (functionS chunkFn sndS seqFn skipExpr bv64 prodMk : Expr)
    (items : Array Expr) (inCs : Expr) : Sym.Simp.SimpM (Expr × Expr × Expr × Expr) := do
  let mut curCs := inCs
  let mut accInProg := items[0]!
  let (out0, cs0) ← evalCopySimp functionS sndS seqFn bv64 items[0]! curCs
  curCs := cs0
  let mut accOutProg := out0
  let mut idx := 1
  let mut leavesInChunk := countLeaves items[0]!
  while idx < items.size && leavesInChunk + countLeaves items[idx]! <= 500 do
    let item := items[idx]!
    let (outItem, csNext) ← evalCopySimp functionS sndS seqFn bv64 item curCs
    curCs := csNext
    accInProg := mkApp3 seqFn bv64 accInProg item
    accOutProg := mkApp3 seqFn bv64 accOutProg outItem
    leavesInChunk := leavesInChunk + countLeaves item
    idx := idx + 1
  let lhs0 := mkApp2 functionS accInProg inCs
  let rhs0 := mkApp2 prodMk accOutProg curCs
  let thm0 ← liftMetaM <| mkFreshUserName (currNs ++ `copyChunk)
  let rfl0 ← liftMetaM <| mkEqRefl rhs0
  liftMetaM <| addDecl (.thmDecl {
    name := thm0, levelParams := [],
    type := ← liftMetaM <| mkEq lhs0 rhs0, value := rfl0 })
  let mut accProof := mkConst thm0
  while idx < items.size do
    let prevCs := curCs
    let prevInProg := accInProg
    let prevOutProg := accOutProg
    let mut chunkTerm := skipExpr
    let mut chunkLeaves := 0
    while idx < items.size && (chunkLeaves == 0 || chunkLeaves + countLeaves items[idx]! <= 500) do
      let item := items[idx]!
      let (outItem, csNext) ← evalCopySimp functionS sndS seqFn bv64 item curCs
      curCs := csNext
      chunkTerm := mkApp3 seqFn bv64 chunkTerm item
      accInProg := mkApp3 seqFn bv64 accInProg item
      accOutProg := mkApp3 seqFn bv64 accOutProg outItem
      chunkLeaves := chunkLeaves + countLeaves item
      idx := idx + 1
    let chunkLhs := mkApp3 chunkFn prevOutProg prevCs chunkTerm
    let chunkRhs := mkApp2 prodMk accOutProg curCs
    let chunkThm ← liftMetaM <| mkFreshUserName (currNs ++ `copyChunk)
    let chunkRfl ← liftMetaM <| mkEqRefl chunkRhs
    liftMetaM <| addDecl (.thmDecl {
      name := chunkThm, levelParams := [],
      type := ← liftMetaM <| mkEq chunkLhs chunkRhs, value := chunkRfl })
    let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `copyStep)
    let stepLhs := mkApp2 functionS accInProg inCs
    let stepVal := mkAppN (mkConst ``copyProp_plugLeft_step)
      #[prevInProg, chunkTerm, inCs, prevCs, curCs, prevOutProg, accOutProg, accProof, mkConst chunkThm]
    liftMetaM <| addDecl (.thmDecl {
      name := stepThm, levelParams := [],
      type := ← liftMetaM <| mkEq stepLhs chunkRhs, value := stepVal })
    accProof := mkConst stepThm
  return (accInProg, accOutProg, curCs, accProof)

open Lean Meta Elab Command in
private partial def solveCopyExact
    (currNs : Name)
    (function functionS sndS seqFn bv64 prodMk : Expr)
    (e : Expr) (inCs : Expr) (forceSeal : Bool) :
    Sym.Simp.SimpM (Expr × Expr × Expr × Nat) := do
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let s1 := args[1]!
    let s2 := args[2]!
    let (out1, midCs, prf1, cnt1) ←
      solveCopyExact currNs function functionS sndS seqFn bv64 prodMk s1 inCs false
    let (out2, outCs, prf2, cnt2) ←
      solveCopyExact currNs function functionS sndS seqFn bv64 prodMk s2 midCs false
    let outProg := mkApp3 seqFn bv64 out1 out2
    let prf := mkAppN (mkConst ``copyProp_seq_split_pair)
      #[s1, s2, out1, out2, inCs, midCs, outCs, prf1, prf2]
    let totalCnt := cnt1 + cnt2
    if forceSeal || totalCnt >= 200 then
      let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `copyStep)
      let lhs := mkApp2 function e inCs
      let rhs := mkApp2 prodMk outProg outCs
      liftMetaM <| addDecl (.thmDecl {
        name := stepThm, levelParams := [],
        type := ← liftMetaM <| mkEq lhs rhs, value := prf })
      return (outProg, outCs, mkConst stepThm, 0)
    else
      return (outProg, outCs, prf, totalCnt)
  else
    let eU ← liftMetaM <| Sym.unfoldReducible e
    let eS ← Sym.shareCommon eU
    let tJ ← Sym.Internal.mkAppS₂ functionS eS inCs
    let rJ ← Sym.Simp.simp tJ
    let outJ := rJ.getResultExpr tJ
    let pOut := outJ.getAppArgs[2]!
    let sndApp ← Sym.Internal.mkAppS sndS outJ
    let resSnd ← Sym.Simp.simp sndApp
    let nextCs := resSnd.getResultExpr sndApp
    let rhs := mkApp2 prodMk pOut nextCs
    let rflPrf ← liftMetaM <| mkEqRefl rhs
    if forceSeal then
      let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `copyLeaf)
      let lhs := mkApp2 function e inCs
      liftMetaM <| addDecl (.thmDecl {
        name := stepThm, levelParams := [],
        type := ← liftMetaM <| mkEq lhs rhs, value := rflPrf })
      return (pOut, nextCs, mkConst stepThm, 0)
    else
      return (pOut, nextCs, rflPrf, 1)

open Lean Meta Elab Command in
elab "wave8_certified_prealloc" : command => do
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

    let width := mkNatLit 64
    let inst ← synthInstance (← mkAppM ``NeZero #[width])
    let bv64 := mkApp (mkConst ``BitVec) width
    let progType := mkApp (mkConst ``WordLangProgHOL [Level.zero]) bv64
    let seqFn := mkConst ``WordLangProgHOL.seq [Level.zero]
    let skipExpr := mkApp (mkConst ``WordLangProgHOL.skip [Level.zero]) bv64

    -- 1. copied := WordCopy.copyProp common
    let commonConst := mkConst (currNs ++ `common)
    let commonVal := (← getConstInfo (currNs ++ `common)).value!
    let cs := mkConst ``WordCopy.emptyEq
    let copyFn := mkApp2 (mkConst ``WordCopy.copyPropProg) width inst
    let copyState := mkConst ``WordCopy.CopyState
    let sndCopy := mkApp2 (mkConst ``Prod.snd [Level.zero, Level.zero]) progType copyState
    let prodMkCopy := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) progType copyState
    let csU ← Sym.unfoldReducible cs
    let copyFnU ← Sym.unfoldReducible copyFn
    let sndCopyU ← Sym.unfoldReducible sndCopy
    let (copiedProg, finalCs, copyTreePrf, _) ← (Sym.withoutShareCommonChecks do
      let csS ← Sym.shareCommon csU
      let copyFnS ← Sym.shareCommon copyFnU
      let sndCopyS ← Sym.shareCommon sndCopyU
      let act : Sym.Simp.SimpM (Expr × Expr × Expr × Nat) :=
        solveCopyExact currNs copyFnU copyFnS sndCopyS seqFn bv64 prodMkCopy commonVal csS true
      act.run' methods config).run
    let copiedName := currNs ++ `copied
    addDecl (.defnDecl {
      name := copiedName, levelParams := [], type := progType, value := copiedProg
      hints := .regular (getMaxHeight (← getEnv) copiedProg + 1), safety := .safe })
    let copiedConst := mkConst copiedName
    let copiedLhs ← mkAppM ``WordCopy.copyProp #[commonConst]
    let copiedEqType ← mkEq copiedLhs copiedConst
    let copiedPrf := mkAppN (mkConst ``copyProp_finalize) #[commonVal, copiedProg, finalCs, copyTreePrf]
    addDecl (.thmDecl {
      name := currNs ++ `copied_eq, levelParams := [], type := copiedEqType, value := copiedPrf })

    -- 2. twoRegister := WordInst.threeToTwoRegProg riscvConfig.twoRegArith copied
    let twoRegName := currNs ++ `twoRegister
    addDecl (.defnDecl {
      name := twoRegName, levelParams := [], type := progType, value := copiedProg
      hints := .regular (getMaxHeight (← getEnv) copiedProg + 1), safety := .safe })
    let twoRegConst := mkConst twoRegName
    let twoRegArith ← Term.elabTerm (← `(riscvConfig.twoRegArith)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let twoRegArith ← instantiateMVars twoRegArith
    let twoRegLhs ← mkAppM ``WordInst.threeToTwoRegProg #[twoRegArith, copiedConst]
    let twoRegEqType ← mkEq twoRegLhs twoRegConst
    let twoRegPrf ← mkEqRefl twoRegConst
    addDecl (.thmDecl {
      name := currNs ++ `twoRegister_eq, levelParams := [], type := twoRegEqType, value := twoRegPrf })

    -- 3. reachable := WordUnreach.removeUnreach twoRegister
    let unrCall ← mkAppM ``WordUnreach.removeUnreach #[twoRegConst]
    let unrU ← Sym.unfoldReducible unrCall
    let unrExpr ← (Sym.withoutShareCommonChecks do
      let unrS ← Sym.shareCommon unrU
      let act : Sym.Simp.SimpM Expr := do
        let r ← Sym.Simp.simp unrS
        return r.getResultExpr unrS
      act.run' methods config).run
    let reachName := currNs ++ `reachable
    addDecl (.defnDecl {
      name := reachName, levelParams := [], type := progType, value := unrExpr
      hints := .regular (getMaxHeight (← getEnv) unrExpr + 1), safety := .safe })
    let reachConst := mkConst reachName
    let reachEqType ← mkEq unrCall reachConst
    let reachPrf ← mkEqRefl reachConst
    addDecl (.thmDecl {
      name := currNs ++ `reachable_eq, levelParams := [], type := reachEqType, value := reachPrf })

    -- 4. prefixProgram := WordAlloc.removeDeadProg reachable
    let rdFn ← Sym.unfoldReducible (mkApp2 (mkConst ``WordAlloc.removeDead) width inst)
    let lnUnit ← Sym.unfoldReducible (mkApp (mkConst ``Spt.ln) (mkConst ``Unit))
    let nilStore ← Sym.unfoldReducible (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``WordStoreHOL))
    let numSet := mkConst ``NumSet
    let pairNumSet := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) numSet numSet
    let nilLt ← Sym.unfoldReducible (mkApp (mkConst ``List.nil [Level.zero]) pairNumSet)
    let storeListType := mkApp (mkConst ``List [Level.zero]) (mkConst ``WordStoreHOL)
    let pair2Type := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) numSet storeListType
    let prodMk1 := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) progType pair2Type
    let prodMk2 := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) numSet storeListType

    let (deadProg, finalLive, finalNlive, rdTreePrf, _) ← (Sym.withoutShareCommonChecks do
      let rdFnS ← Sym.shareCommon rdFn
      let initLive ← Sym.shareCommon lnUnit
      let initNlive ← Sym.shareCommon nilStore
      let nilLtS ← Sym.shareCommon nilLt
      let act : Sym.Simp.SimpM (Expr × Expr × Expr × Expr × Nat) :=
        solveRemoveDeadExact currNs rdFn rdFnS nilLtS seqFn skipExpr bv64 prodMk1 prodMk2 unrExpr initLive initNlive true
      act.run' methods config).run
    let prefixName := currNs ++ `prefixProgram
    addDecl (.defnDecl {
      name := prefixName, levelParams := [], type := progType, value := deadProg
      hints := .regular (getMaxHeight (← getEnv) deadProg + 1), safety := .safe })
    let prefixConst := mkConst prefixName
    let prefixLhs ← mkAppM ``WordAlloc.removeDeadProg #[reachConst]
    let prefixEqType ← mkEq prefixLhs prefixConst
    let prefixPrf := mkAppN (mkConst ``removeDead_finalize) #[unrExpr, deadProg, finalLive, finalNlive, rdTreePrf]
    addDecl (.thmDecl {
      name := currNs ++ `prefixProgram_eq, levelParams := [], type := prefixEqType, value := prefixPrf })
    logInfo m!"Staged preAllocation {prefixName}"

open Lean Meta Elab Command in
elab "wave8_certified_check_program" : command => do
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
    logInfo m!"Staged checkProgram {currNs ++ `checkedProgram}"

end InitECandidate.Solver.Wave8Stage
