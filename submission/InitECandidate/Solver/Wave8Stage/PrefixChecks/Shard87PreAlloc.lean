import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87Cse

/-! Staged pre-allocation passes (`copyProp`, `threeToTwoRegProg`, `removeUnreach`, `removeDeadProg`) for `Shard87`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
open InitECandidate.Solver.Wave8Stage
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
private partial def collectLeftSpine (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let acc := collectLeftSpine args[1]! acc
    acc.push args[2]!
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
private partial def solveCopyTree (currNs : Name) (functionS chunkFn sndS seqFn skipExpr bv64 prodMk : Expr)
    (e : Expr) (inCs : Expr) : Sym.Simp.SimpM (Expr × Expr × Expr) := do
  if countLeaves e <= 500 then
    let (outProg, outCs) ← evalCopySimp functionS sndS seqFn bv64 e inCs
    let lhs := mkApp2 functionS e inCs
    let rhs := mkApp2 prodMk outProg outCs
    let thm ← liftMetaM <| mkFreshUserName (currNs ++ `copyLeaf)
    let rflPrf ← liftMetaM <| mkEqRefl rhs
    liftMetaM <| addDecl (.thmDecl {
      name := thm, levelParams := [],
      type := ← liftMetaM <| mkEq lhs rhs, value := rflPrf })
    return (outProg, outCs, mkConst thm)
  else if e.isAppOfArity ``WordLangProgHOL.seq 3 then
    let args := e.getAppArgs
    let left := args[1]!
    let right := args[2]!
    if countLeaves right > 500 then
      let (outLeft, midCs, prfLeft) ← solveCopyTree currNs functionS chunkFn sndS seqFn skipExpr bv64 prodMk left inCs
      let (outRight, outCs, prfRight) ← solveCopyTree currNs functionS chunkFn sndS seqFn skipExpr bv64 prodMk right midCs
      let outProg := mkApp3 seqFn bv64 outLeft outRight
      let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `copySplit)
      let lhs := mkApp2 functionS e inCs
      let rhs := mkApp2 prodMk outProg outCs
      let val := mkAppN (mkConst ``copyProp_seq_split_pair)
        #[left, right, outLeft, outRight, inCs, midCs, outCs, prfLeft, prfRight]
      liftMetaM <| addDecl (.thmDecl {
        name := stepThm, levelParams := [],
        type := ← liftMetaM <| mkEq lhs rhs, value := val })
      return (outProg, outCs, mkConst stepThm)
    else
      let items := collectLeftSpine e #[]
      let (_, outProg, outCs, prf) ←
        solveCopyLeftSpineChunks currNs functionS chunkFn sndS seqFn skipExpr bv64 prodMk items inCs
      return (outProg, outCs, prf)
  else
    let (outProg, outCs) ← evalCopySimp functionS sndS seqFn bv64 e inCs
    let rhs := mkApp2 prodMk outProg outCs
    let prf ← liftMetaM <| mkEqRefl rhs
    return (outProg, outCs, prf)

open Lean Meta Elab Command in
elab "wave8_shard87_prealloc" : command => do
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
    let copyChunkFn := mkApp2 (mkConst ``copyPropChunk) width inst
    let copyState := mkConst ``WordCopy.CopyState
    let sndCopy := mkApp2 (mkConst ``Prod.snd [Level.zero, Level.zero]) progType copyState
    let prodMkCopy := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) progType copyState
    let csU ← Sym.unfoldReducible cs
    let copyFnU ← Sym.unfoldReducible copyFn
    let sndCopyU ← Sym.unfoldReducible sndCopy
    let (copiedProg, finalCs, copyTreePrf) ← (Sym.withoutShareCommonChecks do
      let csS ← Sym.shareCommon csU
      let copyFnS ← Sym.shareCommon copyFnU
      let sndCopyS ← Sym.shareCommon sndCopyU
      let act : Sym.Simp.SimpM (Expr × Expr × Expr) :=
        solveCopyTree currNs copyFnS copyChunkFn sndCopyS seqFn skipExpr bv64 prodMkCopy commonVal csS
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
    let rLeaves := collectRightSpine unrExpr #[]
    let rdFn ← Sym.unfoldReducible (mkApp2 (mkConst ``WordAlloc.removeDead) width inst)
    let lnUnit ← Sym.unfoldReducible (mkApp (mkConst ``Spt.ln) (mkConst ``Unit))
    let nilStore ← Sym.unfoldReducible (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``WordStoreHOL))
    let numSet := mkConst ``NumSet
    let pairNumSet := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) numSet numSet
    let nilLt ← Sym.unfoldReducible (mkApp (mkConst ``List.nil [Level.zero]) pairNumSet)
    let rLeavesU ← liftMetaM <| rLeaves.mapM Sym.unfoldReducible
    let rdChunkFn := mkApp2 (mkConst ``removeDeadChunk) width inst
    let storeListType := mkApp (mkConst ``List [Level.zero]) (mkConst ``WordStoreHOL)
    let pair2Type := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) numSet storeListType
    let prodMk1 := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) progType pair2Type
    let prodMk2 := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) numSet storeListType

    let (deadProg, finalLive, finalNlive, rdTreePrf) ← (Sym.withoutShareCommonChecks do
      let rdFnS ← Sym.shareCommon rdFn
      let initLive ← Sym.shareCommon lnUnit
      let initNlive ← Sym.shareCommon nilStore
      let nilLtS ← Sym.shareCommon nilLt
      let rLeavesS ← rLeavesU.mapM Sym.shareCommon
      let act : Sym.Simp.SimpM (Expr × Expr × Expr × Expr) := do
        let n := rLeaves.size
        let lastIdx := n - 1
        let c1 ← Sym.Internal.mkAppS₂ rdFnS rLeavesS[lastIdx]! initLive
        let c2 ← Sym.Internal.mkAppS₂ c1 initNlive nilLtS
        let r0 ← Sym.Simp.simp c2
        let out0 := r0.getResultExpr c2
        let mut accProg := out0.getAppArgs[2]!
        let snd0 := out0.getAppArgs[3]!
        let mut curLive := snd0.getAppArgs[2]!
        let mut curNlive := snd0.getAppArgs[3]!
        let mut accIn := rLeaves[lastIdx]!
        let mut curTuple := mkApp2 prodMk1 accProg (mkApp2 prodMk2 curLive curNlive)
        let lhs0 := mkApp4 rdFn accIn initLive initNlive nilLtS
        let thm0 ← liftMetaM <| mkFreshUserName (currNs ++ `rdChunk)
        let rfl0 ← liftMetaM <| mkEqRefl curTuple
        liftMetaM <| addDecl (.thmDecl {
          name := thm0, levelParams := [],
          type := ← liftMetaM <| mkEq lhs0 curTuple, value := rfl0 })
        let mut accProof := mkConst thm0
        let mut i := lastIdx
        while i > 0 do
          let chunkEnd := i
          let chunkStart := if i > 500 then i - 500 else 0
          let prevIn := accIn
          let prevTuple := curTuple
          let mut chunkTerm := skipExpr
          let mut j := chunkEnd
          while j > chunkStart do
            j := j - 1
            let cj1 ← Sym.Internal.mkAppS₂ rdFnS rLeavesS[j]! curLive
            let cj2 ← Sym.Internal.mkAppS₂ cj1 curNlive nilLtS
            let rj ← Sym.Simp.simp cj2
            let outj := rj.getResultExpr cj2
            let pOut := outj.getAppArgs[2]!
            let sndj := outj.getAppArgs[3]!
            curLive := sndj.getAppArgs[2]!
            curNlive := sndj.getAppArgs[3]!
            chunkTerm := mkApp3 seqFn bv64 rLeaves[j]! chunkTerm
            accIn := mkApp3 seqFn bv64 rLeaves[j]! accIn
            if pOut.isAppOfArity ``WordLangProgHOL.skip 1 then
              pure ()
            else if accProg.isAppOfArity ``WordLangProgHOL.skip 1 then
              accProg := pOut
            else
              accProg := mkApp3 seqFn bv64 pOut accProg
          curTuple := mkApp2 prodMk1 accProg (mkApp2 prodMk2 curLive curNlive)
          let chunkLhs := mkApp3 rdChunkFn chunkTerm prevTuple nilLtS
          let chunkThm ← liftMetaM <| mkFreshUserName (currNs ++ `rdChunk)
          let chunkRfl ← liftMetaM <| mkEqRefl curTuple
          liftMetaM <| addDecl (.thmDecl {
            name := chunkThm, levelParams := [],
            type := ← liftMetaM <| mkEq chunkLhs curTuple, value := chunkRfl })
          let stepThm ← liftMetaM <| mkFreshUserName (currNs ++ `rdStep)
          let stepLhs := mkApp4 rdFn accIn initLive initNlive nilLtS
          let stepVal := mkAppN (mkConst ``removeDead_plugRight_step)
            #[chunkTerm, prevIn, initLive, initNlive, nilLtS, prevTuple, curTuple, accProof, mkConst chunkThm]
          liftMetaM <| addDecl (.thmDecl {
            name := stepThm, levelParams := [],
            type := ← liftMetaM <| mkEq stepLhs curTuple, value := stepVal })
          accProof := mkConst stepThm
          i := chunkStart
        return (accProg, curLive, curNlive, accProof)
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

wave8_shard87_prealloc

theorem prefixCompileEq :
    WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith arity
      wordProgram = prefixProgram :=
  preAllocation_step arity
    wordProgram simplified temporary selected ssa dead common copied twoRegister reachable prefixProgram
    simplified_eq temporary_eq selected_eq ssa_eq dead_eq common_eq copied_eq twoRegister_eq reachable_eq prefixProgram_eq

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
