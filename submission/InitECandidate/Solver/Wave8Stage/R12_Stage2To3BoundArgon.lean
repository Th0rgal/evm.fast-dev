import InitECandidate.Bitmaps
import InitECandidate.Solver.ConcreteCompilationWitness
import InitECandidate.Solver.PipelineInitialStates
import InitECandidate.Solver.Wave8GuestInv.CertifiedPipelineTransfer
import InitECandidate.Solver.Wave8Stage.ConcreteWordCheckInput
import InitECandidate.Solver.Wave8Stage.ConcreteWordCostData
import InitECandidate.Solver.Wave8Stage.WordSourceOracle
import InitECandidate.Solver.Wave8Stage.WordToStackFallbackInitialization

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.R12_Stage2To3BoundArgon

open Classical InitE Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics Flapjack.LoopToWord.CompileCorrect
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.LoopToWordStateRelImpSemanticsSupport WordToStackProofs.InitializationStateRel
open StackRemove.Proofs.InitMake InitECandidate.Solver.FastEnv
open InitECandidate.Solver.SelfContainedStageBounds InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedConcretePipelineMaster InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EntryClassTransfer
open InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer
open InitECandidate.Solver.Wave8GuestInv.CertifiedPipelineTransfer InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8Stage.RuntimeLabels InitECandidate.Solver.Wave8Stage.InitializedTransfer
open InitECandidate.Solver.Wave8Stage.WordCostEffects InitECandidate.Solver.Wave8Stage.WordSourceOracle
open InitECandidate.Solver.Wave8Stage.WordCostCertificates
open InitECandidate.Solver.Wave8Stage.WordCostEntryCertificate
open InitECandidate.Solver.Wave8Stage.ConcreteWordCostAnnotations
open InitECandidate.Solver.Wave8Stage.ConcreteWordCheckInput

theorem noLabels (dest : Option Nat) (label : Nat) :
    summaries dest (.breakTo label) = none ∧ summaries dest (.continueTo label) = none := by
  cases dest <;> exact ⟨rfl, rfl⟩

theorem indirect (name : Nat) :
    Subeffects (summaries (some name)) (summaries none) := by
  intro exit; cases exit <;> simp [summaries]; intro cost hcost
  by_cases h66 : name = 66 <;> by_cases h90 : name = 90 <;> simp [h66, h90] at hcost <;> omega

theorem entryBound (exit : Exit) :
    AtMost (summaries (some BvlToBvi.initGlobalsLocation) exit) 1 := by
  have h66 : BvlToBvi.initGlobalsLocation ≠ 66 := by decide
  have h90 : BvlToBvi.initGlobalsLocation ≠ 90 := by decide
  cases exit <;> simp [summaries, AtMost, h66, h90]

theorem bitmapBound : InitECandidate.bitmaps.length + 1 < 2 ^ 64 := by decide

theorem bitmapPrefix : [(4 : BitVec 64)] <+: InitECandidate.bitmaps := by
  refine ⟨InitECandidate.bitmaps.tail, ?_⟩; decide

theorem fullMakeInit_withBitmaps_stateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width)) (scc : StackToLab.Config) (dc : DataToWord.Config)
    (maxHeap sp : Nat) (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C) (dimension : goodDimindex width)
    (widthBound : 8 ≤ width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32) (hBitmapBound : bitmaps.length + 1 < 2 ^ width)
    (hBitmapPrefix : [(4 : BitVec width)] <+: bitmaps)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps, wconf, fs, stackCode)) :
    let stack := (FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], []))).1
    WordToStackProofs.stateRel ac (ac.regCount - (5 + ac.avoidRegs.length)) 0 0
      (WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
        (fun _ => ((bitmaps.length, cfg), [])))
      { stack with bitmaps := bitmaps } [] 0 := by
  intro stack
  rcases hinit : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) with ⟨stack0, NoneOrAux⟩
  have hstack : stack = stack0 := by dsimp [stack]; rw [hinit]
  rw [hstack]
  cases NoneOrAux with
  | some aux =>
    obtain ⟨bitmapEq, _⟩ := fullMakeInit_bitmaps_code scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp _ stack0 aux hinit
    have hsame : { stack0 with bitmaps := bitmaps } = stack0 := by
      cases stack0; simp only at bitmapEq; subst bitmapEq; rfl
    rw [hsame]
    exact WordToStackPipelineBudget.initialized_stateRel ac wc panCode col wordCode bitmaps
      wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack0 aux
      dimension registers isa wtw wts hinit
  | none =>
    obtain ⟨lowerCode, base, failed, actual⟩ : ∃ (lowerCode : Spt (HolProg width))
        (base : StackSemStateFiniteExact width C F),
        makeInitOpt (StackToLab.isGenGc dc.gcKind) maxHeap bitmaps dataSp (fun _ => (cfg, [], []))
          scc.jump offset sp lowerCode base = none ∧
        StackAlloc.makeInit dc (sptFromAList stackCode) (fun _ => (cfg, [], []))
          (makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap bitmaps dataSp (fun _ => (cfg, [], []))
            scc.jump offset sp lowerCode base) = stack0 := by
      unfold FullMakeInit.fullMakeInit at hinit; simp only [Prod.mk.injEq] at hinit
      exact ⟨_, _, hinit.2, hinit.1⟩
    have registerBound : 4 < ac.regCount - (5 + ac.avoidRegs.length) := by omega
    have ok := WordToStackFallbackInitialization.fallback_initStateOk ac dc _ cfg
      (StackToLab.isGenGc dc.gcKind) scc.jump maxHeap dataSp sp offset bitmaps lowerCode
      (sptFromAList stackCode) base dimension widthBound registerBound hBitmapBound hBitmapPrefix failed
    rw [actual] at ok
    have targetCode : stack0.code = sptFromAList stackCode := by rw [← actual]; rfl
    obtain ⟨noRaise, noStore⟩ := panToTargetStubLocationsFree wc ac panCode col wordCode isa wtw
    have conv := (BackendProof.compileToWordConventions2 wc ac _ col wordCode wtw
      (fun _ _ => Or.inr isa)).2.2
    have related := WordToStackCompileBudget.compile_stateRel ac wordCode
      { stack0 with bitmaps := bitmaps } _ (fun _ => ((bitmaps.length, cfg), []))
      (by change stack0.code = _; rw [targetCode, wts]) rfl ok noRaise noStore
      (by change (WordToStack.Native.compileNative ac false wordCode).1 <+: bitmaps; rw [wts])
      (fun entry member => ⟨(conv entry member).1, (conv entry member).2.1⟩)
    simpa only [WordToStackFallbackInitialization.makeInit_withBitmaps] using related

theorem initialized_word_to_stack_not_timeOut_two_mul
    (ac : AsmConfigExact 64) (wc : WordToWord.Config) (panCode : List (DeclHOL 64))
    (col : List (Option (Spt Nat))) (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bitmaps : List (BitVec 64)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg 64)) (scc : StackToLab.Config) (dc : DataToWord.Config)
    (maxHeap sp : Nat) (offset : BitVec 64 × BitVec 64)
    (lab : LabSem.State 64 LabToTarget.Config Guest.HostMemory)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : LabToTarget.Config)
    (stack aux : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory) (clock : Nat)
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram summaries terminal 20000
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (summaries (some entry.1)) = true)
    (oracleEq : lab.ffi.oracle = InitE.sourceOracle)
    (dimension : goodDimindex 64) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps, wconf, fs, stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (notError : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { WordToStack.Native.Initialization.makeInit ac
          (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
          (fun _ => ((bitmaps.length, cfg), [])) with clock := clock }).1 ≠ some .error)
    (notTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { WordToStack.Native.Initialization.makeInit ac
          (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
          (fun _ => ((bitmaps.length, cfg), [])) with clock := clock }).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
        { stack with clock := 2 * clock })).1 ≠ some .timeOut :=
  WordCostPipelineCertificate.initialized_notTimeOut_two_mul ac wc panCode col wordCode bitmaps
    wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
    BvlToBvi.initGlobalsLocation clock summaries terminal InitE.sourceOracle 20000
    noLabels indirect checked entryBound oracleEq terminalOracle dimension registers isa
    wtw wts initialized notError notTimeout

theorem pan_to_certified_lab_complete_of_checked
    (ac : AsmConfigExact 64) (wc : WordToWord.Config) (panCode : List (DeclHOL 64))
    (col : List (Option (Spt Nat))) (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bitmaps : List (BitVec 64)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg 64)) (scc : StackToLab.Config) (dc : DataToWord.Config)
    (maxHeap sp : Nat) (offset : BitVec 64 × BitVec 64)
    (lab : LabSem.State 64 LabToTarget.Config Guest.HostMemory)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : LabToTarget.Config)
    (stack aux : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (dimension : goodDimindex 64) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col, wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps, wconf, fs, stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram summaries terminal 20000
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (summaries (some entry.1)) = true)
    (oracleEq : lab.ffi.oracle = InitE.sourceOracle)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec 64)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL 64) = (result, post))
    (notError : panEntryClass result ≠ .RunError) (notTimeout : result ≠ some .timeOut)
    (assumptions : FullMakeInitSemantics.Assumptions scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])))
    (memorySafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    ∃ outcome, (LabSem.evaluate { lab with
      clock := 2 * (M + 1) * certifiedStackClock panCode start k + (3 * M + 2) }).1 =
      .halt outcome :=
  CertifiedPipelineTransfer.pan_to_certified_lab_complete ac wc panCode col wordCode bitmaps
    wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized summaries terminal InitE.sourceOracle 20000 noLabels
    indirect checked entryBound oracleEq terminalOracle source start globalsSize heapLen
    front stCtxt s_decls hst decls k result post run notError notTimeout assumptions memorySafe

theorem stage2_to_3_word_to_stack_withBitmaps_affine_not_timeOut
    (w : ConcreteOracleCompilationWitness) (allChecked : ConcreteCompilerWord.source.all check = true)
    (input : Guest.InputBlob) (k_word : Nat) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (hwtw : WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog))
    (hwts : WordToStack.Native.compileNative riscvConfig false wprog =
      (InitECandidate.bitmaps, wconf, fs, p))
    (h_word_no_err : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
          3788 ltconf sourceDeclarations wprog InitECandidate.bitmaps p 0 with
          clock := k_word }).1 ≠ some .error)
    (h_word_nt : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
          3788 ltconf sourceDeclarations wprog InitECandidate.bitmaps p 0 with
          clock := k_word }).1 ≠ some .timeOut) :
    let stack := pipelineStackInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
      (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
      InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0
    (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
        { stack with bitmaps := InitECandidate.bitmaps, clock := 2 * k_word })).1 ≠ some .timeOut := by
  intro stack
  let c := oracleCompilerConfig w.oracles
  let lab := pipelineLabInitState c baselineMachineConfig (sourceFfi input) t m bitmapsDm sdm
    baselineInstalledState InitECandidate.nativeCode 3788 ltconf p
  have related := fullMakeInit_withBitmaps_stateRel riscvConfig c.wordToWordConf
    sourceDeclarations col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    lab (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0 ltconf
    (Or.inr rfl) (by decide) (by decide) (by decide) bitmapBound bitmapPrefix hwtw hwts
  have hgc : WordSimp.gcFunConstOk (pipelinePanToWordInitState c baselineMachineConfig
      (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode 3788
      ltconf sourceDeclarations wprog InitECandidate.bitmaps p 0).gcFun := by
    unfold pipelinePanToWordInitState pipelineWordInitState pipelineStackInitState
      FullMakeInit.fullMakeInit StackAlloc.makeInit WordToStack.Native.Initialization.makeInit
    exact DataToWord.Proofs.Gc.gcFunConstOkWordGcFun (width := 64) (c := c.dataConf)
  have agree := word_to_word_clocked_agree c.wordToWordConf riscvConfig
    (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) col wprog
    (pipelinePanToWordInitState c baselineMachineConfig (sourceFfi input) t m bitmapsDm sdm
      baselineInstalledState InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
      InitECandidate.bitmaps p 0)
    BvlToBvi.initGlobalsLocation k_word hwtw hgc
    (PanToWord.pan_to_word_compile_prog_no_install_code _ sourceDeclarations _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_alloc_code _ sourceDeclarations _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ sourceDeclarations _ rfl) rfl rfl h_word_no_err
  have h_wprog_no_err : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { WordToStack.Native.Initialization.makeInit riscvConfig
          (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) stack
          (sptFromAList wprog) (fun _ => ((InitECandidate.bitmaps.length, ltconf), [])) with
          clock := k_word }).1 ≠ some .error := by
    change (WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState c baselineMachineConfig (sourceFfi input) t m bitmapsDm sdm
          baselineInstalledState InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
          InitECandidate.bitmaps p 0 with clock := k_word, code := sptFromAList wprog }).1 ≠ some .error
    rw [agree.1]; exact h_word_no_err
  have h_wprog_nt : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { WordToStack.Native.Initialization.makeInit riscvConfig
          (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) stack
          (sptFromAList wprog) (fun _ => ((InitECandidate.bitmaps.length, ltconf), [])) with
          clock := k_word }).1 ≠ some .timeOut := by
    change (WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState c baselineMachineConfig (sourceFfi input) t m bitmapsDm sdm
          baselineInstalledState InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
          InitECandidate.bitmaps p 0 with clock := k_word, code := sptFromAList wprog }).1 ≠ some .timeOut
    rw [agree.1]; exact h_word_nt
  have certificates := WordCostCodeCertificates.compile_codeCertified summaries terminal
    c.wordToWordConf riscvConfig (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations)
    20000 noLabels indirect
    (WordCostPipelineCertificate.panToWord_noMt_members riscvConfig.isa sourceDeclarations)
    (original_of_all allChecked)
  rw [hwtw] at certificates
  have ffiEq := FullMakeInit.fullMakeInitFfi c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps p lab (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs))
    0 (fun _ => (ltconf, [], []))
  have noInstall := WordToStackCompileBudget.compile_noInstall c.wordToWordConf riscvConfig _
    col wprog hwtw (PanToWord.pan_to_word_compile_prog_no_install_code _ sourceDeclarations _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ sourceDeclarations _ rfl)
  exact WordCostEntryCertificate.notTimeOut_two_mul riscvConfig _
    BvlToBvi.initGlobalsLocation k_word summaries terminal (sptFromAList wprog)
    InitE.sourceOracle noInstall certificates terminalOracle _
    { stack with bitmaps := InitECandidate.bitmaps }
    ⟨rfl, congrArg HolFfiState.oracle ffiEq⟩ entryBound related h_wprog_no_err h_wprog_nt

theorem stage2_to_3_word_to_stack_affine_not_timeOut_of_initialized
    (w : ConcreteOracleCompilationWitness) (allChecked : ConcreteCompilerWord.source.all check = true)
    (input : Guest.InputBlob) (k_word : Nat) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg 64))
    (ltconf : LabToTarget.Config) (aux : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (hwtw : WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog))
    (hwts : WordToStack.Native.compileNative riscvConfig false wprog = (InitECandidate.bitmaps, wconf, fs, p))
    (hinit : (FullMakeInit.fullMakeInit (oracleCompilerConfig w.oracles).stackConf
      (oracleCompilerConfig w.oracles).dataConf
      (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      InitECandidate.bitmaps p
      (pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig (sourceFfi input)
        t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode 3788 ltconf p)
      (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0 (fun _ => (ltconf, [], []))).2 = some aux)
    (h_word_no_err : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
          3788 ltconf sourceDeclarations wprog InitECandidate.bitmaps p 0 with clock := k_word }).1 ≠ some .error)
    (h_word_nt : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
          3788 ltconf sourceDeclarations wprog InitECandidate.bitmaps p 0 with clock := k_word }).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
        { pipelineStackInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
            (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
            3788 ltconf InitECandidate.bitmaps p 0 with clock := 2 * k_word })).1 ≠ some .timeOut := by
  have h := stage2_to_3_word_to_stack_withBitmaps_affine_not_timeOut w allChecked input k_word
    t m bitmapsDm sdm col wprog wconf fs p ltconf hwtw hwts h_word_no_err h_word_nt
  let c := oracleCompilerConfig w.oracles
  let stack := pipelineStackInitState c baselineMachineConfig (sourceFfi input) t m bitmapsDm sdm
    baselineInstalledState InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0
  obtain ⟨bitmapEq, _⟩ := fullMakeInit_bitmaps_code c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps p
    (pipelineLabInitState c baselineMachineConfig (sourceFfi input) t m bitmapsDm sdm
      baselineInstalledState InitECandidate.nativeCode 3788 ltconf p)
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0 (fun _ => (ltconf, [], []))
    stack aux (Prod.ext rfl hinit)
  have hsame : { stack with bitmaps := InitECandidate.bitmaps, clock := 2 * k_word } =
      { stack with clock := 2 * k_word } := by
    generalize hst : stack = stack0 at bitmapEq ⊢; cases stack0; simp only at bitmapEq; subst bitmapEq; rfl
  exact hsame ▸ h

end InitECandidate.Solver.Wave8Stage.R12_Stage2To3BoundArgon
