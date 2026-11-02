import InitECandidate.Solver.Wave8Stage.WordToStackBitmapPipeline

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.WordCostFallbackCertificate
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open StackRemove.Proofs.InitMake WordCostEffects WordCostEntryCertificate WordCostCertificates

/-- Factor-two transfer on the actual initialization-failure branch. A ghost
full bitmap table establishes the native relation; evaluator refinement
transfers non-timeout back to the real short-table fallback. No successful
initialization or installed-machine premise is assumed. -/
theorem fallback_notTimeOut_two_mul {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width)) (dc : DataToWord.Config) (cfg : C)
    (generateGc jump : Bool) (maxHeap dataSpace pointer : Nat)
    (bounds : BitVec width × BitVec width) (lowerCode : Spt (HolProg width))
    (base target : StackSemStateFiniteExact width C F) (start clock : Nat)
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (defs (some entry.1)) = true)
    (entryBound : ∀ exit, AtMost (defs (some start) exit) 1)
    (oracleEq : target.ffi.oracle = oracle) (terminalCalls : TerminalOracle terminal oracle)
    (dimension : goodDimindex width) (widthBound : 8 ≤ width)
    (registers : ac.avoidRegs.length + 13 ≤ ac.regCount) (isa : ac.isa ≠ .ag32)
    (bitmapBound : bitmaps.length + 1 < 2 ^ width)
    (bitmapPrefix : [(4 : BitVec width)] <+: bitmaps)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (failed : makeInitOpt generateGc maxHeap bitmaps dataSpace (fun _ => (cfg, [], []))
      jump bounds pointer lowerCode base = none)
    (actual : StackAlloc.makeInit dc (sptFromAList stackCode) (fun _ => (cfg, [], []))
      (makeInitAny generateGc maxHeap bitmaps dataSpace (fun _ => (cfg, [], []))
        jump bounds pointer lowerCode base) = target)
    (notError : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) target (sptFromAList wordCode)
        (fun _ => ((bitmaps.length,cfg), [])) with clock := clock}).1 ≠ some .error)
    (notTimeout : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) target (sptFromAList wordCode)
        (fun _ => ((bitmaps.length,cfg), [])) with clock := clock}).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      {target with clock := 2 * clock})).1 ≠ some .timeOut := by
  let ghost := {target with bitmaps := bitmaps}
  have registerBound : 4 < ac.regCount - (5 + ac.avoidRegs.length) := by omega
  have ok := WordToStackFallbackInitialization.fallback_initStateOk ac dc _ cfg generateGc jump
    maxHeap dataSpace pointer bounds bitmaps lowerCode (sptFromAList stackCode) base
    dimension widthBound registerBound bitmapBound bitmapPrefix failed
  rw [actual] at ok
  have targetCode : target.code = sptFromAList stackCode := by rw [← actual]; rfl
  have short : target.bitmaps = [4] := by
    rw [← actual]
    simp only [StackAlloc.makeInit,makeInitAny,failed]
  have targetOracle : target.compileOracle = (fun _ => (cfg, [], [])) := by rw [← actual]; rfl
  obtain ⟨noRaise,noStore⟩ := panToTargetStubLocationsFree wc ac panCode col wordCode isa wtw
  have conventions := (BackendProof.compileToWordConventions2 wc ac _ col wordCode wtw
    (fun _ _ => Or.inr isa)).2.2
  have related := WordToStackCompileBudget.compile_stateRel ac wordCode ghost _
    (fun _ => ((bitmaps.length,cfg), []))
    (by change target.code = _; rw [targetCode,wts]) rfl ok noRaise noStore
    (by change (WordToStack.Native.compileNative ac false wordCode).1 <+: bitmaps
        rw [wts])
    (fun entry member => ⟨(conventions entry member).1,(conventions entry member).2.1⟩)
  simp only [ghost,WordToStackFallbackInitialization.makeInit_withBitmaps] at related
  have certificates := WordCostCodeCertificates.compile_codeCertified defs terminal wc ac
    (panToWordCompileProgHOL ac.isa panCode) fuel noLabels indirect
    (WordCostPipelineCertificate.panToWord_noMt_members ac.isa panCode) checked
  rw [wtw] at certificates
  have noInstall := WordToStackCompileBudget.compile_noInstall wc ac _ col wordCode wtw
    (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl)
  have extended := WordCostEntryCertificate.notTimeOut_two_mul ac _ start clock defs terminal
    (sptFromAList wordCode) oracle noInstall certificates terminalCalls _ ghost
    ⟨rfl,oracleEq⟩ entryBound related notError notTimeout
  obtain ⟨extra,appendEq⟩ := bitmapPrefix
  have targetEq : { {target with clock := 2 * clock} with bitmaps := target.bitmaps ++ extra} =
      {ghost with clock := 2 * clock} := by
    simp only [short,appendEq,ghost]
  apply StackBitmapRefinement.notTimeOut_of_append (.call none (.inl start) none)
    {target with clock := 2 * clock} extra (by trivial)
    (by change StackBitmapRefinement.CodeSafe target.code
        rw [targetCode]
        exact WordToStackBitmapPipeline.pipeline_codeSafe wc ac panCode col wordCode bitmaps wconf fs stackCode wtw wts)
    (by intro index; change (target.compileOracle index).2.1 = [] ∧ (target.compileOracle index).2.2 = []
        rw [targetOracle]; exact ⟨rfl,rfl⟩)
  simpa only [targetEq] using extended

end InitECandidate.Solver.Wave8Stage.WordCostFallbackCertificate
