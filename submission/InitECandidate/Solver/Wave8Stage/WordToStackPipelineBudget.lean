import InitECandidate.Solver.Wave8Stage.WordToStackCompileBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordToStackPipelineBudget
open Classical Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- The complete native relation for a successfully initialized Pan-to-target
pipeline. The compiler establishes all code and program-convention premises. -/
theorem initialized_stateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux)) :
    WordToStackProofs.stateRel ac (ac.regCount - (5 + ac.avoidRegs.length)) 0 0
      (WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
        (fun _ => ((bitmaps.length,cfg), []))) stack [] 0 := by
  obtain ⟨bitmapEq,codeEq⟩ := fullMakeInit_bitmaps_code scc dc maxHeap sp offset bitmaps
    stackCode lab saveRegs dataSp _ stack aux initialized
  have ok := panToTargetInitStateOk ac wordCode bitmaps wconf fs stackCode cfg scc dc
    maxHeap sp offset lab saveRegs dataSp stack aux dimension registers wts initialized
  rw [Nat.add_comm ac.avoidRegs.length 5] at ok
  obtain ⟨noRaise,noStore⟩ := panToTargetStubLocationsFree wc ac panCode col wordCode isa wtw
  have conventions := (BackendProof.compileToWordConventions2 wc ac _ col wordCode wtw
    (fun _ _ => Or.inr isa)).2.2
  apply WordToStackCompileBudget.compile_stateRel ac wordCode stack _ _
    (by rw [codeEq,wts]) rfl ok noRaise noStore
    (by rw [wts,bitmapEq])
  intro entry member
  exact ⟨(conventions entry member).1,(conventions entry member).2.1⟩

/-- Static affine budget on the actual initialized pipeline, with no assumed
native state relation or output conventions. -/
theorem initialized_notTimeOutOfStaticBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F) (start clock : Nat)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (notError : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
        (fun _ => ((bitmaps.length,cfg), [])) with clock := clock}).1 ≠ some .error)
    (notTimeout : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
        (fun _ => ((bitmaps.length,cfg), [])) with clock := clock}).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      {stack with clock := (WordToStackStaticBudget.codeBudget (sptFromAList wordCode) + 1) *
        clock})).1 ≠ some .timeOut := by
  have related := initialized_stateRel ac wc panCode col wordCode bitmaps wconf fs stackCode
    scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension registers isa
    wtw wts initialized
  apply WordToStackStaticBudget.notTimeOutOfStaticBudget ac start _ clock _ stack related
  · exact WordToStackCompileBudget.compile_noInstall wc ac _ col wordCode wtw
      (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
      (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl)
  · exact notError
  · exact notTimeout

#print axioms initialized_stateRel
#print axioms initialized_notTimeOutOfStaticBudget

end InitECandidate.Solver.Wave8Stage.WordToStackPipelineBudget
