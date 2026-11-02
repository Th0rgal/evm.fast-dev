import InitECandidate.Solver.Wave8Stage.WordCostCodeCertificates
import InitECandidate.Solver.Wave8Stage.WordToStackPipelineBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostPipelineCertificate
open Classical Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open WordCostEffects WordCostCertificates WordCostEntryCertificate

/-- The no-MustTerminate property holds for every compiled association,
including associations hidden by another entry with the same key. -/
theorem panToWord_noMt_members {width : Nat} [NeZero width]
    (isa : AsmArchitecture) (source : List (DeclHOL width)) :
    ∀ entry ∈ panToWordCompileProgHOL isa source, noMtSubprogsHOL entry.2.2 = true := by
  intro entry member
  rcases entry with ⟨name,arity,body⟩
  rw [noMtSubprogsHOL_eq_notCreated]
  apply LoopToWord.loop_to_word_compile_not_created_MEM name arity body _ _ member
  intro x hx
  cases x <;> simp_all

/-- Actual initialized Pan-to-target pipeline at factor two. The only
remaining code evidence is a finite Boolean prefix check for every function;
no semantic cost bound or target execution is assumed. -/
theorem initialized_notTimeOut_two_mul {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F) (start clock : Nat)
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (oracle : HolOracle F) (fuel : Nat)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (indirect : ∀ name, Subeffects (defs (some name)) (defs none))
    (checked : ∀ entry ∈ panToWordCompileProgHOL ac.isa panCode,
      WordCostCheck.checkProgram defs terminal fuel
        (WordCostCompilerControl.preAllocation ac ac.twoRegArith entry.2.1 entry.2.2)
        (defs (some entry.1)) = true)
    (entryBound : ∀ exit, AtMost (defs (some start) exit) 1)
    (oracleEq : lab.ffi.oracle = oracle) (terminalCalls : TerminalOracle terminal oracle)
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
      {stack with clock := 2 * clock})).1 ≠ some .timeOut := by
  have related := WordToStackPipelineBudget.initialized_stateRel ac wc panCode col wordCode bitmaps
    wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized
  have certificates := WordCostCodeCertificates.compile_codeCertified defs terminal wc ac
    (panToWordCompileProgHOL ac.isa panCode) fuel noLabels indirect
    (panToWord_noMt_members ac.isa panCode) checked
  rw [wtw] at certificates
  have ffiEq := FullMakeInit.fullMakeInitFfi scc dc maxHeap sp offset bitmaps stackCode lab
    saveRegs dataSp (fun _ => (cfg, [], []))
  rw [initialized] at ffiEq
  have noInstall := WordToStackCompileBudget.compile_noInstall wc ac _ col wordCode wtw
    (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl)
  exact WordCostEntryCertificate.notTimeOut_two_mul ac _ start clock defs terminal
    (sptFromAList wordCode) oracle noInstall certificates terminalCalls _ stack
    ⟨rfl,by change stack.ffi.oracle = oracle; rw [ffiEq]; exact oracleEq⟩
    entryBound related notError notTimeout

#print axioms panToWord_noMt_members
#print axioms initialized_notTimeOut_two_mul
end InitECandidate.Solver.Wave8Stage.WordCostPipelineCertificate
