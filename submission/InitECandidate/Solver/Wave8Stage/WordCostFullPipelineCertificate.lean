import InitECandidate.Solver.Wave8Stage.WordCostFallbackCertificate

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.WordCostFullPipelineCertificate
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open WordCostEffects WordCostCertificates WordCostEntryCertificate
open StackRemove.Proofs.InitMake

/-- Unconditional-initialization factor-two transfer for the actual complete
pipeline. Both successful initialization and the literal fallback are covered.
Only finite cost checks and static bitmap bounds remain as code evidence. -/
theorem notTimeOut_two_mul {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack : StackSemStateFiniteExact width C F)
    (aux : Option (StackSemStateFiniteExact width C F)) (start clock : Nat)
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
    (dimension : goodDimindex width) (widthBound : 8 ≤ width)
    (bitmapBound : bitmaps.length + 1 < 2 ^ width)
    (bitmapPrefix : [(4 : BitVec width)] <+: bitmaps) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, aux))
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
  cases aux with
  | some aux =>
    exact WordCostPipelineCertificate.initialized_notTimeOut_two_mul ac wc panCode col wordCode
      bitmaps wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux start clock
      defs terminal oracle fuel noLabels indirect checked entryBound oracleEq terminalCalls dimension
      registers isa wtw wts initialized notError notTimeout
  | none =>
    have fallback : ∃ (lowerCode : Spt (HolProg width)) (base : StackSemStateFiniteExact width C F),
        makeInitOpt (StackToLab.isGenGc dc.gcKind) maxHeap bitmaps dataSp
          (fun _ => (cfg, [], [])) scc.jump offset sp lowerCode base = none ∧
        StackAlloc.makeInit dc (sptFromAList stackCode) (fun _ => (cfg, [], []))
          (makeInitAny (StackToLab.isGenGc dc.gcKind) maxHeap bitmaps dataSp
            (fun _ => (cfg, [], [])) scc.jump offset sp lowerCode base) = stack := by
      unfold FullMakeInit.fullMakeInit at initialized
      simp only [Prod.mk.injEq] at initialized
      exact ⟨_,_,initialized.2,initialized.1⟩
    obtain ⟨lowerCode,base,failed,actual⟩ := fallback
    have ffiEq := FullMakeInit.fullMakeInitFfi scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], []))
    rw [initialized] at ffiEq
    exact WordCostFallbackCertificate.fallback_notTimeOut_two_mul ac wc panCode col wordCode
      bitmaps wconf fs stackCode dc cfg (StackToLab.isGenGc dc.gcKind) scc.jump maxHeap dataSp sp
      offset lowerCode base stack start clock defs terminal oracle fuel noLabels indirect checked entryBound
      (by rw [ffiEq]; exact oracleEq) terminalCalls
      dimension widthBound registers isa bitmapBound bitmapPrefix wtw wts failed actual notError notTimeout

end InitECandidate.Solver.Wave8Stage.WordCostFullPipelineCertificate
