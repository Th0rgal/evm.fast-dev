import InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer

/-! Compose the initialized frontend/Word/Stack result with Stage4.
Original frontend, initialization and memory premises remain explicit. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace InitECandidate.Solver.Wave8GuestInv.InitializedLabTransfer
open Classical InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.LoopToWord.CompileCorrect
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.SelfContainedStageBounds
open EntryClassTransfer

open InitializedPipelineTransfer
open InitECandidate.Solver.Wave8Stage.RuntimeLabels

theorem pan_to_initialized_lab_not_timeOut {width : Nat} [NeZero width] {C F : Type}
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
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (source : PanSemStateFiniteExact width F) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width))
    (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result,post))
    (notError : panEntryClass result ≠ .RunError)
    (notTimeout : result ≠ some .timeOut)
    (assumptions : FullMakeInitSemantics.Assumptions scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])))
    (memorySafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    (LabSem.evaluate {lab with
      clock := 2 * (M + 1) * stackClock panCode start wordCode k + (3 * M + 2)}).1 ≠ .timeOut := by
  have complete := pan_to_initialized_stack_complete ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout
  have ready := stack_complete_ready _ complete
  have compiled : stackCode = (WordToStack.Native.compileNative ac false
      (WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode)).2).2.2.2 := by
    rw [wtw, wts]
  have bridge := Stage4.fullMakeInit_lab_affine_of_source_run scc dc maxHeap sp offset
    bitmaps stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) assumptions
    ac false wc ac.isa panCode compiled memorySafe (fun _ => rfl)
    (stackClock panCode start wordCode k)
  simp only [initialized] at bridge
  exact bridge ready.1 ready.2

/-- Preserve the completed result at the affine Lab clock. This supplies the
Stage 5 halt premise from the original source run, with no intermediate run premise. -/
theorem pan_to_initialized_lab_complete {width : Nat} [NeZero width] {C F : Type}
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
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (source : PanSemStateFiniteExact width F) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width))
    (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result,post))
    (notError : panEntryClass result ≠ .RunError)
    (notTimeout : result ≠ some .timeOut)
    (assumptions : FullMakeInitSemantics.Assumptions scc dc maxHeap sp offset bitmaps
      stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])))
    (memorySafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory) :
    let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 scc dc maxHeap sp offset stackCode)
    ∃ outcome, (LabSem.evaluate {lab with
      clock := 2 * (M + 1) * stackClock panCode start wordCode k + (3 * M + 2)}).1 = .halt outcome := by
  obtain ⟨outcome, complete⟩ := pan_to_initialized_stack_complete ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout
  have bounded := pan_to_initialized_lab_not_timeOut ac wc panCode col wordCode bitmaps wconf
    fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux dimension
    registers isa wtw wts initialized source start globalsSize heapLen front stCtxt s_decls
    hst decls k result post run notError notTimeout assumptions memorySafe
  exact ⟨outcome, (full_make_init_halt_of_lab_not_timeOut initialized assumptions
    (stackClock panCode start wordCode k) _ _ outcome rfl complete _ bounded).1⟩

end InitECandidate.Solver.Wave8GuestInv.InitializedLabTransfer
