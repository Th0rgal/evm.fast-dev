import InitECandidate.Solver.Wave8GuestInv.FrontendStackTransfer
import InitECandidate.Solver.Wave8Stage.Stage4AllocGlue
import InitECandidate.Solver.Wave8Stage.WordToStackPipelineBudget

/-! Preserve entry completion through the bounded native simulation. This
also permits the compiler's resource-limit result, which is a complete run.
The result supplies Stage4's stronger entry-class premise. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.EntryClassTransfer
open Classical InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
open InitECandidate.Solver.Wave8Stage

theorem compiled_word_complete {width : Nat} [NeZero width]
    (result : Option (WordSemResult width))
    (complete : ∃ outcome, wordEntryClass result = .CompleteResult outcome) :
    ∃ outcome, stackEntryClass (result.map compileResult) = .CompleteResult outcome := by
  obtain ⟨outcome,complete⟩ := complete
  cases result with
  | none => cases complete
  | some result =>
    cases result <;> simp_all [wordEntryClass, stackEntryClass, compileResult]

theorem stack_complete_ready {width : Nat} [NeZero width]
    (result : Option (StackSemResult width))
    (complete : ∃ outcome, stackEntryClass result = .CompleteResult outcome) :
    stackEntryClass result ≠ .RunError ∧ result ≠ some .timeOut := by
  obtain ⟨outcome,complete⟩ := complete
  constructor
  · rw [complete]
    intro impossible
    cases impossible
  · intro timedOut
    rw [timedOut] at complete
    cases complete

/-- A real complete Stack entry run at the static code budget, including the
resource-limit branch of the original simulation. No target run is assumed. -/
theorem word_to_stack_static_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start registers clock : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (related : WordToStackProofs.stateRel ac registers 0 0 source target [] 0)
    (noInstall : WordProps.noInstallCode source.code)
    (complete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 =
        .CompleteResult outcome) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {target with clock := (WordToStackStaticBudget.codeBudget source.code + 1) * clock})).1 =
      .CompleteResult outcome := by
  have notError : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .error := by
    intro bad
    obtain ⟨outcome,complete⟩ := complete
    rw [bad] at complete
    cases complete
  rcases run : WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock} with ⟨result,post⟩
  rw [run] at complete notError
  obtain ⟨extra,extraBound,targetPost,targetResult,targetRun,_,_,contract⟩ :=
    WordToStackCostEntry.compCall ac start {source with clock := clock} registers result post
      {target with clock := clock} []
      ⟨run,notError,WordToStackProofs.SemanticsHelpers.stateRelWithClock
        ac registers clock source target [] 0 related⟩
  have targetComplete : ∃ outcome, stackEntryClass targetResult = .CompleteResult outcome := by
    by_cases same : result.map compileResult = targetResult
    · rw [← same]
      exact compiled_word_complete result complete
    · rw [if_neg same] at contract
      rw [contract.1]
      exact ⟨_,rfl⟩
  have targetNotTimeout := (stack_complete_ready targetResult targetComplete).2
  have cost := WordToStackStaticBudget.entryCost_bound start {source with clock := clock}
    noInstall (by rw [run]; exact notError)
  let budget := (WordToStackStaticBudget.codeBudget source.code + 1) * clock
  have enough : clock + extra ≤ budget := by
    dsimp only [budget]
    change WordToStackSourceCost.sourceCost _ _ ≤
      WordToStackStaticBudget.codeBudget source.code * clock at cost
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have lifted := Flapjack.Compiler.Backend.StackProps.evaluateAddClock
    (budget-(clock+extra)) (.call none (.inl start) none)
    {target with clock := clock+extra} targetResult targetPost ⟨targetRun,targetNotTimeout⟩
  have clockEq : clock+extra+(budget-(clock+extra)) = budget := by omega
  simp only [clockEq] at lifted
  change ∃ outcome, stackEntryClass
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      {target with clock := budget})).1 = .CompleteResult outcome
  rw [lifted]
  exact targetComplete

/-- Entry completion on the actual successfully initialized compiler pipeline. -/
theorem initialized_word_to_stack_complete {width : Nat} [NeZero width] {C F : Type}
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
    (complete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none)
      {WordToStack.Native.Initialization.makeInit ac
        (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList wordCode)
        (fun _ => ((bitmaps.length,cfg), [])) with clock := clock}).1 = .CompleteResult outcome) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {stack with clock := (WordToStackStaticBudget.codeBudget (sptFromAList wordCode) + 1) *
          clock})).1 = .CompleteResult outcome := by
  have related := WordToStackPipelineBudget.initialized_stateRel ac wc panCode col wordCode
    bitmaps wconf fs stackCode scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux
    dimension registers isa wtw wts initialized
  apply word_to_stack_static_complete ac start _ clock _ stack related
  · exact WordToStackCompileBudget.compile_noInstall wc ac _ col wordCode wtw
      (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
      (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl)
  · exact complete

end InitECandidate.Solver.Wave8GuestInv.EntryClassTransfer
