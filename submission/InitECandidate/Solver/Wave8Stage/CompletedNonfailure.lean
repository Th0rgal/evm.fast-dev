import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CompletedNonfailure
open Flapjack Compiler.Backend Compiler.Backend.StackLang
open Compiler.Backend.StackToLab.Proofs.FlattenSemantics

/-- Two completed evaluations of the same Stack program have the same result. -/
theorem stack_result_agreement {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) (a b : Nat)
    (ha : (StackSemEvaluate.evaluate (p, {s with clock := a})).1 ≠ some .timeOut)
    (hb : (StackSemEvaluate.evaluate (p, {s with clock := b})).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate (p, {s with clock := a})).1 =
      (StackSemEvaluate.evaluate (p, {s with clock := b})).1 := by
  have ea := StackProps.evaluateAddClock (max a b - a) p {s with clock := a} _ _ ⟨rfl, ha⟩
  have eb := StackProps.evaluateAddClock (max a b - b) p {s with clock := b} _ _ ⟨rfl, hb⟩
  have ca : a + (max a b - a) = max a b := Nat.add_sub_of_le (Nat.le_max_left _ _)
  have cb : b + (max a b - b) = max a b := Nat.add_sub_of_le (Nat.le_max_right _ _)
  simp only [ca, cb] at ea eb
  have fa := congrArg (fun x : Option (StackSemResult width) × StackSemStateFiniteExact width C F => x.1) ea
  have fb := congrArg (fun x : Option (StackSemResult width) × StackSemStateFiniteExact width C F => x.1) eb
  exact fa.symm.trans fb

/-- A finite completed entry of an accepted class establishes semantic
nonfailure, without assuming the behavior of any other clock. -/
theorem stack_nonfail_of_ready {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (s : StackSemStateFiniteExact width C F) (k : Nat)
    (hne : stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {s with clock := k})).1 ≠ .RunError)
    (hnt : (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {s with clock := k})).1 ≠ some .timeOut) :
    StackSemEvaluate.semantics start s ≠ .fail := by
  have safe : ¬ ∃ clock trace, stackRuns start s clock = (.RunError, trace) := by
    rintro ⟨clock, trace, run⟩
    have bad := congrArg Prod.fst run
    change stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {s with clock := clock})).1 = .RunError at bad
    by_cases timeout : (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {s with clock := clock})).1 = some .timeOut
    · rw [timeout] at bad
      cases bad
    · have same := stack_result_agreement (.call none (.inl start) none) s clock k timeout hnt
      rw [same] at bad
      exact hne bad
  rw [stackSemIsWrapper]
  unfold crepToLoopSemanticsWrapper
  rw [if_neg safe]
  cases choice : holOptionSome (fun result => ∃ clock outcome events,
      stackRuns start s clock = (.CompleteResult outcome, events) ∧
        result = HolBehaviour.terminate outcome events) with
  | none => simp
  | some result =>
    obtain ⟨clock, outcome, events, _, rfl⟩ := holOptionSome_some choice
    simp

/-- Carry that nonfailure through the real full initializer. -/
theorem lab_nonfail_of_ready {width : Nat} [NeZero width] {C F : Type}
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (stack : StackSemStateFiniteExact width C F) (aux : Option (StackSemStateFiniteExact width C F))
    (initialized : StackToLab.Proofs.FullMakeInit.fullMakeInit sc dc maxHeap sp offset bitmaps code
      lab saveRegs dataSp oracle = (stack, aux))
    (assumptions : StackToLab.Proofs.FullMakeInitSemantics.Assumptions sc dc maxHeap sp offset
      bitmaps code lab saveRegs dataSp oracle)
    (k : Nat)
    (hne : stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        {stack with clock := k})).1 ≠ .RunError)
    (hnt : (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        {stack with clock := k})).1 ≠ some .timeOut) :
    LabSem.semantics lab ≠ .fail := by
  have ready := stack_nonfail_of_ready BvlToBvi.initGlobalsLocation stack k hne hnt
  have equal := (StackToLab.Proofs.FullMakeInitSemantics.assemble initialized assumptions).2 ready
  rw [equal]
  exact ready

#print axioms stack_result_agreement
#print axioms stack_nonfail_of_ready
#print axioms lab_nonfail_of_ready
end InitECandidate.Solver.Wave8Stage.CompletedNonfailure
