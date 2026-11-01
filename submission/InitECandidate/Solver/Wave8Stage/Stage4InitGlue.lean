import InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.Stage4

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock

/-- Initialization adds one StackSem entry-call tick, independently of its
straight-line instruction count. This does not claim a one-tick LabSem cost. -/
theorem stack_init_entry_result {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (s post : StackSemStateFiniteExact width C F) (k : Nat)
    (hentry : sptLookup 0 s.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s) =
      (none, post)) :
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s with clock := k + 1 })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { post with clock := k })).1 := by
  have clockRun := evaluateInitCodeClock generateGc maxHeap pointer s post none k hrun
  have body : StackSemEvaluate.evaluate
      (.seq (StackRemove.initCode generateGc maxHeap pointer) (.call none (.inl start) none),
        { s with clock := k }) =
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { post with clock := k }) := by
    rw [StackSemEvaluate.evaluate_seq, clockRun]
    simp [StackSemControl.fixClock]
  have notBad := StackRemove.Proofs.InitSemantics.callNotBad start { post with clock := k }
  rw [StackSemEvaluate.evaluate_call]
  simp only [StackSemControl.findCode, hentry, Nat.add_one_ne_zero, if_false,
    StackSemStateOps.decClock, Nat.add_sub_cancel]
  rw [show ({ ({ s with clock := k + 1 } : StackSemStateFiniteExact width C F) with
      clock := k } : StackSemStateFiniteExact width C F) = { s with clock := k } from rfl, body]
  simp only [StackSemControl.fixClock, notBad]
  rfl

/-- The initializer transfers non-timeout at the exact additional tick. -/
theorem stack_init_entry_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (s post : StackSemStateFiniteExact width C F) (k : Nat)
    (hentry : sptLookup 0 s.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s) =
      (none, post))
    (hnt : (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { post with clock := k })).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s with clock := k + 1 })).1 ≠ some .timeOut := by
  rw [stack_init_entry_result generateGc maxHeap pointer start s post k hentry hrun]
  exact hnt

#print axioms stack_init_entry_result
#print axioms stack_init_entry_not_timeOut

end InitECandidate.Solver.Wave8Stage.Stage4
