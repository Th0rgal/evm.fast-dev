import InitECandidate.Solver.StackToLabClockBound
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock

/-!
The StackRemove initializer has exactly zero StackSem clock cost, independently
of the store table length. This is NOT a bound on the existential `ck_lab` in
`stack_to_lab_linear_clock_halt`: that witness is produced by flattening the
whole entry execution (FlattenSemantics.stackRunsSim / flattenCallCorrect).
A concrete LabSem bound requires a quantitative flattening theorem as well.
In particular, zero StackSem ticks do not imply zero LabSem instructions.
-/
namespace InitECandidate.Solver.StackRemoveInitOffsetBound
open Flapjack Flapjack.Compiler.Backend
open StackLang StackProps StackRemove StackRemove.Proofs.InitClock

set_option autoImplicit false

/-- Every store-table initializer is neutral, with no length restriction. -/
theorem store_list_neutral {width : Nat} [NeZero width]
    (values : List (Sum (BitVec width) Nat)) (address temporary : Nat) :
    clockNeutralHOL (storeListCode address temporary values) :=
  clockNeutralStoreListCode values address temporary

/-- The four memory setup instructions and the whole store table are neutral. -/
theorem init_memory_neutral {width : Nat} [NeZero width]
    (pointer : Nat) (values : List (Sum (BitVec width) Nat)) :
    clockNeutralHOL (initMemory pointer values) := by
  simp [initMemory, listSeqHOL, constInst, subInst, storeInst,
    clockNeutralHOL, clockNeutralStoreListCode]

/-- All branches of the complete initializer have zero StackSem clock cost. -/
theorem init_code_neutral {width : Nat} [NeZero width]
    (generateGc : Bool) (maximumHeap pointer : Nat) :
    clockNeutralHOL (initCode (width := width) generateGc maximumHeap pointer) :=
  initCodeClockNeutral generateGc maximumHeap pointer

private theorem neutral_post_clock {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (h : clockNeutralHOL p) :
    (StackSemEvaluate.evaluate (p, s)).2.clock = s.clock := by
  rcases he : StackSemEvaluate.evaluate (p, s) with ⟨r, t⟩
  have hx := EvaluateNeutral.evaluateClockNeutral p s t r s.clock ⟨he, h⟩
  have hs : {s with clock := s.clock} = s := rfl
  rw [hs, he] at hx
  have ht := congrArg (fun x => x.2.clock) hx
  exact ht

/-- Exact cost, including unsuccessful store-list evaluations. -/
theorem store_list_post_clock {width : Nat} [NeZero width] {C F : Type}
    (values : List (Sum (BitVec width) Nat)) (address temporary : Nat)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (storeListCode address temporary values, s)).2.clock = s.clock :=
  neutral_post_clock _ s (store_list_neutral values address temporary)

/-- Exact memory-initialization clock, for arbitrary values and pointer aliases. -/
theorem init_memory_post_clock {width : Nat} [NeZero width] {C F : Type}
    (pointer : Nat) (values : List (Sum (BitVec width) Nat))
    (s : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (initMemory pointer values, s)).2.clock = s.clock :=
  neutral_post_clock _ s (init_memory_neutral pointer values)

/-- Exact initializer clock, independent of heap size and GC configuration. -/
theorem init_code_post_clock {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s)).2.clock = s.clock :=
  neutral_post_clock _ s (init_code_neutral generateGc maximumHeap pointer)

/-- Replacing the clock by zero preserves the complete initialization result. -/
theorem init_code_at_zero {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, {s with clock := 0}) =
      ((StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s)).1,
       {(StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s)).2 with clock := 0}) := by
  exact evaluateInitCodeClock generateGc maximumHeap pointer s _ _ 0 rfl

/-- The concrete, sharp StackSem initialization offset is zero. This statement
makes no assertion about the distinct whole-execution LabSem overhead. -/
theorem init_code_consumed_ticks {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    s.clock - (StackSemEvaluate.evaluate
      (initCode generateGc maximumHeap pointer, s)).2.clock = 0 := by
  rw [init_code_post_clock]; omega

/-- Arithmetic composition once a quantitative flattening bound is supplied.
The overhead premise is explicit: initialization neutrality cannot discharge it. -/
theorem compose_lab_budget (k_stack ck_lab C D : Nat)
    (positive : 1 ≤ k_stack) (flatten_bound : ck_lab ≤ C * k_stack + D) :
    (k_stack - 1) + ck_lab + 2 ≤ (C + 1) * k_stack + D + 1 := by
  have he : (C + 1) * k_stack = C * k_stack + k_stack := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

#print axioms init_code_consumed_ticks
#print axioms compose_lab_budget
end InitECandidate.Solver.StackRemoveInitOffsetBound
