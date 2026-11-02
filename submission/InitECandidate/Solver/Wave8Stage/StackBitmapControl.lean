import InitECandidate.Solver.Wave8Stage.StackBitmapAtomic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapControl
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open StackSemStateOps StackSemEvaluate StackSemControl

/-- Every nonerror execution survives appending the same bitmap suffix,
with exactly the same result and every other returned state field. -/
def Refines {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) : Prop :=
  ∀ (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F),
    res ≠ some .error → evaluate (p,s) = (res,post) →
    evaluate (p,{s with bitmaps := s.bitmaps ++ extra}) =
      (res,{post with bitmaps := post.bitmaps ++ extra})

/-- Sequential composition needs refinement only at its actual recursive
states, including the evaluator's clock clamp. -/
theorem seq {width : Nat} [NeZero width] {C F : Type}
    (a b : HolProg width) (s : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width))
    (firstIH : Refines a s extra)
    (secondIH : ∀ middle, evaluate (a,s) = (none,middle) →
      Refines b {middle with clock := min s.clock middle.clock} extra) :
    Refines (.seq a b) s extra := by
  intro res post notError run
  rw [evaluate_seq] at run ⊢
  rcases evaluated : evaluate (a,s) with ⟨result,middle⟩
  have fine : result ≠ some .error := by
    intro bad
    subst result
    simp only [evaluated,fixClock] at run
    cases run
    exact notError rfl
  have lifted := firstIH result middle fine evaluated
  rw [lifted]
  simp only [evaluated,fixClock] at run
  simp only [fixClock]
  cases result with
  | none => exact secondIH middle evaluated res post notError run
  | some value => cases run; rfl

private theorem getVarImm_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (bitmaps : List (BitVec width))
    (ri : HolRegImm width) :
    StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) {s with bitmaps := bitmaps} =
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s := by
  cases ri <;> rfl

/-- Both conditional branches run in the unchanged source state. -/
theorem ite {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F) (extra : List (BitVec width))
    (leftIH : Refines a s extra) (rightIH : Refines b s extra) :
    Refines (.ite cmp r ri a b) s extra := by
  intro res post notError run
  rw [evaluate_ite] at run ⊢
  simp only [getVar,getVarImm_withBitmaps]
  simp only [getVar] at run
  split at run
  · split at run
    · exact leftIH res post notError run
    · exact rightIH res post notError run
    · cases run; contradiction
  · cases run; contradiction

/-- Loop refinement includes normal completion, every loop control result,
timeout at the reentry boundary, and recursive reentry after a decrement. -/
theorem loop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) (bodyIH : Refines body s extra)
    (loopIH : ∀ middle result, evaluate (body,s) = (result,middle) →
      contLoop result = true → min s.clock middle.clock ≠ 0 →
      Refines (.loop body) (decClock {middle with clock := min s.clock middle.clock}) extra) :
    Refines (.loop body) s extra := by
  intro res post notError run
  rw [evaluate_loop] at run ⊢
  rcases evaluated : evaluate (body,s) with ⟨result,middle⟩
  have fine : result ≠ some .error := by
    intro bad
    subst result
    simp only [evaluated,fixClock,StackSemControl.contLoop,StackSemControl.exitLoop,Bool.false_eq_true,if_false] at run
    cases run
    exact notError rfl
  rw [bodyIH result middle fine evaluated]
  simp only [evaluated,fixClock] at run
  simp only [fixClock]
  split at run
  · rename_i continues
    simp only [continues,if_true]
    split at run
    · rename_i zero
      simp only [zero,if_true]
      cases run
      simp only [emptyEnv,zero]
    · rename_i nonzero
      simp only [nonzero,if_false]
      exact loopIH middle result evaluated continues nonzero res post notError run
  · rename_i stopped
    simp only [stopped]
    cases run
    rfl

end InitECandidate.Solver.Wave8Stage.StackBitmapControl
