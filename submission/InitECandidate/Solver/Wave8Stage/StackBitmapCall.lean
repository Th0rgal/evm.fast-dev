import InitECandidate.Solver.Wave8Stage.StackBitmapControl

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapCall
open Flapjack Flapjack.Compiler.Backend.StackLang
open StackSemStateOps StackSemEvaluate StackSemControl StackBitmapControl

/-- Tail-call refinement uses only the selected callee after the actual
entry decrement. All bad-return and absent-code guards are retained. -/
theorem tail {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (s : StackSemStateFiniteExact width C F) (extra : List (BitVec width))
    (calleeIH : ∀ prog, findCode dest s.regs s.code = some prog → s.clock ≠ 0 →
      Refines prog (decClock s) extra) :
    Refines (.call none dest handler) s extra := by
  intro res post notError run
  rw [evaluate_call] at run ⊢
  dsimp only at run ⊢
  split at run
  · cases run; contradiction
  · rename_i prog found
    cases handler with
    | some handler => cases run; contradiction
    | none =>
      dsimp only at run ⊢
      split at run
      · rename_i zero
        try simp only [zero,if_true]
        cases run
        simp only [emptyEnv,zero]
      · rename_i nonzero
        try simp only [nonzero,if_false]
        rcases evaluated : evaluate (prog,decClock s) with ⟨result,middle⟩
        have fine : result ≠ some .error := by
          intro bad
          subst result
          simp only [evaluated,fixClock,StackSemControl.badFunReturn,Bool.false_eq_true,if_false] at run
          cases run
          exact notError rfl
        have lifted := calleeIH prog found nonzero result middle fine evaluated
        simp only [decClock] at lifted ⊢
        simp only [lifted]
        simp only [evaluated,fixClock] at run
        simp only [fixClock]
        split at run
        · cases run; contradiction
        · rename_i good
          simp only [good]
          cases run
          rfl

/-- Returning calls refine the actual callee, matching return continuation,
and matching exception handler, preserving link registers and clock clamps. -/
theorem returning {width : Nat} [NeZero width] {C F : Type}
    (retH : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (s : StackSemStateFiniteExact width C F) (extra : List (BitVec width))
    (calleeIH : ∀ prog, findCode dest (s.regs.eraseEq link) s.code = some prog → s.clock ≠ 0 →
      Refines prog (decClock (setVar link (.loc l1 l2) s)) extra)
    (returnIH : ∀ prog middle,
      findCode dest (s.regs.eraseEq link) s.code = some prog → s.clock ≠ 0 →
      evaluate (prog,decClock (setVar link (.loc l1 l2) s)) =
        (some (.result (.loc l1 l2)),middle) →
      Refines retH {middle with clock := min (s.clock - 1) middle.clock} extra)
    (exceptionIH : ∀ prog middle h hl1 hl2,
      findCode dest (s.regs.eraseEq link) s.code = some prog → s.clock ≠ 0 →
      handler = some (h,hl1,hl2) →
      evaluate (prog,decClock (setVar link (.loc l1 l2) s)) =
        (some (.exception (.loc hl1 hl2)),middle) →
      Refines h {middle with clock := min (s.clock - 1) middle.clock} extra) :
    Refines (.call (some (retH,link,l1,l2)) dest handler) s extra := by
  classical
  intro res post notError run
  rw [evaluate_call] at run ⊢
  dsimp only at run ⊢
  split at run
  · cases run; contradiction
  · rename_i prog found
    split at run
    · rename_i zero
      simp only [zero,if_true]
      cases run
      simp only [emptyEnv,zero]
    · rename_i nonzero
      simp only [nonzero,if_false]
      rcases evaluated : evaluate (prog,decClock (setVar link (.loc l1 l2) s)) with ⟨result,middle⟩
      have fine : result ≠ some .error := by
        intro bad
        subst result
        simp only [evaluated,fixClock] at run
        cases run
        exact notError rfl
      have lifted := calleeIH prog found nonzero result middle fine evaluated
      simp only [decClock,setVar] at lifted ⊢
      simp only [lifted]
      simp only [evaluated,fixClock] at run
      simp only [setVar,decClock] at run
      simp only [fixClock]
      cases result with
      | none => cases run; contradiction
      | some value =>
        cases value with
        | result value =>
          dsimp only at run ⊢
          split at run
          · cases run; contradiction
          · rename_i matched
            have equality : value = .loc l1 l2 := by simpa using matched
            subst value
            simp only [ne_eq,not_true_eq_false,if_false]
            exact returnIH prog middle found nonzero evaluated res post notError run
        | exception value =>
          dsimp only at run ⊢
          cases handler with
          | none => cases run; rfl
          | some handler =>
            obtain ⟨h,hl1,hl2⟩ := handler
            dsimp only at run ⊢
            split at run
            · cases run; contradiction
            · rename_i matched
              have equality : value = .loc hl1 hl2 := by simpa using matched
              subst value
              simp only [ne_eq,not_true_eq_false,if_false]
              exact exceptionIH prog middle h hl1 hl2 found nonzero rfl evaluated res post notError run
        | «break» value => cases run; contradiction
        | «continue» value => cases run; contradiction
        | halt value => cases run; rfl
        | finalFFI value => cases run; rfl
        | timeOut => cases run; rfl
        | error => cases run; contradiction

#print axioms tail
#print axioms returning
end InitECandidate.Solver.Wave8Stage.StackBitmapCall
