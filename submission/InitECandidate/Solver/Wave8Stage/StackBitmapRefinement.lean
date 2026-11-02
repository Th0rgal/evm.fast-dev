import InitECandidate.Solver.Wave8Stage.StackBitmapCall

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapRefinement
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackProps
open StackSemStateOps StackSemEvaluate StackSemControl StackSemMeasure
open StackBitmapControl

/-- Native control fragment: allocation and installation are excluded;
all recursive children, return continuations and handlers satisfy the same
condition. The two lower-level jump constructors are not generated here. -/
def Safe {width : Nat} [NeZero width] : HolProg width → Prop
  | .alloc _ | .install _ _ _ _ _ | .jumpLower _ _ _ | .rawCall _ => False
  | .seq a b | .ite _ _ _ a b => Safe a ∧ Safe b
  | .loop body => Safe body
  | .call ret _ handler =>
      (match ret with | none => True | some (body,_,_,_) => Safe body) ∧
      (match handler with | none => True | some (body,_,_) => Safe body)
  | _ => True

/-- Every code lookup selects a program in the refinement fragment. -/
def CodeSafe {width : Nat} [NeZero width] (code : Spt (HolProg width)) : Prop :=
  ∀ name body, sptLookup name code = some body → Safe body

private theorem find_safe {width : Nat} [NeZero width]
    (code : Spt (HolProg width)) (regs : HolFiniteMapExact Nat (WordLocW width))
    (dest : Sum Nat Nat) (body : HolProg width) (safe : CodeSafe code)
    (found : findCode dest regs code = some body) : Safe body := by
  cases dest with
  | inl name => exact safe name body found
  | inr register =>
    simp only [findCode] at found
    split at found
    · exact safe _ body found
    · contradiction

private theorem after {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s post : StackSemStateFiniteExact width C F)
    (res : Option (StackSemResult width)) (empty : StackEmptyOracle.EmptyOracle s)
    (safe : CodeSafe s.code) (run : evaluate (p,s) = (res,post)) :
    StackEmptyOracle.EmptyOracle post ∧ CodeSafe post.code := by
  have kept := StackEmptyOracle.preserved p s empty
  rw [run] at kept
  exact ⟨kept.2.2,by rw [kept.1]; exact safe⟩

private theorem ordinary {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) (empty : StackEmptyOracle.EmptyOracle s)
    (atomic : StackBitmapAtomic.Ordinary p) : Refines p s extra := by
  intro res post notError run
  have lifted := StackBitmapAtomic.ordinary_append p s extra atomic empty
  rw [run] at lifted
  exact lifted

private theorem measure_refines {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = measure → Safe p → CodeSafe s.code →
      StackEmptyOracle.EmptyOracle s → ∀ extra, Refines p s extra := by
  intro measure
  induction measure using EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
    intro p s hm safe codes empty extra
    subst hm
    cases p
    case alloc n => exact False.elim safe
    case install a b c d e => exact False.elim safe
    case jumpLower a b c => exact False.elim safe
    case rawCall dest => exact False.elim safe
    case storeConsts a b stub =>
      intro res post ne run
      exact StackBitmapAtomic.storeConsts_append a b stub s post extra res ne run
    case bitmapLoad r v =>
      intro res post ne run
      exact StackBitmapAtomic.bitmapLoad_append r v s post extra res ne run
    case seq a b =>
      apply StackBitmapControl.seq a b s extra
      · exact ih _ (seq_first_measure_lt a b s) a s rfl safe.1 codes empty extra
      · intro middle run
        have next := after a s middle none empty codes run
        exact ih _ (seq_second_measure_lt a b s ((none : Option (StackSemResult width)),middle)) b _ rfl
          safe.2 next.2 next.1 extra
    case ite cmp r ri a b =>
      exact StackBitmapControl.ite cmp r ri a b s extra
        (ih _ (if_first_measure_lt cmp r ri a b s) a s rfl safe.1 codes empty extra)
        (ih _ (if_second_measure_lt cmp r ri a b s) b s rfl safe.2 codes empty extra)
    case loop body =>
      apply StackBitmapControl.loop body s extra
      · exact ih _ (loop_body_measure_lt body s) body s rfl safe codes empty extra
      · intro middle result run continues nonzero
        have next := after body s middle result empty codes run
        exact ih _ (loop_reentry_measure_lt body s (result,middle) nonzero) (.loop body) _ rfl
          safe next.2 next.1 extra
    case call ret dest handler =>
      cases ret with
      | none =>
        apply StackBitmapCall.tail dest handler s extra
        intro prog found nonzero
        exact ih _ (callee_measure_lt prog (.call none dest handler) s nonzero) prog _ rfl
          (find_safe s.code s.regs dest prog codes found) codes empty extra
      | some ret =>
        obtain ⟨retH,link,l1,l2⟩ := ret
        rw [Safe.eq_def] at safe
        dsimp only at safe
        apply StackBitmapCall.returning retH link l1 l2 dest handler s extra
        · intro prog found nonzero
          exact ih _ (callee_measure_lt prog (.call (some (retH,link,l1,l2)) dest handler)
            (setVar link (.loc l1 l2) s) nonzero) prog _ rfl
            (find_safe s.code (s.regs.eraseEq link) dest prog codes found) codes empty extra
        · intro prog middle found nonzero run
          have next := after prog (decClock (setVar link (.loc l1 l2) s)) middle
            (some (.result (.loc l1 l2))) empty codes run
          exact ih _ (call_continuation_measure_lt retH (.call (some (retH,link,l1,l2)) dest handler)
            s link l1 l2 (some (.result (.loc l1 l2) : StackSemResult width),middle) nonzero)
            retH _ rfl safe.1 next.2 next.1 extra
        · intro prog middle h hl1 hl2 found nonzero handlerEq run
          have next := after prog (decClock (setVar link (.loc l1 l2) s)) middle
            (some (.exception (.loc hl1 hl2))) empty codes run
          have handlerSafe : Safe h := by
            simpa only [Safe,handlerEq] using safe.2
          exact ih _ (call_continuation_measure_lt h (.call (some (retH,link,l1,l2)) dest handler)
            s link l1 l2 (some (.exception (.loc hl1 hl2) : StackSemResult width),middle) nonzero)
            h _ rfl handlerSafe next.2 next.1 extra
    all_goals exact ordinary _ s extra empty (by trivial)

/-- Full native evaluator refinement. Appending bitmap entries preserves
all nonerror executions in the fragment, including timeout executions. -/
theorem evaluate_append {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) (safe : Safe p) (codes : CodeSafe s.code)
    (empty : StackEmptyOracle.EmptyOracle s) : Refines p s extra :=
  measure_refines (stackSemMeasure p s) p s rfl safe codes empty extra

/-- Contraposition transfers a non-timeout proof on the extended table back
to the original table without assuming the original execution succeeds. -/
theorem notTimeOut_of_append {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) (safe : Safe p) (codes : CodeSafe s.code)
    (empty : StackEmptyOracle.EmptyOracle s)
    (extended : (evaluate (p,{s with bitmaps := s.bitmaps ++ extra})).1 ≠ some .timeOut) :
    (evaluate (p,s)).1 ≠ some .timeOut := by
  intro timedOut
  have run : evaluate (p,s) = (some .timeOut,(evaluate (p,s)).2) := by
    exact Prod.ext timedOut rfl
  have lifted := evaluate_append p s extra safe codes empty (some .timeOut) _ (by intro h; cases h) run
  exact extended (congrArg Prod.fst lifted)

end InitECandidate.Solver.Wave8Stage.StackBitmapRefinement
