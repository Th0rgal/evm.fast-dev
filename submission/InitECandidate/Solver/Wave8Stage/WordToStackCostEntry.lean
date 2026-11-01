import InitECandidate.Solver.Wave8Stage.WordToStackCostSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordToStackCostEntry
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open InitECandidate.Solver.Wave8Stage.WordToStackSourceCost

/-- The native entry-call simulation retains its actual source-cost bound. -/
theorem compCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) :
    ∀ (start : Nat) (s : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
      (t : StackSemStateFiniteExact width C F) (lens : List Nat),
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k 0 0 s t lens 0 →
      ∃ (ck : Nat), ck ≤ sourceCost (.call none (some start) [0] none) s ∧
        ∃ (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
        StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := t.clock + ck}) =
          (res1, t1) ∧ (1 : BitVec width) ≠ 0 ∧ (2 : BitVec width) ≠ 0 ∧
        (open Classical in if res.map compileResult = res1 then s1.ffi = t1.ffi ∧ s1.clock = t1.clock
         else res1 = some (.halt (.word 2)) ∧ List.IsPrefix t1.ffi.ioEvents s1.ffi.ioEvents ∧
           s1.stackMax.getD (s1.stackLimit + 1) > s1.stackLimit) := by
  intro start s k res s1 t lens ⟨run, notError, related⟩
  have kBound : 4 < k := related.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ck, clockBound, t1, res1, targetRun, resultRel⟩ :=
    WordToStackCostSimulation.compCorrect ac (.call none (some start) [0] none) s k 0 0 s1 t res
      .nil .nil t.bitmaps.length t.bitmaps.length (.seq .skip (.call none (.inl start) none)) lens
      ⟨run, notError, related, by simp [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, isPhyVar], by simp [flatExpConventions], by
        simp [compNative, callDestNative, seqStackFreeNative, Compiler.Backend.WordToStack.stackFree],
        by simp [appListAppend, appendAux], by simp [appListAppend, appendAux], by simp [appListAppend, appendAux],
        by simp [StackSem.getLabelsExact], by simp [maxVarHOL, maxList]; omega⟩
  have wide : 8 ≤ width := by
    unfold stateRel at related
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩ := related
    exact h
  have oneLt : 1 < 2 ^ width := Nat.one_lt_two_pow (by omega)
  have twoLt : 2 < 2 ^ width :=
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by norm_num) wide
  refine ⟨ck, clockBound, t1, res1, (WordToStackProofs.CompCall.evaluateSeqSkip _ _).symm.trans targetRun, ?_, ?_, ?_⟩
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt oneLt] at this
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt twoLt] at this
  · unfold compCorrectResult at resultRel
    by_cases same : res.map compileResult = res1
    · rw [if_pos same]
      rw [if_neg (not_not.mpr same)] at resultRel
      have ffiClock : ∀ {f frame lens' extra} {s' : WordSemStateFiniteExact width (Nat × C) F},
          stateRel ac k f frame s' t1 lens' extra → s'.ffi = t1.ffi ∧ s'.clock = t1.clock :=
        fun rel => ⟨rel.2.2.2.1.symm, rel.1⟩
      rcases res with _ | r
      · exact ffiClock resultRel
      · cases r with
        | result _ values => exact ffiClock resultRel.1
        | exception _ value =>
          obtain ⟨nonGc, gc, rel, _, _⟩ := resultRel
          exact ffiClock (s' := pushLocals nonGc gc s1) rel
        | «break» _ => exact ffiClock resultRel
        | «continue» _ => exact ffiClock resultRel
        | _ => exact resultRel
    · rw [if_neg same]
      rw [if_pos same] at resultRel
      exact resultRel


/-- Any supplied upper bound on the source cost pays for a real non-timeout
native execution. Resource-failure runs are non-timeouts as well. -/
theorem notTimeOutOfCostBound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start registers clock budget : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (related : stateRel ac registers 0 0 source target [] 0)
    (notError : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .error)
    (notTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .timeOut)
    (costBound : clock + sourceCost (.call none (some start) [0] none)
      {source with clock := clock} ≤ budget) :
    (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {target with clock := budget})).1 ≠
      some .timeOut := by
  classical
  rcases run : WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock} with ⟨result,post⟩
  rw [run] at notError notTimeout
  obtain ⟨extra,extraBound,targetPost,targetResult,targetRun,_,_,contract⟩ :=
    compCall ac start {source with clock := clock} registers result post
      {target with clock := clock} []
      ⟨run,notError,SemanticsHelpers.stateRelWithClock ac registers clock source target [] 0 related⟩
  have targetNotTimeout : targetResult ≠ some .timeOut := by
    by_cases same : result.map compileResult = targetResult
    · intro timedOut
      have bad := same.trans timedOut
      cases result with
      | none => cases bad
      | some r =>
        cases r <;> simp [compileResult] at bad
        exact notTimeout rfl
    · rw [if_neg same] at contract
      rw [contract.1]
      simp
  have lifted := Compiler.Backend.StackProps.evaluateAddClock (budget-(clock+extra))
    (.call none (.inl start) none) {target with clock := clock+extra}
    targetResult targetPost ⟨targetRun,targetNotTimeout⟩
  have enough : clock + extra ≤ budget := by omega
  have budgetEq : clock+extra+(budget-(clock+extra)) = budget := by omega
  simp only [budgetEq] at lifted
  rw [lifted]
  exact targetNotTimeout

#print axioms notTimeOutOfCostBound

#print axioms compCall

end InitECandidate.Solver.Wave8Stage.WordToStackCostEntry
