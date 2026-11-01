import InitECandidate.Solver.Wave8Stage.WordToStackSourceCost
import InitECandidate.Solver.Wave8Stage.WordToStackSeqClock
import InitECandidate.Solver.Wave8Stage.WordToStackIfClock
import InitECandidate.Solver.Wave8Stage.WordToStackLoopClock

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
Compose the source execution cost through Seq, If and Loop using their
original guarded source induction hypotheses. The result bounds the actual
extra-clock witnesses of the complete native simulations.
-/

namespace InitECandidate.Solver.Wave8Stage.WordToStackCostComposition
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open InitECandidate.Solver.Wave8Stage.WordToStackBounded
open InitECandidate.Solver.Wave8Stage.WordToStackSourceCost

/-- Weakening the bound keeps the very same execution witness. -/
theorem simulation_mono {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {program : WordLangProgHOL (BitVec width)}
    {source : WordSemStateFiniteExact width (Nat × C) F} {small large : Nat}
    (simulation : SimulationB ac program source small) (bound : small ≤ large) :
    SimulationB ac program source large := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises
  obtain ⟨clock, clockBound, targetPost, targetResult, run, conclusion⟩ :=
    simulation k f frame post target result bs bsPost n nPost compiled lens premises
  exact ⟨clock, clockBound.trans bound, targetPost, targetResult, run, conclusion⟩

theorem compCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ result middle, (result,middle) = evaluate first source ∧ result = none →
      SimulationB ac second middle (sourceCost second middle)) ∧
      SimulationB ac first source (sourceCost first source)) :
    SimulationB ac (.seq first second) source (sourceCost (.seq first second) source) := by
  rw [sourceCost]
  split
  rename_i result middle run
  split
  · rename_i noneResult
    apply WordToStackSeqClock.compCorrectSeq ac first second source
      (sourceCost first source) (sourceCost second middle)
    refine ⟨?_,ih.2⟩
    intro result post facts
    have same := Prod.mk.inj (facts.1.trans run)
    rcases same with ⟨rfl,rfl⟩
    exact ih.1 _ _ facts
  · rename_i value someResult
    apply WordToStackSeqClock.compCorrectSeq ac first second source (sourceCost first source) 0
    refine ⟨?_,ih.2⟩
    intro result post facts
    have same := Prod.mk.inj (facts.1.trans run)
    have bad : none = some value := facts.2.symm.trans same.1
    cases bad

theorem compCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width)) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ v3 v4 x y value,
      (getVar register source,getVarImm operand source) = (v3,v4) ∧
      v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧ value = true →
      SimulationB ac first source (sourceCost first source)) ∧
      (∀ v3 v4 x y value,
      (getVar register source,getVarImm operand source) = (v3,v4) ∧
      v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧ ¬ value = true →
      SimulationB ac second source (sourceCost second source))) :
    SimulationB ac (.ite comparison register operand first second) source
      (sourceCost (.ite comparison register operand first second) source) := by
  apply WordToStackIfClock.compCorrectIf
  constructor
  · intro v3 v4 x y value facts
    have selected := ih.1 v3 v4 x y value facts
    rcases facts with ⟨get,left,right,compared,rfl⟩
    obtain ⟨getLeft,getRight⟩ := Prod.mk.inj get
    rw [left] at getLeft
    rw [right] at getRight
    rw [sourceCost,getLeft,getRight]
    dsimp only
    rw [compared]
    exact selected
  · intro v3 v4 x y value facts
    have selected := ih.2 v3 v4 x y value facts
    rcases facts with ⟨get,left,right,compared,notTrue⟩
    have valueFalse : value = false := by cases value <;> simp_all
    subst value
    obtain ⟨getLeft,getRight⟩ := Prod.mk.inj get
    rw [left] at getLeft
    rw [right] at getRight
    rw [sourceCost,getLeft,getRight]
    dsimp only
    rw [compared]
    exact selected


theorem compCorrectLoop {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ cutSource result post,
      WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource ∧
      (result,post) = evaluate body cutSource ∧ wordSemContLoop result = true ∧ post.clock ≠ 0 →
      SimulationB ac (wordSemSTOP (.loop names body exitNames)) (WordSemStateFiniteExact.decClock post)
        (sourceCost (wordSemSTOP (.loop names body exitNames)) (WordSemStateFiniteExact.decClock post))) ∧
      (∀ cutSource, WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource →
      SimulationB ac body cutSource (sourceCost body cutSource))) :
    SimulationB ac (.loop names body exitNames) source
      (sourceCost (.loop names body exitNames) source) := by
  classical
  rw [sourceCost]
  split
  · rename_i cut
    apply WordToStackLoopClock.compCorrectLoop ac names exitNames body source 0 0
    constructor
    · intro cutSource result post facts
      rw [cut] at facts
      cases facts.1
    · intro cutSource found
      rw [cut] at found
      cases found
  · rename_i cutSource cut
    split
    rename_i result post run
    let tailBudget := if wordSemContLoop result = true ∧ post.clock ≠ 0 then
      sourceCost (wordSemSTOP (.loop names body exitNames))
        (WordSemStateFiniteExact.decClock post) else 0
    apply WordToStackLoopClock.compCorrectLoop ac names exitNames body source
      (sourceCost body cutSource) tailBudget
    constructor
    · intro cutAgain resultAgain postAgain facts
      have selected := ih.1 cutAgain resultAgain postAgain facts
      have cutEq : cutAgain = cutSource := Option.some.inj (facts.1.symm.trans cut)
      subst cutAgain
      have same := Prod.mk.inj (facts.2.1.trans run)
      rcases same with ⟨rfl,rfl⟩
      have more := facts.2.2
      simpa only [tailBudget,if_pos more] using selected
    · intro cutAgain found
      have same : cutAgain = cutSource := Option.some.inj (found.symm.trans cut)
      subst cutAgain
      exact ih.2 cutSource cut


#print axioms compCorrectSeq
#print axioms compCorrectIf
#print axioms compCorrectLoop

end InitECandidate.Solver.Wave8Stage.WordToStackCostComposition
