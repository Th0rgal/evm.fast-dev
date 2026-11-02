import InitECandidate.Solver.Wave8Stage.WordToStackCostBound
import InitECandidate.Solver.Wave8Stage.WordToStackCostEntry

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordToStackStaticBudget
open Flapjack WordToStackCostBound WordToStackSourceCost

/-- The maximum fragment potential in the actual finite source code. -/
def codeBudget {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Nat :=
  ((sptToAList code).map fun entry => programCost entry.2.2).foldr max 0

private theorem fold_max_member (xs : List Nat) (n : Nat) (h : n ∈ xs) :
    n ≤ xs.foldr max 0 := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem codeBudget_bounds {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) :
    codeCostBound code (codeBudget code) := by
  intro name arity body found
  apply fold_max_member
  apply List.mem_map.mpr
  refine ⟨(name,arity,body), ?_, rfl⟩
  apply sptAListLookup_mem
  rw [← sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList]
  exact found

/-- Entry has zero initial potential; every callee fragment is paid by a
source clock decrement. This also covers early errors in unreachable branches. -/
theorem entryCost_bound {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (source : WordSemStateFiniteExact width C F)
    (noInstall : WordProps.noInstallCode source.code)
    (notError : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) source).1 ≠ some .error) :
    sourceCost (.call none (some start) [0] none) source ≤ codeBudget source.code * source.clock := by
  have bound := sourceCost_bound (.call none (some start) [0] none) source
    (codeBudget source.code) (by simp) (codeBudget_bounds source.code)
    (by simp [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]) noInstall notError
  simp only [programCost, Nat.add_zero] at bound
  omega

/-- A fully static affine clock budget for the native entry simulation. The
coefficient is computed from source code, with no target execution premise. -/
theorem notTimeOutOfStaticBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width) (start registers clock : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (related : WordToStackProofs.stateRel ac registers 0 0 source target [] 0)
    (noInstall : WordProps.noInstallCode source.code)
    (notError : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .error)
    (notTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some start) [0] none) {source with clock := clock}).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate
      ((.call none (.inl start) none : Compiler.Backend.StackLang.HolProg width),
        {target with clock := (codeBudget source.code + 1) * clock})).1 ≠ some .timeOut := by
  apply WordToStackCostEntry.notTimeOutOfCostBound ac start registers clock _ source target
    related notError notTimeout
  have bound := entryCost_bound start {source with clock := clock} noInstall notError
  change sourceCost _ _ ≤ codeBudget source.code * clock at bound
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end InitECandidate.Solver.Wave8Stage.WordToStackStaticBudget
