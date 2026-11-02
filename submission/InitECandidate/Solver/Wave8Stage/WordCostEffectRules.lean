import InitECandidate.Solver.Wave8Stage.WordCostEffects

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostEffects
open Flapjack WordSemStateFiniteExact WordToStackSourceCost

theorem fits_merge_left {width : Nat} [NeZero width] {C F : Type}
    (a b : Effects) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (h : Fits a p s) : Fits (merge a b) p s :=
  covers_join_left _ _ _ h

theorem fits_merge_right {width : Nat} [NeZero width] {C F : Type}
    (a b : Effects) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (h : Fits b p s) : Fits (merge a b) p s :=
  covers_join_right _ _ _ h

/-- Branches combine by maximum separately for each result class. -/
theorem branch_at {width : Nat} [NeZero width] {C F : Type}
    (a b : Effects) (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (left : At a first s) (right : At b second s) :
    At (merge a b) (.ite cmp reg operand first second) s := by
  intro notError notTimeout
  cases hl : getVar reg s <;> cases hr : getVarImm operand s <;>
    simp only [evaluate,hl,hr] at notError notTimeout
  all_goals try exact (notError rfl).elim
  rename_i x y
  cases hc : wordSemWordCmp cmp x y with
  | none => simp only [hc] at notError; exact (notError rfl).elim
  | some value =>
    cases value with
    | false =>
      simp only [hc] at notError notTimeout
      have h := fits_merge_right a b second s (right notError notTimeout)
      simpa only [Fits,netCost,evaluate,sourceCost,hl,hr,hc] using h
    | true =>
      simp only [hc] at notError notTimeout
      have h := fits_merge_left a b first s (left notError notTimeout)
      simpa only [Fits,netCost,evaluate,sourceCost,hl,hr,hc] using h

/-- A tail-call entry pays one unit before the actual callee runs. This rule
uses the found body and its concrete call environment, including frame size. -/
theorem tailCall_at {width : Nat} [NeZero width] {C F : Type}
    (effects : Effects) (dest : Option Nat) (args : List Nat)
    (s : WordSemStateFiniteExact width C F)
    (callee : ∀ xs values body frame,
      getVars args s = some xs →
      wordSemFindCode dest xs s.code s.stackSize = some (values,body,frame) →
      At effects body (WordSemStateFiniteExact.callEnv values frame (decClock s))) :
    At (shift (some (-1)) effects) (.call none dest args none) s := by
  intro notError notTimeout
  rw [evaluate] at notError notTimeout
  cases hg : getVars args s with
  | none => simp only [hg] at notError; exact (notError rfl).elim
  | some xs =>
    simp only [hg] at notError notTimeout
    by_cases badArgs : wordSemBadDestArgs dest args = true
    · simp only [badArgs,if_true] at notError; exact (notError rfl).elim
    simp only [badArgs,Bool.false_eq_true,if_false,wordSemAddRetLoc] at notError notTimeout
    cases hf : wordSemFindCode dest xs s.code s.stackSize with
    | none => simp only [hf] at notError; exact (notError rfl).elim
    | some found =>
      rcases found with ⟨values,body,frame⟩
      simp only [hf] at notError notTimeout
      by_cases zero : s.clock = 0
      · simp only [zero,dite_true] at notTimeout; exact (notTimeout rfl).elim
      simp only [zero,dite_false] at notError notTimeout
      let entry := WordSemStateFiniteExact.callEnv values frame (decClock s)
      rcases run : evaluate body entry with ⟨r,t⟩
      change (if wordSemBadFunReturn (evaluate body entry).1 then
        (some .error, (evaluate body entry).2) else evaluate body entry).1 ≠ some .error at notError
      change (if wordSemBadFunReturn (evaluate body entry).1 then
        (some .error, (evaluate body entry).2) else evaluate body entry).1 ≠ some .timeOut at notTimeout
      simp only [run] at notError notTimeout
      by_cases badReturn : wordSemBadFunReturn r = true
      · simp only [badReturn,if_true] at notError; exact (notError rfl).elim
      simp only [badReturn,Bool.false_eq_true,if_false] at notError notTimeout
      have bodyFits := callee xs values body frame hg hf
        (by rw [run]; exact notError) (by rw [run]; exact notTimeout)
      have expandedRun := run
      dsimp only [entry] at expandedRun
      simp only [Fits,netCost,expandedRun] at bodyFits
      have credit : Covers (some (-1)) (-1) := ⟨-1,rfl,by omega⟩
      have paid := covers_add (some (-1)) (effects (classify r)) _ _ credit bodyFits
      have whole : evaluate (.call none dest args none) s = (r,t) := by
        rw [evaluate]
        simp only [hg,badArgs,Bool.false_eq_true,if_false,wordSemAddRetLoc,hf,zero,dite_false]
        change (if wordSemBadFunReturn (evaluate body entry).1 then
          (some .error,(evaluate body entry).2) else evaluate body entry) = (r,t)
        simp only [run,badReturn,Bool.false_eq_true,if_false]
      have cost : sourceCost (.call none dest args none) s = sourceCost body entry := by
        rw [sourceCost]
        simp only [hg,wordSemAddRetLoc,hf,zero,dite_false]
        rfl
      simp only [Fits,netCost,whole,cost,shift]
      apply covers_mono paid
      dsimp only [entry,WordSemStateFiniteExact.callEnv,decClock]
      omega

end InitECandidate.Solver.Wave8Stage.WordCostEffects
