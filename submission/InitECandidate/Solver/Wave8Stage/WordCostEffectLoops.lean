import InitECandidate.Solver.Wave8Stage.WordCostEffects
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Control

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostEffects
open Flapjack WordSemStateFiniteExact WordToStackSourceCost

/-- Loop exit labels lose one nesting level; break zero falls through. -/
def loopEffects (body : Effects) : Effects
  | .fall => body (.breakTo 0)
  | .breakTo label => body (.breakTo (label+1))
  | .continueTo label => body (.continueTo (label+1))
  | exit => body exit

def AtMost (bound : Budget) (limit : Int) : Prop :=
  ∀ cost, Covers bound cost → cost ≤ limit

theorem covers_continuing {width : Nat} [NeZero width]
    (effects : Effects) (r : Option (WordSemResult width)) (cost : Int)
    (cont : wordSemContLoop r = true) (bound : Covers (effects (classify r)) cost) :
    Covers (join (effects .fall) (effects (.continueTo 0))) cost := by
  cases r with
  | none => exact covers_join_left _ _ _ bound
  | some r =>
    cases r <;> simp only [wordSemContLoop,Bool.false_eq_true] at cont
    rename_i label
    have zero : label = 0 := by simpa using cont
    subst label
    exact covers_join_right _ _ _ bound

theorem loop_exit_effect {width : Nat} [NeZero width]
    (effects : Effects) (r : Option (WordSemResult width))
    (cont : wordSemContLoop r ≠ true) (notBreak : r ≠ some (.break 0)) :
    loopEffects effects (classify (wordSemExitLoop r)) = effects (classify r) := by
  cases r with
  | none => exact (cont rfl).elim
  | some r =>
    cases r <;> try rfl
    case «break» label =>
      cases label with
      | zero => exact (notBreak rfl).elim
      | succ label => simp [wordSemExitLoop,classify,loopEffects]
    case «continue» label =>
      cases label with
      | zero => exact (cont rfl).elim
      | succ label => simp [wordSemExitLoop,classify,loopEffects]

/-- Local loop induction step. Each continuing iteration may use at most one
unit of net potential; the real loop-back tick pays that unit. -/
theorem loop_at {width : Nat} [NeZero width] {C F : Type}
    (effects : Effects) (names exits : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (cycle : AtMost (join (effects .fall) (effects (.continueTo 0))) 1)
    (bodyRule : ∀ cut, cutState (names,.ln) s = some cut → At effects body cut)
    (tailRule : ∀ cut r post,
      cutState (names,.ln) s = some cut → evaluate body cut = (r,post) →
      wordSemContLoop r = true → post.clock ≠ 0 →
      At (loopEffects effects) (wordSemSTOP (.loop names body exits)) (decClock post)) :
    At (loopEffects effects) (.loop names body exits) s := by
  intro notError notTimeout
  cases cutRun : cutState (names,.ln) s with
  | none => rw [evaluate,cutRun] at notError; exact (notError rfl).elim
  | some cut =>
    rcases run : evaluate body cut with ⟨r,t⟩
    have cutClock := (cutState_clock_termdep _ _ _ cutRun).1
    have whole := Compiler.Backend.WordToWord.evaluate_loop_run names exits body s cut cutRun r t run
    have cost : sourceCost (.loop names body exits) s = sourceCost body cut +
        (if wordSemContLoop r = true ∧ t.clock ≠ 0 then
          sourceCost (wordSemSTOP (.loop names body exits)) (decClock t) else 0) := by
      rw [sourceCost]
      split
      · rename_i failed
        rw [cutRun] at failed
        cases failed
      · rename_i cut' found
        have same := Option.some.inj (found.symm.trans cutRun)
        subst cut'
        split
        rename_i result post otherRun
        have same := Prod.mk.inj (otherRun.symm.trans run)
        obtain ⟨rfl,rfl⟩ := same
        cases result <;> rfl
    have ne : r ≠ some .error := by
      intro bad
      rw [whole,bad] at notError
      simp [wordSemContLoop,wordSemExitLoop] at notError
    have nt : r ≠ some .timeOut := by
      intro bad
      rw [whole,bad] at notTimeout
      simp [wordSemContLoop,wordSemExitLoop] at notTimeout
    have bodyFits := bodyRule cut cutRun (by rw [run]; exact ne) (by rw [run]; exact nt)
    simp only [Fits,netCost,run] at bodyFits
    by_cases cont : wordSemContLoop r = true
    · by_cases zero : t.clock = 0
      · simp [whole,cont,zero] at notTimeout
      have bounded := cycle _ (covers_continuing effects r _ cont bodyFits)
      have tailFits := tailRule cut r t cutRun run cont zero
        (by simpa [whole,cont,zero,wordSemSTOP] using notError)
        (by simpa [whole,cont,zero,wordSemSTOP] using notTimeout)
      simp only [Fits,netCost,wordSemSTOP] at tailFits
      simp [Fits,netCost,whole,cont,zero,cost,wordSemSTOP,Int.natCast_add]
      apply covers_mono tailFits
      dsimp only [decClock]
      rw [cutClock] at bounded
      omega
    · by_cases broke : r = some (.break 0)
      · cases exitRun : cutState (exits,.ln) t with
        | none => simp [whole,broke,exitRun,wordSemContLoop] at notError
        | some out =>
          have outClock := (cutState_clock_termdep _ _ _ exitRun).1
          have bodyFits' := bodyFits
          simp only [broke,classify] at bodyFits'
          simp [Fits,netCost,whole,broke,exitRun,cost,wordSemContLoop,classify,loopEffects]
          apply covers_mono bodyFits'
          omega
      · have exitEffect := loop_exit_effect effects r cont broke
        simp [Fits,netCost,whole,cont,broke,cost,exitEffect]
        apply covers_mono bodyFits
        omega

#print axioms covers_continuing
#print axioms loop_exit_effect
#print axioms loop_at
end InitECandidate.Solver.Wave8Stage.WordCostEffects
