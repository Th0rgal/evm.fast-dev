import InitECandidate.Solver.GuestUniformClockBound
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseBodyStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

/-- The unconditional loop cannot fall through to the defensive zero return:
its body has no escaping break statement. -/
theorem inverseOuterLoop_not_none {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s inverseOuterLoop).1 ≠ none := by
  have hall : ∀ n (s : PanSemStateFiniteExact 64 F), s.clock = n →
      (evaluateHOLFiniteState s inverseOuterLoop).1 ≠ none := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hr
      rw [inverseOuterLoop_eq, evaluateHOLFiniteState_while_fixClockRewrite] at hr
      simp only [evalHOLFinite, evalHOLExact] at hr
      rw [if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · rw [if_neg hz] at hr
        rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) inverseOuterBody with ⟨res, mid⟩
        rw [hb] at hr
        have hclock := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) inverseOuterBody
        rw [hb] at hclock
        change mid.clock ≤ s.clock - 1 at hclock
        cases res with
        | none => exact ih mid.clock (by omega) mid rfl hr
        | some result =>
          cases result with
          | «continue» => exact ih mid.clock (by omega) mid rfl hr
          | «break» =>
            have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
              inverseOuterBody (by decide) (decClockHOLFinite s)
            exact hno (congrArg Prod.fst hb)
          | _ => simp at hr
  exact hall s.clock s rfl

end InitECandidate.Solver.Wave8GuestInv.Arith
