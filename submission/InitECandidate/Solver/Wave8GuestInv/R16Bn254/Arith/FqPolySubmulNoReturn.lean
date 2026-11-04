import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.NoReturnFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

theorem polySubmulTail_not_returned {F : Type} (state : PanSemStateFiniteExact 64 F) (ret : ValueHOL 64) :
    (evaluateHOLFiniteState state polySubmulTail).1 ≠ some (.returned ret) := by
  apply arith_seq_not_returned state _ _ ret
  · exact arith_call_local_not_returned state _ _ _ ret
  · intro mid
    apply arith_seq_not_returned mid _ _ ret
    · rcases (evaluate_store_control_frame mid polySubmulDst (polySubmulVar "ai")).1 with h | h
      all_goals change (evaluateHOLFiniteState mid (.store polySubmulDst (polySubmulVar "ai"))).1 ≠ _
      all_goals rw [h]; simp
    · intro last
      unfold polySubmulIncrement
      rw [evaluateHOLFiniteState_assign]
      repeat' first | split | simp

theorem polySubmulBody_not_returned {F : Type} (state : PanSemStateFiniteExact 64 F) (ret : ValueHOL 64) :
    (evaluateHOLFiniteState state polySubmulBody).1 ≠ some (.returned ret) := by
  intro h
  have hr : evaluateHOLFiniteState state polySubmulBody =
      (some (.returned ret),(evaluateHOLFiniteState state polySubmulBody).2) := Prod.ext h rfl
  unfold polySubmulBody at hr
  obtain ⟨_,_,_,_,hmul⟩ := arith_dec_returned hr
  unfold polySubmulMultiply at hmul
  obtain ⟨_,_,_,_,_,_,resumed,_,_,_,_,_,_,_,_,hload,_⟩ := arith_decCall_returned hmul
  unfold polySubmulLoadA at hload
  obtain ⟨_,_,_,_,htail⟩ := arith_dec_returned hload
  exact polySubmulTail_not_returned _ ret (congrArg Prod.fst htail)

theorem polySubmulLoop_not_returned {F : Type} (state : PanSemStateFiniteExact 64 F) (ret : ValueHOL 64) :
    (evaluateHOLFiniteState state polySubmulLoop).1 ≠ some (.returned ret) := by
  have hall : ∀ n (s post : PanSemStateFiniteExact 64 F), s.clock = n →
      evaluateHOLFiniteState s polySubmulLoop = (some (.returned ret),post) → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s post hn hr
      unfold polySubmulLoop at hr
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hr
      split at hr
      · split at hr
        · split at hr
          · simp at hr
          · rename_i hclock
            rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) polySubmulBody with ⟨result,mid⟩
            rw [hb] at hr
            have hbound := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) polySubmulBody
            rw [hb] at hbound
            change mid.clock ≤ s.clock-1 at hbound
            cases result with
            | none => exact ih mid.clock (by omega) mid post rfl hr
            | some result =>
              cases result with
              | «continue» => exact ih mid.clock (by omega) mid post rfl hr
              | returned value => exact polySubmulBody_not_returned (decClockHOLFinite s) value (congrArg Prod.fst hb)
              | _ => simp at hr
        · simp at hr
      · simp at hr
  intro h
  exact hall state.clock state (evaluateHOLFiniteState state polySubmulLoop).2 rfl (Prod.ext h rfl)

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
