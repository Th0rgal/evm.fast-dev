import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ZeroHalfLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def inverseHalfStep (counter coefficient : MlS) : ProgHOL 64 :=
  .seq (.assign .local counter (inverseHalfExpr counter)) (modHalfCall coefficient)

def inverseHalfTyped (counter coefficient : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ a x m : Limbs256, s.locals.lookup counter = some a.toValue ∧
    s.locals.lookup coefficient = some x.toValue ∧ s.locals.lookup (ofString "m") = some m.toValue

theorem inverseHalfStep_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter coefficient : MlS) (a x m : Limbs256)
    (hcx : counter ≠ coefficient) (hcm : counter ≠ ofString "m")
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup counter = some a.toValue)
    (hx : s.locals.lookup coefficient = some x.toValue)
    (hm : s.locals.lookup (ofString "m") = some m.toValue) :
    (evaluateHOLFiniteState s (inverseHalfStep counter coefficient)).1 = some .timeOut ∨
      ∃ r : Limbs256,
        (evaluateHOLFiniteState s (inverseHalfStep counter coefficient)).1 = none ∧
        (evaluateHOLFiniteState s (inverseHalfStep counter coefficient)).2.locals =
          (s.locals.update (counter, (half256 a).toValue)).update (coefficient, r.toValue) := by
  unfold inverseHalfStep
  rw [evaluateHOLFiniteState_seq_line780, inverseHalf_assign s counter a ha]
  dsimp only
  apply modHalf_call_typed (setVarHOLFinite counter (half256 a).toValue s) coefficient x m hc
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcx, hx]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcm, hm]

/-- Both zero and positive typed operands satisfy the proposed halving-loop cap. -/
theorem while_inverse_half_typed (counter coefficient : MlS)
    (hcx : counter ≠ coefficient) (hcm : counter ≠ ofString "m")
    (hxm : coefficient ≠ ofString "m") :
    TerminatingProgBoundedOn (inverseHalfTyped counter coefficient)
      (.while (inverseEvenExpr counter) (inverseHalfStep counter coefficient))
      ((2 ^ 8 + 1) * ((K.«mod_half» + 1) + 1)) := by
  intro F s hc hp hnt
  obtain ⟨a, x, m, ha, hx, hm⟩ := hp
  by_cases hz : a.toNat = 0
  · have ht := while_inverse_half_zero s counter coefficient hcx hcm hxm
      ⟨hc, a, x, m, ha, hz, hx, hm⟩
    exact False.elim (hnt ht)
  · exact while_inverse_half_positive counter
      (TerminatingProgBounded.call ub_mod_half (some (.local, coefficient))
        [.var .local coefficient, .var .local (ofString "m")])
      (by simp [PanRunBounded.avoidsLocal, Ne.symm hcx]) s hc ⟨a, ha, by omega⟩ hnt

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
