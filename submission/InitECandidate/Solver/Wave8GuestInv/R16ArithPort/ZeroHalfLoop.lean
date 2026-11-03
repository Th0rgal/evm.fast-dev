import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.ModHalfSemantics
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.WhileTrap
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.InverseSource

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingCombinators

def inverseZeroTrap (counter coefficient : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ ∃ a x m : Limbs256,
    s.locals.lookup counter = some a.toValue ∧ a.toNat = 0 ∧
    s.locals.lookup coefficient = some x.toValue ∧ s.locals.lookup (ofString "m") = some m.toValue

/-- A typed zero operand keeps the halving guard true forever; mod_half cannot
turn a later iteration into an error. Every finite-clock run therefore times out. -/
theorem while_inverse_half_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter coefficient : MlS) (hcx : counter ≠ coefficient)
    (hcm : counter ≠ ofString "m") (hxm : coefficient ≠ ofString "m")
    (hp : inverseZeroTrap counter coefficient s) :
    (evaluateHOLFiniteState s (.while (inverseEvenExpr counter)
      (.seq (.assign .local counter (inverseHalfExpr counter)) (modHalfCall coefficient)))).1 =
      some .timeOut := by
  apply while_timeout_of_trap (inverseZeroTrap counter coefficient) _ _ _ _ _ s hp
  · intro t ht
    exact ht
  · intro t ht
    obtain ⟨hc, a, x, m, ha, hz, hx, hm⟩ := ht
    refine ⟨1, ?_, by decide⟩
    change arithEval t (inverseEvenExpr counter) = _
    rw [inverseEvenExpr_eval t counter a ha]
    simp [hz]
  · intro t ht
    obtain ⟨hc, a, x, m, ha, hz, hx, hm⟩ := ht
    rw [evaluateHOLFiniteState_seq_line780, inverseHalf_assign t counter a ha]
    dsimp only
    let shifted := setVarHOLFinite counter (half256 a).toValue t
    have hxs : shifted.locals.lookup coefficient = some x.toValue := by
      simp [shifted, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcx, Ne.symm hcx, hx]
    have hms : shifted.locals.lookup (ofString "m") = some m.toValue := by
      simp [shifted, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcm, Ne.symm hcm, hm]
    have hr := modHalf_call_typed shifted coefficient x m hc hxs hms
    rcases hr with htimeout | ⟨r, hnone, hlocals⟩
    · exact Or.inl htimeout
    · refine Or.inr ⟨hnone, ?_⟩
      refine ⟨(evalP_code shifted (modHalfCall coefficient)).trans hc,
        half256 a, r, m, ?_, half256_zero a hz, ?_, ?_⟩
      · change (evaluateHOLFiniteState shifted (modHalfCall coefficient)).2.locals.lookup counter = _
        rw [hlocals]
        simp [shifted, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcx, Ne.symm hcx]
      · change (evaluateHOLFiniteState shifted (modHalfCall coefficient)).2.locals.lookup coefficient = _
        rw [hlocals]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      · change (evaluateHOLFiniteState shifted (modHalfCall coefficient)).2.locals.lookup (ofString "m") = _
        rw [hlocals]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, hxm, Ne.symm hxm, hms]

theorem inverseUHalf_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : inverseZeroTrap (ofString "u") (ofString "x1") s) :
    (evaluateHOLFiniteState s inverseUHalfLoop).1 = some .timeOut := by
  rw [inverseUHalfLoop_eq]
  exact while_inverse_half_zero s _ _ (by decide) (by decide) (by decide) h

theorem inverseVHalf_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : inverseZeroTrap (ofString "v") (ofString "x2") s) :
    (evaluateHOLFiniteState s inverseVHalfLoop).1 = some .timeOut := by
  rw [inverseVHalfLoop_eq]
  exact while_inverse_half_zero s _ _ (by decide) (by decide) (by decide) h
end InitECandidate.Solver.Wave8GuestInv.Arith
