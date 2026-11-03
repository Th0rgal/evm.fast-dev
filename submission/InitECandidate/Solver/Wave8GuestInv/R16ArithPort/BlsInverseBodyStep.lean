import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsInverseSource

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators

/-- The source body's continuing step preserves typed locals and strictly drops
its bit-length/odd-phase rank. The halving postconditions supply the exact
normalization factors used by the arithmetic rank theorem. -/
theorem blsInverseOuterBody_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (q : BlsInverseLocals) (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hr : evaluateHOLFiniteState s blsInverseOuterBody = (none, post)) :
    ∃ r : BlsInverseLocals, r.Matches post ∧
      tightInverseRank r.u.toNat r.v.toNat < tightInverseRank q.u.toNat q.v.toNat := by
  rw [blsInverseOuterBody_eq] at hr
  obtain ⟨mid1, hcheck1, hrest1⟩ := arith_seq_none hr
  have hm1 := blsInverseExitCheck_passive (ofString "u") (ofString "x1") s mid1 hcheck1
  subst mid1
  obtain ⟨mid2, hcheck2, hrest2⟩ := arith_seq_none hrest1
  have hm2 := blsInverseExitCheck_passive (ofString "v") (ofString "x2") s mid2 hcheck2
  subst mid2
  obtain ⟨us, huRun, hafteru⟩ := arith_seq_none hrest2
  obtain ⟨vs, hvRun, htail⟩ := arith_seq_none hafteru
  obtain ⟨hu, hv, hx1, hx2⟩ := hq
  have hnormu := bls_half_normalizes (ofString "u") (ofString "x1")
    (by decide) s q.u q.x1 hc hu hx1
  change (evaluateHOLFiniteState s blsInverseUHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState s blsInverseUHalfLoop).1 = none ∧
      BlsHalfNormalPost (ofString "u") (ofString "x1") s q.u (evaluateHOLFiniteState s blsInverseUHalfLoop).2) at hnormu
  rw [huRun] at hnormu
  rcases hnormu with htimeout | ⟨_, u, x1, ku, huu, hux1, huodd, hufactor, hurest⟩
  · cases htimeout
  · have huc : us.code = originalRuntimeCode := by
      have h := evalP_code s blsInverseUHalfLoop
      rw [huRun] at h
      exact h.trans hc
    have huv : us.locals.lookup (ofString "v") = some q.v.toValue :=
      (hurest _ (by decide) (by decide)).trans hv
    have hux2 : us.locals.lookup (ofString "x2") = some q.x2.toValue :=
      (hurest _ (by decide) (by decide)).trans hx2
    have hnormv := bls_half_normalizes (ofString "v") (ofString "x2")
      (by decide) us q.v q.x2 huc huv hux2
    change (evaluateHOLFiniteState us blsInverseVHalfLoop).1 = some .timeOut ∨
      ((evaluateHOLFiniteState us blsInverseVHalfLoop).1 = none ∧
        BlsHalfNormalPost (ofString "v") (ofString "x2") us q.v (evaluateHOLFiniteState us blsInverseVHalfLoop).2) at hnormv
    rw [hvRun] at hnormv
    rcases hnormv with htimeout | ⟨_, v, x2, kv, hvv, hvx2, hvodd, hvfactor, hvrest⟩
    · cases htimeout
    · have hvc : vs.code = originalRuntimeCode := by
        have h := evalP_code us blsInverseVHalfLoop
        rw [hvRun] at h
        exact h.trans huc
      have hqv : (BlsInverseLocals.mk u v x1 x2).Matches vs :=
        ⟨(hvrest _ (by decide) (by decide)).trans huu, hvv,
          (hvrest _ (by decide) (by decide)).trans hux1, hvx2⟩
      obtain ⟨r, hrmatch, hru, hrv⟩ := blsInverseSubtractTail_none
        (BlsInverseLocals.mk u v x1 x2) hvc hqv htail
      refine ⟨r, hrmatch, ?_⟩
      dsimp only at hru hrv
      rw [hru, hrv, hufactor, hvfactor]
      exact tightInverseRank_normalize_subtract u.toNat v.toNat ku kv huodd hvodd
end InitECandidate.Solver.Wave8GuestInv.Arith
