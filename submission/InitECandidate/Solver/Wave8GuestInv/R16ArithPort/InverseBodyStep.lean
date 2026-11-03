import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.InverseSubtractTail
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.ReadOnlyPrefix

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators

def inverseExitCheck (counter coefficient : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (.op .or [.rfield 1 (.var .local counter),
    .rfield 2 (.var .local counter), .rfield 3 (.var .local counter)]) (.const 0))
    (.ite (.cmp .equal (.rfield 0 (.var .local counter)) (.const 1))
      (.return (.var .local coefficient)) .skip) .skip

theorem inverseExitCheck_passive (counter coefficient : MlS) :
    NoChangeOnNone (inverseExitCheck counter coefficient) :=
  NoChangeOnNone.ite _ (NoChangeOnNone.ite _ (NoChangeOnNone.ret _) NoChangeOnNone.skip) NoChangeOnNone.skip

theorem inverseOuterBody_eq : inverseOuterBody =
    .seq (inverseExitCheck (ofString "u") (ofString "x1"))
      (.seq (inverseExitCheck (ofString "v") (ofString "x2"))
        (.seq inverseUHalfLoop (.seq inverseVHalfLoop inverseSubtractTail))) := rfl

theorem inverseOuterBody_not_continue {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s inverseOuterBody).1 ≠ some .continue :=
  evaluate_noTopContinue inverseOuterBody (by decide) s

/-- The source body's continuing step preserves typed locals and strictly drops
its bit-length/odd-phase rank. The halving postconditions supply the exact
normalization factors used by the arithmetic rank theorem. -/
theorem inverseOuterBody_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (q : InverseLocals) (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hr : evaluateHOLFiniteState s inverseOuterBody = (none, post)) :
    ∃ r : InverseLocals, r.Matches post ∧
      tightInverseRank r.u.toNat r.v.toNat < tightInverseRank q.u.toNat q.v.toNat := by
  rw [inverseOuterBody_eq] at hr
  obtain ⟨mid1, hcheck1, hrest1⟩ := arith_seq_none hr
  have hm1 := inverseExitCheck_passive (ofString "u") (ofString "x1") s mid1 hcheck1
  subst mid1
  obtain ⟨mid2, hcheck2, hrest2⟩ := arith_seq_none hrest1
  have hm2 := inverseExitCheck_passive (ofString "v") (ofString "x2") s mid2 hcheck2
  subst mid2
  obtain ⟨us, huRun, hafteru⟩ := arith_seq_none hrest2
  obtain ⟨vs, hvRun, htail⟩ := arith_seq_none hafteru
  obtain ⟨hu, hv, hx1, hx2, hm⟩ := hq
  have hnormu := inverse_half_normalizes (ofString "u") (ofString "x1")
    (by decide) (by decide) (by decide) s q.u q.x1 q.m hc hu hx1 hm
  change (evaluateHOLFiniteState s inverseUHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState s inverseUHalfLoop).1 = none ∧
      HalfNormalPost (ofString "u") (ofString "x1") s q.u (evaluateHOLFiniteState s inverseUHalfLoop).2) at hnormu
  rw [huRun] at hnormu
  rcases hnormu with htimeout | ⟨_, u, x1, ku, huu, hux1, huodd, hufactor, hurest⟩
  · cases htimeout
  · have huc : us.code = originalRuntimeCode := by
      have h := evalP_code s inverseUHalfLoop
      rw [huRun] at h
      exact h.trans hc
    have huv : us.locals.lookup (ofString "v") = some q.v.toValue :=
      (hurest _ (by decide) (by decide)).trans hv
    have hux2 : us.locals.lookup (ofString "x2") = some q.x2.toValue :=
      (hurest _ (by decide) (by decide)).trans hx2
    have hum : us.locals.lookup (ofString "m") = some q.m.toValue :=
      (hurest _ (by decide) (by decide)).trans hm
    have hnormv := inverse_half_normalizes (ofString "v") (ofString "x2")
      (by decide) (by decide) (by decide) us q.v q.x2 q.m huc huv hux2 hum
    change (evaluateHOLFiniteState us inverseVHalfLoop).1 = some .timeOut ∨
      ((evaluateHOLFiniteState us inverseVHalfLoop).1 = none ∧
        HalfNormalPost (ofString "v") (ofString "x2") us q.v (evaluateHOLFiniteState us inverseVHalfLoop).2) at hnormv
    rw [hvRun] at hnormv
    rcases hnormv with htimeout | ⟨_, v, x2, kv, hvv, hvx2, hvodd, hvfactor, hvrest⟩
    · cases htimeout
    · have hvc : vs.code = originalRuntimeCode := by
        have h := evalP_code us inverseVHalfLoop
        rw [hvRun] at h
        exact h.trans huc
      have hqv : (InverseLocals.mk u v x1 x2 q.m).Matches vs :=
        ⟨(hvrest _ (by decide) (by decide)).trans huu, hvv,
          (hvrest _ (by decide) (by decide)).trans hux1, hvx2,
          (hvrest _ (by decide) (by decide)).trans hum⟩
      obtain ⟨r, hrmatch, hru, hrv⟩ := inverseSubtractTail_none
        (InverseLocals.mk u v x1 x2 q.m) hvc hqv htail
      refine ⟨r, hrmatch, ?_⟩
      dsimp only at hru hrv
      rw [hru, hrv, hufactor, hvfactor]
      exact tightInverseRank_normalize_subtract u.toNat v.toNat ku kv huodd hvodd
end InitECandidate.Solver.Wave8GuestInv.Arith
