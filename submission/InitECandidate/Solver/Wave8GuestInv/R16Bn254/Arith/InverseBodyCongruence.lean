import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseSubtractExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.HalfCongruence
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseBodyStep
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ReadOnlyPrefix

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators

theorem inverseOuterBody_congruence_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (input : Nat) (q : InverseLocals) (hinv : q.CoefficientInvariant input) (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hr : evaluateHOLFiniteState s inverseOuterBody = (none, post)) :
    ∃ r : InverseLocals, r.Matches post ∧
      r.CoefficientInvariant input := by
  obtain ⟨hinu, hinv, hx1range, hx2range, hmodd⟩ := hinv
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
  have hnormu := inverse_half_congruence (ofString "u") (ofString "x1")
    (by decide) (by decide) (by decide) s q.u q.x1 q.m input hmodd hx1range hinu hc hu hx1 hm
  change (evaluateHOLFiniteState s inverseUHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState s inverseUHalfLoop).1 = none ∧
      HalfCongruencePost (ofString "u") (ofString "x1") input q.m s q.u (evaluateHOLFiniteState s inverseUHalfLoop).2) at hnormu
  rw [huRun] at hnormu
  rcases hnormu with htimeout | ⟨_, u, x1, ku, huu, hux1, huodd, hufactor, huinv, huxrange, hurest⟩
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
    have hnormv := inverse_half_congruence (ofString "v") (ofString "x2")
      (by decide) (by decide) (by decide) us q.v q.x2 q.m input hmodd hx2range hinv huc huv hux2 hum
    change (evaluateHOLFiniteState us inverseVHalfLoop).1 = some .timeOut ∨
      ((evaluateHOLFiniteState us inverseVHalfLoop).1 = none ∧
        HalfCongruencePost (ofString "v") (ofString "x2") input q.m us q.v (evaluateHOLFiniteState us inverseVHalfLoop).2) at hnormv
    rw [hvRun] at hnormv
    rcases hnormv with htimeout | ⟨_, v, x2, kv, hvv, hvx2, hvodd, hvfactor, hvinv, hvxrange, hvrest⟩
    · cases htimeout
    · have hvc : vs.code = originalRuntimeCode := by
        have h := evalP_code us inverseVHalfLoop
        rw [hvRun] at h
        exact h.trans huc
      have hqv : (InverseLocals.mk u v x1 x2 q.m).Matches vs :=
        ⟨(hvrest _ (by decide) (by decide)).trans huu, hvv,
          (hvrest _ (by decide) (by decide)).trans hux1, hvx2,
          (hvrest _ (by decide) (by decide)).trans hum⟩
      have hm := inverseSubtractTail_exact_none
        (InverseLocals.mk u v x1 x2 q.m) hvc hqv htail
      refine ⟨inverseSubtractLocals (InverseLocals.mk u v x1 x2 q.m), hm, ?_⟩
      exact inverseSubtractLocals_congruence input _ ⟨huinv, hvinv, huxrange, hvxrange, hmodd⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
