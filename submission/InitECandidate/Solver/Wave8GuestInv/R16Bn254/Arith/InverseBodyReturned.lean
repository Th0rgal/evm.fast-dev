import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseExitCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.NoReturnFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators

theorem inverseNormalizationTail_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (q : InverseLocals) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (hq : q.Matches s) :
    (evaluateHOLFiniteState s (.seq inverseUHalfLoop (.seq inverseVHalfLoop inverseSubtractTail))).1 ≠
      some (.returned ret) := by
  intro hr
  have he : evaluateHOLFiniteState s (.seq inverseUHalfLoop (.seq inverseVHalfLoop inverseSubtractTail)) =
      (some (.returned ret), (evaluateHOLFiniteState s
        (.seq inverseUHalfLoop (.seq inverseVHalfLoop inverseSubtractTail))).2) := Prod.ext hr rfl
  obtain ⟨hu, hv, hx1, hx2, hm⟩ := hq
  have hnormu := inverse_half_normalizes (ofString "u") (ofString "x1")
    (by decide) (by decide) (by decide) s q.u q.x1 q.m hc hu hx1 hm
  change (evaluateHOLFiniteState s inverseUHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState s inverseUHalfLoop).1 = none ∧
      HalfNormalPost (ofString "u") (ofString "x1") s q.u (evaluateHOLFiniteState s inverseUHalfLoop).2) at hnormu
  rcases arith_seq_returned he with hur | ⟨us, huRun, hafteru⟩
  · rw [hur] at hnormu
    simp at hnormu
  · rw [huRun] at hnormu
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
      rcases arith_seq_returned hafteru with hvr | ⟨vs, _, htail⟩
      · rw [hvr] at hnormv
        simp at hnormv
      · exact inverseSubtractTail_not_returned vs ret (congrArg Prod.fst htail)

/-- A body return is an inverse coefficient whose operand equals one. -/
theorem inverseOuterBody_returned_correct {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (input : Nat) (q : InverseLocals) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hinv : q.CoefficientInvariant input)
    (hr : evaluateHOLFiniteState s inverseOuterBody = (some (.returned ret), post)) :
    ∃ x : Limbs256, ret = x.toValue ∧ x.toNat < q.m.toNat ∧
      InverseCongruence input q.m.toNat 1 x.toNat := by
  rw [inverseOuterBody_eq] at hr
  rcases arith_seq_returned hr with hcheck | ⟨mid, hcheck, hrest⟩
  · obtain ⟨hone, hret⟩ := inverseExitCheck_returned _ _ q.u q.x1 ret hq.1 hq.2.2.1 hcheck
    exact ⟨q.x1, hret, hinv.2.2.1, by simpa only [hone] using hinv.1⟩
  · have he := inverseExitCheck_passive (ofString "u") (ofString "x1") s mid hcheck
    subst mid
    rcases arith_seq_returned hrest with hcheck | ⟨mid, hcheck, htail⟩
    · obtain ⟨hone, hret⟩ := inverseExitCheck_returned _ _ q.v q.x2 ret hq.2.1 hq.2.2.2.1 hcheck
      exact ⟨q.x2, hret, hinv.2.2.2.1, by simpa only [hone] using hinv.2.1⟩
    · have he := inverseExitCheck_passive (ofString "v") (ofString "x2") s mid hcheck
      subst mid
      exact False.elim (inverseNormalizationTail_not_returned s q ret hc hq (congrArg Prod.fst htail))

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
