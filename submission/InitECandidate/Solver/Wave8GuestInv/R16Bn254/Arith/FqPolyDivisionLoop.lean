import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

private theorem signed_less_eq (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

/-- Every successful exit of the actual inner loop leaves a canonical
remainder whose signed degree is below the unchanged divisor's degree. -/
theorem polyDivLoop_none {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (inverse : Limbs256)
    (ctx : PolyDivContext a b quotient d1 B inverse)
    (hc : s.code = originalRuntimeCode) (hi : PolyDivInvariant a b quotient d1 B inverse s)
    (hr : evaluateHOLFiniteState s polyDivLoop = (none,post)) :
    PolyDivInvariant a b quotient d1 B inverse post ∧
      (∃ degree : BitVec 64, post.locals.lookup (ofString "d0") = some (.val (.word degree)) ∧
        degree.toInt < (d1 : Int)) ∧
      polyDivisionRank post ≤ polyDivisionRank s ∧
      ∀ x, PolynomialOutside a x → PolynomialOutside quotient x → post.memory x = s.memory x := by
  obtain ⟨A,Q,degree,hA,hQ,hmA,hmQ,hdegree,hlocal⟩ := hi.dividend
  rw [polyDivLoop,evaluateHOLFiniteState_while_fixClockRewrite] at hr
  have hg : evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyDivGuard =
      some (.val (.word (if wordCmpHOL .notLess degree (BitVec.ofNat 64 d1) then 1 else 0))) := by
    simp [evalHOLFinite,evalHOLExact,polyDivGuard,polyDivVar,hlocal,hi.degree1]
  rw [hg] at hr
  dsimp only at hr
  by_cases hcmp : wordCmpHOL .notLess degree (BitVec.ofNat 64 d1) = true
  · rw [if_pos hcmp,if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
    by_cases hclock : s.clock = 0
    · simp [hclock] at hr
    · rw [if_neg hclock] at hr
      rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody with ⟨result,mid⟩
      rw [hbody] at hr
      cases result with
      | none =>
          have hactive : evalHOLFinite (decClockHOLFinite s)
              (h := fun x => Classical.propDecidable ((decClockHOLFinite s).memaddrs x)) polyDivGuard =
              some (.val (.word 1)) := by
            simp [evalHOLFinite,evalHOLExact,polyDivGuard,polyDivVar,decClockHOLFinite,
              hlocal,hi.degree1,hcmp]
          have hstep := polyDivBody_invariant (decClockHOLFinite s) mid a b quotient d1 B inverse ctx hc
            (polyDivInvariant_decClock s a b quotient d1 B inverse hi) 1 hactive (by decide) hbody
          have hmeta := evaluateHOLFiniteState_metadata (decClockHOLFinite s) polyDivBody
          rw [hbody] at hmeta
          obtain ⟨hi',hexit,hrank,hframe⟩ := polyDivLoop_none mid post a b quotient d1 B inverse ctx
            (hmeta.1.trans hc) hstep.2.1 hr
          refine ⟨hi',hexit,Nat.le_trans hrank (Nat.le_of_lt hstep.1),?_⟩
          intro x hxa hxq
          rw [hframe x hxa hxq,hstep.2.2 x hxa hxq]
          rfl
      | some result =>
          cases result with
          | «continue» =>
              have hno := evaluate_noTopContinue polyDivBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | «break» =>
              have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                polyDivBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | _ => simp at hr
  · rw [if_neg hcmp,if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)] at hr
    have he : s = post := (Prod.mk.inj hr).2
    subst post
    have hslt : degree.slt (BitVec.ofNat 64 d1) = true := by
      simpa only [wordCmpHOL,signed_less_eq,Bool.not_eq_true',Bool.eq_false_iff,not_not] using hcmp
    have hlt := BitVec.slt_iff_toInt_lt.mp hslt
    rw [degreeIndex_toInt d1 ctx.bound] at hlt
    exact ⟨hi,⟨degree,hlocal,hlt⟩,Nat.le_refl _,fun _ _ _ => rfl⟩
termination_by polyDivisionRank s
decreasing_by exact hstep.1

end InitECandidate.Solver.Wave8GuestInv.Arith
