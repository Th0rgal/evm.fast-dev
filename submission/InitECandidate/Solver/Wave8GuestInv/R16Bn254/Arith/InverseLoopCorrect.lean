import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseBodyReturned

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

theorem Limbs256.toValue_injective : Function.Injective Limbs256.toValue := by
  intro a b he
  cases a
  cases b
  simp_all [Limbs256.toValue]

theorem inverseOuterBody_modulus_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (q r : InverseLocals) (hq : q.Matches s) (hr : r.Matches post)
    (he : evaluateHOLFiniteState s inverseOuterBody = (none, post)) : r.m = q.m := by
  have hp := evaluate_avoidsLocal_flowing (ofString "m") inverseOuterBody (by decide) s
    (Or.inl (by rw [he]))
  rw [he] at hp
  dsimp only at hp
  rw [hq.2.2.2.2, hr.2.2.2.2] at hp
  exact Limbs256.toValue_injective (Option.some.inj hp)

/-- Successful returns of the actual inverse loop carry a canonical inverse
coefficient for the initial input and the unchanged modulus. -/
theorem inverseOuterLoop_returned_correct {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input : Nat) (q : InverseLocals) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hq : q.Matches s)
    (hinv : q.CoefficientInvariant input)
    (hr : evaluateHOLFiniteState s inverseOuterLoop = (some (.returned ret), post)) :
    ∃ x : Limbs256, ret = x.toValue ∧ x.toNat < q.m.toNat ∧
      InverseCongruence input q.m.toNat 1 x.toNat := by
  have hall : ∀ n (s post : PanSemStateFiniteExact 64 F) (q : InverseLocals),
      s.clock = n → s.code = originalRuntimeCode → q.Matches s → q.CoefficientInvariant input →
      evaluateHOLFiniteState s inverseOuterLoop = (some (.returned ret), post) →
      ∃ x : Limbs256, ret = x.toValue ∧ x.toNat < q.m.toNat ∧
        InverseCongruence input q.m.toNat 1 x.toNat := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s post q hn hc hq hinv hr
      rw [inverseOuterLoop_eq, evaluateHOLFiniteState_while_fixClockRewrite] at hr
      simp only [evalHOLFinite, evalHOLExact] at hr
      rw [if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · rw [if_neg hz] at hr
        rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) inverseOuterBody with ⟨res, middle⟩
        rw [hbody] at hr
        have hclock := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) inverseOuterBody
        rw [hbody] at hclock
        change middle.clock ≤ s.clock - 1 at hclock
        cases res with
        | none =>
          obtain ⟨r, hrmatch, hrinv⟩ := inverseOuterBody_congruence_none
            (s := decClockHOLFinite s) input q hinv hc hq hbody
          have hm := inverseOuterBody_modulus_none (s := decClockHOLFinite s) q r hq hrmatch hbody
          have hmc : middle.code = originalRuntimeCode := by
            have h := evalP_code (decClockHOLFinite s) inverseOuterBody
            rw [hbody] at h
            exact h.trans hc
          have hi := ih middle.clock (by omega) middle post r rfl hmc hrmatch hrinv hr
          simpa only [hm] using hi
        | some result =>
          cases result with
          | «continue» =>
            exact False.elim (inverseOuterBody_not_continue _ (congrArg Prod.fst hbody))
          | returned value =>
            have hv := inverseOuterBody_returned_correct (s := decClockHOLFinite s)
              input q value hc hq hinv hbody
            have he : value = ret := by simpa using (Prod.mk.inj hr).1
            simpa only [he] using hv
          | _ => simp at hr
  exact hall s.clock s post q rfl hc hq hinv hr

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
