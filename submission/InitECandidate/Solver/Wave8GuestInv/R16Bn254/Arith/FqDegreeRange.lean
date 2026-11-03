import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

/-- An early return in the actual degree scan is strictly below its starting index. -/
theorem fqDegreeLoop_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (ret : ValueHOL 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hr : evaluateHOLFiniteState s fqDegreeLoop = (some (.returned ret), post)) :
    ∃ r : BitVec 64, ret = .val (.word r) ∧ r.toNat < w.toNat := by
  have hall : ∀ n (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64) (ret : ValueHOL 64),
      s.clock = n → s.locals.lookup (ofString "i") = some (.val (.word w)) →
      evaluateHOLFiniteState s fqDegreeLoop = (some (.returned ret), post) →
      ∃ r : BitVec 64, ret = .val (.word r) ∧ r.toNat < w.toNat := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s post w ret hn hi hr
      unfold fqDegreeLoop at hr
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hr
      by_cases hw : w.toNat = 0
      · have hw0 : w = 0 := BitVec.toNat_inj.mp hw
        subst w
        simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL] at hr
      · have hpos : 0 < w.toNat := by omega
        have hg : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .lower (.const 0) (.var .local (ofString "i"))) = some (.val (.word 1)) := by
          simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, hpos]
        rw [hg] at hr
        dsimp only at hr
        rw [if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
        by_cases hz : s.clock = 0
        · simp [hz] at hr
        · rw [if_neg hz] at hr
          rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) fqDegreeBody with ⟨res, middle⟩
          rw [hbody] at hr
          have hclock := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) fqDegreeBody
          rw [hbody] at hclock
          change middle.clock ≤ s.clock - 1 at hclock
          have hnext : (w - 1).toNat < w.toNat := by
            have hmax := w.isLt
            rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 by decide]
            omega
          cases res with
          | none =>
            have hm := fqDegreeBody_flow_lookup (decClockHOLFinite s) w hi (Or.inl (by rw [hbody]))
            rw [hbody] at hm
            obtain ⟨r, hret, hlt⟩ := ih middle.clock (by omega) middle post (w - 1) ret rfl hm hr
            exact ⟨r, hret, hlt.trans hnext⟩
          | some result =>
            cases result with
            | «continue» =>
              have hno := evaluate_noTopContinue fqDegreeBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno
              exact False.elim (hno rfl)
            | returned value =>
              have hv := fqDegreeBody_returned (s := decClockHOLFinite s) w hi hbody
              have he : value = ret := by simpa using (Prod.mk.inj hr).1
              exact ⟨w - 1, he.symm.trans hv, hnext⟩
            | _ => simp at hr
  exact hall s.clock s post w ret rfl hi hr

/-- Successful degree returns are either the all-zero sentinel or an in-range index. -/
theorem fqDegree_returned_range {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (ret : ValueHOL 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_poly_deg) =
      (some (.returned ret), post)) :
    ret = .val (.word (0 - 1)) ∨ ∃ r : BitVec 64, ret = .val (.word r) ∧ r.toNat < n.toNat := by
  rw [fqDegree_source_eq] at hr
  obtain ⟨value, he, hs, inner, hbody⟩ := arith_dec_returned hr
  have hv : value = .val (.word n) := by
    simpa [evalHOLFinite, evalHOLExact, hn] using he.symm
  subst value
  rcases arith_seq_returned hbody with hloop | ⟨mid, _, hret⟩
  · right
    exact fqDegreeLoop_returned _ _ n ret
      (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hloop
  · left
    have hreturn : evaluateHOLFiniteState mid (.return (.op .sub [.const 0, .const 1])) =
        (some (.returned (.val (.word (0 - 1)))), emptyLocalsHOLFinite mid) := by
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hreturn] at hret
    simpa using (Prod.mk.inj hret).1.symm

theorem fqDegree13_returned_range {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (ret : ValueHOL 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 13)))
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_poly_deg) =
      (some (.returned ret), post)) :
    ret = .val (.word (0 - 1)) ∨ ∃ r : BitVec 64, ret = .val (.word r) ∧ r.toNat ≤ 12 := by
  rcases fqDegree_returned_range s post 13 ret hn hr with hz | ⟨r, hv, hlt⟩
  · exact Or.inl hz
  · exact Or.inr ⟨r, hv, by change r.toNat < 13 at hlt; omega⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
