import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulRange
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulControl

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

theorem polySubmulLoop_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift i db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hiBound : i ≤ db+1) (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hdb : state.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hACanon : CanonicalPolynomial A) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (hr : evaluateHOLFiniteState state polySubmulLoop = (none,post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧ MemoryPolynomial post.memory a C ∧
      MemoryPolynomial post.memory b B ∧ SubmulRange q shift i db A B C ∧
      PolynomialFrame state.memory post.memory a := by
  unfold polySubmulLoop at hr
  rw [evaluateHOLFiniteState_while_fixClockRewrite] at hr
  have hg := polySubmul_guard state i db hiBound hdbBound hi hdb
  change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) _ = _ at hg
  rw [hg] at hr
  dsimp only at hr
  by_cases hindex : i ≤ db
  · rw [if_pos hindex,if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
    by_cases hclock : state.clock = 0
    · simp [hclock] at hr
    · rw [if_neg hclock] at hr
      rcases hbody : evaluateHOLFiniteState (decClockHOLFinite state) polySubmulBody with ⟨res,mid⟩
      rw [hbody] at hr
      cases res with
      | none =>
          obtain ⟨out,hstep,hmA',hcanon',hmB',hframe⟩ := polySubmulBody_polynomial
            (decClockHOLFinite state) mid a b shift i A B q (by omega) (by omega)
            hc ha hb hs hi hq hACanon hBCanon hdA hdB hmA hmB hsep hbody
          let nextA := fun j => if j = shift+i then out else A j
          have ha' : mid.locals.lookup (ofString "a") = some (.val (.word a)) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "a") (by simp) hbody).trans ha
          have hb' : mid.locals.lookup (ofString "b") = some (.val (.word b)) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "b") (by simp) hbody).trans hb
          have hs' : mid.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "s") (by simp) hbody).trans hs
          have hq' : mid.locals.lookup (ofString "q") = some q.toValue :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "q") (by simp) hbody).trans hq
          have hdb' : mid.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "db") (by simp) hbody).trans hdb
          have hi' := polySubmulBody_index (decClockHOLFinite state) mid i hi hbody
          have hmeta := evaluateHOLFiniteState_metadata (decClockHOLFinite state) polySubmulBody
          rw [hbody] at hmeta
          have hc' : mid.code = originalRuntimeCode := hmeta.1.trans hc
          have hdom : mid.memaddrs = state.memaddrs := hmeta.2.1
          have hdA' : DomainPolynomial mid.memaddrs a := by rw [hdom]; exact hdA
          have hdB' : DomainPolynomial mid.memaddrs b := by rw [hdom]; exact hdB
          obtain ⟨C,hC,hmemC,hmemB,hrange,hframe'⟩ := polySubmulLoop_none mid post a b shift (i+1) db
            nextA B q (by omega) hdbBound htarget hc' ha' hb' hs' hi' hdb' hq' hcanon' hBCanon
            hdA' hdB' hmA' hmB' hsep hr
          exact ⟨C,hC,hmemC,hmemB,submulRange_step q out shift i db A B C hindex hstep hrange,
            polynomialFrame_trans state.memory mid.memory post.memory a hframe hframe'⟩
      | some result =>
          cases result with
          | «continue» =>
              have hno := evaluate_noTopContinue polySubmulBody (by decide) (decClockHOLFinite state)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | «break» =>
              have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                polySubmulBody (by decide) (decClockHOLFinite state)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | _ => simp at hr
  · rw [if_neg hindex,if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)] at hr
    have he : state = post := (Prod.mk.inj hr).2
    subst post
    exact ⟨A,hACanon,hmA,hmB,submulRange_empty q shift i db A B (by omega),
      polynomialFrame_refl state.memory a⟩
termination_by db+1-i
decreasing_by omega

end InitECandidate.Solver.Wave8GuestInv.Arith
