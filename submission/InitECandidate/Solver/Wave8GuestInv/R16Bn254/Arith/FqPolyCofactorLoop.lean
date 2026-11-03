import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyCofactorBody

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
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

theorem polyCofactor_guard {F : Type} (s : PanSemStateFiniteExact 64 F) (j : Nat) (hj : j ≤ 13)
    (hl : s.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 j)))) :
    arithEval s (.cmp .lower (polyDivVar "j") (.const 13)) =
      some (.val (.word (if j < 13 then 1 else 0))) := by
  have hj64 : j < 18446744073709551616 := by omega
  simp [arithEval,polyDivVar,evalHOLExact,hl,Compiler.Encoders.Asm.wordCmpHOL,
    BitVec.lt_def,Nat.mod_eq_of_lt hj64]

/-- The entire actual cofactor loop preserves canonicality and modifies only
tmp, leaving its source cofactor and quotient polynomials unchanged. -/
theorem polyCofactorLoop_none {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (t b q : BitVec 64) (j : Nat) (T B Q : Nat → Limbs256) (hj : j ≤ 13)
    (hc : s.code = originalRuntimeCode) (hl : PolyCofactorLocals s.locals t b q j)
    (hT : CanonicalPolynomial T) (hB : CanonicalPolynomial B)
    (hdT : DomainPolynomial s.memaddrs t) (hdB : DomainPolynomial s.memaddrs b)
    (hdQ : DomainPolynomial s.memaddrs q)
    (hmT : MemoryPolynomial s.memory t T) (hmB : MemoryPolynomial s.memory b B)
    (hmQ : MemoryPolynomial s.memory q Q)
    (hTB : PolynomialDisjoint t b) (hTQ : PolynomialDisjoint t q)
    (hr : evaluateHOLFiniteState s polyCofactorLoop = (none,post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧ MemoryPolynomial post.memory t C ∧
      MemoryPolynomial post.memory b B ∧ MemoryPolynomial post.memory q Q ∧
      PolynomialFrame s.memory post.memory t ∧
      post.locals.lookup (ofString "j") = some (.val (.word 13)) := by
  rw [polyCofactorLoop,evaluateHOLFiniteState_while_fixClockRewrite] at hr
  have hg := polyCofactor_guard s j hj hl.index
  change evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) _ = _ at hg
  rw [hg] at hr
  dsimp only at hr
  by_cases hindex : j < 13
  · rw [if_pos hindex,if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
    by_cases hclock : s.clock = 0
    · simp [hclock] at hr
    · rw [if_neg hclock] at hr
      rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) polyCofactorBody with ⟨result,mid⟩
      rw [hbody] at hr
      cases result with
      | none =>
          obtain ⟨C,hC,hmC,hmB',hmQ',hframe⟩ := polyCofactorBody_none (decClockHOLFinite s) mid t b q j T B Q
            hindex hc hl hT hB hdT hdB hdQ hmT hmB hmQ hTB hTQ hbody
          have hjNext : mid.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 (j+1)))) := by
            have hs := polyCofactorBody_counter (decClockHOLFinite s) (BitVec.ofNat 64 j) hl.index
            dsimp only at hs
            rw [hbody] at hs
            rw [BitVec.ofNat_add]
            exact hs (Or.inl rfl)
          have hl' : PolyCofactorLocals mid.locals t b q (j+1) :=
            ⟨(polyCofactorBody_keeps (decClockHOLFinite s) mid (ofString "tmp") (by simp) hbody).trans hl.t,
             (polyCofactorBody_keeps (decClockHOLFinite s) mid (ofString "s1") (by simp) hbody).trans hl.b,
             (polyCofactorBody_keeps (decClockHOLFinite s) mid (ofString "q") (by simp) hbody).trans hl.q,hjNext⟩
          have hmeta := evaluateHOLFiniteState_metadata (decClockHOLFinite s) polyCofactorBody
          rw [hbody] at hmeta
          have hdom : mid.memaddrs = s.memaddrs := hmeta.2.1
          obtain ⟨D,hD,hmD,hmB'',hmQ'',hframe',hfinal⟩ := polyCofactorLoop_none mid post t b q (j+1) C B Q
            (by omega) (hmeta.1.trans hc) hl' hC hB
            (by rw [hdom]; exact hdT) (by rw [hdom]; exact hdB) (by rw [hdom]; exact hdQ)
            hmC hmB' hmQ' hTB hTQ hr
          exact ⟨D,hD,hmD,hmB'',hmQ'',polynomialFrame_trans s.memory mid.memory post.memory t hframe hframe',hfinal⟩
      | some result =>
          cases result with
          | «continue» =>
              have hno := evaluate_noTopContinue polyCofactorBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | «break» =>
              have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                polyCofactorBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | _ => simp at hr
  · rw [if_neg hindex,if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)] at hr
    have he : s = post := (Prod.mk.inj hr).2
    subst post
    have hjEq : j = 13 := by omega
    exact ⟨T,hT,hmT,hmB,hmQ,fun _ _ => rfl,hl.index.trans (congrArg (fun w : BitVec 64 => some (ValueHOL.val (.word w))) (by rw [hjEq]; decide))⟩
termination_by 13-j
decreasing_by omega

theorem polyCofactorLoop_keeps {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (name : MlS) (hn : name ∈ [ofString "r0",ofString "r1",ofString "s0",ofString "s1",ofString "tmp",ofString "q",ofString "d0",ofString "d1"])
    (hr : evaluateHOLFiniteState s polyCofactorLoop = (none,post)) :
    post.locals.lookup name = s.locals.lookup name := by
  have ha : avoidsLocal name polyCofactorLoop = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h := evaluate_avoidsLocal_flowing name polyCofactorLoop ha s (Or.inl (by rw [hr]))
  rw [hr] at h
  exact h

end InitECandidate.Solver.Wave8GuestInv.Arith
