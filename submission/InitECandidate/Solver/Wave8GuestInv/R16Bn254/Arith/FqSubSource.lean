import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithmeticAddExprCall
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModSubExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseSource

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
attribute [local irreducible] wordAddCarryHOL addCarry256 subCarry256

def fqSubTail : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "lt")) (.const 1))
    (.call (some (some (.local, ofString "d"), none)) (ofString "u256_add")
      [.var .local (ofString "d"), limbs256ConstExpr fqModulus]) .skip)
    (.return (.var .local (ofString "d")))

theorem fqSub_source_eq : arithSourceBody Guest.Software.guestFn_fq_sub =
    .decCall (ofString "lt") .one (ofString "u256_lt")
      [.var .local (ofString "a"), .var .local (ofString "b")]
      (.decCall (ofString "d") arithU256Shape (ofString "u256_sub")
        [.var .local (ofString "a"), .var .local (ofString "b")] fqSubTail) := rfl

theorem fqSubTail_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hlt : s.locals.lookup (ofString "lt") = some (.val (.word (if a.toNat < b.toNat then 1 else 0))))
    (hd : s.locals.lookup (ofString "d") = some (subCarry256 a b).1.toValue)
    (hr : evaluateHOLFiniteState s fqSubTail = (some (.returned ret), post)) :
    ret = (modSub256 a b fqModulus).toValue := by
  have hg : evalHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
      (.cmp .equal (.var .local (ofString "lt")) (.const 1)) =
      some (.val (.word (if a.toNat < b.toNat then 1 else 0))) := by
    by_cases h : a.toNat < b.toNat <;>
      simp [evalHOLFinite, evalHOLExact, hlt, h, Compiler.Encoders.Asm.wordCmpHOL]
  dsimp only [evalHOLFinite] at hg
  unfold fqSubTail at hr
  rcases arith_seq_returned hr with hfirst | ⟨mid, hfirst, hret⟩
  · rw [evaluateHOLFiniteState_ite, hg] at hfirst
    by_cases h : a.toNat < b.toNat
    · simp only [h, if_true, show (1 : BitVec 64) ≠ 0 by decide, if_false] at hfirst
      exact False.elim (arith_call_local_not_returned s _ _ _ ret (congrArg Prod.fst hfirst))
    · simp [h, evaluateHOLFiniteState_skip] at hfirst
  · rw [evaluateHOLFiniteState_ite, hg] at hfirst
    have hlocal : mid.locals.lookup (ofString "d") = some (modSub256 a b fqModulus).toValue := by
      by_cases h : a.toNat < b.toNat
      · simp only [h, if_true, show (1 : BitVec 64) ≠ 0 by decide, if_false] at hfirst
        have hl := arith_add_call_exprs_none (ofString "d") _
          (subCarry256 a b).1 fqModulus hc
          (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hd,
            limbs256ConstExpr, Limbs256.toValue]) hfirst
        simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, modSub256, h]
      · have heq : s = mid := by simpa [h, evaluateHOLFiniteState_skip] using (congrArg Prod.snd hfirst)
        subst mid
        simpa [modSub256, h] using hd
    rw [evaluateHOLFiniteState_return] at hret
    simp [evalHOLExact, hlocal, Limbs256.toValue, shapeOfHOLExact,
      sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL] at hret
    exact hret.1.symm

/-- Exact successful-return behavior of fq_sub, without canonicality assumptions. -/
theorem fqSub_returned_exact {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_sub) =
      (some (.returned ret), post)) :
    ret = (modSub256 a b fqModulus).toValue := by
  rw [fqSub_source_eq] at hr
  obtain ⟨s1, p1, hl1, hc1, hr1, _⟩ := inverse_lt_decCall_returned
    (ofString "lt") (ofString "a") (ofString "b") a b _ ret hc ha hb hr
  have ha1 : s1.locals.lookup (ofString "a") = some a.toValue := by
    simp [hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "lt" ≠ ofString "a" by decide, ha]
  have hb1 : s1.locals.lookup (ofString "b") = some b.toValue := by
    simp [hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "lt" ≠ ofString "b" by decide, hb]
  obtain ⟨s2, p2, hl2, hc2, hr2, _⟩ := inverse_sub_decCall_returned
    (ofString "d") (ofString "a") (ofString "b") a b _ ret (hc1.trans hc) ha1 hb1 hr1
  apply fqSubTail_returned a b ret (hc2.trans (hc1.trans hc)) _ _ hr2
  · simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "d" ≠ ofString "lt" by decide]
  · simp [hl2, HolFiniteMapExact.lookup_update, FUPDATE]

/-- Canonical inputs give a canonical result and the expected modular difference. -/
theorem fqSub_returned_canonical {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue)
    (haCanon : a.toNat < fqModulus.toNat) (hbCanon : b.toNat < fqModulus.toNat)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_sub) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (out.toNat + b.toNat) a.toNat := by
  refine ⟨modSub256 a b fqModulus, fqSub_returned_exact a b ret hc ha hb hr,
    modSub256_lt_modulus a b fqModulus haCanon hbCanon, ?_⟩
  exact modSub256_add_mod a b fqModulus haCanon hbCanon

end InitECandidate.Solver.Wave8GuestInv.Arith
