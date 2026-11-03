import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeScan
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialStore

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

/-- Whole actual fq_poly_deg source correctness, including the zero-polynomial
sentinel and maximality of a returned nonzero coefficient. -/
theorem fqDegree_returned_correct {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (n : Nat) (ret : ValueHOL 64)
    (hn : n ≤ 13) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hcount : s.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_poly_deg) =
      (some (.returned ret), post)) :
    (ret = .val (.word (0 - 1)) ∧ ∀ j, j < n → (coefficients j).toNat = 0) ∨
    ∃ j : Nat, j < n ∧ ret = .val (.word (BitVec.ofNat 64 j)) ∧ (coefficients j).toNat ≠ 0 ∧
      ∀ k, j < k → k < n → (coefficients k).toNat = 0 := by
  rw [fqDegree_source_eq] at hr
  obtain ⟨value, hinit, hshape, inner, hbody⟩ := arith_dec_returned hr
  have hv : value = .val (.word (BitVec.ofNat 64 n)) := by
    simpa [evalHOLFinite, evalHOLExact, hcount] using hinit.symm
  subst value
  let entry := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 n))) s
  have ha' : entry.locals.lookup (ofString "a") = some (.val (.word base)) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "a" by decide] using ha
  have hs := fqDegreeLoop_scan entry base coefficients n hn hc ha'
    (by simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) halign hbound hd hm
  rcases arith_seq_returned hbody with hret | ⟨mid, hnone, hreturn⟩
  · change evaluateHOLFiniteState entry fqDegreeLoop = _ at hret
    rw [hret] at hs
    exact Or.inr (hs.2 ret rfl)
  · change evaluateHOLFiniteState entry fqDegreeLoop = _ at hnone
    rw [hnone] at hs
    have hreturn' : evaluateHOLFiniteState mid (.return (.op .sub [.const 0, .const 1])) =
        (some (.returned (.val (.word (0 - 1)))), emptyLocalsHOLFinite mid) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp,
        valueIsWord, valueWord, shapeOfHOLExact]
    rw [hreturn'] at hreturn
    have he : ret = .val (.word (0 - 1)) := by
      simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using (Prod.mk.inj hreturn).1.symm
    exact Or.inl ⟨he, hs.1 rfl⟩

/-- Once all coefficients at or above d have been cleared, an actual degree
scan returns the sentinel or an index strictly below d. No canonicality premise
is needed for this scan theorem. -/
theorem fqDegree_returned_below {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (d : Nat) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hcount : s.locals.lookup (ofString "n") = some (.val (.word 13)))
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients)
    (hdegree : PolynomialDegreeBelow coefficients d)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_poly_deg) =
      (some (.returned ret), post)) :
    ret = .val (.word (0 - 1)) ∨ ∃ j : Nat, j < d ∧ ret = .val (.word (BitVec.ofNat 64 j)) := by
  rcases fqDegree_returned_correct s post base coefficients 13 ret (by decide) hc ha hcount
    halign hbound hd hm hr with ⟨he,hzero⟩ | ⟨j,hj,he,hne,habove⟩
  · exact Or.inl he
  · refine Or.inr ⟨j, ?_, he⟩
    by_contra h
    exact hne (hdegree j hj (by omega))

end InitECandidate.Solver.Wave8GuestInv.Arith
