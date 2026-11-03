import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithmeticAddScopedExpr
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqReductionSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
attribute [local irreducible] wordAddCarryHOL addCarry256 subCarry256

theorem fqAdd_source_eq : arithSourceBody Guest.Software.guestFn_fq_add =
    .decCall (ofString "r") arithU256Shape (ofString "u256_add")
      [montVar "a", montVar "b"] fqReductionBody := rfl

/-- For arbitrary typed inputs, the source reduces their wrapped 256-bit sum. -/
theorem fqAdd_returned_exact {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_add) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧
      out.toNat = montFinalReduce (addCarry256 a b).1.toNat fqModulus.toNat := by
  rw [fqAdd_source_eq] at hr
  obtain ⟨resumed, inner, hl, hcode, hrun, _⟩ :=
    arith_add_decCall_exprs_returned (s := s) (ofString "r") _ a b _ ret hc
      (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, montVar, ha, hb]) hr
  apply fqReduction_returned_exact (s := resumed) (addCarry256 a b).1 ret (hcode.trans hc) _ hrun
  simp [hl, HolFiniteMapExact.lookup_update, FUPDATE]

/-- Canonical inputs cannot overflow the radix and their sum remains canonical
following the source's single subtraction. -/
theorem fqAdd_returned_canonical {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue)
    (haCanon : a.toNat < fqModulus.toNat) (hbCanon : b.toNat < fqModulus.toNat)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_add) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat out.toNat (a.toNat + b.toNat) := by
  obtain ⟨out, hret, hout⟩ := fqAdd_returned_exact a b ret hc ha hb hr
  have hsum : (addCarry256 a b).1.toNat = a.toNat + b.toNat := by
    have h := addCarry256_conserve a b
    have hp := fqModulus_double_lt_radix
    omega
  refine ⟨out, hret, ?_, ?_⟩
  · rw [hout, hsum]
    exact montFinalReduce_lt _ _ (by omega)
  · rw [hout, hsum]
    exact montFinalReduce_modEq _ _

end InitECandidate.Solver.Wave8GuestInv.Arith
