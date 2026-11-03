import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryReduction
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithmeticExprCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.TailNoFallthrough

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
attribute [local irreducible] wordAddCarryHOL subCarry256

def fqReductionBody : ProgHOL 64 :=
  .decCall (ofString "lt") .one (ofString "u256_lt") [montVar "r", limbs256ConstExpr fqModulus]
    (.seq (.ite (.cmp .equal (montVar "lt") (.const 0))
      (.call none (ofString "u256_sub") [montVar "r", limbs256ConstExpr fqModulus]) .skip)
      (.return (montVar "r")))

theorem fqMulFinish_source_eq : fqMulFinish =
    .dec (ofString "r") arithU256Shape
      (.rstruct [
        .op .or [montVar "u0", .shift .lsl (montVar "u1") (.const 32)],
        .op .or [montVar "u2", .shift .lsl (montVar "u3") (.const 32)],
        .op .or [montVar "u4", .shift .lsl (montVar "u5") (.const 32)],
        .op .or [montVar "u6", .shift .lsl (montVar "c") (.const 32)]]) fqReductionBody := rfl

/-- The actual final source reduction returns precisely the one-subtraction
numeric result. This is valid for every typed raw value. -/
theorem fqReduction_returned_exact {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (raw : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hr : s.locals.lookup (ofString "r") = some raw.toValue)
    (he : evaluateHOLFiniteState s fqReductionBody = (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧
      out.toNat = montFinalReduce raw.toNat fqModulus.toNat := by
  unfold fqReductionBody at he
  obtain ⟨resumed, inner, hl, hcode, hcont, _⟩ :=
    arith_lt_decCall_exprs_returned (ofString "lt") _ raw fqModulus _ ret hc
      (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, montVar, limbs256ConstExpr,
        Limbs256.toValue, hr]) he
  have hlt : resumed.locals.lookup (ofString "lt") =
      some (.val (.word (if raw.toNat < fqModulus.toNat then 1 else 0))) := by
    simp [hl, HolFiniteMapExact.lookup_update, FUPDATE]
  have hrr : resumed.locals.lookup (ofString "r") = some raw.toValue := by
    simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "r" by decide, hr]
  have hg : evaluateHOLFiniteState resumed
      (.ite (.cmp .equal (montVar "lt") (.const 0))
        (.call none (ofString "u256_sub") [montVar "r", limbs256ConstExpr fqModulus]) .skip) =
      if raw.toNat < fqModulus.toNat then (none, resumed) else
        evaluateHOLFiniteState resumed
          (.call none (ofString "u256_sub") [montVar "r", limbs256ConstExpr fqModulus]) := by
    by_cases h : raw.toNat < fqModulus.toNat <;>
      simp [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact,
        montVar, hlt, h, Compiler.Encoders.Asm.wordCmpHOL]
  rcases arith_seq_returned hcont with hfirst | ⟨mid, hfirst, hret⟩
  · rw [hg] at hfirst
    by_cases hsmall : raw.toNat < fqModulus.toNat
    · simp [hsmall] at hfirst
    · rw [if_neg hsmall] at hfirst
      have hv := arith_sub_tailCall_exprs_returned (s := resumed) _ raw fqModulus ret (hcode.trans hc)
        (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, montVar, limbs256ConstExpr,
          Limbs256.toValue, hrr]) hfirst
      exact ⟨(subCarry256 raw fqModulus).1, hv,
        by simpa only [montFinalReduce, if_neg hsmall] using subCarry256_no_borrow raw fqModulus (by omega)⟩
  · rw [hg] at hfirst
    by_cases hsmall : raw.toNat < fqModulus.toNat
    · rw [if_pos hsmall] at hfirst
      have hmid : resumed = mid := (Prod.mk.inj hfirst).2
      subst mid
      have hv : ret = raw.toValue := by
        rw [evaluateHOLFiniteState_return] at hret
        simpa [evalHOLExact, montVar, hrr, Limbs256.toValue, shapeOfHOLExact,
          sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL] using (congrArg Prod.fst hret).symm
      exact ⟨raw, hv, by simp [montFinalReduce, hsmall]⟩
    · rw [if_neg hsmall] at hfirst
      exact False.elim (arith_tailCall_not_none resumed _ _ (congrArg Prod.fst hfirst))

end InitECandidate.Solver.Wave8GuestInv.Arith
