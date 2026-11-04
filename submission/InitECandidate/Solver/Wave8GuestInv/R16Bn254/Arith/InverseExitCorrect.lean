import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseBodyCongruence

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

theorem inverseExitCheck_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (counter coefficient : MlS) (a x : Limbs256) (ret : ValueHOL 64)
    (ha : s.locals.lookup counter = some a.toValue)
    (hx : s.locals.lookup coefficient = some x.toValue)
    (hr : evaluateHOLFiniteState s (inverseExitCheck counter coefficient) =
      (some (.returned ret), post)) :
    a.toNat = 1 ∧ ret = x.toValue := by
  by_cases htop : a.l1 = 0#64 ∧ a.l2 = 0#64 ∧ a.l3 = 0#64
  · by_cases hlow : a.l0 = 1#64
    · have ht := htop
      refine ⟨by simp [Limbs256.toNat, ht.1, ht.2.1, ht.2.2, hlow], ?_⟩
      simpa [inverseExitCheck, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
        evalHOLExact, evalListHOLExact, ha, hx, Limbs256.toValue, wordOpHOL, wordOp,
        valueIsWord, valueWord, OrOp.or, Compiler.Encoders.Asm.wordCmpHOL, BitVec.or_eq_zero_iff, htop, hlow,
        shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL] using
        (congrArg Prod.fst hr).symm
    · simp [inverseExitCheck, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip,
        evalHOLExact, evalListHOLExact, ha, hx, Limbs256.toValue, wordOpHOL, wordOp,
        valueIsWord, valueWord, OrOp.or, Compiler.Encoders.Asm.wordCmpHOL, BitVec.or_eq_zero_iff, htop, hlow] at hr
  · simp [inverseExitCheck, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip,
      evalHOLExact, evalListHOLExact, ha, hx, Limbs256.toValue, wordOpHOL, wordOp,
      valueIsWord, valueWord, OrOp.or, Compiler.Encoders.Asm.wordCmpHOL, BitVec.or_eq_zero_iff, htop] at hr

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
