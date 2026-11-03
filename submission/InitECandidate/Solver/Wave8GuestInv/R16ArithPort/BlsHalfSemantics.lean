import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsArithmetic
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.InverseHalfSemantics

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Six-limb cross-word shift returned by bls_fp_shr1. -/
def blsHalfExpr (counter : MlS) : ExpHOL 64 :=
  .rstruct [
    .op .or [.shift .lsr (.rfield 0 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 1 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 1 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 2 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 2 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 3 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 3 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 4 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 4 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 5 (.var .local counter)) (.const 63)],
    .shift .lsr (.rfield 5 (.var .local counter)) (.const 1)]

theorem blsHalfExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs384)
    (hl : s.locals.lookup counter = some a.toValue) :
    arithEval s (blsHalfExpr counter) = some (half384 a).toValue := by
  simp [blsHalfExpr, arithEval, evalHOLExact, evalListHOLExact, hl,
    Limbs384.toValue, wordShiftHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
    half384, halfWord256, OrOp.or]

theorem blsEvenExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs384)
    (hl : s.locals.lookup counter = some a.toValue) :
    arithEval s (inverseEvenExpr counter) =
      some (.val (.word (if a.toNat % 2 = 0 then 1 else 0))) := by
  have hp : a.toNat % 2 = a.l0.toNat % 2 := by
    unfold Limbs384.toNat
    omega
  have hz : (a.l0 &&& (1 : BitVec 64)) = 0 ↔ a.toNat % 2 = 0 := by
    rw [← BitVec.toNat_inj]
    simp [BitVec.toNat_and, hp]
  simp [inverseEvenExpr, arithEval, evalHOLExact, evalListHOLExact, hl,
    Limbs384.toValue, wordOpHOL, wordOp, valueIsWord, valueWord, AndOp.and,
    Compiler.Encoders.Asm.wordCmpHOL]
  change (if a.l0 &&& (1 : BitVec 64) = 0 then (1 : BitVec 64) else 0) = _
  by_cases heven : a.toNat % 2 = 0
  · rw [if_pos (hz.mpr heven), if_pos heven]
    rfl
  · rw [if_neg (fun h => heven (hz.mp h)), if_neg heven]
    rfl


theorem blsHalf_source_eq : arithSourceBody Guest.Software.guestFn_bls_fp_shr1 =
    .return (blsHalfExpr (ofString "x")) := rfl

theorem eval_bls_fp_shr1_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Limbs384) (ha : s.locals.lookup (ofString "x") = some a.toValue) :
    evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_bls_fp_shr1) =
      (some (.returned (half384 a).toValue), emptyLocalsHOLFinite s) := by
  rw [blsHalf_source_eq, evaluateHOLFiniteState_return]
  have he := blsHalfExpr_eval s (ofString "x") a ha
  dsimp only [arithEval] at he
  rw [he]
  simp [Limbs384.toValue, shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
end InitECandidate.Solver.Wave8GuestInv.Arith
