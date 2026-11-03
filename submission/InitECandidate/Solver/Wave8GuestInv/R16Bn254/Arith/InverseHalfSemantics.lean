import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseRank
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ReadFailure
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256CallFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The literal four-limb shift expression in both modinv_bin halving loops. -/
def inverseHalfExpr (counter : MlS) : ExpHOL 64 :=
  .rstruct [
    .op .or [.shift .lsr (.rfield 0 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 1 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 1 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 2 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 2 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 3 (.var .local counter)) (.const 63)],
    .shift .lsr (.rfield 3 (.var .local counter)) (.const 1)]

def inverseEvenExpr (counter : MlS) : ExpHOL 64 :=
  .cmp .equal (.op .and [.rfield 0 (.var .local counter), .const 1]) (.const 0)

theorem inverseHalfExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs256)
    (hl : s.locals.lookup counter = some a.toValue) :
    arithEval s (inverseHalfExpr counter) = some (half256 a).toValue := by
  simp [inverseHalfExpr, arithEval, evalHOLExact, evalListHOLExact, hl,
    Limbs256.toValue, wordShiftHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
    half256, halfWord256, OrOp.or]

theorem inverseHalf_assign {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs256)
    (hl : s.locals.lookup counter = some a.toValue) :
    evaluateHOLFiniteState s (.assign .local counter (inverseHalfExpr counter)) =
      (none, setVarHOLFinite counter (half256 a).toValue s) := by
  have he := inverseHalfExpr_eval s counter a hl
  dsimp only [arithEval] at he
  simp [evaluateHOLFiniteState_assign, he, lookupKvarHOLExact, hl,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL,
    Limbs256.toValue, shapeEqHOL.shapeEqListHOL]

theorem inverseHalf_assign_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs256)
    (hl : s.locals.lookup counter = some a.toValue) (ha : 0 < a.toNat) :
    ∃ b : Limbs256,
      (evaluateHOLFiniteState s (.assign .local counter (inverseHalfExpr counter))).2.locals.lookup counter =
        some b.toValue ∧ b.toNat.size < a.toNat.size := by
  refine ⟨half256 a, ?_, half256_size_lt a ha⟩
  rw [inverseHalf_assign s counter a hl]
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem inverseEvenExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs256)
    (hl : s.locals.lookup counter = some a.toValue) :
    arithEval s (inverseEvenExpr counter) =
      some (.val (.word (if a.toNat % 2 = 0 then 1 else 0))) := by
  have hp : a.toNat % 2 = a.l0.toNat % 2 := by
    unfold Limbs256.toNat
    omega
  have hz : (a.l0 &&& (1 : BitVec 64)) = 0 ↔ a.toNat % 2 = 0 := by
    rw [← BitVec.toNat_inj]
    simp [BitVec.toNat_and, hp]
  simp [inverseEvenExpr, arithEval, evalHOLExact, evalListHOLExact, hl,
    Limbs256.toValue, wordOpHOL, wordOp, valueIsWord, valueWord, AndOp.and,
    Compiler.Encoders.Asm.wordCmpHOL]
  change (if a.l0 &&& (1 : BitVec 64) = 0 then (1 : BitVec 64) else 0) = _
  by_cases heven : a.toNat % 2 = 0
  · rw [if_pos (hz.mpr heven), if_pos heven]
    rfl
  · rw [if_neg (fun h => heven (hz.mp h)), if_neg heven]
    rfl

theorem half256_positive_of_even (a : Limbs256) (ha : 0 < a.toNat)
    (he : a.toNat % 2 = 0) : 0 < (half256 a).toNat := by
  rw [half256_toNat]
  omega

end InitECandidate.Solver.Wave8GuestInv.Arith
