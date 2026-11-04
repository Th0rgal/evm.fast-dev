import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryDigits
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The machine words introduced by the eight input-digit declarations. -/
def limbs256Words (a : Limbs256) (i : Fin 8) : BitVec 64 :=
  match i.val with
  | 0 => montLow32 a.l0
  | 1 => montHigh32 a.l0
  | 2 => montLow32 a.l1
  | 3 => montHigh32 a.l1
  | 4 => montLow32 a.l2
  | 5 => montHigh32 a.l2
  | 6 => montLow32 a.l3
  | _ => montHigh32 a.l3

theorem limbs256Words_toNat (a : Limbs256) (i : Fin 8) :
    (limbs256Words a i).toNat = limbs256Digits a i := by
  fin_cases i <;> rfl

theorem limbs256Words_lt (a : Limbs256) (i : Fin 8) :
    (limbs256Words a i).toNat < 2 ^ 32 := by
  rw [limbs256Words_toNat]
  exact limbs256Digits_lt a i

theorem limbs256Words_value (a : Limbs256) :
    montRadix8 (fun i => (limbs256Words a i).toNat) = a.toNat := by
  have h : (fun i => (limbs256Words a i).toNat) = limbs256Digits a :=
    funext (limbs256Words_toNat a)
  rw [h, limbs256Digits_value]

/-- Exact expression shapes used by the input initializers. -/
def fqInputWordExpr (name : MlS) (i : Fin 8) : ExpHOL 64 :=
  match i.val with
  | 0 => montLoExpr (.rfield 0 (.var .local name))
  | 1 => montHiExpr (.rfield 0 (.var .local name))
  | 2 => montLoExpr (.rfield 1 (.var .local name))
  | 3 => montHiExpr (.rfield 1 (.var .local name))
  | 4 => montLoExpr (.rfield 2 (.var .local name))
  | 5 => montHiExpr (.rfield 2 (.var .local name))
  | 6 => montLoExpr (.rfield 3 (.var .local name))
  | _ => montHiExpr (.rfield 3 (.var .local name))

theorem fqInputWordExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (a : Limbs256) (i : Fin 8)
    (ha : s.locals.lookup name = some a.toValue) :
    arithEval s (fqInputWordExpr name i) = some (.val (.word (limbs256Words a i))) := by
  fin_cases i <;>
    simp [arithEval, fqInputWordExpr, limbs256Words, montLoExpr, montHiExpr,
      evalHOLExact, evalListHOLExact, ha, Limbs256.toValue, wordOpHOL, wordOp,
      valueIsWord, valueWord, wordShiftHOL, montLow32, montHigh32, AndOp.and]

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
