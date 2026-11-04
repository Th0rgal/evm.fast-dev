import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryWord

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact three local updates made by each product-accumulation block. -/
def montAccState {F : Type} (s : PanSemStateFiniteExact 64 F)
    (low high a b : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "H") (.val (.word (high + montHigh32 (a*b))))
    (setVarHOLFinite (ofString "L") (.val (.word (low + montLow32 (a*b))))
      (setVarHOLFinite (ofString "pr") (.val (.word (a*b))) s))

theorem montAccProduct_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ae be : ExpHOL 64) (tail : ProgHOL 64) (oldPr low high a b : BitVec 64)
    (ha : arithEval s ae = some (.val (.word a)))
    (hb : arithEval s be = some (.val (.word b)))
    (hpr : s.locals.lookup (ofString "pr") = some (.val (.word oldPr)))
    (hl : s.locals.lookup (ofString "L") = some (.val (.word low)))
    (hh : s.locals.lookup (ofString "H") = some (.val (.word high))) :
    evaluateHOLFiniteState s (montAccProduct ae be tail) =
      evaluateHOLFiniteState (montAccState s low high a b) tail := by
  dsimp only [arithEval] at ha hb
  simp [montAccProduct, montVar, montLoExpr, montHiExpr,
    evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign,
    evalHOLExact, evalListHOLExact, ha, hb, panOpHOL, wordOpHOL, wordOp,
    valueIsWord, valueWord, wordShiftHOL, lookupKvarHOLExact, hpr, hl, hh,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "pr" ≠ ofString "L" by decide,
    show ofString "L" ≠ ofString "pr" by decide,
    show ofString "pr" ≠ ofString "H" by decide,
    show ofString "H" ≠ ofString "pr" by decide,
    show ofString "L" ≠ ofString "H" by decide,
    show ofString "H" ≠ ofString "L" by decide,
    montAccState, montLow32, montHigh32, AndOp.and]

theorem montAccProduct_conserve (low high a b : BitVec 64)
    (hl : low.toNat ≤ 16 * 2 ^ 32) (hh : high.toNat ≤ 16 * 2 ^ 32)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (low + montLow32 (a*b)).toNat + 2 ^ 32 * (high + montHigh32 (a*b)).toNat =
      low.toNat + 2 ^ 32 * high.toNat + a.toNat * b.toNat := by
  have hlo := montLow32_lt (a*b)
  have hhi := montHigh32_lt (a*b)
  rw [montAccumulator_add_toNat _ _ hl (by omega), montAccumulator_add_toNat _ _ hh (by omega)]
  have hsplit := montDigit_product_split a b ha hb
  omega

/-- Count bounds using monotonicity, without expanding a symbolic multiple of
2^32-1 inside an arithmetic decision procedure. -/
theorem montAccumulator_add_count (n : Nat) (low digit : BitVec 64)
    (hn : n < 16) (hl : low.toNat ≤ n * (2 ^ 32 - 1))
    (hd : digit.toNat < 2 ^ 32) :
    (low+digit).toNat ≤ (n+1) * (2 ^ 32 - 1) := by
  have hl16 : low.toNat ≤ 16 * 2 ^ 32 :=
    (hl.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt hn))).trans
      (Nat.mul_le_mul_left 16 (Nat.sub_le _ _))
  have hd32 : digit.toNat < 32 * 2 ^ 32 := hd.trans_le (by decide)
  rw [montAccumulator_add_toNat low digit hl16 hd32]
  calc
    low.toNat + digit.toNat ≤ n * (2 ^ 32 - 1) + (2 ^ 32 - 1) :=
      Nat.add_le_add hl (Nat.le_pred_of_lt hd)
    _ = (n+1) * (2 ^ 32 - 1) := by rw [Nat.add_mul, Nat.one_mul]

theorem montAccProduct_bounds (n : Nat) (low high a b : BitVec 64)
    (hn : n < 16)
    (hl : low.toNat ≤ n * (2 ^ 32 - 1)) (hh : high.toNat ≤ n * (2 ^ 32 - 1)) :
    (low + montLow32 (a*b)).toNat ≤ (n+1) * (2 ^ 32 - 1) ∧
      (high + montHigh32 (a*b)).toNat ≤ (n+1) * (2 ^ 32 - 1) := by
  exact ⟨montAccumulator_add_count n low (montLow32 (a*b)) hn hl (montLow32_lt _),
    montAccumulator_add_count n high (montHigh32 (a*b)) hn hh (montHigh32_lt _)⟩


end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
