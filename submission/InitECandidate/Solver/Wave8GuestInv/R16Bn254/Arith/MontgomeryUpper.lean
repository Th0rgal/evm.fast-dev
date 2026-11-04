import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryWord
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryColumn

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

def montUpperCarryWord (low high carry : BitVec 64) : BitVec 64 := montHigh32 (low+carry) + high

def montUpperFinishState {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "H") (.val (.word 0))
    (setVarHOLFinite (ofString "L") (.val (.word 0))
      (setVarHOLFinite (ofString "c") (.val (.word (montUpperCarryWord low high carry)))
        (setVarHOLFinite (ofString dest) (.val (.word (montLow32 (low+carry))))
          (setVarHOLFinite (ofString "col") (.val (.word (low+carry))) s))))

theorem montUpperFinish_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (tail : ProgHOL 64) (low high carry oldCol oldDest : BitVec 64)
    (hdcol : ofString dest ≠ ofString "col") (hdc : ofString dest ≠ ofString "c")
    (hdL : ofString dest ≠ ofString "L") (hdH : ofString dest ≠ ofString "H")
    (hl : s.locals.lookup (ofString "L") = some (.val (.word low)))
    (hh : s.locals.lookup (ofString "H") = some (.val (.word high)))
    (hc : s.locals.lookup (ofString "c") = some (.val (.word carry)))
    (hcol : s.locals.lookup (ofString "col") = some (.val (.word oldCol)))
    (hd : s.locals.lookup (ofString dest) = some (.val (.word oldDest))) :
    evaluateHOLFiniteState s (montUpperColumn dest [] tail) =
      evaluateHOLFiniteState (montUpperFinishState s dest low high carry) tail := by
  simp [montUpperColumn, montAccProducts, montVar, montLoExpr, montHiExpr,
    evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign,
    evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL,
    lookupKvarHOLExact, hl, hh, hc, hcol, hd, isValidValueHOLExact, setKvarHOLFinite,
    shapeOfHOLExact, shapeEqHOL, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    hdcol, Ne.symm hdcol, hdc, Ne.symm hdc, hdL, Ne.symm hdL, hdH, Ne.symm hdH,
    show ofString "col" ≠ ofString "c" by decide,
    show ofString "col" ≠ ofString "L" by decide,
    show ofString "col" ≠ ofString "H" by decide,
    show ofString "c" ≠ ofString "L" by decide,
    show ofString "c" ≠ ofString "H" by decide,
    show ofString "L" ≠ ofString "H" by decide,
    montUpperFinishState, montUpperCarryWord, montLow32, montHigh32, AndOp.and]

theorem montUpperCarryWord_toNat (low high carry : BitVec 64)
    (hl : low.toNat ≤ 16 * 2 ^ 32) (hh : high.toNat ≤ 16 * 2 ^ 32)
    (hc : carry.toNat < 32 * 2 ^ 32) :
    (montUpperCarryWord low high carry).toNat = montUpperCarry low.toNat high.toNat carry.toNat := by
  have hcol := montAccumulator_add_toNat low carry hl hc
  have hhi : (montHigh32 (low+carry)).toNat < 48 := by rw [montHigh32_toNat,hcol]; omega
  rw [montUpperCarryWord, montAccumulator_add_toNat _ _ (by omega) (by omega), montHigh32_toNat, hcol]
  rfl

theorem montUpperCarryWord_conserve (low high carry : BitVec 64)
    (hl : low.toNat ≤ 16 * 2 ^ 32) (hh : high.toNat ≤ 16 * 2 ^ 32)
    (hc : carry.toNat < 32 * 2 ^ 32) :
    (montLow32 (low+carry)).toNat + 2 ^ 32 * (montUpperCarryWord low high carry).toNat =
      low.toNat + 2 ^ 32 * high.toNat + carry.toNat := by
  rw [montLow32_toNat, montAccumulator_add_toNat low carry hl hc,
    montUpperCarryWord_toNat low high carry hl hh hc]
  exact montUpperCarry_conserve _ _ _

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
