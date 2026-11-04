import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryCarry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def montLowerFinishState {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let col := low + carry
  let digit := montLow32 col
  let correction := fqCorrectionWord digit
  let product := correction * 3632069959#64
  let col2 := digit + montLow32 product
  setVarHOLFinite (ofString "H") (.val (.word 0))
    (setVarHOLFinite (ofString "L") (.val (.word 0))
      (setVarHOLFinite (ofString "c") (.val (.word (montLowerCarryWord low high carry)))
        (setVarHOLFinite (ofString "col2") (.val (.word col2))
          (setVarHOLFinite (ofString "pr") (.val (.word product))
            (setVarHOLFinite (ofString dest) (.val (.word correction))
              (setVarHOLFinite (ofString "dg") (.val (.word digit))
                (setVarHOLFinite (ofString "col") (.val (.word col)) s)))))))

/-- The first four assignments, separated to bound kernel checking work. -/
def montLowerPrefix (dest : String) (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "col") (.op .add [montVar "L", montVar "c"]))
    (.seq (.assign .local (ofString "dg") (montLoExpr (montVar "col")))
      (.seq (.assign .local (ofString dest) (montLoExpr (.panop .mul [montVar "dg", .const 3834012553])))
        (.seq (.assign .local (ofString "pr") (.panop .mul [montVar dest, .const 3632069959])) tail)))

def montLowerPrefixState {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low carry : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "pr") (.val (.word (fqCorrectionWord (montLow32 (low+carry)) * 3632069959#64)))
    (setVarHOLFinite (ofString dest) (.val (.word (fqCorrectionWord (montLow32 (low+carry)))))
      (setVarHOLFinite (ofString "dg") (.val (.word (montLow32 (low+carry))))
        (setVarHOLFinite (ofString "col") (.val (.word (low+carry))) s)))

def montLowerSuffix (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "col2") (.op .add [montVar "dg", montLoExpr (montVar "pr")]))
    (.seq (.assign .local (ofString "c") (.op .add [montHiExpr (montVar "col"), montVar "H",
      montHiExpr (montVar "col2"), montHiExpr (montVar "pr")]))
      (.seq (.assign .local (ofString "L") (.const 0))
        (.seq (.assign .local (ofString "H") (.const 0)) tail)))

def montLowerSuffixState {F : Type} (s : PanSemStateFiniteExact 64 F)
    (col digit product high : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "H") (.val (.word 0))
    (setVarHOLFinite (ofString "L") (.val (.word 0))
      (setVarHOLFinite (ofString "c") (.val (.word
        (montHigh32 col + (high + (montHigh32 (digit + montLow32 product) + montHigh32 product)))))
        (setVarHOLFinite (ofString "col2") (.val (.word (digit + montLow32 product))) s)))

theorem montLowerPrefix_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (tail : ProgHOL 64) (low carry oldCol oldDg oldPr oldDest : BitVec 64)
    (hdcol : ofString dest ≠ ofString "col")
    (hddg : ofString dest ≠ ofString "dg")
    (hdpr : ofString dest ≠ ofString "pr")
    (hL : s.locals.lookup (ofString "L") = some (.val (.word low)))
    (hc : s.locals.lookup (ofString "c") = some (.val (.word carry)))
    (hcol : s.locals.lookup (ofString "col") = some (.val (.word oldCol)))
    (hdg : s.locals.lookup (ofString "dg") = some (.val (.word oldDg)))
    (hpr : s.locals.lookup (ofString "pr") = some (.val (.word oldPr)))
    (hdest : s.locals.lookup (ofString dest) = some (.val (.word oldDest))) :
    evaluateHOLFiniteState s (montLowerPrefix dest tail) =
      evaluateHOLFiniteState (montLowerPrefixState s dest low carry) tail := by
  simp [montLowerPrefix, montLowerPrefixState, montVar, montLoExpr, montHiExpr,
    evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign,
    evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord,
    wordShiftHOL, panOpHOL, lookupKvarHOLExact, hL, hc, hcol, hdg, hpr, hdest,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    hdcol, Ne.symm hdcol, hddg, Ne.symm hddg, hdpr, Ne.symm hdpr,
    show ofString "col" ≠ ofString "dg" by decide,
    show ofString "col" ≠ ofString "pr" by decide,
    show ofString "col" ≠ ofString "col2" by decide,
    show ofString "col" ≠ ofString "c" by decide,
    show ofString "col" ≠ ofString "L" by decide,
    show ofString "col" ≠ ofString "H" by decide,
    show ofString "dg" ≠ ofString "col" by decide,
    show ofString "dg" ≠ ofString "pr" by decide,
    show ofString "dg" ≠ ofString "col2" by decide,
    show ofString "dg" ≠ ofString "c" by decide,
    show ofString "dg" ≠ ofString "L" by decide,
    show ofString "dg" ≠ ofString "H" by decide,
    show ofString "pr" ≠ ofString "col" by decide,
    show ofString "pr" ≠ ofString "dg" by decide,
    show ofString "pr" ≠ ofString "col2" by decide,
    show ofString "pr" ≠ ofString "c" by decide,
    show ofString "pr" ≠ ofString "L" by decide,
    show ofString "pr" ≠ ofString "H" by decide,
    show ofString "col2" ≠ ofString "col" by decide,
    show ofString "col2" ≠ ofString "dg" by decide,
    show ofString "col2" ≠ ofString "pr" by decide,
    show ofString "col2" ≠ ofString "c" by decide,
    show ofString "col2" ≠ ofString "L" by decide,
    show ofString "col2" ≠ ofString "H" by decide,
    show ofString "c" ≠ ofString "col" by decide,
    show ofString "c" ≠ ofString "dg" by decide,
    show ofString "c" ≠ ofString "pr" by decide,
    show ofString "c" ≠ ofString "col2" by decide,
    show ofString "c" ≠ ofString "L" by decide,
    show ofString "c" ≠ ofString "H" by decide,
    show ofString "L" ≠ ofString "col" by decide,
    show ofString "L" ≠ ofString "dg" by decide,
    show ofString "L" ≠ ofString "pr" by decide,
    show ofString "L" ≠ ofString "col2" by decide,
    show ofString "L" ≠ ofString "c" by decide,
    show ofString "L" ≠ ofString "H" by decide,
    show ofString "H" ≠ ofString "col" by decide,
    show ofString "H" ≠ ofString "dg" by decide,
    show ofString "H" ≠ ofString "pr" by decide,
    show ofString "H" ≠ ofString "col2" by decide,
    show ofString "H" ≠ ofString "c" by decide,
    show ofString "H" ≠ ofString "L" by decide, fqCorrectionWord, montLow32, montHigh32, AndOp.and]

theorem montLowerSuffix_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (tail : ProgHOL 64) (col digit product high oldCol2 oldCarry oldLow : BitVec 64)
    (hcol : s.locals.lookup (ofString "col") = some (.val (.word col)))
    (hdg : s.locals.lookup (ofString "dg") = some (.val (.word digit)))
    (hpr : s.locals.lookup (ofString "pr") = some (.val (.word product)))
    (hH : s.locals.lookup (ofString "H") = some (.val (.word high)))
    (hcol2 : s.locals.lookup (ofString "col2") = some (.val (.word oldCol2)))
    (hc : s.locals.lookup (ofString "c") = some (.val (.word oldCarry)))
    (hL : s.locals.lookup (ofString "L") = some (.val (.word oldLow))) :
    evaluateHOLFiniteState s (montLowerSuffix tail) =
      evaluateHOLFiniteState (montLowerSuffixState s col digit product high) tail := by
  simp [montLowerSuffix, montLowerSuffixState, montVar, montLoExpr, montHiExpr,
    evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign,
    evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord,
    wordShiftHOL, lookupKvarHOLExact, hL, hc, hcol, hdg, hpr, hH, hcol2,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "col" ≠ ofString "dg" by decide,
    show ofString "col" ≠ ofString "pr" by decide,
    show ofString "col" ≠ ofString "col2" by decide,
    show ofString "col" ≠ ofString "c" by decide,
    show ofString "col" ≠ ofString "L" by decide,
    show ofString "col" ≠ ofString "H" by decide,
    show ofString "dg" ≠ ofString "col" by decide,
    show ofString "dg" ≠ ofString "pr" by decide,
    show ofString "dg" ≠ ofString "col2" by decide,
    show ofString "dg" ≠ ofString "c" by decide,
    show ofString "dg" ≠ ofString "L" by decide,
    show ofString "dg" ≠ ofString "H" by decide,
    show ofString "pr" ≠ ofString "col" by decide,
    show ofString "pr" ≠ ofString "dg" by decide,
    show ofString "pr" ≠ ofString "col2" by decide,
    show ofString "pr" ≠ ofString "c" by decide,
    show ofString "pr" ≠ ofString "L" by decide,
    show ofString "pr" ≠ ofString "H" by decide,
    show ofString "col2" ≠ ofString "col" by decide,
    show ofString "col2" ≠ ofString "dg" by decide,
    show ofString "col2" ≠ ofString "pr" by decide,
    show ofString "col2" ≠ ofString "c" by decide,
    show ofString "col2" ≠ ofString "L" by decide,
    show ofString "col2" ≠ ofString "H" by decide,
    show ofString "c" ≠ ofString "col" by decide,
    show ofString "c" ≠ ofString "dg" by decide,
    show ofString "c" ≠ ofString "pr" by decide,
    show ofString "c" ≠ ofString "col2" by decide,
    show ofString "c" ≠ ofString "L" by decide,
    show ofString "c" ≠ ofString "H" by decide,
    show ofString "L" ≠ ofString "col" by decide,
    show ofString "L" ≠ ofString "dg" by decide,
    show ofString "L" ≠ ofString "pr" by decide,
    show ofString "L" ≠ ofString "col2" by decide,
    show ofString "L" ≠ ofString "c" by decide,
    show ofString "L" ≠ ofString "H" by decide,
    show ofString "H" ≠ ofString "col" by decide,
    show ofString "H" ≠ ofString "dg" by decide,
    show ofString "H" ≠ ofString "pr" by decide,
    show ofString "H" ≠ ofString "col2" by decide,
    show ofString "H" ≠ ofString "c" by decide,
    show ofString "H" ≠ ofString "L" by decide, montLow32, montHigh32, AndOp.and]

theorem montLowerFinish_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (tail : ProgHOL 64) (low high carry oldCol oldDg oldPr oldCol2 oldDest : BitVec 64)
    (hdcol : ofString dest ≠ ofString "col")
    (hddg : ofString dest ≠ ofString "dg")
    (hdpr : ofString dest ≠ ofString "pr")
    (hdcol2 : ofString dest ≠ ofString "col2")
    (hdc : ofString dest ≠ ofString "c")
    (hdL : ofString dest ≠ ofString "L")
    (hdH : ofString dest ≠ ofString "H")
    (hL : s.locals.lookup (ofString "L") = some (.val (.word low)))
    (hH : s.locals.lookup (ofString "H") = some (.val (.word high)))
    (hc : s.locals.lookup (ofString "c") = some (.val (.word carry)))
    (hcol : s.locals.lookup (ofString "col") = some (.val (.word oldCol)))
    (hdg : s.locals.lookup (ofString "dg") = some (.val (.word oldDg)))
    (hpr : s.locals.lookup (ofString "pr") = some (.val (.word oldPr)))
    (hcol2 : s.locals.lookup (ofString "col2") = some (.val (.word oldCol2)))
    (hdest : s.locals.lookup (ofString dest) = some (.val (.word oldDest))) :
    evaluateHOLFiniteState s (montLowerColumn dest [] tail) =
      evaluateHOLFiniteState (montLowerFinishState s dest low high carry) tail := by
  change evaluateHOLFiniteState s (montLowerPrefix dest (montLowerSuffix tail)) = _
  rw [montLowerPrefix_eval s dest (montLowerSuffix tail) low carry oldCol oldDg oldPr oldDest
    hdcol hddg hdpr hL hc hcol hdg hpr hdest]
  have hs := montLowerSuffix_eval (montLowerPrefixState s dest low carry) tail
    (low+carry) (montLow32 (low+carry))
    (fqCorrectionWord (montLow32 (low+carry)) * 3632069959#64) high oldCol2 carry low
  have hcol' : (montLowerPrefixState s dest low carry).locals.lookup (ofString "col") =
      some (.val (.word (low+carry))) := by
    simp [montLowerPrefixState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hdcol, Ne.symm hdcol, show ofString "col" ≠ ofString "dg" by decide,
    show ofString "col" ≠ ofString "pr" by decide,
    show ofString "col" ≠ ofString "col2" by decide,
    show ofString "col" ≠ ofString "c" by decide,
    show ofString "col" ≠ ofString "L" by decide,
    show ofString "col" ≠ ofString "H" by decide,
    show ofString "dg" ≠ ofString "col" by decide,
    show ofString "dg" ≠ ofString "pr" by decide,
    show ofString "dg" ≠ ofString "col2" by decide,
    show ofString "dg" ≠ ofString "c" by decide,
    show ofString "dg" ≠ ofString "L" by decide,
    show ofString "dg" ≠ ofString "H" by decide,
    show ofString "pr" ≠ ofString "col" by decide,
    show ofString "pr" ≠ ofString "dg" by decide,
    show ofString "pr" ≠ ofString "col2" by decide,
    show ofString "pr" ≠ ofString "c" by decide,
    show ofString "pr" ≠ ofString "L" by decide,
    show ofString "pr" ≠ ofString "H" by decide,
    show ofString "col2" ≠ ofString "col" by decide,
    show ofString "col2" ≠ ofString "dg" by decide,
    show ofString "col2" ≠ ofString "pr" by decide,
    show ofString "col2" ≠ ofString "c" by decide,
    show ofString "col2" ≠ ofString "L" by decide,
    show ofString "col2" ≠ ofString "H" by decide,
    show ofString "c" ≠ ofString "col" by decide,
    show ofString "c" ≠ ofString "dg" by decide,
    show ofString "c" ≠ ofString "pr" by decide,
    show ofString "c" ≠ ofString "col2" by decide,
    show ofString "c" ≠ ofString "L" by decide,
    show ofString "c" ≠ ofString "H" by decide,
    show ofString "L" ≠ ofString "col" by decide,
    show ofString "L" ≠ ofString "dg" by decide,
    show ofString "L" ≠ ofString "pr" by decide,
    show ofString "L" ≠ ofString "col2" by decide,
    show ofString "L" ≠ ofString "c" by decide,
    show ofString "L" ≠ ofString "H" by decide,
    show ofString "H" ≠ ofString "col" by decide,
    show ofString "H" ≠ ofString "dg" by decide,
    show ofString "H" ≠ ofString "pr" by decide,
    show ofString "H" ≠ ofString "col2" by decide,
    show ofString "H" ≠ ofString "c" by decide,
    show ofString "H" ≠ ofString "L" by decide]
  have hdg' : (montLowerPrefixState s dest low carry).locals.lookup (ofString "dg") =
      some (.val (.word (montLow32 (low+carry)))) := by
    simp [montLowerPrefixState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hddg, Ne.symm hddg, show ofString "col" ≠ ofString "dg" by decide,
    show ofString "col" ≠ ofString "pr" by decide,
    show ofString "col" ≠ ofString "col2" by decide,
    show ofString "col" ≠ ofString "c" by decide,
    show ofString "col" ≠ ofString "L" by decide,
    show ofString "col" ≠ ofString "H" by decide,
    show ofString "dg" ≠ ofString "col" by decide,
    show ofString "dg" ≠ ofString "pr" by decide,
    show ofString "dg" ≠ ofString "col2" by decide,
    show ofString "dg" ≠ ofString "c" by decide,
    show ofString "dg" ≠ ofString "L" by decide,
    show ofString "dg" ≠ ofString "H" by decide,
    show ofString "pr" ≠ ofString "col" by decide,
    show ofString "pr" ≠ ofString "dg" by decide,
    show ofString "pr" ≠ ofString "col2" by decide,
    show ofString "pr" ≠ ofString "c" by decide,
    show ofString "pr" ≠ ofString "L" by decide,
    show ofString "pr" ≠ ofString "H" by decide,
    show ofString "col2" ≠ ofString "col" by decide,
    show ofString "col2" ≠ ofString "dg" by decide,
    show ofString "col2" ≠ ofString "pr" by decide,
    show ofString "col2" ≠ ofString "c" by decide,
    show ofString "col2" ≠ ofString "L" by decide,
    show ofString "col2" ≠ ofString "H" by decide,
    show ofString "c" ≠ ofString "col" by decide,
    show ofString "c" ≠ ofString "dg" by decide,
    show ofString "c" ≠ ofString "pr" by decide,
    show ofString "c" ≠ ofString "col2" by decide,
    show ofString "c" ≠ ofString "L" by decide,
    show ofString "c" ≠ ofString "H" by decide,
    show ofString "L" ≠ ofString "col" by decide,
    show ofString "L" ≠ ofString "dg" by decide,
    show ofString "L" ≠ ofString "pr" by decide,
    show ofString "L" ≠ ofString "col2" by decide,
    show ofString "L" ≠ ofString "c" by decide,
    show ofString "L" ≠ ofString "H" by decide,
    show ofString "H" ≠ ofString "col" by decide,
    show ofString "H" ≠ ofString "dg" by decide,
    show ofString "H" ≠ ofString "pr" by decide,
    show ofString "H" ≠ ofString "col2" by decide,
    show ofString "H" ≠ ofString "c" by decide,
    show ofString "H" ≠ ofString "L" by decide]
  have hpr' : (montLowerPrefixState s dest low carry).locals.lookup (ofString "pr") =
      some (.val (.word (fqCorrectionWord (montLow32 (low+carry)) * 3632069959#64))) := by
    simp [montLowerPrefixState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  apply hs hcol' hdg' hpr'
  all_goals simp [montLowerPrefixState, montLowerSuffixState, montLowerFinishState,
    montLowerCarryWord, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    hdH, Ne.symm hdH, hdcol2, Ne.symm hdcol2, hdc, Ne.symm hdc, hdL, Ne.symm hdL,
    hH, hcol2, hc, hL, show ofString "col" ≠ ofString "dg" by decide,
    show ofString "col" ≠ ofString "pr" by decide,
    show ofString "col" ≠ ofString "col2" by decide,
    show ofString "col" ≠ ofString "c" by decide,
    show ofString "col" ≠ ofString "L" by decide,
    show ofString "col" ≠ ofString "H" by decide,
    show ofString "dg" ≠ ofString "col" by decide,
    show ofString "dg" ≠ ofString "pr" by decide,
    show ofString "dg" ≠ ofString "col2" by decide,
    show ofString "dg" ≠ ofString "c" by decide,
    show ofString "dg" ≠ ofString "L" by decide,
    show ofString "dg" ≠ ofString "H" by decide,
    show ofString "pr" ≠ ofString "col" by decide,
    show ofString "pr" ≠ ofString "dg" by decide,
    show ofString "pr" ≠ ofString "col2" by decide,
    show ofString "pr" ≠ ofString "c" by decide,
    show ofString "pr" ≠ ofString "L" by decide,
    show ofString "pr" ≠ ofString "H" by decide,
    show ofString "col2" ≠ ofString "col" by decide,
    show ofString "col2" ≠ ofString "dg" by decide,
    show ofString "col2" ≠ ofString "pr" by decide,
    show ofString "col2" ≠ ofString "c" by decide,
    show ofString "col2" ≠ ofString "L" by decide,
    show ofString "col2" ≠ ofString "H" by decide,
    show ofString "c" ≠ ofString "col" by decide,
    show ofString "c" ≠ ofString "dg" by decide,
    show ofString "c" ≠ ofString "pr" by decide,
    show ofString "c" ≠ ofString "col2" by decide,
    show ofString "c" ≠ ofString "L" by decide,
    show ofString "c" ≠ ofString "H" by decide,
    show ofString "L" ≠ ofString "col" by decide,
    show ofString "L" ≠ ofString "dg" by decide,
    show ofString "L" ≠ ofString "pr" by decide,
    show ofString "L" ≠ ofString "col2" by decide,
    show ofString "L" ≠ ofString "c" by decide,
    show ofString "L" ≠ ofString "H" by decide,
    show ofString "H" ≠ ofString "col" by decide,
    show ofString "H" ≠ ofString "dg" by decide,
    show ofString "H" ≠ ofString "pr" by decide,
    show ofString "H" ≠ ofString "col2" by decide,
    show ofString "H" ≠ ofString "c" by decide,
    show ofString "H" ≠ ofString "L" by decide]

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
