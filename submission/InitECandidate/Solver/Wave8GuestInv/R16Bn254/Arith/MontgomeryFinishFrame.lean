import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryLower
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryUpper

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The lower finishing block preserves every digit except its destination. -/
theorem montLowerFinish_lookup_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64) (key : MlS)
    (hH : key ≠ ofString "H") (hL : key ≠ ofString "L") (hc : key ≠ ofString "c")
    (hcol2 : key ≠ ofString "col2") (hpr : key ≠ ofString "pr")
    (hd : key ≠ ofString dest) (hdg : key ≠ ofString "dg") (hcol : key ≠ ofString "col") :
    (montLowerFinishState s dest low high carry).locals.lookup key = s.locals.lookup key := by
  simp [montLowerFinishState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    Ne.symm hH, Ne.symm hL, Ne.symm hc, Ne.symm hcol2, Ne.symm hpr, Ne.symm hd,
    Ne.symm hdg, Ne.symm hcol]

/-- The upper finishing block preserves every digit except its destination. -/
theorem montUpperFinish_lookup_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64) (key : MlS)
    (hH : key ≠ ofString "H") (hL : key ≠ ofString "L") (hc : key ≠ ofString "c")
    (hd : key ≠ ofString dest) (hcol : key ≠ ofString "col") :
    (montUpperFinishState s dest low high carry).locals.lookup key = s.locals.lookup key := by
  simp [montUpperFinishState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    Ne.symm hH, Ne.symm hL, Ne.symm hc, Ne.symm hd, Ne.symm hcol]

theorem montLowerFinish_lookup_dest {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64)
    (hH : ofString dest ≠ ofString "H") (hL : ofString dest ≠ ofString "L")
    (hc : ofString dest ≠ ofString "c") (hcol2 : ofString dest ≠ ofString "col2")
    (hpr : ofString dest ≠ ofString "pr") :
    (montLowerFinishState s dest low high carry).locals.lookup (ofString dest) =
      some (.val (.word (fqCorrectionWord (montLow32 (low+carry))))) := by
  simp [montLowerFinishState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    Ne.symm hH, Ne.symm hL, Ne.symm hc, Ne.symm hcol2, Ne.symm hpr]

theorem montUpperFinish_lookup_dest {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64)
    (hH : ofString dest ≠ ofString "H") (hL : ofString dest ≠ ofString "L")
    (hc : ofString dest ≠ ofString "c") :
    (montUpperFinishState s dest low high carry).locals.lookup (ofString dest) =
      some (.val (.word (montLow32 (low+carry)))) := by
  simp [montUpperFinishState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    Ne.symm hH, Ne.symm hL, Ne.symm hc]

theorem montLowerFinish_lookup_acc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64) :
    (montLowerFinishState s dest low high carry).locals.lookup (ofString "L") = some (.val (.word 0)) ∧
    (montLowerFinishState s dest low high carry).locals.lookup (ofString "H") = some (.val (.word 0)) ∧
    (montLowerFinishState s dest low high carry).locals.lookup (ofString "c") =
      some (.val (.word (montLowerCarryWord low high carry))) := by
  simp [montLowerFinishState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "H" ≠ ofString "L" by decide,
    show ofString "H" ≠ ofString "c" by decide,
    show ofString "L" ≠ ofString "c" by decide]

theorem montUpperFinish_lookup_acc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (low high carry : BitVec 64) :
    (montUpperFinishState s dest low high carry).locals.lookup (ofString "L") = some (.val (.word 0)) ∧
    (montUpperFinishState s dest low high carry).locals.lookup (ofString "H") = some (.val (.word 0)) ∧
    (montUpperFinishState s dest low high carry).locals.lookup (ofString "c") =
      some (.val (.word (montUpperCarryWord low high carry))) := by
  simp [montUpperFinishState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "H" ≠ ofString "L" by decide,
    show ofString "H" ≠ ofString "c" by decide,
    show ofString "L" ≠ ofString "c" by decide]

end InitECandidate.Solver.Wave8GuestInv.Arith
