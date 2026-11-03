import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryOperands
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

/-- Product accumulation retains a word in the product scratch slot. -/
theorem montAccTrace_pr_word {F : Type} {s final : PanSemStateFiniteExact 64 F}
    {expressions : List (ExpHOL 64 × ExpHOL 64)} (h : MontAccTrace s expressions final) :
    (∃ w : BitVec 64, s.locals.lookup (ofString "pr") = some (.val (.word w))) →
    ∃ w : BitVec 64, final.locals.lookup (ofString "pr") = some (.val (.word w)) := by
  induction h with
  | nil => exact id
  | cons oldPr low high a b ha hb hpr hl hh rest ih =>
    intro _
    apply ih
    refine ⟨a*b, ?_⟩
    simp [montAccState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "H" ≠ ofString "pr" by decide,
      show ofString "L" ≠ ofString "pr" by decide]

/-- Whole upper-column execution, including every product block. -/
theorem montUpperColumn_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (expressions : List (ExpHOL 64 × ExpHOL 64))
    (values : List (BitVec 64 × BitVec 64)) (tail : ProgHOL 64)
    (carry oldPr oldCol oldDest : BitVec 64)
    (hdcol : ofString dest ≠ ofString "col") (hdc : ofString dest ≠ ofString "c")
    (hdL : ofString dest ≠ ofString "L") (hdH : ofString dest ≠ ofString "H")
    (hdpr : ofString dest ≠ ofString "pr")
    (hops : List.Forall₂ (fun es vs =>
      MontOperandValue s es.1 vs.1 ∧ MontOperandValue s es.2 vs.2) expressions values)
    (hpr : s.locals.lookup (ofString "pr") = some (.val (.word oldPr)))
    (hL : s.locals.lookup (ofString "L") = some (.val (.word 0)))
    (hH : s.locals.lookup (ofString "H") = some (.val (.word 0)))
    (hc : s.locals.lookup (ofString "c") = some (.val (.word carry)))
    (hcol : s.locals.lookup (ofString "col") = some (.val (.word oldCol)))
    (hd : s.locals.lookup (ofString dest) = some (.val (.word oldDest))) :
    ∃ accumulated, MontAccTrace s expressions accumulated ∧
      evaluateHOLFiniteState s (montUpperColumn dest expressions tail) =
        evaluateHOLFiniteState (montUpperFinishState accumulated dest
          (montAccWords 0 0 values).1 (montAccWords 0 0 values).2 carry) tail := by
  obtain ⟨accumulated, ht, hl', hh'⟩ :=
    montAccTrace_of_operands values s expressions oldPr 0 0 hops hpr hL hH
  have hc' := (montAccTrace_lookup_other ht (ofString "c") (by decide) (by decide) (by decide)).trans hc
  have hcol' := (montAccTrace_lookup_other ht (ofString "col") (by decide) (by decide) (by decide)).trans hcol
  have hd' := (montAccTrace_lookup_other ht (ofString dest) hdH hdL hdpr).trans hd
  refine ⟨accumulated, ht, ?_⟩
  change evaluateHOLFiniteState s (montAccProducts expressions (montUpperColumn dest [] tail)) = _
  rw [montAccProducts_eval_of_trace ht]
  exact montUpperFinish_eval accumulated dest tail _ _ carry oldCol oldDest
    hdcol hdc hdL hdH hl' hh' hc' hcol' hd'

/-- Whole lower-column execution, including every product block and the
correction-digit assignment. -/
theorem montLowerColumn_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest : String) (expressions : List (ExpHOL 64 × ExpHOL 64))
    (values : List (BitVec 64 × BitVec 64)) (tail : ProgHOL 64)
    (carry oldPr oldCol oldDg oldCol2 oldDest : BitVec 64)
    (hdcol : ofString dest ≠ ofString "col") (hddg : ofString dest ≠ ofString "dg")
    (hdpr : ofString dest ≠ ofString "pr") (hdcol2 : ofString dest ≠ ofString "col2")
    (hdc : ofString dest ≠ ofString "c")
    (hdL : ofString dest ≠ ofString "L") (hdH : ofString dest ≠ ofString "H")
    (hops : List.Forall₂ (fun es vs =>
      MontOperandValue s es.1 vs.1 ∧ MontOperandValue s es.2 vs.2) expressions values)
    (hpr : s.locals.lookup (ofString "pr") = some (.val (.word oldPr)))
    (hL : s.locals.lookup (ofString "L") = some (.val (.word 0)))
    (hH : s.locals.lookup (ofString "H") = some (.val (.word 0)))
    (hc : s.locals.lookup (ofString "c") = some (.val (.word carry)))
    (hcol : s.locals.lookup (ofString "col") = some (.val (.word oldCol)))
    (hdg : s.locals.lookup (ofString "dg") = some (.val (.word oldDg)))
    (hcol2 : s.locals.lookup (ofString "col2") = some (.val (.word oldCol2)))
    (hd : s.locals.lookup (ofString dest) = some (.val (.word oldDest))) :
    ∃ accumulated, MontAccTrace s expressions accumulated ∧
      evaluateHOLFiniteState s (montLowerColumn dest expressions tail) =
        evaluateHOLFiniteState (montLowerFinishState accumulated dest
          (montAccWords 0 0 values).1 (montAccWords 0 0 values).2 carry) tail := by
  obtain ⟨accumulated, ht, hl', hh'⟩ :=
    montAccTrace_of_operands values s expressions oldPr 0 0 hops hpr hL hH
  obtain ⟨lastPr, hpr'⟩ := montAccTrace_pr_word ht ⟨oldPr, hpr⟩
  have hc' := (montAccTrace_lookup_other ht (ofString "c") (by decide) (by decide) (by decide)).trans hc
  have hcol' := (montAccTrace_lookup_other ht (ofString "col") (by decide) (by decide) (by decide)).trans hcol
  have hdg' := (montAccTrace_lookup_other ht (ofString "dg") (by decide) (by decide) (by decide)).trans hdg
  have hcol2' := (montAccTrace_lookup_other ht (ofString "col2") (by decide) (by decide) (by decide)).trans hcol2
  have hd' := (montAccTrace_lookup_other ht (ofString dest) hdH hdL hdpr).trans hd
  refine ⟨accumulated, ht, ?_⟩
  change evaluateHOLFiniteState s (montAccProducts expressions (montLowerColumn dest [] tail)) = _
  rw [montAccProducts_eval_of_trace ht]
  exact montLowerFinish_eval accumulated dest tail _ _ carry oldCol oldDg lastPr oldCol2 oldDest
    hdcol hddg hdpr hdcol2 hdc hdL hdH hl' hh' hc' hcol' hdg' hpr' hcol2' hd'

end InitECandidate.Solver.Wave8GuestInv.Arith
