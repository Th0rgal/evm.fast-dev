import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryFinishSlots

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

theorem montAccTrace_code {F : Type} {s final : PanSemStateFiniteExact 64 F}
    {expressions : List (ExpHOL 64 × ExpHOL 64)} (h : MontAccTrace s expressions final) :
    final.code = s.code := by
  induction h with
  | nil => rfl
  | cons oldPr low high a b ha hb hpr hl hh rest ih => exact ih

/-- A whole lower column preserves the complete local invariant while
executing the exact source block. Numeric bounds are supplied separately. -/
theorem montLowerStep {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry : BitVec 64}
    (hs : MontSlots s a b m u carry 0 0) (dest : String) (i : Fin 8)
    (hdest : ofString dest = montMName i)
    (expressions : List (ExpHOL 64 × ExpHOL 64)) (values : List (BitVec 64 × BitVec 64))
    (hops : List.Forall₂ (fun es vs =>
      MontOperandValue s es.1 vs.1 ∧ MontOperandValue s es.2 vs.2) expressions values)
    (tail : ProgHOL 64) :
    let low := (montAccWords 0 0 values).1
    let high := (montAccWords 0 0 values).2
    ∃ final, MontSlots final a b (Function.update m i (fqCorrectionWord (montLow32 (low+carry)))) u
        (montLowerCarryWord low high carry) 0 0 ∧
      final.code = s.code ∧
      evaluateHOLFiniteState s (montLowerColumn dest expressions tail) =
        evaluateHOLFiniteState final tail := by
  obtain ⟨accumulated, ht, hslots⟩ := montSlots_accumulate hs expressions values hops
  let low := (montAccWords 0 0 values).1
  let high := (montAccWords 0 0 values).2
  refine ⟨montLowerFinishState accumulated dest low high carry,
    montSlots_lower_finish hslots dest i hdest, (by exact montAccTrace_code (final := accumulated) ht), ?_⟩
  obtain ⟨hH, hL, hc, hcol2, hpr, hdg, hcol⟩ := montMName_scratch_all i
  rw [← hdest] at hH hL hc hcol2 hpr hdg hcol
  obtain ⟨oldCol, hOldCol⟩ := hslots.columnWord
  obtain ⟨oldDg, hOldDg⟩ := hslots.digitWord
  obtain ⟨oldPr, hOldPr⟩ := hslots.productWord
  obtain ⟨oldCol2, hOldCol2⟩ := hslots.column2Word
  change evaluateHOLFiniteState s (montAccProducts expressions (montLowerColumn dest [] tail)) = _
  rw [montAccProducts_eval_of_trace ht]
  apply montLowerFinish_eval accumulated dest tail low high carry oldCol oldDg oldPr oldCol2 (m i)
    hcol hdg hpr hcol2 hc hL hH hslots.lowWord hslots.highWord hslots.carryWord
    hOldCol hOldDg hOldPr hOldCol2
  simpa only [hdest] using hslots.mWords i

/-- A whole upper column preserves the complete local invariant while
executing the exact source block. Numeric bounds are supplied separately. -/
theorem montUpperStep {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry : BitVec 64}
    (hs : MontSlots s a b m u carry 0 0) (dest : String) (i : Fin 7)
    (hdest : ofString dest = montUName i)
    (expressions : List (ExpHOL 64 × ExpHOL 64)) (values : List (BitVec 64 × BitVec 64))
    (hops : List.Forall₂ (fun es vs =>
      MontOperandValue s es.1 vs.1 ∧ MontOperandValue s es.2 vs.2) expressions values)
    (tail : ProgHOL 64) :
    let low := (montAccWords 0 0 values).1
    let high := (montAccWords 0 0 values).2
    ∃ final, MontSlots final a b m (Function.update u i (montLow32 (low+carry)))
        (montUpperCarryWord low high carry) 0 0 ∧
      final.code = s.code ∧
      evaluateHOLFiniteState s (montUpperColumn dest expressions tail) =
        evaluateHOLFiniteState final tail := by
  obtain ⟨accumulated, ht, hslots⟩ := montSlots_accumulate hs expressions values hops
  let low := (montAccWords 0 0 values).1
  let high := (montAccWords 0 0 values).2
  refine ⟨montUpperFinishState accumulated dest low high carry,
    montSlots_upper_finish hslots dest i hdest, (by exact montAccTrace_code (final := accumulated) ht), ?_⟩
  obtain ⟨hH, hL, hc, hcol2, hpr, hdg, hcol⟩ := montUName_scratch_all i
  rw [← hdest] at hH hL hc hcol2 hpr hdg hcol
  obtain ⟨oldCol, hOldCol⟩ := hslots.columnWord
  change evaluateHOLFiniteState s (montAccProducts expressions (montUpperColumn dest [] tail)) = _
  rw [montAccProducts_eval_of_trace ht]
  apply montUpperFinish_eval accumulated dest tail low high carry oldCol (u i)
    hcol hc hL hH hslots.lowWord hslots.highWord hslots.carryWord hOldCol
  simpa only [hdest] using hslots.uWords i

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
