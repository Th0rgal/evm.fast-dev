import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomerySlotNames
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryFinishFrame

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

/-- Assigning a word preserves word typing of every already-typed local. -/
theorem montWordLocal_set {F : Type} (s : PanSemStateFiniteExact 64 F)
    (key name : MlS) (word : BitVec 64)
    (h : ∃ w : BitVec 64, s.locals.lookup key = some (.val (.word w))) :
    ∃ w : BitVec 64, (setVarHOLFinite name (.val (.word word)) s).locals.lookup key =
      some (.val (.word w)) := by
  by_cases he : name = key
  · subst name
    exact ⟨word, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  · obtain ⟨w, hw⟩ := h
    exact ⟨w, by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, he] using hw⟩

/-- The lower finishing block preserves the complete digit-local invariant. -/
theorem montSlots_lower_finish {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry low high : BitVec 64}
    (hs : MontSlots s a b m u carry low high) (dest : String) (i : Fin 8)
    (hdest : ofString dest = montMName i) :
    MontSlots (montLowerFinishState s dest low high carry) a b
      (Function.update m i (fqCorrectionWord (montLow32 (low+carry)))) u
      (montLowerCarryWord low high carry) 0 0 := by
  obtain ⟨hH, hL, hc, hcol2, hpr, hdg, hcol⟩ := montMName_scratch_all i
  rw [← hdest] at hH hL hc hcol2 hpr hdg hcol
  have hout := montLowerFinish_lookup_dest s dest low high carry hH hL hc hcol2 hpr
  have hacc := montLowerFinish_lookup_acc s dest low high carry
  refine ⟨?_, ?_, ?_, ?_, hacc.2.2, hacc.1, hacc.2.1, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montAName_scratch_all j
    have hne : montAName j ≠ ofString dest := by
      rw [hdest]
      exact montAName_ne_montMName j i
    exact (montLowerFinish_lookup_other s dest low high carry (montAName j)
      hjH hjL hjc hjcol2 hjpr hne hjdg hjcol).trans (hs.aWords j)
  · intro j
    obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montBName_scratch_all j
    have hne : montBName j ≠ ofString dest := by
      rw [hdest]
      exact montBName_ne_montMName j i
    exact (montLowerFinish_lookup_other s dest low high carry (montBName j)
      hjH hjL hjc hjcol2 hjpr hne hjdg hjcol).trans (hs.bWords j)
  · intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self, ← hdest] using hout
    · rw [Function.update_of_ne hj]
      obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montMName_scratch_all j
      have hne : montMName j ≠ ofString dest := by
        rw [hdest]
        exact fun he => hj (montMName_injective he)
      exact (montLowerFinish_lookup_other s dest low high carry (montMName j)
        hjH hjL hjc hjcol2 hjpr hne hjdg hjcol).trans (hs.mWords j)
  · intro j
    obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montUName_scratch_all j
    have hne : montUName j ≠ ofString dest := by
      rw [hdest]
      exact Ne.symm (montMName_ne_montUName i j)
    exact (montLowerFinish_lookup_other s dest low high carry (montUName j)
      hjH hjL hjc hjcol2 hjpr hne hjdg hjcol).trans (hs.uWords j)
  · unfold montLowerFinishState
    repeat apply montWordLocal_set
    exact hs.productWord
  · unfold montLowerFinishState
    repeat apply montWordLocal_set
    exact hs.columnWord
  · unfold montLowerFinishState
    repeat apply montWordLocal_set
    exact hs.column2Word
  · unfold montLowerFinishState
    repeat apply montWordLocal_set
    exact hs.digitWord

/-- The upper finishing block preserves the complete digit-local invariant. -/
theorem montSlots_upper_finish {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry low high : BitVec 64}
    (hs : MontSlots s a b m u carry low high) (dest : String) (i : Fin 7)
    (hdest : ofString dest = montUName i) :
    MontSlots (montUpperFinishState s dest low high carry) a b
      m (Function.update u i (montLow32 (low+carry)))
      (montUpperCarryWord low high carry) 0 0 := by
  obtain ⟨hH, hL, hc, hcol2, hpr, hdg, hcol⟩ := montUName_scratch_all i
  rw [← hdest] at hH hL hc hcol2 hpr hdg hcol
  have hout := montUpperFinish_lookup_dest s dest low high carry hH hL hc
  have hacc := montUpperFinish_lookup_acc s dest low high carry
  refine ⟨?_, ?_, ?_, ?_, hacc.2.2, hacc.1, hacc.2.1, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montAName_scratch_all j
    have hne : montAName j ≠ ofString dest := by
      rw [hdest]
      exact montAName_ne_montUName j i
    exact (montUpperFinish_lookup_other s dest low high carry (montAName j)
      hjH hjL hjc hne hjcol).trans (hs.aWords j)
  · intro j
    obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montBName_scratch_all j
    have hne : montBName j ≠ ofString dest := by
      rw [hdest]
      exact montBName_ne_montUName j i
    exact (montUpperFinish_lookup_other s dest low high carry (montBName j)
      hjH hjL hjc hne hjcol).trans (hs.bWords j)
  · intro j
    obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montMName_scratch_all j
    have hne : montMName j ≠ ofString dest := by
      rw [hdest]
      exact montMName_ne_montUName j i
    exact (montUpperFinish_lookup_other s dest low high carry (montMName j)
      hjH hjL hjc hne hjcol).trans (hs.mWords j)
  · intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self, ← hdest] using hout
    · rw [Function.update_of_ne hj]
      obtain ⟨hjH, hjL, hjc, hjcol2, hjpr, hjdg, hjcol⟩ := montUName_scratch_all j
      have hne : montUName j ≠ ofString dest := by
        rw [hdest]
        exact fun he => hj (montUName_injective he)
      exact (montUpperFinish_lookup_other s dest low high carry (montUName j)
        hjH hjL hjc hne hjcol).trans (hs.uWords j)
  · unfold montUpperFinishState
    repeat apply montWordLocal_set
    exact hs.productWord
  · unfold montUpperFinishState
    repeat apply montWordLocal_set
    exact hs.columnWord
  · unfold montUpperFinishState
    repeat apply montWordLocal_set
    exact hs.column2Word
  · unfold montUpperFinishState
    repeat apply montWordLocal_set
    exact hs.digitWord

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
