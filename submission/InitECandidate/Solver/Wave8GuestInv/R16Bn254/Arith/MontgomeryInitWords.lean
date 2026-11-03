import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryInitTrace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The state inside a sequence of word declarations. -/
def montSetWords {F : Type} (s : PanSemStateFiniteExact 64 F)
    (assignments : List (String × BitVec 64)) : PanSemStateFiniteExact 64 F :=
  assignments.foldl (fun state ne => setVarHOLFinite (ofString ne.1) (.val (.word ne.2)) state) s

theorem montSetWords_code {F : Type} (s : PanSemStateFiniteExact 64 F)
    (assignments : List (String × BitVec 64)) :
    (montSetWords s assignments).code = s.code := by
  induction assignments generalizing s with
  | nil => rfl
  | cons ne rest ih => exact ih _

theorem montSetWords_lookup_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (assignments : List (String × BitVec 64)) (key : MlS)
    (hfree : ∀ ne ∈ assignments, key ≠ ofString ne.1) :
    (montSetWords s assignments).locals.lookup key = s.locals.lookup key := by
  induction assignments generalizing s with
  | nil => rfl
  | cons ne rest ih =>
    have hn := hfree ne (List.mem_cons_self)
    have hr := ih (setVarHOLFinite (ofString ne.1) (.val (.word ne.2)) s)
      (fun item hi => hfree item (List.mem_cons_of_mem _ hi))
    exact hr.trans (by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn])

/-- A unique declared name has exactly its assigned word after the entire
initializer sequence, independently of the initial local map. -/
theorem montSetWords_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    (assignments : List (String × BitVec 64)) (name : String) (word : BitVec 64)
    (hn : (assignments.map (fun ne => ofString ne.1)).Nodup)
    (hm : (name,word) ∈ assignments) :
    (montSetWords s assignments).locals.lookup (ofString name) = some (.val (.word word)) := by
  induction assignments generalizing s with
  | nil => simp at hm
  | cons ne rest ih =>
    obtain ⟨n,v⟩ := ne
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | hmem
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hfree : ∀ item ∈ rest, ofString name ≠ ofString item.1 := by
        intro item hi heq
        exact hnd.1 (List.mem_map.mpr ⟨item, hi, heq.symm⟩)
      exact (montSetWords_lookup_other (setVarHOLFinite (ofString name) (.val (.word word)) s)
        rest (ofString name) hfree).trans (by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    · exact ih (setVarHOLFinite (ofString n) (.val (.word v)) s) hnd.2 hmem

end InitECandidate.Solver.Wave8GuestInv.Arith
