import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInitializers
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomerySlots

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

theorem fqInitAssigned_lookup {F : Type} (s : PanSemStateFiniteExact 64 F) (A B : Limbs256)
    (name : String) (factor : FqInitFactor) (hm : (name,factor) ∈ fqInitSpecs) :
    (montSetWords s (fqInitAssignments A B fqInitSpecs)).locals.lookup (ofString name) =
      some (.val (.word (fqInitValue A B factor))) := by
  apply montSetWords_lookup s (fqInitAssignments A B fqInitSpecs) name (fqInitValue A B factor)
    (fqInitAssignments_nodup A B)
  exact List.mem_map.mpr ⟨(name,factor), hm, rfl⟩

/-- The actual declaration prefix establishes every digit value and scratch
word required by the checked fifteen-column execution. -/
theorem fqInitialState_slots {F : Type} (s : PanSemStateFiniteExact 64 F) (A B : Limbs256) :
    MontSlots (montSetWords s (fqInitAssignments A B fqInitSpecs))
      (limbs256Words A) (limbs256Words B) (fun _ => 0) (fun _ => 0) 0 0 0 := by
  constructor
  · intro i
    fin_cases i
    · exact fqInitAssigned_lookup s A B "a0" (.a 0) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "a1" (.a 1) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "a2" (.a 2) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "a3" (.a 3) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "a4" (.a 4) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "a5" (.a 5) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "a6" (.a 6) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "a7" (.a 7) (by simp [fqInitSpecs])
  · intro i
    fin_cases i
    · exact fqInitAssigned_lookup s A B "b0" (.b 0) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "b1" (.b 1) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "b2" (.b 2) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "b3" (.b 3) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "b4" (.b 4) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "b5" (.b 5) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "b6" (.b 6) (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "b7" (.b 7) (by simp [fqInitSpecs])
  · intro i
    fin_cases i
    · exact fqInitAssigned_lookup s A B "m0" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "m1" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "m2" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "m3" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "m4" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "m5" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "m6" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "m7" .zero (by simp [fqInitSpecs])
  · intro i
    fin_cases i
    · exact fqInitAssigned_lookup s A B "u0" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "u1" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "u2" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "u3" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "u4" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "u5" .zero (by simp [fqInitSpecs])
    · exact fqInitAssigned_lookup s A B "u6" .zero (by simp [fqInitSpecs])
  · exact fqInitAssigned_lookup s A B "c" .zero (by simp [fqInitSpecs])
  · exact fqInitAssigned_lookup s A B "L" .zero (by simp [fqInitSpecs])
  · exact fqInitAssigned_lookup s A B "H" .zero (by simp [fqInitSpecs])
  · exact ⟨0, fqInitAssigned_lookup s A B "pr" .zero (by simp [fqInitSpecs])⟩
  · exact ⟨0, fqInitAssigned_lookup s A B "col" .zero (by simp [fqInitSpecs])⟩
  · exact ⟨0, fqInitAssigned_lookup s A B "col2" .zero (by simp [fqInitSpecs])⟩
  · exact ⟨0, fqInitAssigned_lookup s A B "dg" .zero (by simp [fqInitSpecs])⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
