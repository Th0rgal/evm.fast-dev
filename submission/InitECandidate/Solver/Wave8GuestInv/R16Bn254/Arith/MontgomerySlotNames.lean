import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomerySlots

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack.Basis.Pure.MlString

theorem montAName_scratch_all (i : Fin 8) :
    montAName i ≠ ofString "H" ∧
    montAName i ≠ ofString "L" ∧
    montAName i ≠ ofString "c" ∧
    montAName i ≠ ofString "col2" ∧
    montAName i ≠ ofString "pr" ∧
    montAName i ≠ ofString "dg" ∧
    montAName i ≠ ofString "col" := by
  fin_cases i <;> decide

theorem montBName_scratch_all (i : Fin 8) :
    montBName i ≠ ofString "H" ∧
    montBName i ≠ ofString "L" ∧
    montBName i ≠ ofString "c" ∧
    montBName i ≠ ofString "col2" ∧
    montBName i ≠ ofString "pr" ∧
    montBName i ≠ ofString "dg" ∧
    montBName i ≠ ofString "col" := by
  fin_cases i <;> decide

theorem montMName_scratch_all (i : Fin 8) :
    montMName i ≠ ofString "H" ∧
    montMName i ≠ ofString "L" ∧
    montMName i ≠ ofString "c" ∧
    montMName i ≠ ofString "col2" ∧
    montMName i ≠ ofString "pr" ∧
    montMName i ≠ ofString "dg" ∧
    montMName i ≠ ofString "col" := by
  fin_cases i <;> decide

theorem montUName_scratch_all (i : Fin 7) :
    montUName i ≠ ofString "H" ∧
    montUName i ≠ ofString "L" ∧
    montUName i ≠ ofString "c" ∧
    montUName i ≠ ofString "col2" ∧
    montUName i ≠ ofString "pr" ∧
    montUName i ≠ ofString "dg" ∧
    montUName i ≠ ofString "col" := by
  fin_cases i <;> decide

theorem montAName_ne_montMName (i : Fin 8) (j : Fin 8) : montAName i ≠ montMName j := by
  fin_cases i <;> fin_cases j <;> decide

theorem montBName_ne_montMName (i : Fin 8) (j : Fin 8) : montBName i ≠ montMName j := by
  fin_cases i <;> fin_cases j <;> decide

theorem montAName_ne_montUName (i : Fin 8) (j : Fin 7) : montAName i ≠ montUName j := by
  fin_cases i <;> fin_cases j <;> decide

theorem montBName_ne_montUName (i : Fin 8) (j : Fin 7) : montBName i ≠ montUName j := by
  fin_cases i <;> fin_cases j <;> decide

theorem montMName_ne_montUName (i : Fin 8) (j : Fin 7) : montMName i ≠ montUName j := by
  fin_cases i <;> fin_cases j <;> decide

theorem montMName_injective : Function.Injective montMName := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem montUName_injective : Function.Injective montUName := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
