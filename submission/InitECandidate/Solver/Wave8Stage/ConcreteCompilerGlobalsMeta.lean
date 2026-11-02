import InitECandidate.Solver.Wave8Stage.CompilerFunctionNames
import InitECandidate.Solver.Wave8Stage.CompilerMetadataReduction

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsMeta
open InitE Flapjack Lean

local cbv_simproc ↓ freezeCodec (Flapjack.Pancake.PanLang.progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)

wave8_list_spine resorted := resortDeclsHOL ConcreteCompilerStruct.source
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

wave8_list_spine names := CompilerFunctionNames.names ConcreteCompilerSource.source

def newName := ofString "main'"

theorem fresh_eq : freshNameMlS (ofString "main") names = newName := by
  have main_mem : ofString "main" ∈ names := by decide +kernel
  have fresh : ofString "main'" ∉ names := by decide +kernel
  rw [freshNameMlS.eq_1]
  simp only [main_mem, ↓reduceIte]
  have append : mlstrAppend (ofString "main") (ofString "'") = ofString "main'" := rfl
  rw [append, freshNameMlS.eq_1]
  simp only [fresh, ↓reduceIte, newName]

theorem newName_eq : newMainNameHOL ConcreteCompilerStruct.source = newName := by
  unfold newMainNameHOL
  change freshNameMlS _ (CompilerFunctionNames.names ConcreteCompilerStruct.source) = _
  rw [CompilerFunctionNames.concrete, names_eq]
  exact fresh_eq

end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsMeta
