import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsInit

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsSplit
open InitE Flapjack Lean Flapjack.Pancake.PanLang

local cbv_simproc ↓ freezeCodec (Flapjack.Pancake.PanLang.progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezePerm (fpermHOL _ _ _) := fun _ => return .rfl (done := true)

wave8_list_spine header := ConcreteCompilerGlobalsRename.renamed.take 77
wave8_list_spine functions := ConcreteCompilerGlobalsRename.renamed.drop 77

theorem split : ConcreteCompilerGlobalsRename.renamed = header ++ functions := by
  rw [← header_eq, ← functions_eq]
  exact (List.take_append_drop 77 ConcreteCompilerGlobalsRename.renamed).symm

theorem allFunctions : ∀ declaration ∈ functions, isFunctionHOL declaration = true := by
  apply List.all_eq_true.mp
  decide +kernel

end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsSplit
