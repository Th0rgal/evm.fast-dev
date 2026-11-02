import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsHeader

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsFunctions
open InitE Flapjack Lean Flapjack.Pancake.PanLang

local cbv_simproc ↓ freezeCodec (progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezePerm (fpermHOL _ _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeGlobals (compileProgExactHOL _ _) := fun _ => return .rfl (done := true)

wave8_list_spine compiled := ConcreteCompilerGlobalsSplit.functions.map (fun declaration =>
  match declaration with
  | .function function => DeclHOL.function { function with
      body := compileProgExactHOL ConcreteCompilerGlobalsHeader.compiled.2.2.2 function.body }
  | _ => DeclHOL.name (Flapjack.Basis.Pure.MlString.ofString "") [])

#print axioms compiled_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsFunctions
