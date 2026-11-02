import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsSplit

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsHeader
open InitE Flapjack Lean

local cbv_simproc ↓ freezeCodec (Flapjack.Pancake.PanLang.progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezePerm (fpermHOL _ _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeGlobals (compileProgExactHOL _ _) := fun _ => return .rfl (done := true)

wave8_certified_reduce input := ConcreteCompilerGlobalsSplit.header
wave8_certified_reduce result := compileDecsExactHOL ConcreteCompilerGlobalsInit.initial input

noncomputable def compiled := result

theorem compiled_eq :
    compileDecsExactHOL ConcreteCompilerGlobalsInit.initial ConcreteCompilerGlobalsSplit.header = result :=
  (congrArg (compileDecsExactHOL ConcreteCompilerGlobalsInit.initial) input_eq).trans result_eq

end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsHeader
