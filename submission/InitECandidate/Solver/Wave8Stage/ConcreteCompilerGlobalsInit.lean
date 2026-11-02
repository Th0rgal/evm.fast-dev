import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsRename

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsInit
open InitE Flapjack Lean Flapjack.Pancake.PanLang

local cbv_simproc ↓ freezeCodec (Flapjack.Pancake.PanLang.progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezePerm (fpermHOL _ _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeGlobals (compileProgExactHOL _ _) := fun _ => return .rfl (done := true)

wave8_certified_reduce initial := ({
  globals := HolFiniteMapExact.empty
  globalsSize := 0
  maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64
    ((decShapesHOL ConcreteCompilerGlobalsRename.renamed).map sizeOfShapeHOL).sum } : PanGlobalsContextExact 64)

end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsInit
