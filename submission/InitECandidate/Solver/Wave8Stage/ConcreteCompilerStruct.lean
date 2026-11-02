import InitECandidate.Solver.Wave8Stage.ConcreteCompilerSimp
import InitECandidate.Solver.Wave8Stage.CompilerMetadataReduction
import InitECandidate.Solver.Wave8Stage.CompilerStructContext
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000
open InitE Flapjack Lean
/-! Kernel-certified declaration-list structure; function-body reductions
are deliberately deferred to the individual concrete function checks. -/

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerStruct
local cbv_simproc ↓ freezeCodec (Flapjack.Pancake.PanLang.progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)
open Flapjack.Pancake.PanStructs.CompileShapeExact

/- Compute shared structure metadata once, before capturing it in every
declaration. This avoids repeatedly scanning the complete source list. -/
wave8_certified_reduce namesContext := getNamesExact
  ({ structs := [], locals := [], globals := [] } : ContextExact) ConcreteCompilerSimp.source

wave8_certified_reduce globalsContext := CompilerStructContext.finalContext
  namesContext ConcreteCompilerSimp.source

wave8_list_spine rendered := CompilerStructContext.render
  namesContext globalsContext ConcreteCompilerSimp.source
noncomputable def source := rendered

theorem source_eq : compileTopExact ConcreteCompilerSimp.source = source := by
  change (compileDeclsExact _ ConcreteCompilerSimp.source).1 = source
  rw [namesContext_eq, CompilerStructContext.compile_eq]
  change CompilerStructContext.render namesContext
    (CompilerStructContext.finalContext namesContext ConcreteCompilerSimp.source)
    ConcreteCompilerSimp.source = source
  rw [globalsContext_eq]
  exact rendered_eq

end InitECandidate.Solver.Wave8Stage.ConcreteCompilerStruct
