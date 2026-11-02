import InitECandidate.Solver.Wave8Stage.ConcreteCompilerLoop
import InitECandidate.Solver.Wave8Stage.CompilerPipelineComposition

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerWord
open InitE Flapjack Lean

wave8_list_spine source := loopToWordCompileHOL ConcreteCompilerLoop.source

theorem compile_eq : panToWordCompileProgHOL .riscv sourceDeclarations = source := by
  exact CompilerPipelineComposition.assemble .riscv sourceDeclarations
    ConcreteCompilerSource.source ConcreteCompilerSimp.source ConcreteCompilerStruct.source
    ConcreteCompilerGlobals.source ConcreteCompilerCrep.source ConcreteCompilerLoop.source source
    ConcreteCompilerSource.source_eq ConcreteCompilerSimp.source_eq
    ConcreteCompilerStruct.source_eq ConcreteCompilerGlobals.compile_eq
    ConcreteCompilerCrep.source_eq ConcreteCompilerLoop.source_eq source_eq

end InitECandidate.Solver.Wave8Stage.ConcreteCompilerWord
