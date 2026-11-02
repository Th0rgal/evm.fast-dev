import InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrep

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerLoop
open InitE Flapjack Lean

wave8_list_spine source := compileProgHOLExact .riscv ConcreteCompilerCrep.source

#print axioms source_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerLoop
