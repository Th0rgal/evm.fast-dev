import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Frame
open InitE Flapjack Flapjack.Compiler.Backend
open BackendDecomposition PrefixChecks.Shard87

wave8_certified_reduce maximum := maxVarHOL Word151.program

noncomputable def stackArguments := arity - registers
noncomputable def stackVariables := max ((maximum / 2 + 1) - registers) stackArguments
noncomputable def frame := if stackVariables = 0 then 0 else stackVariables + 1

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Frame
