import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Batch00
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000
namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Parts
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition Stack151Frame
wave8_stack151_parts 100 900
end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Parts
