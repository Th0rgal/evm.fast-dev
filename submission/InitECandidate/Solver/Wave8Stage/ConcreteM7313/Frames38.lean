import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk38
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames37
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames38
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Solver.Wave8Stage

wave8_kernel_reduce info := StackRawCall.collectInfo Chunk38.bodies Frames37.info
end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames38
