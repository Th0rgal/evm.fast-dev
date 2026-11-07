import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk27
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames26
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.FrameState27
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames27
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Solver.Wave8Stage

wave8_kernel_reduce info := StackRawCall.collectInfo Chunk27.bodies Frames26.info

theorem info_eq_frameState27 : info = FrameState27.info := rfl

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames27
