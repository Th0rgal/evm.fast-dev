import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk50
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames49
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.GlobalFrameInfo

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames50
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Solver.Wave8Stage

wave8_kernel_reduce info := StackRawCall.collectInfo Chunk50.bodies Frames49.info

theorem info_eq_global : info = GlobalFrameInfo.info := rfl

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames50
