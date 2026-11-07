import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk33
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames32

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames33
open Flapjack Flapjack.Compiler.Backend

wave8_certified_reduce info := StackRawCall.collectInfo Chunk33.bodies Frames32.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames33
