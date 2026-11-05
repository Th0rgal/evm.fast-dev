import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk01
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames00

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames01
open Flapjack Flapjack.Compiler.Backend

wave8_certified_reduce info := StackRawCall.collectInfo Chunk01.bodies Frames00.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames01
