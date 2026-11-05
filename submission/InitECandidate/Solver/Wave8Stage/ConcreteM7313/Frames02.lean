import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk02
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames01

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames02
open Flapjack Flapjack.Compiler.Backend

wave8_certified_reduce info := StackRawCall.collectInfo Chunk02.bodies Frames01.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames02
