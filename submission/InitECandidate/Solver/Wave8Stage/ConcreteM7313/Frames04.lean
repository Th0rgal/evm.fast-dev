import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames03

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames04
open Flapjack Flapjack.Compiler.Backend

wave8_certified_reduce info := StackRawCall.collectInfo Chunk04.bodies Frames03.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames04
