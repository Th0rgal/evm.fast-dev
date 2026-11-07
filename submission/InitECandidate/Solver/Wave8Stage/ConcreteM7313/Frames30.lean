import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk30
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames29

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames30
open Flapjack Flapjack.Compiler.Backend

wave8_certified_reduce info := StackRawCall.collectInfo Chunk30.bodies Frames29.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames30
