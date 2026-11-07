import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk29
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames28

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames29
open Flapjack Flapjack.Compiler.Backend

wave8_certified_reduce info := StackRawCall.collectInfo Chunk29.bodies Frames28.info

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames29
