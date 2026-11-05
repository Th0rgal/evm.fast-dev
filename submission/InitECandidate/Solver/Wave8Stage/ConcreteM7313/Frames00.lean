import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk00
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackPasses

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames00
open Flapjack Flapjack.Compiler.Backend

wave8_certified_reduce initial := StackRawCall.collectInfo StackPasses.nativeStubs .ln
wave8_certified_reduce info := StackRawCall.collectInfo Chunk00.bodies initial

theorem collected : StackRawCall.collectInfo (StackPasses.nativeStubs ++ Chunk00.bodies)
    .ln = info := by
  rw [TableComposition.collectInfo_append, initial_eq, info_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames00
