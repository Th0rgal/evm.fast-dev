import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard90Ssa
import InitECandidate.Solver.Wave8Stage.CertifiedPreAlloc

/-! Stage 5 initial dead-code elimination (`dead := WordAlloc.removeDeadProg ssa`) for `Shard90` (`Function154`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard90
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_chunked_remove_dead dead := ssa

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard90
