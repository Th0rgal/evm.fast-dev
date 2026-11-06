import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard92Dead

/-! Stage 5 CSE pass for `Shard92` (`Function156`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard92
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_certified_cse common := dead

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard92
