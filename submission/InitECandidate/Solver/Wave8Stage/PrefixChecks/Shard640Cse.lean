import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard640Dead
import InitECandidate.Solver.Wave8Stage.CertifiedCse

/-! Stage 5 CSE pass for `Shard640` (`Function704`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 256000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 128000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard640
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_certified_cse common := dead

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard640
