import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87Prefix
import InitECandidate.Solver.Wave8Stage.CertifiedCse

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 100000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend

wave8_certified_cse common := dead

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard87
