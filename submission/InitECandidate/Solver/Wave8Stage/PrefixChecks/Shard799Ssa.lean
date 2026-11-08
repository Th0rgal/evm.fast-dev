import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard799Prefix
import InitECandidate.Solver.Wave8Stage.CertifiedPreAlloc

/-! Stage 5 SSA pass for `Shard799` (`Word863`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 256000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 128000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard799
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_certified_reduce ssa := WordAlloc.fullSsaCcTrans arity selected

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard799
