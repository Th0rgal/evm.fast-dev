import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard799Cse
import InitECandidate.Solver.Wave8Stage.CertifiedPreAlloc
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

/-! Stage 5 `copyProp`, `threeToTwoRegProg`, and `removeUnreach` passes for `Shard799` (`Word863`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 256000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 128000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard799
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_kernel_reduce copied := WordCopy.copyProp common
wave8_kernel_reduce twoRegister := WordInst.threeToTwoRegProg riscvConfig.twoRegArith copied
wave8_kernel_reduce reachable := WordUnreach.removeUnreach twoRegister

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard799
