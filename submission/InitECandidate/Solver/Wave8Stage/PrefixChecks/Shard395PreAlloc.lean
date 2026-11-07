import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard395Copy

/-! Stage 5 final `removeDeadProg` pre-allocation pass for `Shard395` (`Function459`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 256000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 128000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard395
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_chunked_remove_dead prefixProgram := reachable

theorem prefixCompileEq :
    WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith arity
      wordProgram = prefixProgram :=
  preAllocation_step arity
    wordProgram simplified temporary selected ssa dead common copied twoRegister reachable prefixProgram
    simplified_eq temporary_eq selected_eq ssa_eq dead_eq common_eq copied_eq twoRegister_eq reachable_eq prefixProgram_eq

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard395
