import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard92PreAlloc

/-! One original compiler entry, independently checked through named passes (`Shard92` / `Function156`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard92
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_certified_check_program

theorem checkedEntry : ConcreteWordCheckInput.check entry = true := by
  unfold ConcreteWordCheckInput.check
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq]
  exact checkedProgram

wave8_list_spine entries := (ConcreteCompilerWord.source.drop 92).take 1

theorem checked : entries.all ConcreteWordCheckInput.check = true := by
  wave8_all [checkedEntry]

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard92
