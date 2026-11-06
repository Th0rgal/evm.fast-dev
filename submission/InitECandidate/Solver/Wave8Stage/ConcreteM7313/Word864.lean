import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard800
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle864
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 20000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word864
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition PrefixChecks.Shard800

wave8_certified_reduce allocated := WordToWord.wordAllocWith RegAlloc.regAllocExecutable
  name riscvConfig (oracleCompilerConfig []).wordToWordConf.regAlg registers
  prefixProgram oracle864
wave8_certified_reduce program := WordRemove.removeMustTerminate allocated

theorem wordFunction_eq : wordFunction oracle864 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq, program_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word864
