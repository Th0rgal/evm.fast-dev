import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard58
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle122
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function121

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function122
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition PrefixChecks.Shard58

wave8_certified_reduce allocated := WordToWord.wordAllocWith RegAlloc.regAllocExecutable
  name riscvConfig (oracleCompilerConfig []).wordToWordConf.regAlg registers
  prefixProgram oracle122
wave8_certified_reduce program := WordRemove.removeMustTerminate allocated

theorem wordFunction_eq : wordFunction oracle122 entry = (name, arity, program) := by
  unfold wordFunction
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq,
    allocated_eq, program_eq]

wave8_certified_reduce stackResult := WordToStack.Native.compileProgNative
  riscvConfig false program arity registers Function121.stackResult.2.2

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function122
